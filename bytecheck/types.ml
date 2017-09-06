open Listx

exception Undefined
let todo () = raise Undefined

module Int = struct type t = int let compare = Pervasives.compare end
module Subst = Map.Make (Int)

type num_constant = int (* number of  constant constructor *)
type tag = int (* block tags *)
and ty
  =
  | Empty (* signals an error in type checking *)
  | Unit
  | Bool
  | Int
  | Variant of num_constant * ty list list
  | Block of tag * ty list
  | String
  | Char
  | Float
  | Array of ty
  | Fun of ty * ty
  (*  | Ref of ty *)
  | Var of int
  | Cvar of int (* constant variable *)

module Ty = struct type t = ty let compare = Pervasives.compare end
module TySet = Set.Make (Ty)

type mty (* virtual machine type *)
  = { acc : ty
    ; stack : ty list
    ; env : ty list
    ; ret : ty
    }

let is_bool = function
  | Unit | Bool -> true
  | _ -> false
let is_int = function
  | Unit | Bool | Int -> true
  | _ -> false

let is_block = function
  | Block (_,_) -> true
  | _ -> false

let is_variant = function
  | Unit | Bool | Int | Block (_,_) | Variant (_,_) -> true
  | _ -> false

let is_fun = function
  | Fun (_,_) -> true
  | _ -> false

let is_array = function
  | String | Array _ -> true
  | _ -> false

(* is the term [t] constant? i.e. doesn't contain variables *)
let rec is_constant t = match t with
  | Var n -> false
  | Array t' -> is_constant t'
  | Fun (a, b) -> is_constant a && is_constant b
  | Block (_, ts) -> List.for_all is_constant ts
  | Variant (_, cs) -> List.for_all (List.for_all is_constant) cs
  | _ -> true

(* does variable [n] occur in term [t] ? *)
let rec var_in n t = match t with
  | Var n' -> n = n'
  | Array t' -> var_in n t'
  | Fun (a, b) -> var_in n a || var_in n b
  | Block (_, ts) -> List.exists (var_in n) ts
  | Variant (_, cs) -> List.exists (var_in_cons n) cs
  | _ -> false
and var_in_cons n ts = List.exists (var_in n) ts

(* true if t = Var n *)
let eq_var n t = match t with
  | Var n' -> n = n'
  | _ -> false

(* Computes the n first arguments of a curried function type if possible and the result (which might be a function) *)
let rec args_res n t =
  if n <= 0 then ([], t) else
  match t with
  | Fun (a, b) ->
    let (args, res) = args_res (n - 1) b
    in (a :: args, res)
  | r -> invalid_arg "args_res"

(* applies a substitution [s] to a type [t] *)
let rec subst s t =
  match t with
  | Var k -> (try Subst.find k s
              with Not_found -> t)
  | Empty | Unit | Bool | Int | String | Char | Float | Cvar _
    -> t
  | Array t' -> Array (subst s t')
  | Fun (a, b) -> Fun (subst s a , subst s b)
  | Variant (n, cs) -> Variant (n, subst_cons s cs)
  | Block (n, ts) -> Block (n, subst_list s ts)
and subst_list s = List.map (subst s)
and subst_cons s cs = List.map (subst_list s) cs

let subst1 n t t' =
  subst (Subst.singleton n t) t'

let substeq n t (a,b) = subst1 n t a, subst1 n t b

let substeqs n t g =
  List.map (substeq n t) g

let counter = ref (-1)
let fresh_var () =
  incr counter;
  Var (!counter)


(* Martelli Montanari unification
- Start with a set of equations and apply rules until the set is of the form
G = {x0 = t0, ..., xn = tn} where xn are variables.

RULES:
- DELETE: remove reflexive equations { t = t }
- DECOMPOSE: replace equations { f(s0,...sk) = f(t0,...tk)} with {s0=t0,...sk=tk}
- CONFLICT: fail if trying to unify f(s0,...,sk) = g(t0,...,tm)
- SWAP: put the variables on the left hand side: { f(s0,...,sk) = x } 	-> { x = f(s0,...,sk) }
- ELIMINATE: substitute variables: G u { x = t } 	-> 	G{x := t} u { x = t } 	if x not in vars(t) and x in vars(G)
- CHECK: fail if { x = t } and x appears in the right hand side (other than {x = x})
*)


exception Unification_failure

(* only functions of arity > 0 *)
let decompose t t' = match t , t' with
  | Array t , Array t' -> [(t,t')]
  | Fun (a,b) , Fun (a',b') -> [(a,a'); (b,b')]
  | Block (n, ts), Block (n', ts') ->
    if n <> n' then raise Unification_failure else
      List.combine ts ts'
  | Variant (n, cs), Variant (n', cs') ->
    if n <> n' then raise Unification_failure else
      List.concat (List.map2 List.combine cs cs')
  | _ -> raise Unification_failure

let rec unify g s =
  match g with
  | [] -> s
  | (t, t') :: g' ->
    if t = t' then unify g' s (* delete *)
    else match t with
      | Var n -> if var_in n t' then raise Unification_failure (* check *)
        else unify (substeqs n t' g') (Subst.add n t' s) (* eliminate *)
      | _ -> match t' with
        | Var n -> unify ((t', t) :: g') s (* swap *)
        | _ -> unify (decompose t t' @ g') s

(* MERGE *******************************)
(* SEMANTICS of merge:
there is a subtyping relation on terms:
unit < bool < int < any variant
closed under application (t < t' ==> f t < f t')

merge t t' computes smallest solution (if it exists) that
solves the inequalities:
t < merge t t'  &  t' < merge t t'
*)

exception Merge_failure

(*type merge_eq = Equ of ty * ty | App of (ty list -> ty) * merge_eq list*)
type merged = Mvar of int * ty | Mty of ty | Mapp of (ty list -> ty) * merged list

let rec merge_eq t t' =
  if t = t' then Mty t (* delete *)
  else match t with
    | Var n -> if var_in n t' then raise Merge_failure (* check *)
      else Mvar (n, t') (* eliminate *)
    | _ -> match t' with
      | Var n -> merge_eq t' t (* swap *)
      | _ ->  merge_decompose t t'

and merge_decompose t t' = match t , t' with
  | Unit , Bool
  | Bool , Unit
    -> Mty Bool
  | (Unit | Bool) , Int
  | Int, (Unit | Bool)
    -> Mty Int
  | (Unit | Bool | Int) , Variant (n, cs) -> Mty t'
  | Variant (n, cs) , (Unit | Bool | Int) -> Mty t
  | Block (tag, ts) , Variant (n, cs)
  | Variant (n, cs) , Block (tag, ts)
    -> let ts' = List.nth cs tag in
       Mapp ((fun ts -> Variant (n, Listx.set tag cs ts))
            , List.map2 merge_eq ts ts')
  | Array t , Array t'
    -> Mapp ((function [t] -> Array t
                     | _ -> raise Merge_failure)
            , [merge_eq t t'])
  | Fun (a,b) , Fun (a',b')
    -> Mapp ((function [a;b] -> Fun (a,b)
                     | _ -> raise Merge_failure)
            , List.map2 merge_eq [a;b] [a';b'])
  | Block (n, ts), Block (n', ts')
    -> if n <> n' then raise Merge_failure
       else Mapp ((fun ts -> Block (n, ts)) , List.map2 merge_eq ts ts')
  | Variant (n, cs), Variant (n', cs')
    -> if n <> n' then raise Merge_failure
       else Mapp ((fun ts -> Variant (n, replace_cons ts cs))
                  , List.concat (List.map2 (List.map2 merge_eq) cs cs'))

  | _ -> raise Merge_failure

and replace_cons ts = function
  | [] -> []
  | c :: cs -> let (c', ts') = take_pop (List.length c) ts in
    c' :: replace_cons ts' cs

and collect_vars s m =
  let append _ x y = Some (x @ y) in
  match m with
  | Mvar (n, t) -> Subst.union append (Subst.singleton n [t]) s
  | Mty t -> s
  | Mapp (f, ms) ->
    List.fold_left collect_vars s ms

(* build a graph of dependencies between variables.  it
   should not contain cycles. Start with the sinks and walk
   up the graph applying subst and merge_ty.

   -- Less efficient: iterate over a set of equalities.
   Pick the equalities whose rhs doesn't contain variables, merge
   then substitute in all other rhs and remove from the set
   (add to the result set).
   The algorithm will loop if the graph contains cycles.
*)
(*and solve_vars g s =
  (* true if rhs doesn't contain variables *)
  let cst_rhs n rhs = List.for_all is_constant rhs
  (* substitute (n = t) in the rhs of the map *)
  and subst_rhs n t m = Subst.map (List.map (subst1 n t)) m in
  if Subst.is_empty g then s else
    let (cst, ncst) = Subst.partition cst_rhs g in
    let defs = Subst.map merge_list cst in
    let g' = Subst.fold subst_rhs defs ncst
    and s' = Subst.union (fun _ _ _ -> None) defs s
    in solve_vars g' s'
*)

(* merge the rhs, then subsitute in the original equations
   merge again, remove reflexive equations (x = x)
   check if a variable appears in its own definition
   otherwise return the last merged map.
*)
and solve_vars g =
  (* true if rhs doesn't contain variables *)
  let subst_rhs n t m = Subst.map (List.map (subst1 n t)) m in
  let defs = Subst.map merge_list g in
  let g' = Subst.fold subst_rhs defs g in
  let defs' = Subst.map merge_list g' in
  let rm_id = Subst.filter (fun n t -> not (eq_var n t)) defs' in
  if Subst.exists var_in rm_id then
    raise Merge_failure
  else defs'

(* merge a non-empty  list of terms *)
and merge_list = function
  | [] -> raise Merge_failure
  | (t :: ts) -> List.fold_left merge_ty t ts

and merged s = function
  | Mvar (n, t) -> Subst.find n s
  | Mty t -> subst s t
  | Mapp (f, ms) -> f (List.map (merged s) ms)

and merge_ty t t' =
  let m = merge_eq t t' in
  let s = solve_vars (collect_vars Subst.empty m) in
  merged s m

let merge_mty t t' =
  { acc = merge_ty t.acc t'.acc
  ; stack = List.map2 merge_ty t.stack t'.stack
  ; env = List.map2 merge_ty t.env t'.env
  ; ret = merge_ty t.ret t'.ret
  }


(* printing *)
let rec string_of_list string_of_el sep = function
  | [] -> ""
  | [x] -> string_of_el x
  | x :: (y :: z) -> string_of_el x ^ sep ^ string_of_list string_of_el sep (y :: z)

let string_of_var n = "?" ^ string_of_int n

let rec string_of_ty = function
  | Empty -> "Empty"
  | Unit -> "Unit"
  | Bool -> "Bool"
  | Int -> "Int"
  | Float -> "Float"
  | Char -> "Char"
  | String -> "String"
  | Var n -> string_of_var n
  | Cvar n -> "!" ^ string_of_int n
  | Array t -> "Array (" ^ string_of_ty t ^ ")"
  | Fun (a,b) -> string_of_ty a ^ " -> " ^ string_of_ty b
  | Block (n, ts) -> string_of_block (n, ts)
  | Variant (n, cs) -> "[" ^ string_of_int n ^  ":" ^ string_of_list string_of_cons " | " cs ^"]"
and string_of_block (n, ts) =
  "(" ^ string_of_int n ^  ":" ^ string_of_list string_of_ty ", " ts ^")"
and string_of_cons ts = string_of_list string_of_ty ", " ts

let string_of_def a b (x,y) = a x ^ " := " ^ b y
let string_of_assoc a b abs = "{ " ^ string_of_list (string_of_def a b) " ; " abs ^ " }"

let string_of_subst s =
  string_of_assoc string_of_var string_of_ty (Subst.bindings s)
