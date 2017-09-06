open Types
open OByteLib
open Normalised_instr
open Listx

type addr = int

module Addr = struct type t = addr let compare = Pervasives.compare end
module AddrSet = Set.Make (Addr)
module AddrMap = Map.Make (Addr)

let keys m =
  AddrMap.fold (fun k _ s -> AddrSet.add k s) m AddrSet.empty

let map_of_list l =
  List.fold_left (fun m (k,x) -> AddrMap.add k x m) AddrMap.empty l

type rule = addr * mty -> mty AddrMap.t
type rulemap = Normalised_instr.t -> rule

let checked = ref AddrSet.empty
let tocheck = ref (AddrMap.empty : mty AddrMap.t)

let check rulemap code pc =
  let merge pc t t' = Some (merge_mty t t') in
  if AddrSet.mem pc !checked then () else
  if not (AddrMap.mem pc !tocheck) then invalid_arg "initial type missing" else
    let t = AddrMap.find pc !tocheck in
    let m = rulemap code.(pc) (pc, t) in
    tocheck := AddrMap.union merge m !tocheck;
    checked := AddrSet.add pc !checked


(** rule requirement *)
let require condition =
  if condition then ()
  else invalid_arg "rule requirement unmet"

exception Type_error of int * string

(* rules instr (pc, t)
globals: ty array, types of the global data
cfuns: (ty list * ty) array, type of the c primitives
closures: (ty list * ty) AddrMap.t type of the closures
instr: Normalised_instr.t instruction that is typed-checked
pc: int program counter, i.e. the address of the instruction
t: mty before the instruction is executed.
*)
let rules globals cfuns closures instr (pc, t) =
  let err msg = raise (Type_error (pc, msg)) in
  let open AddrMap in
  let branch = map_of_list in
  let next t = branch [pc + 1, t] in
  match instr with
    | ACC n    -> next {t with acc = List.nth t.stack n}
    | PUSH     -> next {t with stack = t.acc :: t.stack}
    | POP n    -> next {t with stack = pop n t.stack}
    | ASSIGN n -> next {t with stack = set n t.stack t.acc
                             ; acc = Unit}
    | ENVACC n -> next {t with acc = List.nth t.env n}
    | PUSH_RETADDR ptr -> next t

    | APPLY n ->
      let (args, res) = args_res n t.acc in
      let (before, after) = take_pop n t.stack in
      require (is_fun t.acc
               && List.for_all2 (=) args before);
      next {t with acc = res
                 ; stack = after }

    | APPTERM (n, s) ->
      let (args, res) = args_res n t.acc in
      let (before, after) = take_pop n t.stack in
      require (is_fun t.acc
               && List.for_all2 (=) args before);
      next {t with acc = res
                 ; stack = pop (s - n) after }

    | RETURN n ->
      require (t.acc = t.ret
               && List.length t.stack = 0);
      branch []

    | RESTART -> next t
    | GRAB n -> next t

    | CLOSURE (n, ptr) ->
      (try
         let (env,r) = AddrMap.find ptr closures in
         let (before, after) = take_pop n t.stack in
         require (List.for_all2 (=) env (t.acc :: before));
         next {t with acc = r; stack = after}
       with Not_found -> err ("rules.closure"))

    | CLOSUREREC (n, ps) ->
      (try
         let (env,r) = AddrMap.find ps.(0) closures in
         let (before, after) = take_pop n t.stack in
         require (List.for_all2 (=) env (t.acc :: before));
         let st = ref after in
         for i = 1 to Array.length ps - 1 do
           st := snd (AddrMap.find ps.(i) closures) :: !st
         done;
         next {t with acc = r; stack = !st}
       with Not_found -> err ("rules.closure"))


    | OFFSETCLOSURE n ->
      next {t with acc = List.nth t.env n}

    | GETGLOBAL n ->
      next {t with acc = globals.(n)}
    | SETGLOBAL n ->
      require (t.acc = globals.(n));
      next {t with acc = Unit}

    | ATOM tag ->
      next { t with acc = Block (tag , []) }

    | MAKEBLOCK (n, tag) ->
      (* the output type for acc is a block type for which we only know the type of tag [t] *)
      next {t with stack = pop (n - 1) t.stack
                 ; acc = Block (tag , t.acc :: take (n - 1) t.stack)
           }

    | GETFIELD n -> (* the type be a tuple (block with only one constructor) or an array*)
      (match t.acc with
       | Block (_, ts)
       | Variant (_, [ts]) ->
         require (n <= List.length ts);
         next {t with acc = List.nth ts n}
       | _ -> err "rules.getfield")

    | SETFIELD n ->
      (match t.acc with
       | Block (_, ts)
       | Variant (_, [ts]) ->
         require (n <= List.length ts
          && List.length t.stack >= 1
          && List.hd t.stack = List.nth ts n);
         next {t with acc = Unit
                    ; stack = pop 1 t.stack}
       | _ -> err "rules.getfield")

    | MAKEFLOATBLOCK n ->
      next {t with stack = pop (n - 1) t.stack
                 ; acc = Array Float}
    | GETFLOATFIELD n ->
      require (t.acc = Array Float);
      next {t with acc = Float}
    | SETFLOATFIELD n ->
      require (t.acc = Array Float
               && match t.stack with
               | Float :: _ -> true
               | _ -> false);
      next {t with stack = pop 1 t.stack
                 ; acc = Unit}

    | GETVECTITEM ->
      (match t.acc with
       | Array t' ->
         require (List.length t.stack >= 1
                  && List.hd t.stack = Int);
         next {t with stack = pop 1 t.stack
                    ; acc = t'}
       | _ -> err "rules.getvectitem")
    | SETVECTITEM ->
      (match t.acc with
       | Array t' ->
         require (List.length t.stack >= 2
                  && List.hd t.stack = Int
                  && List.nth t.stack 1 = t');
         next {t with stack = pop 2 t.stack
                    ; acc = Unit}
       | _ -> err "rules.setvectitem")

    | GETSTRINGCHAR ->
      require (t.acc = String
               && List.length t.stack >= 1
               && List.hd t.stack = Int);
      next {t with stack = pop 1 t.stack
                 ; acc = Char}

    | SETSTRINGCHAR ->
      require (t.acc = String
               && List.length t.stack >= 2
               && List.hd t.stack = Int
               && List.nth t.stack 1 = Char);
      next {t with stack = pop 2 t.stack
                 ; acc = Unit}

    | BRANCH ptr ->
      branch [ ptr, t ]

    | BRANCHIF ptr
    | BRANCHIFNOT ptr ->
      require (is_bool t.acc);
      branch [ pc + 1, t
          ; ptr, t]
    | SWITCH (iptrs, pptrs) ->
      (match t.acc with
       | Variant (n, cs) ->
         require (n = Array.length iptrs
                  && List.length cs = Array.length pptrs);
         branch (List.map (fun p
                         -> (p, {t with acc = Int}))
                (Array.to_list iptrs)
              @ List.map (fun (p,(tag,ts))
                           -> (p, {t with acc = Block (tag, ts)}))
                (zip (Array.to_list pptrs) (with_index cs)))
       | _ -> err "rules.switch") (* bool ? unit ? int ? *)

    | PUSHTRAP ptr ->
      next {t with stack = Empty :: Empty :: Empty :: Empty :: t.stack}
    | POPTRAP ->
      next {t with stack = pop 4 t.stack}
    | RAISE | RERAISE | RAISE_NOTRACE ->
      branch []

    | CHECK_SIGNALS -> next t

    | C_CALL (n, i) ->
      let (env, r) = cfuns.(i) in
      let (before, after) = take_pop n t.stack in
      require (List.for_all2 (=) env (t.acc :: before));
      next {t with acc = r; stack = after}

    | CONSTINT n ->
      if n == 0 then
        next {t with acc = Unit}
      else if n == 1 then
        next {t with acc = Bool}
      else
        next {t with acc = Int}

    | UNAPP op ->
      (match op with
       | NOT ->
         require (is_bool t.acc);
         next {t with acc = Bool}
       | NEG | OFFSET _ ->
         require (is_int t.acc);
         next {t with acc = Int}
       | ISINT ->
         require (is_int t.acc);
         next {t with acc = Bool}
       | VECTLENGTH ->
         (match t.acc with
          | Block (_,_) | Array _ | String ->
            next {t with acc = Int}
          | _ -> err "rules.vectlength"))

    | BINAPP op ->
      require (is_int t.acc
               && List.length t.stack >= 1
               && List.hd t.stack = Int);
      next {t with acc = Int; stack = pop 1 t.stack}

    | COMPARE op ->
      (match op with
       | EQ | NEQ ->
         require (List.length t.stack >=1
                  && List.hd t.stack == t.acc)
       | _ -> require (is_int t.acc
               && List.length t.stack >= 1
               && List.hd t.stack = Int));
      next {t with acc = Bool; stack = pop 1 t.stack}

    | COMPBRANCH (op, n, ptr) ->
      require (is_int t.acc);
      branch [ pc + 1, t
             ; ptr, t]

    | OFFSETREF ofs ->
      (match t.acc with
       | Block (tag, Int :: ts) ->
         next {t with acc = Unit}
       | _ -> err "rules.offsetref")

(*  | GETMETHOD -> (* the type of the method is only known at runtime (depends on the accumulator's value) *)
    | GETPUBMET tag  (* the type of the method could be known statically if we add type information *)
    | GETDYNMET (* the type of the method is only known at runtime (depends on the accumulator's value) *)
*)
    | STOP -> branch []

let checkcode globals cfuns funs code =
  checked := AddrSet.empty;
  tocheck := AddrMap.empty;
  for pc = 0 to Array.length code - 1 do
    check (rules globals cfuns funs) (Normalised_code.of_code code) pc
  done
