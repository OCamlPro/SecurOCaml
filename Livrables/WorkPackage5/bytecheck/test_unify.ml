open Types

let t1 = Array (Var 1)
let t2 t = Fun (Var 1, t)
let t3 a b = Block (0, [a; t1; t2 b])
let t4 t = t3 t t;;
let t5 = Variant (3, [[Var 1]; [Array Bool]; [Var 2; Int; Unit]])
let t6 = Variant (3, [[Var 2]; [Array Unit]; [Float; Var 1; Int]])
let t7 = Block (0, [Var 1; Var 2; Int])
let t8 = Block (0, [Var 2; Float; Var 1])
let t9 a b = Fun (a,b)
let b3 x y z = Block (0, [x; y; z])
let v3 a b c = Variant (0, [a; b; c])
let b2 n x y = Block (n, [x;y])

let unifying a b =
try print_endline ("Unifying " ^ string_of_ty a ^ " and " ^ string_of_ty b);
  print_endline ("    " ^ string_of_subst (unify [(a, b)] Subst.empty))
with Unification_failure -> print_endline "    failed to unify";;

let merging a b =
 try print_endline ("Merging " ^ string_of_ty a ^ " and " ^ string_of_ty b);
   print_endline ("    "^ string_of_ty (merge_ty a b))
 with Merge_failure -> print_endline "    failed to merge"
    | Unification_failure -> print_endline "    failed to unify";;


unifying (t4 (Var 1)) (t4 Int);;
unifying (t4 (Var 1)) (t3 Int Bool);;
unifying (t2 t1) (t2 Int);;
unifying (Fun (Unit, Var 2)) (t2 (Array Bool));;
unifying t7 t8;;
unifying (Var 1) t1;;
unifying (t9 (Var 1) (Var 2)) (t9 (Var 2) (Var 1));;
unifying (t9 (Var 1) (Var 2)) (t9 (Var 2) (Array (Var 1)));;
unifying (t9 (Var 1) (Var 2)) (t9 (Array (Var 2)) (Array (Var 1)));;

merging Int Bool;;
merging (Array Unit) (Array Bool);;
merging (Array Unit) Bool;;
merging (t3 (Var 1) Bool) (t4 Unit);;
merging (Block (0, [Var 1; Array Int; t2 Bool]))   (t4 Unit);;
merging (Block (1, [Var 1; Array Int; t2 Bool]))   (t4 Unit);;
merging (Fun (Unit, Var 2)) (t2 (Array Bool));;
merging t7 t8;;
merging t5 t6;;
merging (Var 1) t1;;
merging (t9 (Var 1) (Var 2)) (t9 (Var 2) (Var 1));;
merging (t9 (Var 1) (Var 2)) (t9 (Var 2) (Array (Var 1)));;
merging (b3 (Var 1) (Var 2) (Var 3)) (b3 (Var 2) (Var 3) (Var 1));;
merging (b3 (Var 1) (Var 2) (Var 3)) (b3 (Var 2) (Var 3) (Array (Var 1)));;
merging (b2 1 Bool (Array Int)) (v3 [String] [Int; Array Unit] [Int]);;
