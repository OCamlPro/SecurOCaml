(** split a list after [n] elements *)
let rec take_pop n l =
  if n <= 0 then ([], l)
  else match l with
    | [] -> ([], [])
    | h :: t ->
      let (a,b) = take_pop (n-1) t in
      (h :: a, b)

(** remove the first [n] elements from the list
*)
let rec pop n l =
  if n < 0 then invalid_arg "pop: negative argument"
  else if n = 0 then l
  else match l with
    | [] -> invalid_arg "pop: list too small"
    | h :: t -> pop (n - 1) t

(** sets the [n]-th element of the list [l] to [x]
*)
let rec set n l x =
  if n < 0 then invalid_arg "set: negative argument"
  else match l with
    | [] -> invalid_arg "set: list too small"
    | h :: t ->
      if n == 0 then x :: t else
        h :: set (n - 1) t x

(** replicate builds a list of [n] times the same element *)
let rec replicate n x =
  if n <= 0 then []
  else x :: replicate (n - 1) x

(* takes the [n] first elements of a list *)
let rec take n l =
  if n <= 0 then []
  else match l with
    | [] -> [] (* or error *)
    | h :: t -> h :: take (n - 1) t

(** combine two lists element-wise,
the result has the length of the smallest of the two lists
*)
let rec zip a b =
  match a , b with
  | [] , _ | _ , [] -> []
  | x :: xs , y :: ys -> (x , y) :: zip xs ys

(* computes the list (0,x0)...(n,xn) from a list x0..xn *)
let with_index l =
  let rec loop n = function
  | [] -> []
  | x :: t -> (n, x) :: loop (n + 1) t
  in loop 0 l
