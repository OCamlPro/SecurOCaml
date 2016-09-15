(** Useful functions on lists. *)

(** [from_to a b = [a; a+1; ... ; b]] *)
let rec from_to a b =
  if a > b then []
  else a :: from_to (a+1) b

(** [replicate n x = [x; x; ...; x]] with [x] repeated [n] times. *)
let rec replicate n x =
  if n <= 0 then [] else x :: replicate (n-1) x

(** [with_indices [x0; x1; ...; xn] = [(0,x0); (1,x1); ... ; (n, xn)]] *)
let with_indices xs =
  let rec go n = function
      [] -> []
    | x :: xs -> (n,x) :: go (n+1) xs
  in go 0 xs

(** Raised by {!sl_insert} when trying to insert an element that is already in the list. *)
exception Insert_duplicate

(** [sl_insert leq x xs] inserts the new element [x] in the sorted list [xs] using the pre-order [<=].
    @raise Insert_duplicate when [x] is already in [xs].
 *)
let rec sl_insert leq x = function
  | [] -> [x]
  | y :: ys as yys ->  if leq x y then
                         if leq y x then raise Insert_duplicate
                         else x :: yys
                       else y :: sl_insert leq x ys


(** Raised by {!match_list}. *)
exception Match_list_failure

(** [match_list] tries to apply a function to the first
   element of a list. If a [Match_failure] is caught, we
   proceed with the rest of the list. If no more element is available (empty list),
   the exception [Match_list_failure] is raised.
   @raise Match_list_failure if the list is empty or if all the elements of the list
caused a [Match_failure].
 *)
let match_list f =
  let rec go = function
    | [] -> raise Match_list_failure
    | h :: t -> try f h
                with Match_failure (_,_,_) -> go t
  in go
