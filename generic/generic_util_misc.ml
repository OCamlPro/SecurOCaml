(** Miscellaneous definitions. *)

(** This exception indicate a failure. Used by {!guard}, {!only_if}, {!one_of}, {!get_some}.
*)
exception Failed

(** [guard x] does nothing if [x] is true, but raises {!Failed} if [x] is false. *)
let guard x = if x then () else raise Failed

(** [only_if f x] returns [x] only if [f x] is true.
 @raise Failed when [f x] is false.
*)
let only_if f x = begin guard (f x); x end

(** [one_of xs] tries each action of the list [xs]
in turn until one succeeds (meaning that it does not raise {i any} exception).
@raise Failed If the action list is empty or if all the actions raised an exception.
 *)
let rec one_of = function
  | [] -> raise Failed
  | h::t -> try Lazy.force h
            with _ -> one_of t

(** [erase x] is used when only the side effects of a computation are needed, not its value.
{[erase x = ()]} *)
let erase _ = ()

(** [option f] is the functorial action of the functor ['a option]:
{[Some x -> Some (f x)]}
{[None -> None]}
 *)
let option f = function
  | Some x -> Some (f x)
  | None -> None

(** [unopt s n] eliminates an option value by replacing the constructor [Some] by [s] and [None] by [n].
 *)
let unopt s n = function
  | Some x -> s x
  | None -> n

(** Partial function {[get_some (Some x) = x]}
@raise Failed on None
*)
let get_some = function
  | Some x -> x
  | None -> raise Failed

(** [opt_try x] forces the lazy value [x]. If any exception is raised,
[None] is returned, otherwise [Some x] is returned.
*)
let opt_try x =
  let debug = false in (* during development it may be useful to display the exception *)
  if debug then Some (Lazy.force x)
  else
    try Some (Lazy.force x)
    with _ -> None

(** [some_if f x = Some x] if [f x] is true, [None] otherwise *)
let some_if f x =
  if f x then Some x else None

(** [unopt_try s n x = unopt s n (opt_try x)] *)
let unopt_try s n x =
  unopt s n (opt_try x)
