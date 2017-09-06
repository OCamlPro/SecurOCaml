type t = string * int

let dummy = ("d", -1)
let counter = ref (-1)


let fresh n =
  incr counter;
  (n, !counter)

let lfresh () = fresh "v" (* local variable *)
let gfresh () = fresh "g" (* global variable *)
let pfresh () = fresh "p" (* parameter *)

let rec repeat f n =
  if n <= 0 then []
  else f () :: repeat f (n - 1)

(** a list of [n] fresh variables *)
let lfreshn n = repeat lfresh n
let gfreshn n = repeat gfresh n
let pfreshn n = repeat pfresh n

let show (n, x) = n ^ "_" ^ string_of_int x

let print f (n, x) = Format.fprintf f "%s_%d" n x
