type t

val dummy : t
val lfresh : unit -> t
val pfresh : unit -> t
val gfresh : unit -> t

(** a list of [n] fresh local variables *)
val lfreshn : int -> t list

val show : t -> string
val print : Format.formatter -> t -> unit
