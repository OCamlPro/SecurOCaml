(** Safe generic marshalling and unmarshalling operations. *)

open Generic_core
open Ty.T

val to_channel : 'a ty -> out_channel -> 'a -> Marshal.extern_flags list -> unit
val from_channel : 'a ty -> in_channel -> 'a

(** Low level functions *)
val to_repr : 'a ty -> 'a -> Obj.t
val from_repr : 'a ty -> Obj.t -> 'a
