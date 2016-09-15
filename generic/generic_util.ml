(** Namespace of utility modules.

The modules in this namespace provide useful functions on standard datatypes.
They have no particular tie to the generic library, except for module {!Sum} which
exports the type representation of the types that it defines.
*)

(** Type application and defunctionalisation. *)
module App = Generic_util_app

(** Display the memory representation of OCaml values. *)
module Obj_inspect = Generic_util_obj_inspect

(** Functions that directly manipulate the memory representation of ocaml values. *)
module Objx = Generic_util_obj

(** Extra functions on hashtables *)
module Hash = Generic_util_hash

(** Iterative functions. *)
module Iter = Generic_util_iter

(** Useful functions on lists. *)
module Listx = Generic_util_list

(** Miscellaneous definitions. *)
module Misc = Generic_util_misc

(** Function combinators. *)
module Fun = Generic_util_fun

(** Empty and Sum datatypes. *)
module Sum = Generic_util_sum
