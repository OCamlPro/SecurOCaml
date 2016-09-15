open Generic_core
open Generic_util

open App.T
open Ty.T
open Product.Build

let local_invalid_arg s = invalid_arg ("Generic_core_desc_fun." ^ s)

let cons = Desc.Variant.cons
let c0 = Desc.Con.c0
let cn = Desc.Con.make

(***************************************************)
let cons_option t = cons
  [ c0 "None" None
  ; cn "Some" (p1 t)
           (fun (x,()) -> Some x)
           (function Some x -> Some (x,()) | _ -> None)
  ]
let cons_list t = cons
  [ c0 "[]" []
  ; cn "::" (p2 t (Ty.T.List t))
           (fun (x,(xs,())) -> x :: xs)
           (function x :: xs -> Some (x,(xs,())) | _ -> None)
  ]
(* Using the (unsafe) magic trick
let cons_list t = consM (fun {m} ->
  [ cM0 "[]" []
  ; cM2 "::" (m :: m) (t, List t)
  ])
 *)
let cons_bool = cons
  [ c0 "false" false
  ; c0 "true" true
  ]

(***************************************************)
type tag = Tag
type (_,_) app += App : 'a Desc.t -> ('a, tag) app

let unapp (App x) = x

type desc_fun =
  { f : 'a . 'a ty -> 'a Desc.t }

let desc_closure = Extensible.create "Generic_core_desc_fun.view" (* private *)

let view t = unapp (desc_closure.f t)

let ext t f = desc_closure.ext t { f = fun t -> App (f.f t) }

(**************************************************
 * Arrays *)

let array_desc : type a . a ty -> a array Desc.t
  = fun t ->
    let max_array_length = if Ty.eq t Ty.T.Float
      then Sys.max_array_length / 2
      else Sys.max_array_length
    in Desc.Array (t, (module struct
        type t = a array
        type elt = a
        let get = Array.get
        let set = Array.set
        let init = Array.init
        let length = Array.length
        let max_length = max_array_length
      end))
let string_desc =
  Desc.Array (Ty.T.Char, (module struct
      type t = string
      type elt = char
      let get = String.get
      let set x = local_invalid_arg "String.set on a string"
      let init = String.init
      let length = String.length
      let max_length = Sys.max_string_length
    end))

let bytes_desc =
  Desc.Array (Ty.T.Char, (module struct
      type t = bytes
      type elt = char
      let get    = Bytes.get
      let set    = Bytes.set
      let init   = Bytes.init
      let length = Bytes.length
      let max_length = Sys.max_string_length
    end))

(**************************************************)

let fail_desc (_ : 'a ty) = (local_invalid_arg "desc" : 'a Desc.t)

let () =
  begin
    ext Any { f = fun _ -> NoDesc }; (* in particular, [Fun(a,b)] *)

    ext Ty.pair
      { f = fun (type a) (ty : a ty) -> (match ty with
           | Ty.Pair (a,b) -> Product (p2 a b
                                   , { fwd = (fun (x,(y,())) -> (x,y))
                                     ; bck = (fun (x,y) -> (x,(y,())))})
           | _ -> fail_desc ty : a Desc.t)
      };
    ext String
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.String -> (string_desc : a Desc.t)
           | _ -> fail_desc ty
      };
    ext Bytes
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.Bytes -> (bytes_desc : a Desc.t)
           | _ -> fail_desc ty
      };
    ext Ty.array
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.Array t -> (array_desc t : a Desc.t)
           | _ -> fail_desc ty
      };
    ext Bool
      { f = fun (type a) (ty : a ty) -> (match ty with
           | Ty.Bool -> Variant {name = "bool"; cons = cons_bool}
           | _ -> fail_desc ty : a Desc.t)
      };

    ext Ty.option
      { f = fun (type a) (ty : a ty) -> (match ty with
           | Ty.Option a -> Variant {name = "option"; cons = cons_option a}
           | _ -> fail_desc ty : a Desc.t)
      };

    ext Ty.list
      { f = fun (type a) (ty : a ty) -> (match ty with
           | Ty.List a -> Variant {name = "list"; cons = cons_list a}
           | _ -> fail_desc ty : a Desc.t)
      };

    ext Int32
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.Int32 -> Desc.Custom { name = "int32"
                             ; identifier = Generic_util_obj.custom_identifier (Int32.of_int 0)
                             }
           | _ -> fail_desc ty
      };
    ext Int64
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.Int64 -> Desc.Custom { name = "int64"
                             ; identifier = Generic_util_obj.custom_identifier (Int64.of_int 0)
                             }
           | _ -> fail_desc ty
      };
    ext Nativeint
      { f = fun (type a) (ty : a ty) -> match ty with
           | Ty.Nativeint -> Desc.Custom { name = "nativeint"
                                 ; identifier = Generic_util_obj.custom_identifier (Nativeint.of_int 0)
                                 }
           | _ -> fail_desc ty
      };

    ext (Ref Any)
      { f = fun (type a) (ty : a ty) -> (match ty with
           | Ty.Ref t ->
             Record { name = "ref"
                     ; fields = Fcons ( { name = "contents"
                                        ; ty = t
                                        (*; bound = 0 *)
                                        ; set = Some (fun r x -> r := x)
                                        }
                                      , Fnil
                                      )
                     ; iso = { fwd = (fun (x,()) -> ref x)
                             ; bck = (fun r -> (!r, ()))
                             }
                     }
           | _ -> fail_desc ty : a Desc.t)
      };
  end

(*************************************************
 * Extensible types are declared with this function
 *)

let ext_register typat name =
  let cons = Desc.Ext.create() in (* IMPORTANT: the table is created outside the function *)
    ext (Ty.conpat typat)
    { f = fun (type a) (ty : a ty)
          -> (Extensible {name;ty; cons}
              : a Desc.t)
    }

let extensible ty =
  match view ty with
  | Desc.Extensible x -> x
  | _ -> local_invalid_arg "extensible"

(* ext_add_con t {con = f} --> f must match all (x : 'a ty) such that
     Generic_core_patterns.leq x t
 *)
let ext_add_con ty =
  Desc.Ext.add_con (extensible ty)
let ext_iter ty =
  Desc.Ext.iter (extensible ty)
let ext_fold ty =
  Desc.Ext.fold (extensible ty)
let ext_conap ty =
  Desc.Ext.conap (extensible ty)

let () =
  begin
    ext (Ty Any)
    { f = fun (type a) (Ty t : a ty)
          -> (Extensible (Ty_desc.ext t)
              : a Desc.t)
    };
    ext_add_con (Ty Any)
      {con = fun (type a) (Ty Any : a ty) -> (c0 "Any" Any : a Desc.Con.t)};
    ext_add_con (Ty Int32)
      {con = fun (type a) (Ty Int32 : a ty) -> (c0 "Int32" Int32 : a Desc.Con.t)};
    ext_add_con (Ty Int64)
      {con = fun (type a) (Ty Int64 : a ty) -> (c0 "Int64" Int64 : a Desc.Con.t)};
    ext_add_con (Ty Nativeint)
      {con = fun (type a) (Ty Nativeint : a ty) -> (c0 "Nativeint" Nativeint : a Desc.Con.t)};
    ext_add_con (Ty Exn)
      {con = fun (type a) (Ty Exn : a ty) -> (c0 "Exn" Exn : a Desc.Con.t)};
    ext_add_con (Ty Bool)
      {con = fun (type a) (Ty Bool : a ty) -> (c0 "Bool" Bool : a Desc.Con.t)};
    ext_add_con (Ty Int)
      {con = fun (type a) (Ty Int : a ty) -> (c0 "Int" Int : a Desc.Con.t)};
    ext_add_con (Ty Float)
      {con = fun (type a) (Ty Float : a ty) -> (c0 "Float" Float : a Desc.Con.t)};
    ext_add_con (Ty Char)
      {con = fun (type a) (Ty Char : a ty) -> (c0 "Char" Char : a Desc.Con.t)};
    ext_add_con (Ty Bytes)
      {con = fun (type a) (Ty Bytes : a ty) -> (c0 "Bytes" Bytes : a Desc.Con.t)};
    ext_add_con (Ty String)
      {con = fun (type a) (Ty String : a ty) -> (c0 "String" String : a Desc.Con.t)};
    ext_add_con (Ty Ty.option)
      {con = fun (type a) (Ty (Option x) : a ty)
             -> (cn "Option" (p1 (Ty x))
                        (fun (t,()) -> Option t)
                        (function | Option t -> Some (t,()) | _ -> None) : a Desc.Con.t)};
    ext_add_con (Ty Ty.list)
      {con = fun (type a) (Ty (List x) : a ty)
             -> (cn "List" (p1 (Ty x))
                        (fun (t,()) -> List t)
                        (function | List t -> Some (t,()) | _ -> None) : a Desc.Con.t)};
    ext_add_con (Ty (Array Any))
      {con = fun (type a) (Ty (Array x) : a ty)
             -> (cn "Array" (p1 (Ty x))
                        (fun (t,()) -> Array t)
                        (function | Array t -> Some (t,()) | _ -> None) : a Desc.Con.t)};

    ext_add_con (Ty (Ref Any))
      {con = fun (type a) (Ty (Ref x) : a ty)
             -> (cn "Ref" (p1 (Ty x))
                        (fun (t,()) -> Ref t)
                        (function | Ref t -> Some (t,()) | _ -> None) : a Desc.Con.t)};

    ext_add_con (Ty (Lazy Any))
      {con = fun (type a) (Ty (Lazy x) : a ty)
             -> (cn "Lazy" (p1 (Ty x))
                        (fun (t,()) -> Lazy t)
                        (function | Lazy t -> Some (t,()) | _ -> None) : a Desc.Con.t)};

    ext_add_con (Ty (Ty Any))
      {con = fun (type a) (Ty (Ty x) : a ty)
             -> (cn "Ty" (p1 (Ty x))
                        (fun (t,()) -> Ty t)
                        (function | Ty t -> Some (t,()) | _ -> None) : a Desc.Con.t)};
    ext_add_con (Ty Ty.pair)
      {con = fun (type a) (Ty (Pair (x,y)) : a ty)
             -> (cn "Pair" (p2 (Ty x) (Ty y))
                        (fun (x,(y,())) -> Pair(x,y))
                        (function | Pair (x,y) -> Some (x,(y,())) | _ -> None) : a Desc.Con.t)};
  end


let exn_add_con (c : exn Desc.Con.t) =
    ext_add_con Exn {con = fun (type a) (ty : a ty) ->
        match ty with | Exn -> (c : a Desc.Con.t)
                      | _ -> local_invalid_arg "Generic_core_desc_fun.desc_exn" }

let () =
  begin
    ext_register Exn "exn";
    exn_add_con (c0 "Not_found" Not_found);
    exn_add_con (cn "Invalid_argument" (p1 String)
                        (fun (x,()) -> Invalid_argument x)
                        (function Invalid_argument x -> Some (x,()) | _ -> None))
  end
