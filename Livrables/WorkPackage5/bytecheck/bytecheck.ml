open Types
open Rules
open OByteLib
open Normalised_instr

let parse_type t =
  match t with
  |"Empty" -> Empty
  |"Unit" -> Unit
  |"Bool" -> Bool
  |"Int" -> Int
  |"String" -> String
  |"Char" -> Char
  |"Float" -> Float
  | _ ->

let parse_fun env ret =
  let open Scanf in
  let envt = ref [] in
  let ic = Scanning.from_string env in
  while not (Scanning.end_of_input ic) do
    bscanf ic "%s@;" (fun t -> envt := parse_type t :: !envt)
  done
  (!envt, parse_type ret)

let read_funs filename =
  let open Scanf in
  let ic = Scanning.open_in filename in
  let funs = AddrMap.empty
  while not (Scanning.end_of_input ic) do
    bscanf ic "%d [%s@] %s@\n" (fun p env ret -> funs := AddrMap.add p (parse_fun env ret) !funs)
  done
  Scanning.close_in ic
  !funs

let main () =
  if Array.length (Sys.argv) < 2 then
    prerr_endline ("Error: " ^ Sys.argv.(0) ^ ": expected two filenames")
  else begin
    let cmo = Cmofile.read Sys.argv.(1) in
    let (data, symb, prim, code) = Cmofile.reloc cmo in
    let lencode = Array.length code in
    let funs = read_funs Sys.argv.(2)
    and globals = [||]
    and cfuns = [||] in
    checkcode globals cfuns funs code
  end
;;

main ()
