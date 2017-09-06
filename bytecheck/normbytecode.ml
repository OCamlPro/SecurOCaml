(* Print the normalized bytecode from a file whose name is
   the first argument of the command *)

open OByteLib

let main () =
  if Array.length (Sys.argv) < 2 then
    prerr_endline ("Error: " ^ Sys.argv.(0) ^ ": filename missing")
  else begin
    let b = Cmofile.read Sys.argv.(1) in
    let (data, symb, prim, code) = Cmofile.reloc b in
    Normalised_code.print data symb prim stdout (Normalised_code.of_code code)
  end
;;

main ()
