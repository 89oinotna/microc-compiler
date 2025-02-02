open Ast 
open Semant
open Scanner


let () = 
  if Array.length (Sys.argv) == 2 then
    let filename = Sys.argv.(1) in
    let in_channel = open_in filename in 
    let lexbuf = Lexing.from_channel in_channel ~with_positions:true in
    try 
      let (Prog(ds)) as p = Parser_engine.parse lexbuf in 
      Printf.printf "Number of found declarations: %d\n" (List.length ds);
      Printf.printf "Ast dump\n %s\n" (show_program p);
      Semant.check p;
      Printf.printf "Semantic checks: pass\n"
    with 
      | Util.Lexing_error(m) ->
        Printf.fprintf stderr "Lexing error:\n%s:%s\n" filename m
      | Util.Syntax_error(m) ->
        Printf.fprintf stderr "Syntax error:\n%s:%s\n" filename m
      | Util.Semantic_error(m) ->
        Printf.fprintf stderr "Error:\n%s:%s\n" filename m
  else
    Printf.fprintf stderr "Usage:\t%s <source_file>\n" (Sys.argv.(0)) 