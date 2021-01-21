
exception DuplicateEntry
exception Nf of string


type 'a t = Empty | Table of 'a t * (string, 'a) Hashtbl.t (* parent * vars *) (* TODO: this is a dummy definition *)

let empty_table = Empty
(* used to store all key -> entry 
    It has every time all the binding until current scope
*)


(*let scope_list=ref [|empty_table|]*)

let begin_block (table: 'a t)  = 
  match table with
  | Empty -> Table(Empty, (Hashtbl.create 1))
  | x -> Table(x, (Hashtbl.create 1)) (* return table of new block *)


let end_block (Table (parent, vars)) =
  parent

let add_entry symbol info (table: 'a t) = 
(*if it is in the same scope => error
  otherwise shadows it*)
  match table with
  | Empty -> assert false
  | Table(parent, vars) as x ->
    try
      let tp=Hashtbl.find vars symbol
          in raise DuplicateEntry
    with
    | Not_found -> 
            Hashtbl.add vars symbol info;
            x
  

let rec lookup symbol (Table (parent, vars)) = 
  try Hashtbl.find vars symbol with
  | Not_found -> 
    match parent with 
    | Empty ->raise (Nf symbol)
    | x -> lookup symbol parent
    

(*let rec lookup symbol table = Hashtbl.find symbol base_table*)



