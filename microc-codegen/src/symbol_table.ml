
exception DuplicateEntry


type 'a t = Empty | Table of 'a t * (string, 'a) Hashtbl.t (* parent * vars *) 

let empty_table = Empty
(* used to store all key -> entry 
    It has every time all the binding until current scope
*)


let begin_block (table: 'a t)  = 
  match table with
  | Empty -> Table(Empty, (Hashtbl.create 1))
  | x -> Table(x, (Hashtbl.create 1)) (* return table of new block *)


let end_block tb =
  match tb with
  | Empty -> Empty
  | Table (parent, vars) -> parent

let add_entry symbol info (table: 'a t) = 
(*if it is in the same scope => error
  otherwise shadows it*)
  match table with
  | Empty -> assert false
  | Table(parent, vars) as x ->
    try
      let _=Hashtbl.find vars symbol
          in raise DuplicateEntry
    with
    | Not_found -> 
            Hashtbl.add vars symbol info;
            x
  

let rec lookup symbol tb = 
  match tb with
  | Empty -> raise Not_found
  |(Table (parent, vars)) ->
      try Hashtbl.find vars symbol with
      | Not_found -> 
        match parent with 
        | Empty ->raise Not_found
        | x -> lookup symbol parent
    

(*let rec lookup symbol table = Hashtbl.find symbol base_table*)



