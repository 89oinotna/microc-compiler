
exception DuplicateEntry
exception Nf of string


type 'a t = Empty| Table of (string, 'a) Hashtbl.t Array.t (* TODO: this is a dummy definition *)

let empty_table = Empty
(* used to store all key -> entry 
    It has every time all the binding until current scope
*)


(*let scope_list=ref [|empty_table|]*)

let begin_block (table: 'a t)  = 
  match table with
  | Empty -> Table([|(Hashtbl.create 1)|])
  |Table(t) -> Table(Array.append t [|(Hashtbl.create 1)|]) (* return table of new block *)


let end_block (Table table) =
  let len=Array.length table in
  begin
    let f key data=Hashtbl.remove table.(0) key
      in
    Hashtbl.iter f table.(len - 1);
    Table(Array.sub table 0 (len-2))
  end

let add_entry symbol info (table: 'a t) = (*check if exists 
    if it is in the same scope => error
      otherwise shadows it*)
  
  match table with
  | Empty -> assert false
  | Table(tb) ->
    try
      let tp=Hashtbl.find tb.(0) symbol
          in raise DuplicateEntry
    with
    | Not_found -> 
            Hashtbl.add tb.(Array.length tb-1) symbol info;
            Hashtbl.add tb.(0) symbol info;
            table
  

let lookup symbol (Table table) = 
  try Hashtbl.find table.(0) symbol with
  | Not_found -> raise (Nf symbol)

(*let rec lookup symbol table = Hashtbl.find symbol base_table*)



