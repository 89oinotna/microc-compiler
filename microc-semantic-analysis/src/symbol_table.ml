open Sast

exception DuplicateEntry

exception Scope_error of string

type 'a entry_table={typp:'a; annotation: string option}[@@deriving show]


type 'a t = (string, 'a entry_table) Hashtbl.t (* TODO: this is a dummy definition *)


let create_hashtable size init =
  let tbl = Hashtbl.create size in
  begin 
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl
  end

(* used to store all key -> entry 
    It has every time all the binding until current scope
*)
let empty_table =  create_hashtable 8 [
  ("+", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("-", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("*", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("/", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("%", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("==", {typp=Tfun('a, Tfun('a, Tbool)); annotation= None});
  ("!=", {typp=Tfun('a, Tfun('a, Tbool)); annotation= None});
  ("<", {typp=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  (">", {typp=Tfun(Tint, Tfun(Tint, Tbool)); annotation=None});
  ("<=", {typp=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  (">=", {typp=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  ("||", {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("&&", {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("!", {typp=Tfun(Tbool, Tbool); annotation= None});
]

let scope_list=ref [|empty_table|]

let begin_block table = 
  let initialize tb = scope_list:=Array.append !scope_list [|tb|]; tb  
in initialize (Hashtbl.create 1) (* return table of new block *)


let end_block table =
  let f key data=Hashtbl.remove empty_table key
    in
  Hashtbl.iter f table;
  let len=Array.length !scope_list
  in
    if table=(!scope_list.(len-1)) then 
      begin
        scope_list:=(Array.sub !scope_list 0 (len-2)); 
        (!scope_list.(len-2))
      end
    else raise (Scope_error("block"))

let add_entry symbol info table = (*check if exists 
    if it is in the same scope => error
      otherwise shadows it*)
  try
    Hashtbl.find table symbol;
    raise DuplicateEntry
  with
  | Not_found -> Hashtbl.add table symbol info;
          Hashtbl.add empty_table symbol info
  

let lookup symbol table = Hashtbl.find symbol empty_table

(*let rec lookup symbol table = Hashtbl.find symbol base_table*)



