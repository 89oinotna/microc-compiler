exception DuplicateEntry

exception Scope_error of string


type 'a t = int (* TODO: this is a dummy definition *)


let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
  tbl

let base_table=create_hashtable 8 [
  (Add, {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Sub, {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Mult, {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Div, {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Mod, {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Less, {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Greater, {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation:None});
  (Leq, {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Geq, {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Or, {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation: None});
  (And, {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation: None});
  (Neg, {typp=Tfun(Tint, Tint)); annotation: None});
  (Not, {typp=Tfun(Tbool, Tbool); annotation: None});
]
(*
  (Equal, {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});*)

let scope_list=[base_table]

let empty_table =  Hashtbl.create 1

let begin_block table = 
  let initialize tb=
          tb::scope_list; 
          tb (* return table of new block *)
in initialize empty_table

let end_block table =
  let f key data=Hashtbl.remove base_table key
in
  Hashtbl.iter f table
  match scope_list with
| x::xs -> if tb=x then scope_list=tail else raise Scope_error
| _ -> raise Scope_error

let add_entry symbol info table = Hashtbl.add table symbol info;
Hashtbl.add base_table symbol info

let lookup symbol table = Hashtbl.find symbol base_table

(*let rec lookup symbol table = Hashtbl.find symbol base_table*)



