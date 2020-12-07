exception DuplicateEntry
exception Type_error of string
exception Scope_error of string


type 'a t = int (* TODO: this is a dummy definition *)

type ttype =
| Tint
| Tbool
| Tchar
| Tvoid
| Tarr of ttype * ttype
| Tptr of ttype
| Tfun of ttype * ttype
| Treturn ttype

type 'a 'b entry_table={ttype:'a; annotation: 'b}

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
  tbl

let base_table=create_hashtable 8 [
  (Add, {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Sub, {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Mult, {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Div, {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Mod, {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation: None});
  (Less, {ttype=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Greater, {ttype=Tfun(Tbool, Tfun(Tint, Tint)); annotation:None});
  (Leq, {ttype=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Geq, {ttype=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});
  (Or, {ttype=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation: None});
  (And, {ttype=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation: None});
  (Not, {ttype=Tfun(Tbool, Tbool); annotation: None});
  (Neg, {ttype=Tfun(Tint, Tint)); annotation: None});
]
(*
  (Equal, {ttype=Tfun(Tbool, Tfun(Tint, Tint)); annotation: None});*)

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



