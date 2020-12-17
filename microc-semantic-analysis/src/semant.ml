open Ast
open Sast
open Symbol_table

exception Type_error of string

let create_hashtable size init =
  let tbl = Hashtbl.create size in
  begin 
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl
  end


let unpack ann_node=
  match ann_node with
  | { node; loc; id} -> node
  | _  -> raise (Type_error "error in ast node")

let rec type_of_typ (gamma: 'a t) e=
  match e with
  | TypA(tp, i) ->  let i_typ=
                      match i with
                      | Some(x:int) -> Tint(*TODO*)
                      | None -> Tvoid (* solo se come arg in funzione *)
                      | _ -> raise (Type_error "error in function args definition")
                    in
                    Tarr(type_of_typ gamma tp, i_typ)
  | TypP(tp) -> Tptr(type_of_typ gamma tp)
  | TypI -> Tint
  | TypB -> Tbool
  | TypC -> Tchar
  | TypV -> Tvoid

  
  let rec type_of_expr (gamma: 'a t) e=
    let rec type_of_access gamma e=
      match unpack e with
      | AccVar(id) -> Symbol_table.lookup id gamma
      | AccDeref(e) -> type_of_expr gamma e
      | AccIndex(a, e) -> 
        let a_typ=type_of_access gamma a in
        match a_typ with
        | Tarr(_, _) -> 
          if (type_of_expr gamma e) = Tint then
            a_typ
          else raise (Type_error "index is not an int")
        | _ -> raise (Type_error "error with the array access")
    in
    match unpack e with
    | ILiteral(_) -> Tint
    | BLiteral(_) -> Tbool
    | CLiteral(_) -> Tchar
    | Access(a)  -> type_of_access gamma a
    | Assign(a, e) -> let a_typ=type_of_access gamma a in
                      if (a_typ)=(type_of_expr gamma e) then 
                        a_typ
                      else raise (Type_error "type error on assignment")
    | Addr(a) -> type_of_access gamma a
    | UnaryOp(uop, e) -> 
      let e_typ=type_of_expr gamma e in
      let op_typ=Symbol_table.lookup (show_uop uop) gamma in 
      begin
        match op_typ with
        | Tfun(tp1, tp2) -> if tp1=e_typ then tp2 else raise (Type_error ("Wrong type for" ^ (show_uop uop)))
        | _ -> failwith "Inconsistent state"
      end
    | BinaryOp(Equal, e1, e2) -> 
        let typ1=type_of_expr gamma e1 in
        if typ1=(type_of_expr gamma e2) then Tbool
        else raise (Type_error ("Wrong type for" ^ (show_binop Equal)))
    | BinaryOp(binop, e1, e2) ->
        let e1_tp=type_of_expr gamma e1 in
        let e2_tp=type_of_expr gamma e2 in
        let op_typ=Symbol_table.lookup (show_binop binop) gamma in 
        begin
        match op_typ with
          | Tfun(tp1, Tfun(tp2, tres)) ->
            if (tp1=e1_tp && tp2=e2_tp) then tres else raise (Type_error ("error in the arguments of " ^ (show_binop binop)))
          | _ -> failwith "Inconsistent state"
        end
    | Call(id, expr_lst) -> 
        let fun_typ=Symbol_table.lookup id gamma in 
          let rec check_args f_tp args=
            match f_tp, args with
            | Tfun(tp, tp'), [] -> if tp=Tvoid then tp' 
                                    else raise (Type_error ("error in the arguments of " ^ id))
            | Tfun(tp, tp'), x::[] -> if tp=(type_of_expr gamma x) then tp' 
                                      else raise (Type_error ("error in the arguments of " ^ id))
            | Tfun(tp, tp'), x::xs -> if tp=(type_of_expr gamma x) then check_args tp' xs 
                                      else raise (Type_error ("error in the arguments of " ^ id))
            | _ -> raise (Type_error ("error in function " ^ id))
          in check_args fun_typ expr_lst

let rec type_of_stmt gamma e=
  let rec type_of_stmtordec gamma e=
    match unpack e with
    | Dec(typ, id) -> 
                      let tp=type_of_typ gamma typ in
                      begin
                      Symbol_table.add_entry id ({typp=tp; annotation= None}) gamma; 
                      tp
                      end
    | Stmt(st) -> type_of_stmt gamma st
    in
  match unpack e with
  | If(e1, e2, e3) ->
      if (type_of_expr gamma e1) = Tbool then
        let t2=type_of_stmt gamma e2 in
        let t3 = type_of_stmt gamma e3 in
        t3
      else
      raise (Type_error "if with no a boolean guard")
      | Block(lst) -> 
      let return_type_ht = 
        let ht=Hashtbl.create 1 in
        let scope=Symbol_table.begin_block gamma in
          let f stmtordec=
            match (type_of scope stmtordec) with
              | Treturn(tp) -> Hashtbl.add ht tp tp
              | _ -> ()
            in
        List.iter f lst; ht
      in
      if Hashtbl.length return_type_ht > 1 then raise (Type_error "too many return type")
      else 
      begin
        let block_tp=
          let fol key value lst= key::lst
          in 
          Hashtbl.fold fol return_type_ht []
        in
        match block_tp with
          | [] -> Tvoid
          | x::[] -> x
          | _ -> assert false
      end

  | While(e, stmt) -> 
      if (type_of gamma e) = Tbool then
        type_of gamma stmt
      else
        raise (Type_error "while with no a boolean guard")
  | Expr(e) -> type_of gamma e
  | Return(e) -> 
      match e with
      | None -> Treturn(Tvoid)
      | Some(x) -> Treturn(type_of e gamma)
  

let rec type_of_topdecl gamma e=
  match unpack e with
  | Fundecl({typ; fname; formals; body}) ->
    let scope=Symbol_table.begin_block gamma in
    (*args in scope*)
    let formals_tp=
        let f formal=
          match formal with
          (*TODO cambiare fun type*)
          | (tp, id) -> 
            let tp1=(type_of_typ gamma tp)
            in
            begin
              Symbol_table.add_entry id (tp1, None) scope; 
              tp1
            end
          | _ -> raise (Type_error ("error in function args definition"^fname))
        in 
        List.map f formals
    in      
    (*body*)
    let btyp=type_of scope body in  
    if (type_of_typ gamma typ) = btyp then(*end block*) 
      let fun_tp=
        let rec build_tp ls =
          match ls with
          | [] -> Tfun(Tvoid, btyp)
          | x::[] -> Tfun(x, btyp)
          | x::xs -> Tfun(x, get_formals_tp xs)
        in
        build_tp formals_tp
      in 
      begin 
        Symbol_table.add_entry fname {ttype=fun_tp; annotation=None} gamma;
        fun_tp
      end 
    else raise (Type_error "wrong function type")
  | Vardec(typ, id) -> let tp=type_of_typ gamma typ in
    Symbol_table.add_entry id {ttype=tp; annotation=None} gamma;;


let base_table=create_hashtable 8 [
  ("+", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("-", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("*", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("/", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("%", {typp=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("<", {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation= None});
  (">", {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation=None});
  ("<=", {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation= None});
  (">=", {typp=Tfun(Tbool, Tfun(Tint, Tint)); annotation= None});
  ("||", {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("&&", {typp=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("!", {typp=Tfun(Tbool, Tbool); annotation= None});
]
    

let check (Prog(topdecls)) = 
  let rec scan lst table=
    match lst with
    | {node;  loc ; id} ::xs -> type_of_topdecl node; scan xs;
    | [] -> Tvoid
    in
 scan topdecls Symbol_table.begin_block(Symbol_table.empty_table)