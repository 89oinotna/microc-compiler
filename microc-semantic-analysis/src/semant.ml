open Ast
open Sast
open Symbol_table

type 'a entry_table={
  ttype:'a; 
  annotation: string option
}
  [@@deriving show]


let create_hashtable size init =
  let tbl = Hashtbl.create size in
  begin 
    List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
    tbl
  end

let unpack ann_node=
  match ann_node with
  | { loc; node; id} -> node
  | _  -> assert false

let binop_to_key op=
match op with
| Add -> "+"
| Sub ->"-"
| Mult ->"*"
| Div  ->"/"
| Mod ->"%"
| Less -> "<"
| Leq -> "<="
| Greater -> ">" 
| Geq -> ">="
| And ->"&&"
| Or ->"||"
| _ -> assert false        

let rec type_of_typ gamma e=
  match e with
  | TypA(tp, i) ->  let i_typ=
                      match i with
                      | Some(x:int) -> Tint(*TODO*)
                      | None -> Tvoid (* solo se come arg in funzione *)
                      | _ -> assert false
                    in
                    Tarr(type_of_typ gamma tp, i_typ)
  | TypP(tp) -> Tptr(type_of_typ gamma tp)
  | TypI -> Tint
  | TypB -> Tbool
  | TypC -> Tchar
  | TypV -> Tvoid

let rec type_of_expr gamma e=
  let rec type_of_access gamma e=
    match unpack e with
    | AccVar(id) -> begin
                    try 
                      match Symbol_table.lookup id gamma with
                      | {ttype; annotation} -> ttype
                    with
                      |_ -> (Util.raise_semantic_error e.loc "Variable not in scope")
                    end
    | AccDeref(ex) -> 
      let tp=type_of_expr gamma ex 
      in
      begin
      match tp with
        | Tptr(typ) -> typ
        | _ -> (Util.raise_semantic_error e.loc "Dereferencing a non pointer")
      end
    | AccIndex(a, ex) -> 
      let a_typ=type_of_access gamma a in
      match a_typ with
      | Tarr(a_typ, _) -> 
        if (type_of_expr gamma ex) = Tint then
          a_typ
        else  (Util.raise_semantic_error e.loc "Index is not an int")
      | _ ->  (Util.raise_semantic_error e.loc "Not an array")
  in
  match unpack e with
  | Access(a)  -> type_of_access gamma a
  | OpAssign(_, a, ex) -> 
    let a_typ=type_of_access gamma a in
    let e_typ=type_of_expr gamma ex in
    if a_typ=e_typ then
      match a_typ, e_typ with
      | Tint, _  -> a_typ
      | tp, _ -> (Util.raise_semantic_error e.loc ("Cannot operator assign type "^(show_ttype tp)))
    else
      (Util.raise_semantic_error e.loc "Lvalue must be the same type of rvalue")   
  | Assign(a, ex) -> 
    let a_typ=type_of_access gamma a in
    let e_typ=type_of_expr gamma ex in
        if a_typ=e_typ then 
          match a_typ, e_typ with
          | Tarr(_), _ -> (Util.raise_semantic_error e.loc "Cannot assign Array type")
          | _, _  -> a_typ
        else (Util.raise_semantic_error e.loc "type error on assignment")
  | Addr(a) -> 
    let a_typ=type_of_access gamma a in
    Tptr(a_typ)
  | ILiteral(_) -> Tint
  | BLiteral(_) -> Tbool
  | CLiteral(_) -> Tchar
  | UnaryOp(uop, e) -> 
    let op_typ= 
      match uop with
      | Neg -> Tfun(Tint, Tint)
      | Not -> 
        begin
          match Symbol_table.lookup "!" gamma with
          | {ttype; annotation} -> ttype
        end
      | PreInc | PreDec | PostInc | PostDec ->
        Tfun(Tint, Tint)
      | _ -> assert false
      in
    let e_typ=type_of_expr gamma e in
    begin
      match op_typ with
      | Tfun(tp1, tp2) -> if tp1=e_typ then tp2 else (Util.raise_semantic_error e.loc ("Wrong type for" ^ (show_uop uop)))
      | _ -> assert false
    end
  | BinaryOp(Equal, e1, e2) 
  | BinaryOp(Neq, e1, e2) ->
      let typ1=type_of_expr gamma e1 in
      if typ1=(type_of_expr gamma e2) then Tbool
      else (Util.raise_semantic_error e.loc ("Wrong type for" ^ (show_binop Equal)))
  | BinaryOp(binop, e1, e2) ->
      let e1_tp=type_of_expr gamma e1 in
      let e2_tp=type_of_expr gamma e2 in
      let op_typ=
        match Symbol_table.lookup (binop_to_key binop) gamma with
        | {ttype; annotation} -> ttype in 
      begin
      match op_typ with
        | Tfun(tp1, Tfun(tp2, tres)) ->
          if (tp1=e1_tp && tp2=e2_tp) then tres else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ (show_binop binop)))
        | _ -> assert false
      end
  | Call(id, expr_lst) -> 
      let fun_typ=
      match Symbol_table.lookup id gamma with
      | {ttype; annotation} -> ttype in   
        let rec check_args f_tp args=
          match f_tp, args with
          | Tfun(tp, tp'), [] -> if tp=Tvoid then tp' 
                                  else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id))
          | Tfun(tp, tp'), x::[] -> if tp=(type_of_expr gamma x) then tp' 
                                    else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id))
          | Tfun(tp, tp'), x::xs -> if tp=(type_of_expr gamma x) then check_args tp' xs 
                                    else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id))
          | _ -> (Util.raise_semantic_error e.loc ("error in args of function " ^ id))
        in check_args fun_typ expr_lst

let rec type_of_stmt gamma e=
  let rec type_of_stmtordec gamma e=
    match unpack e with
    | Dec(typ, id) -> 
        let tp=type_of_typ gamma typ in
        begin
          Symbol_table.add_entry id ({ttype=tp; annotation=None}) gamma; 
          tp
        end
    | Stmt(st) -> type_of_stmt gamma st
    | Decinit(typ, id, ex) ->
      let tp=type_of_typ gamma typ in
      let e_tp=type_of_expr gamma ex in
      if tp=e_tp then
        begin
          Symbol_table.add_entry id ({ttype=tp; annotation=None}) gamma;
          tp
        end
      else
        (Util.raise_semantic_error e.loc ("Wrong type on variable declaration "^id))
    
  in
  match unpack e with
  | If(e1, e2, e3) ->
      if (type_of_expr gamma e1) = Tbool then
        let t2=type_of_stmt gamma e2 in
        let t3 = type_of_stmt gamma e3 in
        match t2, t3 with
        | Treturn(a),Treturn(b) -> 
          if a=b then t3
          else (Util.raise_semantic_error e.loc "Different return type")
        | Treturn(_), _ -> t2
        | _, Treturn(_) -> t3
        | _, _ -> t3
      else (Util.raise_semantic_error e.loc "if with no boolean guard")
  | While(ex, stmt) -> 
      if (type_of_expr gamma ex) = Tbool then
        type_of_stmt gamma stmt
      else
        (Util.raise_semantic_error e.loc "while with no boolean guard")
  | DoWhile(stmt, ex) -> 
    if (type_of_expr gamma ex) = Tbool then
      type_of_stmt gamma stmt
    else
      (Util.raise_semantic_error e.loc "while with no boolean guard")
  | Expr(e) -> type_of_expr gamma e
  | Return(ex) -> 
    begin
      match ex with
      | None -> Treturn(Tvoid)
      | Some(x) -> let tp=type_of_expr gamma x in 
                    match tp with
                    | Tvoid 
                    | Tint
                    | Tchar
                    | Tbool-> Treturn(tp) 
                    | _ -> (Util.raise_semantic_error e.loc "Wrong return type")
    end
  | Block(lst) -> 
        (* if in function the scope is gamma and we need to check return type*)
      let scope= if e.id=1 then gamma else Symbol_table.begin_block gamma in
        (* need to check all return type in the block *)
      let return_type_ht = 
        let ht=Hashtbl.create 0 in
          let f stmtordec=
            match (type_of_stmtordec scope stmtordec) with
              | Treturn(tp) -> Hashtbl.add ht tp tp
              | _ -> ()
            in
          List.iter f lst; 
          ht
      in
      if Hashtbl.length return_type_ht > 1 then 
        (Util.raise_semantic_error e.loc "Wrong return type")
      else 
        begin
          let block_tp=
            let fol key value lst= key::lst
            in 
            Hashtbl.fold fol return_type_ht []
          in
          Symbol_table.end_block scope;
          match block_tp with
            | [] -> Tvoid
            | x::[] -> x
            | _ -> assert false
        end
     
  

let rec type_of_topdecl gamma e=
  match unpack e with
  | Fundecl({typ; fname; formals; body}) ->
    (*args are in function's scope*)
    let scope=Symbol_table.begin_block gamma in
    (* put args in the scope and type check them*)
    let formals_tp=
        let f formal=
          match formal with
          | (TypV, _) -> (Util.raise_semantic_error e.loc "Cannot use void type")
          | (tp, id) -> 
            let tp1=(type_of_typ gamma tp)
            in
            begin
              Symbol_table.add_entry id {ttype=tp1; annotation=None} scope; 
              tp1
            end
          | _ -> assert false
        in 
        List.map f formals
    in      
    (* fun type *)
    let ftyp=type_of_typ gamma typ in
    (*body*)
    let btyp=type_of_stmt scope body in  
    if ftyp = btyp then(*end block*) 
      let fun_tp= (* build fun type and insert it in the scope *)
        let rec build_tp ls =
          match ls with
          | [] -> Tfun(Tvoid, btyp)
          | x::[] -> Tfun(x, btyp)
          | x::xs -> Tfun(x, build_tp xs)
        in
        build_tp formals_tp
      in 
      begin 
        Symbol_table.add_entry fname {ttype=fun_tp; annotation=None} gamma;
        fun_tp
      end 
    else (Util.raise_semantic_error e.loc ("Return type doesn't match function type "^fname))
  | Vardec(typ, id) -> 
    let tp=type_of_typ gamma typ in
    begin
      Symbol_table.add_entry id {ttype=tp; annotation=None} gamma;
      tp
    end
  | Vardecinit(typ, id, expr) ->
    let tp=type_of_typ gamma typ in
    let e_tp=type_of_expr gamma expr in
    if tp=e_tp then
      begin
        Symbol_table.add_entry id {ttype=tp; annotation=None} gamma;
        tp 
      end
    else
      (Util.raise_semantic_error e.loc ("Wrong type on variable declaration "^id))



let base=[
  ("+", {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("-", {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("*", {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("/", {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("%", {ttype=Tfun(Tint, Tfun(Tint, Tint)); annotation= None});
  ("<", {ttype=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  (">", {ttype=Tfun(Tint, Tfun(Tint, Tbool)); annotation=None});
  ("<=", {ttype=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  (">=", {ttype=Tfun(Tint, Tfun(Tint, Tbool)); annotation= None});
  ("||", {ttype=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("&&", {ttype=Tfun(Tbool, Tfun(Tbool, Tbool)); annotation= None});
  ("!", {ttype=Tfun(Tbool, Tbool); annotation= None});
  ("print", {ttype=Tfun(Tint, Tvoid); annotation= None});
  ("getint", {ttype=Tfun(Tvoid, Tint); annotation= None})
]
         
(* add return type of the main *)
let check (Prog(topdecls)) = 
  let scope=(Symbol_table.begin_block(Symbol_table.empty_table)) in
  let rec scan lst scope=
    match lst with
    | x::xs -> type_of_topdecl scope x; scan xs scope
    | [] -> Tvoid
    in
  let f (x, y)=Symbol_table.add_entry x y scope; () in
    List.iter f base;
 scan topdecls scope