open Ast
open Sast
open Symbol_table

type 'a entry_table={
  ttype:'a; 
  annotation: string option
}
  [@@deriving show]


let unpack ann_node=
  match ann_node with
  | { loc; node; id} -> node

let rec type_eq a b=
  match a, b with
  | Tarr(ttyp1, Tvoid, _), Tarr(ttyp2, _, _) 
  | Tarr(ttyp1, _, _), Tarr(ttyp2, Tvoid, _) -> type_eq ttyp1 ttyp2
  | Tptr(_), Tnull 
  | Tnull, Tptr(_) -> true
  | a, b -> (a=b)

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
                      | Some(x:int) -> Tint (*TODO*)
                      | None -> Tvoid (* solo se come arg in funzione o declaration *)
                    in
                    Tarr(type_of_typ gamma tp, i_typ, i)
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
      | Tarr(a_typ, _, _) -> (*maybe error if index is > array size*)
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
    if (type_eq a_typ e_typ) then
      match a_typ, e_typ with
      | Tint, _  -> a_typ
      | tp, _ -> (Util.raise_semantic_error e.loc ("Cannot operator assign type "^(show_ttype tp)))
    else
      (Util.raise_semantic_error e.loc "Lvalue must be the same type of rvalue")   
  | Assign(a, ex) -> 
    let a_typ=type_of_access gamma a in
    let e_typ=type_of_expr gamma ex in
        if (type_eq a_typ e_typ) then 
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
      in
    let e_typ=type_of_expr gamma e in
    begin
      match op_typ with
      | Tfun(tp1, tp2) -> if (type_eq tp1 e_typ) then tp2 else (Util.raise_semantic_error e.loc ("Wrong type for" ^ (show_uop uop)))
      | _ -> assert false
    end
  | BinaryOp(Equal, e1, e2) 
  | BinaryOp(Neq, e1, e2) ->
      let typ1=type_of_expr gamma e1 in
      if (type_eq typ1 (type_of_expr gamma e2)) then Tbool
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
          if ((type_eq tp1 e1_tp) && (type_eq tp2 e2_tp)) then tres else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ (show_binop binop)))
        | _ -> assert false
      end
  | Call(id, expr_lst) -> 
      let fun_typ=
        match Symbol_table.lookup id gamma with
        | {ttype; annotation} -> (*Printf.printf "%s" (show_ttype ttype);*) ttype
      in   
      let rec check_args f_tp args=
        match f_tp, args with
        | Tfun(tp, tp'), [] -> if tp=Tvoid then tp' 
                                else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id ^ (show_ttype tp) ))
        | Tfun(tp, tp'), x::[] -> if (type_eq tp (type_of_expr gamma x)) then tp' 
                                  else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id ^ (show_ttype tp)))
        | Tfun(tp, tp'), x::xs -> let arg_tp=(type_of_expr gamma x) in
        if (type_eq tp arg_tp) then check_args tp' xs 
                                  else (Util.raise_semantic_error e.loc ("error in the arguments of " ^ id^ (show_ttype tp) ^ (show_ttype arg_tp)))
        | _ -> (Util.raise_semantic_error e.loc ("error in args of function " ^ id))
      in 
      check_args fun_typ expr_lst
  | ArrayInit(ls) -> 
    let tp_ht= Hashtbl.create 0 in
    begin
      let f x=
          let x_pt=type_of_expr gamma x in
          begin
            try
              ignore(Hashtbl.find tp_ht x_pt); ()
            with
            | Not_found -> (Hashtbl.add tp_ht x_pt None)
          end
        in
      List.iter f ls;
      if (Hashtbl.length tp_ht) = 1 then (* must be 1 type *)
        begin
          let tp=
            let fol key value lst= key::lst
            in 
            Hashtbl.fold fol tp_ht []
          in
          match tp with
            | x::[] -> Tarr(x, Tint, Some(List.length ls))
            | _ -> assert false
        end
      else
        (Util.raise_semantic_error e.loc "Invalid array initializer type")
      
    end


let rec type_of_stmt gamma fun_typ e=
  match unpack e with
  | If(e1, e2, e3) ->
      if (type_of_expr gamma e1) = Tbool then
        let t2=type_of_stmt gamma fun_typ e2 in
        let t3 = type_of_stmt gamma fun_typ e3 in
        match t2, t3 with
        | Treturn(a),Treturn(b) -> 
          if (type_eq a b) then t3
          else (Util.raise_semantic_error e.loc "Different return type")
        | Treturn(_), _ -> t2
        | _, Treturn(_) -> t3
        | _, _ -> t3
      else (Util.raise_semantic_error e.loc "if with no boolean guard")
  | While(ex, stmt) -> 
      if (type_of_expr gamma ex) = Tbool then
        type_of_stmt gamma fun_typ stmt
      else
        (Util.raise_semantic_error e.loc "while with no boolean guard")
  | DoWhile(stmt, ex) -> 
    if (type_of_expr gamma ex) = Tbool then
      type_of_stmt gamma fun_typ stmt
    else
      (Util.raise_semantic_error e.loc "while with no boolean guard")
  | Expr(e) -> type_of_expr gamma e
  | Return(ex) -> 
    let ret_tp= 
    begin
      match ex with
      | None -> Tvoid
      | Some(x) -> let tp=type_of_expr gamma x in 
                    match tp with
                    | Tvoid 
                    | Tint
                    | Tchar
                    | Tbool-> tp
                    | _ -> (Util.raise_semantic_error e.loc "Wrong return type")
    end
    in
    if type_eq ret_tp fun_typ then ret_tp
    else (Util.raise_semantic_error e.loc ("Return type " ^ (show_ttype ret_tp)^" not matching function type "  ^ (show_ttype fun_typ)))
  | Block(lst) -> 
    List.iter (type_of_stmtordec gamma fun_typ) lst; fun_typ
      
 and type_of_stmtordec gamma fun_typ e=
    match unpack e with
    | Dec(typ, id) -> 
      begin
        match typ with
        | TypA(tp, i) -> begin
                        match i with
                        | Some(x:int) -> if x>0 then () else (Util.raise_semantic_error e.loc ("Array must have size > 0 "))
                        | None -> (Util.raise_semantic_error e.loc ("Array must have size > 0 "))
                        
                        end 
        | _ -> ()
      end;
        let tp=type_of_typ gamma typ in
        begin
          ignore(Symbol_table.add_entry id ({ttype=tp; annotation=None}) gamma)
        end
    | Stmt(st) -> ignore(type_of_stmt gamma fun_typ st); ()
    | Decinit(typ, id, ex) ->
      let tp=type_of_typ gamma typ in
      let _=match tp with
            | Tarr(_, Tvoid, _) -> ()
            | Tarr(_, _, _) -> (Util.raise_semantic_error e.loc ("Array initialization doesn't need array lenght"))
            | _ -> ()
          in
      let e_tp=type_of_expr gamma ex in
      if (type_eq tp e_tp) then
        begin
          ignore(Symbol_table.add_entry id ({ttype=tp; annotation=None}) gamma)
        end
      else
        match tp, e_tp with
        | Tarr(_, _, Some(x)), Tarr(_, _, Some(y)) -> (Util.raise_semantic_error e.loc ("Wrong size on array declaration "^id))
        | _ ->
          (Util.raise_semantic_error e.loc ("Wrong type on variable declaration "^id))
     

let type_of_topdecl gamma e=
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
            let tp1=(type_of_typ scope tp)
            in
            begin
              ignore(Symbol_table.add_entry id {ttype=tp1; annotation=None} scope); 
              tp1
            end
        in 
        List.map f formals
    in      
    (* fun type *)
    let ftyp=type_of_typ scope typ in
    (* needed for recursion *)
    let fun_tp= (* build fun type and insert it in the scope *)
        let rec build_tp ls =
          match ls with
          | [] -> Tfun(Tvoid, ftyp)
          | x::[] -> Tfun(x, ftyp)
          | x::xs -> Tfun(x, build_tp xs)
        in
        build_tp formals_tp
    in
    let _=
        Symbol_table.add_entry fname {ttype=fun_tp; annotation=None} gamma
    in
    (*body*)
    let _=type_of_stmt scope ftyp body in fun_tp 
    (*if (type_eq ftyp btyp) then
      fun_tp
    else (Util.raise_semantic_error e.loc ("Return type doesn't match function type "^fname))
  *)| Vardec(typ, id) -> 
      begin
        match typ with
        | TypA(tp, i) -> begin
                        match i with
                        | Some(x:int) -> if x>0 then () else (Util.raise_semantic_error e.loc ("Array must have size > 0 "))
                        | None -> (Util.raise_semantic_error e.loc ("Array must have size > 0 "))
                        
                        end 
        | _ -> ()
      end;
      let tp=type_of_typ gamma typ in
      begin
        ignore(Symbol_table.add_entry id {ttype=tp; annotation=None} gamma);
        tp
      end
  | Vardecinit(typ, id, expr) ->
      let tp=type_of_typ gamma typ in
      let _=match tp with
            | Tarr(_, Tvoid, _) -> ()
            | Tarr(_, _, _) -> (Util.raise_semantic_error e.loc ("Array initialization doesn't need array lenght"))
            | _ -> ()
          in
      let i_tp=type_of_expr gamma expr in
      if (type_eq tp i_tp) then
        begin
          ignore(Symbol_table.add_entry id {ttype=tp; annotation=None} gamma);
          tp 
        end
      else
        match tp, i_tp with
        | Tarr(_, _, Some(x)), Tarr(_, _, Some(y)) -> (Util.raise_semantic_error e.loc ("Wrong size on array declaration "^id))
        | _ ->
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
  ("getint", {ttype=Tfun(Tvoid, Tint); annotation= None});
  ("NULL", {ttype=Tnull; annotation= None});
]
 

(* add return type of the main *)
let check (Prog(topdecls)) = 
  let top_scope=(Symbol_table.begin_block(Symbol_table.empty_table)) in
  let f (x, y)= ignore(Symbol_table.add_entry x y top_scope); () in
  let _=  List.iter f base in
  let scope=(Symbol_table.begin_block(top_scope)) in
  let rec scan lst scope=
    match lst with
    | [] ->  Tvoid
    | x::xs -> ignore(type_of_topdecl scope x); scan xs scope
    in
  scan topdecls scope;