open Ast
open Symbol_table


let rec get_formals_tp ls=
              match ls with
              | [] -> Tfun(Tvoid, Tvoid)
              | x::[] -> Tfun(x, Tvoid)
              | x::xs -> Tfun(x, get_formals_tp xs)
            in

let rec type_of gamma e =
      match e with
      (*TODO cambiare fun type*)
      | (tp, id) -> 
        let tp1=(type_of gamma tp)
        in
        Symbol_table.add_entry id {ttype=tp1, annotation: None} gamma; tp1
      | {typ; fname; formals; body} ->
        let scope=Symbol_table.begin_block gamma;
        (*args in scope*)
        let formals_tp=
            let f formal=type_of scope formal
              in 
            List.map f formals
        in      
        (*body*)
        let btyp=type_of scope body 
        in 
        if (type_of gamma typ) = btyp then(*end block*) 
          let fun_tp=
            let rec build_tp ls =
              match ls with
              | [] -> Tfun(Tvoid, btyp)
              | x::[] -> Tfun(x, btyp)
              | x::xs -> Tfun(x, get_formals_tp xs)
            in
            build_tp formals_tp
            in 
          Symbol_table.add_entry fname {ttype=fun_tp; annotation=None} gamma; fun_tp 
        else raise (Type_error "wrong function type")
      | Vardec(typ, id) -> let tp=type_of typ in
              Symbol_table.add_entry id {ttype=tp; annotation=None} gamma;

      | Dec(typ, id) -> let tp=type_of typ in
              Symbol_table.add_entry id {ttype=tp; annotation=None} gamma;
      | Stmt(st) -> type_of gamma st

      | Block(lst) -> 
          let scope=Symbol_table.begin_block gamma;
          let return_type_ht = Hashtbl.create 1 ;
          let f stmtordec=
          match (type_of scope stmtordec) with
            | Treturn(tp) -> Hashtbl.add return_type tp tp
            | _ 
          in 
          List.iter f lst
          if Hashtbl.length > 1 then raise (Type_error "too many return type")
          else 
            let block_tp=
              let fol key value lst= key::lst
              in 
              Hashtbl.fold fol return_type_ht []
            in
            match block_tp with
            | [] -> Tvoid
            | x::[] -> x
            
      | If(e1, e2, e3) ->
          if (type_of gamma e1) = Tbool then
            type_of gamma e3;
            let t3 = type_of gamma e2;
            t3
          else
          raise (Type_error "if with no a boolean guard")
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

      | AccVar(id) -> Symbol_table.lookup id gamma
      | AccDeref(e) -> type_of gamma e
      | AccIndex(a, e) -> 
        if (type_of gamma e) = Tint then
          Symbol_table.lookup id gamma
        else raise (Type_error "index is not an int")

      | ILiteral(_) -> Tint
      | BLiteral(_) -> Tbool
      | CLiteral(_) -> Tchar
      | Access(a)  -> type_of gamma a
      | Assign(a, e) -> if (type_of gamma a) != (type_of gamma e) then raise (Type_error "type error on assignment")
      | Addr(a) -> type_of gamma a
      | UnaryOp(uop, e) -> 
        let e_typ=type_of gamma e in
        let op_typ=Symbol_table.lookup uop gamma in 
        match op_typ with
        | Tfun(tp1, tp2) -> if tp1=e_typ then tp2 else raise (Type_error ("error in the arguments of " ^ op))
        | _ -> failwith "Inconsistent state"
      | BinaryOp(Equal, e1, e2) -> 
          let typ1=type_of gamma e1 in
          if typ1=(type_of gamma e2) then Tbool
          else raise (Type_error ("error in the arguments of " ^ op))
      | BinaryOp(binop, e1, e2) ->
          let e1_tp=type_of gamma e1 in
          let e2_tp=type_of gamma e2 in
          let op_typ=Symbol_table.lookup uop gamma in 
          match op_typ with
          | Tfun(tp1, Tfun(tp2, tres)) ->
            if (tp1=e1_tp && tp2=e2_tp) then tres else raise (Type_error ("error in the arguments of " ^ op))
          | _ -> failwith "Inconsistent state"
      | Call(id, expr_lst) -> 
          let fun_typ=Symbol_table.lookup id gamma in 
          let rec check_args f_tp args=
            match f_tp, args with
            | Tfun(tp, tp'), [] -> if tp=Tvoid then tp' else raise (Type_error ("error in the arguments of " ^ id))
            | Tfun(tp, tp'), x::[] -> if tp=x then tp' else raise (Type_error ("error in the arguments of " ^ id))
            | Tfun(tp, tp'), x::xs -> if tp=x then check_args tp' xs else raise (Type_error ("error in the arguments of " ^ id))
          in check_args fun_tp expr_lst

      | TypA(tp, i) -> Tarr(type_of gamma tp, type_of gamma i)
      | TypP(tp) -> Tptr(type_of gamma tp)
      | Some(x) -> type_of gamma x
      | None -> None
      | TypI -> Tint
      | TypB -> Tbool
      | TypC -> Tchar
      | TypV -> Tvoid

      | Let(x, e1, e2) ->
        let t1 = type_of gamma e1 in
        type_of ((x,t1)::gamma) e2
      | If(e1, e2, e3) ->
        if (type_of gamma e1) = Tbool then
          let t2 = type_of gamma e2 in
          let t3 = type_of gamma e3 in
          if t2 = t3 then t2 else raise (Type_error "if branches have different types")
        else
          raise (Type_error "if with no a boolean guard")
      (* | Fun(x,tx, e) -> Tfun(tx, type_of ((x, tx) :: gamma) e) *)
      | Letfun(f, x, (Tfun(t1,t2) as t), body, e) ->
        let gamma' = (f, t) :: (x, t1) :: gamma in
        if (type_of gamma' body) = t2 then
          type_of ((f, t) :: gamma) e
        else
         raise (Type_error "Return type does not match")
      | Prim("=", e1, e2) ->
        let t1 = type_of gamma e1 in
        let t2 = type_of gamma e2 in
        begin
          match t1, t2 with
          | Tint, Tint
          | Tbool, Tbool -> Tbool
          | Tfun(_,_), Tfun(_,_) ->
            raise (Type_error "Error comparing functional values for equality")
          | _, _ -> raise (Type_error "error in the arguments of =")
        end
      | Prim(op, e1, e2) ->
        let t1 = type_of gamma e1 in
        let t2 = type_of gamma e2 in
        let top = lookup gamma op in
        begin
          match top with
          | Tfun(t1', Tfun(t2', tr')) ->
            if (t1' = t1 && t2' = t2) then
              tr'
            else
              raise (Type_error ("error in the arguments of " ^ op))
          | _ -> failwith "Inconsistent state"
        end
      | Call(e1, e2) ->
        let t1 = type_of gamma e1 in
        let t2 = type_of gamma e2 in
        begin
          match t1 with
          | Tfun(tx, tr) ->
            if tx = t2 then
              tr
            else
              raise (Type_error "fuctional application: argument type mismatch")
          | _ -> raise (Type_error "application to a non functional value")
        end
      | _ -> assert false    (* this should be not reachable *)


let check (Prog(topdecls)) = 
  let rec scan lst table=
    match lst with
    | x::xs -> type_of x; scan xs;
    | [] ->
 scan topdecls Symbol_table.begin_block(Symbol_table.empty_table)
   
