open Ast
open Symbol_table
module L=Llvm

type 'a entry_table={
  llvalue:'a; 
  annotation: string option
}
  [@@deriving show]

let unpack ann_node=
  match ann_node with
  | { loc; node; id} -> node
  | _  -> assert false

(* The LLVM global context *)
let llcontext = L.global_context ()

(* Some useful LLVM IR type to use in the code generation *)
let int_type = L.i32_type llcontext
let bool_type = L.i1_type llcontext
let char_type = L.i8_type llcontext
let void_type = L.void_type llcontext


(* Translate a microc type into a LLVM IR one*)
let rec lltype_of_type = function 
  | TypI  -> int_type
  | TypB -> bool_type
  | TypC -> char_type
  | TypA(typ, i) -> 
    let tp=lltype_of_type typ in
    begin
      match i with
      |None -> L.array_type tp 0 
      |Some(x) -> L.array_type tp x
    end
  | TypP(typ) -> 
    let tp=lltype_of_type typ in
    L.pointer_type tp
  | TypV -> void_type

(* A table mapping a binary operator in the LLVM function that implemets it and its name *)
let primitive_operators = 
  [ Add, (L.build_add, "add") 
  ; Mult, (L.build_mul, "mul")
  ; Sub, (L.build_sub, "mul")
  ; Div, (L.build_sdiv, "div")
  ; Mod, (L.build_srem, "mod")
  ; Less, (L.build_icmp L.Icmp.Slt, "less")
  ; Leq, (L.build_icmp L.Icmp.Sle, "leq")
  ; Greater, (L.build_icmp L.Icmp.Sgt, "greater")
  ; Geq, (L.build_icmp L.Icmp.Sge, "geq")
  ; Equal, (L.build_icmp L.Icmp.Eq, "equal")
  ; Neq, (L.build_icmp L.Icmp.Ne, "neq")
  ; And, (L.build_and, "neq")
  ; Or, (L.build_or, "neq")
  ]

(*
let rec codegen_expr gamma ibuildedr e=
  match unpack e with
  | Access(a) ->
  | OpAssing(bop, a, ex) ->
  | Assign(a, ex) ->
  | Addr(a) ->
  | ILiteral(x) ->
  | CLiteral(x) ->
  | BLiteral(x) ->
  | UnaryOp(uop, e) ->
  | BinaryOp(bop, e) ->
  | Call(id, lst) ->
  | ArrayInit(lst) ->

let rec codegen_access gamma ibuilder e=
  match unpack e with
  | AccVar("NULL") -> L.const_null int_type
  | AccVar(id) -> (Symbol_table.lookup id gamma).llvalue
  | AccDeref(ex) -> 
        begin
          match unpack e with
          |  Access(le) -> 
            let var = codegen_le gamma ibuilder le in
            L.build_load var "" ibuilder
          |  _ -> codegen_ae gamma ibuilder e
        end
  | AccIndex(a, e) -> 
      let expr=codegen_expr gamma ibuilder e in
      codegen_le gamma ibuilder le (*TODO*) *)


let rec codegen_expr gamma ibuilder e=
      match unpack e with
      | Access(le) -> 
        let var=codegen_le gamma ibuilder le in
        L.build_load var "" ibuilder
      | _ -> codegen_re gamma ibuilder e
and codegen_ae gamma ibuilder e= 
    match unpack e with
    | Access(null) ->  L.const_null int_type
    | Addr(a) -> codegen_le gamma ibuilder a
    | ILiteral(i) -> L.const_int int_type i
    | BLiteral(b) -> L.const_int bool_type (if b then 1 else 0)
    | CLiteral(c) -> L.const_int char_type (int_of_char c)
    | _ -> codegen_re gamma ibuilder e
and codegen_le gamma ibuilder e= 
    match unpack e with
    | AccVar(id) -> (Symbol_table.lookup id gamma).llvalue
    | AccDeref(e) -> 
        begin
          match unpack e with
          |  Access(le) -> 
            let var = codegen_le gamma ibuilder le in
            L.build_load var "" ibuilder
          |  _ -> codegen_ae gamma ibuilder e
        end
    | AccIndex(le, e) -> 
      let expr=codegen_expr gamma ibuilder e in
      codegen_le gamma ibuilder le (*TODO*)
    | _ -> codegen_le gamma ibuilder e
and codegen_re gamma ibuilder e= 
    match unpack e with
    | Assign(le, e) ->
      let var=codegen_le gamma ibuilder le in
      let expr= codegen_expr gamma ibuilder e in
      L.build_store expr var ibuilder
    | OpAssign(op, le, e) -> 
      let (llvm_operator, label)=List.assoc op primitive_operators in
      let var=codegen_le gamma ibuilder le in
      let var_value= L.build_load var ""(*"opassign "^id*) ibuilder in
      let expr= codegen_expr gamma ibuilder e in
      let res= llvm_operator var_value expr label ibuilder in
      L.build_store res var ibuilder
    | UnaryOp(uop, e) ->
      begin
        match uop with
        | Not -> 
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_not var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          var_val
        | Neg -> 
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_neg var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          var_val
        | PreInc -> 
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          (*let var=codegen_expr gamma ibuilder e in*)
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_add (L.const_int int_type 1) var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          op
        | PreDec -> 
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_sub (L.const_int int_type 1) var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          op
        | PostInc ->
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_add (L.const_int int_type 1) var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          var_val
        | PostDec ->
          let var=
            match unpack e with
            | Access(le) -> codegen_le gamma ibuilder le
            |_ -> assert false
            in
          let var_val= L.build_load var "" ibuilder in
          let op=L.build_sub (L.const_int int_type 1) var_val "" ibuilder in
          let _=L.build_store op var ibuilder in
          var_val
      end
    | BinaryOp(bop, e1, e2) -> 
      let te1 = codegen_expr gamma ibuilder e1 in 
      let te2 = codegen_expr gamma ibuilder e2 in 
      let (llvm_operator, label) = List.assoc bop primitive_operators in 
      llvm_operator te1 te2 "" ibuilder
    | Call(id, lst) ->
      let f = (Symbol_table.lookup id gamma).llvalue in
      let llargs=List.map (codegen_expr gamma ibuilder) lst in 
      L.build_call f (Array.of_list llargs) "" ibuilder
    | _ -> codegen_ae gamma ibuilder e
(*Add or not terminator depending on last instruction (terminal) *)
let add_terminator ibuilder next=
  let terminator= L.block_terminator (L.insertion_block ibuilder) in
        match terminator with
        | Some _ -> ()
        | None -> ignore(L.build_br next ibuilder)

let rec codegen_stmt current_fun gamma ibuilder e= 
  match unpack e with
  | If(e1, st1, {node=Block([]); id=id}) -> 
      let bthen = L.append_block llcontext "then" current_fun in 
      let bcont = L.append_block llcontext "cont" current_fun in 
      let te1 = codegen_expr gamma ibuilder e1 in 
      let _ = L.build_cond_br te1 bthen bcont ibuilder in
      let te2 =L.position_at_end bthen ibuilder in
      let _ = codegen_stmt current_fun gamma ibuilder st1 in  
        add_terminator ibuilder bcont;
        L.position_at_end bcont ibuilder;
        ibuilder
  | If(e1, st1, st2) ->
      let bthen = L.append_block llcontext "then" current_fun in 
      let belse = L.append_block llcontext "else" current_fun in 
      let bcont = L.append_block llcontext "cont" current_fun in 
      let te1 = codegen_expr gamma ibuilder e1 in 
      let _ = L.build_cond_br te1 bthen belse ibuilder in
      let _ = L.position_at_end bthen ibuilder in
      let te2 = codegen_stmt current_fun gamma ibuilder st1 in 
      let _ = add_terminator ibuilder bcont in 
      let _=L.position_at_end belse ibuilder in
      let te3 = codegen_stmt current_fun gamma ibuilder st2 in 
      let _ = add_terminator ibuilder bcont in 
        L.position_at_end bcont ibuilder;
        ibuilder
        (*Llvm.build_phi [(te2, bthen) ; (te3, belse)] "phi" ibuilder*)
  | While(e, stmt) ->
      let pred=L.append_block llcontext "while_cond" current_fun in
      let bwhile=L.append_block llcontext "while_body" current_fun in
      let bcont=L.append_block llcontext "cont" current_fun in
      let _ = L.build_br pred ibuilder in
      L.position_at_end pred ibuilder;
      let re=codegen_expr gamma ibuilder e in
      let _ = L.build_cond_br re bwhile bcont ibuilder in
      L.position_at_end pred ibuilder;
      let body=codegen_stmt current_fun gamma ibuilder stmt in
      let _=L.build_br pred ibuilder in
        L.position_at_end bcont ibuilder;
        ibuilder
    | DoWhile(stmt, e) -> 
      let bwhile=L.append_block llcontext "while_body" current_fun in
      let pred=L.append_block llcontext "do_while_cond" current_fun in
      let bcont=L.append_block llcontext "cont" current_fun in
      let _= L.build_br bwhile ibuilder in
      L.position_at_end bwhile ibuilder;
      let body=codegen_stmt current_fun gamma ibuilder stmt in
      let _=L.build_br pred ibuilder in
      L.position_at_end bwhile ibuilder;
      let re=codegen_expr gamma ibuilder e in
      let _=L.build_cond_br re bwhile bcont ibuilder in
        L.position_at_end bcont ibuilder;
        ibuilder
  | Expr(e) -> 
        ignore(codegen_expr gamma ibuilder e);
        ibuilder
  | Return(ex) -> 
    ignore(begin
      match ex with
      | None -> L.build_ret_void ibuilder
      | Some(x) -> let ret=codegen_expr gamma ibuilder x in 
                    L.build_ret ret ibuilder
    end);
    ibuilder
  | Block(lst) -> 
      ignore(List.fold_left (codegen_stmtordec current_fun gamma) ibuilder lst);
        ibuilder
and codegen_stmtordec current_fun gamma ibuilder e=
    match unpack e with
    | Dec(typ, id) -> 
        let tp=lltype_of_type typ in
        let local=L.build_alloca tp id ibuilder
        in
          Symbol_table.add_entry id ({llvalue=local; annotation=Some(id)}) gamma;
          ibuilder
    | Stmt(st) -> codegen_stmt current_fun gamma ibuilder st; ibuilder
    (*| Decinit(typ, id, ex) -> 
        let tp=lltype_of_type typ in
        let local=L.build_alloca tp id ibuilder in
        let init=codegen_init gamma ibuilder e in
        let _ = L.build_store init local ibuilder in
          Symbol_table.add_entry id ({llvalue=local; annotation=Some(id)}) gamma;
          ibuilder*)
  
let codegen_fundecl gamma {typ; fname; formals; body;} llmodule=
  let return_type = lltype_of_type typ in 
  let formals_type = 
        let f arr (typ, id)= Array.append arr [|lltype_of_type typ|]
          in
        List.fold_left f [||] formals  
      in
  let fun_type=
    L.function_type return_type formals_type 
  in
  let fundef = L.define_function fname fun_type llmodule in
  let _ =  Symbol_table.add_entry fname ({llvalue=fundef; annotation=None}) gamma in
  let ibuilder = L.builder_at_end llcontext (L.entry_block fundef) in
  let scope=Symbol_table.begin_block gamma in
  let _ = 
    let f i (typ, id)= 
      (* Allocating params on the function's stack *)
      let param_alloc=L.build_alloca (formals_type.(i)) id ibuilder in
      let param=L.param fundef i in
      let _=L.build_store param param_alloc ibuilder in
      ignore(Symbol_table.add_entry id ({llvalue=param_alloc; annotation=Some(id)}) scope);
      i+1
    in List.fold_left f 0 formals 
  in
   ignore(codegen_stmt fundef scope ibuilder body);
   fundef
  

let codegen_topdecl gamma e llmodule=
  match unpack e with
  | Fundecl(f) -> codegen_fundecl gamma f llmodule
  | Vardec(typ, id) -> 
    let tp=lltype_of_type typ in
    let global=L.declare_global tp id llmodule in
    Symbol_table.add_entry id ({llvalue=global; annotation=Some(id)}) gamma;
    global
  (*| Vardecinit(typ, id, expr) -> 
    let tp=lltype_of_type typ in
    let global=L.define_global id (codegen_init gamma expr llmodule) llmodule in
    Symbol_table.add_entry id ({llvalue=global; annotation=Some(id)}) gamma;
    global *)

(* Declare in the current module the print prototype *)  
let print_declaration llvm_module scope =
  let print_t = L.function_type void_type [| int_type |] in
  let decl=L.declare_function "print" print_t llvm_module in
  Symbol_table.add_entry "print" ({llvalue=decl; annotation=None}) scope

(* Declare in the current module the getint prototype *)  
let getint_declaration llvm_module scope =
  let getint_t = L.function_type int_type [| |] in
  let decl=L.declare_function "getint" getint_t llvm_module in
  Symbol_table.add_entry "getint" ({llvalue=decl; annotation=None}) scope           

let to_ir (Prog(topdecls)) =
  let scope=(Symbol_table.begin_block(Symbol_table.empty_table)) in
  let llmodule = L.create_module llcontext "microc-module" in 
    print_declaration llmodule scope |> ignore;
    getint_declaration llmodule scope |> ignore;
    let rec scan lst scope llmodule=
      match lst with
      | x::[] -> codegen_topdecl scope x llmodule
      | x::xs -> codegen_topdecl scope x llmodule; scan xs scope llmodule
      | [] -> assert false
      in
    scan topdecls scope llmodule;
    llmodule