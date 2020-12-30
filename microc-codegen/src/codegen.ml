open Ast
open Symbol_table
module L=Llvm

type 'a entry_table={
  ttype:'a; 
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
      |None -> ()(*TODO*) 
      |Some(x) -> L.array_type tp x
    end
  | TypP(typ) -> 
    let tp=lltype_of_type typ in
    L.pointer_type tp
  | TypV -> void_type

(* A table mapping a binary operator in the LLVM function that implemets it and its name *)
let primitive_operators = 
  [ "Add", (L.build_add, "add") 
  ; "Mult", (L.build_mul, "mul")
  ; "Sub", (L.build_sub, "mul")
  ; "Div", (L.build_sdiv, "div")
  ; "Mod", (L.build_srem, "mod")
  ; "Less", (L.build_icmp L.Icmp.Slt, "less")
  ; "Leq", (L.build_icmp L.Icmp.Sle, "leq")
  ; "Greater", (L.build_icmp L.Icmp.Sgt, "greater")
  ; "Geq", (L.build_icmp L.Icmp.Sge, "geq")
  ; "Equal", (L.build_icmp L.Icmp.Eq, "equal")
  ; "Neq", (L.build_icmp L.Icmp.Ne, "neq")
  ; "And", (L.build_and, "neq")
  ; "Or", (L.build_or, "neq")
  ; "Neg", (L.build_neg, "neg")
  ; "Not", (L.build_not, "not")
  ]

let rec codegen_expr gamma ibuilder e=
  let rec codegen_access gamma ibuilder e=
    match e with
    | AccVar(id) -> 
      let var=Symbol_table.lookup id gamma in
      L.build_load var id ibuilder
    | AccDeref(ex) ->
      let ptr=Symbol_table.lookup id gamma in
      ()
    | AccIndex(a, ex) ->
  in
  match e with
  | Access(a) -> codegen_access gamma ibuilder a
  | OpAssign(op, a, ex) ->
  | Assign(a, ex) ->
  | Addr(a) ->
  | ILiteral(i) ->
  | BLiteral(b) ->
  | CLiteral(c) ->
  | UnaryOp(op, ex) ->
  | BinaryOp(op, ex1, ex2) ->
  | Call(id, lst) ->

let rec codegen_stmt current_fun gamma ibuilder e= 
  let rec codegen_stmtordec current_fun gamma ibuilder e=
    match e with
    | Dec(typ, id) -> 
      let tp=lltype_of_type typ in
      let local=L.build_alloca tp id ibuilder
      in
      Symbol_table.add_entry id local gamma;
      ibuilder
    | Stmt(st) -> codegen_stmt current_fun gamma ibuilder st; ibuilder
    | Decinit(typ, id, ex) -> 
      let tp=lltype_of_type typ in
      let local=L.build_alloca tp id ibuilder in
      let expr=codegen_expr gamma ibuilder e in
      let _ = L.build_store expr local ibuilder
      Symbol_table.add_entry id local gamma;
      ibuilder
  in
  match e with
  | If(e1, e2, e3) ->
    let bthen = L.append_block llcontext "then" current_fun in 
    let belse = L.append_block llcontext "else" current_fun in 
    let bcont = L.append_block llcontext "cont" current_fun in 
    let te1 = codegen_expr gamma ibuilder e1 in 
    let _ = L.build_cond_br te1 bthen belse ibuilder in
    Llvm.position_at_end bthen ibuilder;
    let te2 = codegen_expr gamma ibuilder e2 in 
    let _ = L.build_br belse ibuilder in 
    Llvm.position_at_end belse ibuilder;
    let te3 = codegen_expr gamma ibuilder e3 in 
    let _ = L.build_br bcont ibuilder in 
    Llvm.position_at_end bcont ibuilder;
    Llvm.build_phi [(te2, bthen) ; (te3, belse)] "phi" ibuilder
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
    L.position_at_end bcont ibuilder
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
    L.position_at_end bcont ibuilder
  | Expr(e) -> codegen_expr gamma ibuilder e 
  | Return(e) -> 
    begin
      match ex with
      | None -> L.build_ret_void ibuilder
      | Some(x) -> let ret=codegen_expr gamma ibuilder x in 
                    L.build_ret ret ibuilder
    end
  | Block(lst) -> List.fold_left (codegen_stmtordec current_fun gamma) ibuilder lst


 
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
    Symbol_table.add_entry fname fundef gamma;
  let ibuilder = L.builder_at_end llcontext (L.entry_block fundef) in
  let scope=Symbol_table.begin_block gamma in
  let _ = 
    let f (typ, id) i= 
      (* Allocating params on the function's stack *)
      let param_alloc=L.build_alloca (formals_type.(i)) id ibuilder in
      let param=L.param fundef i in
      let _=L.build_store param param_alloc ibuilder in
      Symbol_table.add_entry id param_alloc scope
    in List.fold_left f formals 0
  in
   codegen_stmt fundef scope ibuilder fbody
  


let codegen_topdecl gamma e llmodule=
  match unpack e with
  | Fundecl(f) -> codegen_fun gamma f llmodule
  | Vardec(typ, id) -> 
    let tp=lltype_of_type typ in
    let global=L.declare_global tp id llmodule in
    Symbol_table.add_entry id global gamma;
    global
  | Vardecinit(typ, id, expr) -> 
    let tp=lltype_of_type typ in
    let global=L.define_global id (codegen_expr gamma expr llmodule) llmodule in
    Symbol_table.add_entry id global gamma;
    global 

(* Declare in the current module the printf prototype *)  
let printf_declaration llvm_module =
  let printf_t = L.var_arg_function_type int_type [| L.pointer_type char_type |] in
  L.declare_function "printf" printf_t llvm_module            

let to_ir (Prog(topdecls)) =
  let scope=(Symbol_table.begin_block(Symbol_table.empty_table)) in
  let llmodule = L.create_module llcontext "microc-module" in 
    printf_declaration llmodule |> ignore;
    let rec scan lst scope llmodule=
      match lst with
      | x::xs -> codegen_topdecl scope x llmodule; scan xs scope llmodule
      | x::[] -> codegen_topdecl scope x llmodule
      | [] -> assert false
      in
    scan topdecls scope llmodule;
    llmodule