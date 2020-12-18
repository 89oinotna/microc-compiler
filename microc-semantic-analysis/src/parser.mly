/*
* MicroC Parser specification
*/

%{
    open Ast

    (* Define here your utility functions 

        | IF LPAREN cond=expr RPAREN st1=stmt
                                        {If(cond, st1, Block()) |@| $loc}
                                          | FOR LPAREN e1=option(expr) SEMICOLON e2=option(expr) SEMICOLON e3=option(expr) RPAREN LBRACE body=list(stmtordec) RBRACE 
                                        {Block([
                                          Stmt(e1) |@| $loc;
                                          Stmt( 
                                            While(e2, 
                                              Block(body@(Stmt(e3) |@| $loc)) |@| $loc
                                            ) |@| $loc
                                          )|@| $loc
                                        ]) |@| $loc}
                                        
*)
  let (|@|) nd loc = { node = nd; loc = loc ; id=0} 

  let compose f (g, s)=((fun x -> g(f(x))), s) (* using to compose with functions *)
  
  let funcblock b=
    match b with
    |{node;loc;id}->{node;loc;1} 
%}

/* Tokens declarations TODO Remember to add null*/


%token EOF
%token ASSIGN ADDASS SUBASS MULTASS DIVASS MODASS
%token IF ELSE RETURN FOR WHILE INT CHAR VOID BOOL TRUE FALSE NULL DO
%token PLUS MINUS TIMES DIV MOD AND INC DEC
%token EQ NEQ LESS GREATER LEQ GEQ L_OR L_AND NOT
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token <string>ID
%token <int>LINT
%token <char>LCHAR
%token SEMICOLON COMMA COLON


/* Precedence and associativity specification */

%right ASSIGN 
%left L_OR
%left L_AND
%left EQ NEQ
%nonassoc GREATER LESS LEQ GEQ
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc NOT AND UMINUS 
%right PRE DEREF
%left POST
%nonassoc LBRACK


/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* Grammar specification */

program:
  | l=list(topdecl) EOF               {Prog(l)}
;

topdecl:
  | fd=fundecl              {Fundecl(fd) |@| $loc}
  | vd=vardecl SEMICOLON    {Vardec(fst vd, snd vd) |@| $loc}
  | vd=vardecinit SEMICOLON {Vardecinit(fst vd, fst (snd vd), snd (snd vd)) |@| $loc}
;

vardecinit:
 | vd=vardecl ASSIGN e=rexpr {(fst vd, (snd vd, e))}
;

vardecl:
  | tp=typ vd=vardesc { ((fst vd) tp, snd vd)}  (* (typ,id) *)
;

vardesc: (* functions in the couple to reconstruct the type*)
  | id=ID                         {((fun t -> t), id)   }
  | TIMES vd=vardesc  %prec DEREF {compose (fun t->TypP(t)) vd}
  | LPAREN vd=vardesc RPAREN      {vd}
  | vd=vardesc LBRACK i=option(LINT) RBRACK 
                                  {compose (fun t -> TypA(t, i)) vd}
;

fundecl:
  | tp=typ id=ID LPAREN fd=separated_list(COMMA, vardecl) RPAREN b=block
                                      {{typ=tp; fname=id; formals=fd; body=(funcblock b)}}
;

stmtordec:
  | st=stmt {Stmt(st) |@| $loc}
  | vd=vardecl SEMICOLON {Dec(fst vd, snd vd) |@| $loc}
  | vd=vardecinit SEMICOLON {Decinit(fst vd, fst (snd vd), snd (snd vd)) |@| $loc}
;

block:
  | LBRACE lst=list(stmtordec) RBRACE {Block(lst) |@| $loc}
;

block_stmt:
  | e=expr SEMICOLON                     {Expr(e) |@| $loc}
  | RETURN e=option(expr) SEMICOLON       {Return(e) |@| $loc}
  | b=block                     {b}
  | IF LPAREN cond=expr RPAREN st1=block_stmt  
                                {If(cond, st1, Block([])|@| $loc) |@| $loc}
;

stmt:
  | IF LPAREN cond=expr RPAREN st1=block_stmt ELSE st2=block_stmt      
                                        {If(cond, st1, st2) |@| $loc}
  | WHILE LPAREN cond=expr RPAREN st=block_stmt(*LBRACE body=list(stmtordec) RBRACE*)
                                        {While(cond, st) |@| $loc}
  | DO st=block_stmt WHILE LPAREN cond=expr RPAREN SEMICOLON
                                        {DoWhile(st, cond) |@| $loc}
  | FOR LPAREN e1=expr SEMICOLON e2=expr SEMICOLON e3=expr RPAREN st=block_stmt (* LBRACE body=list(stmtordec) RBRACE *)
                                        {Block([
                                          Stmt(Expr(e1)|@| $loc) |@| $loc;
                                          Stmt( 
                                            While(e2, 
                                                  Block(
                                                    [(Stmt(st)|@| $loc); 
                                                    Stmt(Expr(e3)|@| $loc)|@| $loc])|@| $loc
                                              (*Block(body@[Stmt(Expr(e3)|@| $loc) |@| $loc]) |@| $loc*)
                                            ) |@| $loc
                                          )|@| $loc
                                        ]) |@| $loc}
  | st=block_stmt                       {st}
;



expr:
  |re=rexpr  {re}
  |le=lexpr {Access(le) |@| $loc}
;

lexpr:
  | id=ID                   {AccVar(id) |@| $loc}
  | LPAREN le=lexpr RPAREN        {le}
  | TIMES le=lexpr                {AccDeref(Access(le)|@| $loc) |@| $loc}
  | TIMES ae=aexpr                {AccDeref(ae) |@| $loc}
  | le=lexpr LBRACK e=expr RBRACK {AccIndex(le, e) |@| $loc}
;

rexpr:
  | ae=aexpr                     {ae}
  | le=lexpr ASSIGN e=expr       {Assign(le, e) |@| $loc}
  | le=lexpr op=opassign e=expr %prec ASSIGN  
    {OpAssign(op, le, e) |@| $loc}
  | NOT e=expr                   {UnaryOp(Not, e)|@| $loc}
  | MINUS e=expr %prec UMINUS    {UnaryOp(Neg, e)|@| $loc}
  | INC le=lexpr                 {UnaryOp(PreInc, Access(le)|@| $loc)|@| $loc}
  | DEC le=lexpr                 {UnaryOp(PreDec, Access(le)|@| $loc)|@| $loc}
  | le=lexpr INC                 {UnaryOp(PostInc, Access(le)|@| $loc)|@| $loc}
  | le=lexpr DEC                 {UnaryOp(PostDec, Access(le)|@| $loc)|@| $loc}
  | e1 = expr PLUS e2 = expr
    { BinaryOp(Add, e1, e2) |@| $loc }
  | e1 = expr MINUS e2 = expr
    { BinaryOp(Sub, e1, e2) |@| $loc }
  | e1 = expr TIMES e2 = expr
    { BinaryOp(Mult, e1, e2) |@| $loc }
  | e1 = expr DIV e2 = expr
    { BinaryOp(Div, e1, e2) |@| $loc }
  | e1 = expr MOD e2 = expr
    { BinaryOp(Mod, e1, e2) |@| $loc }
  | e1 = expr LESS e2 = expr
    { BinaryOp(Less, e1, e2) |@| $loc }
  | e1 = expr GREATER e2 = expr
    { BinaryOp(Greater, e1, e2) |@| $loc }
  | e1 = expr LEQ e2 = expr
    { BinaryOp(Leq, e1, e2) |@| $loc }
  | e1 = expr GEQ e2 = expr
    { BinaryOp(Geq, e1, e2) |@| $loc }
  | e1 = expr EQ e2 = expr
    { BinaryOp(Equal, e1, e2) |@| $loc }
  | e1 = expr NEQ e2 = expr
    { BinaryOp(Equal, e1, e2) |@| $loc }
  | e1 = expr L_OR e2 = expr
    { BinaryOp(Or, e1, e2) |@| $loc }
  | e1 = expr L_AND e2 = expr
    { BinaryOp(And, e1, e2) |@| $loc }
  | id=ID LPAREN l=separated_list(COMMA, expr) RPAREN
    {Call(id, l) |@| $loc}
;


aexpr:
  | i=LINT                      {ILiteral(i) |@| $loc}
  | c=LCHAR                     {CLiteral(c) |@| $loc}
  | TRUE                        {BLiteral(true) |@| $loc}
  | FALSE                       {BLiteral(false) |@| $loc}
  | NULL                        {Access(AccVar("NULL")|@| $loc)|@| $loc}
  | LPAREN re=rexpr RPAREN      {re}
  | AND le=lexpr                {Addr(le) |@| $loc}    
;


typ:
  | INT   {TypI}
  | CHAR  {TypC}
  | BOOL  {TypB}
  | VOID  {TypV}
;

opassign:
  | ADDASS    {Add}
  | SUBASS    {Sub} 
  | MULTASS   {Mult} 
  | DIVASS    {Div}
  | MODASS    {Mod}





