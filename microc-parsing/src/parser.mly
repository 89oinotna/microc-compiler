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

  let compose f (g, s)=(fun x -> g(f(z)), s) (* using to compose with functions *)
  
%}

/* Tokens declarations TODO Remember to add null*/


%token EOF
%token ASSIGN
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
%nonassoc LBRACK
%right DEREF


/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* Grammar specification */

program:
  | l=list(topdecl) EOF               {Prog(l)}
;

topdecl:
  | fd=fundecl {Fundecl(fd) |@| $loc}
  | vd=vardecl SEMICOLON               {Vardec() |@| $loc}
;

typ:
  | INT   {TypI}
  | CHAR  {TypC}
  | BOOL  {TypB}
  | VOID  {TypV}
;


vardesc: (* functions in the couple to reconstruct the type*)
  | id=ID   {((fun t -> t), id)   }
  | TIMES vd=vardesc %prec DEREF {compose TypP vd}
  | LPAREN vd=vardesc RPAREN {vd}
  | vd=vardesc LBRACK i=option(LINT) RBRACK {compose (fun y->TypA(y, i)) vd}
;

vardecl:
  | tp=typ vd=vardesc { ((fst vd) tp, snd vd))} 
;


fundecl:
  | tp=typ id=ID LPAREN fd=separated_list(COMMA, vardecl) RPAREN b=block
                                      {{typ=tp; fname=id; formals=fd; body=b}}
;

stmtordec:
  | st=stmt {Stmt(st) |@| $loc}
  | vd=vardecl {vd |@| $loc}
;

block:
  | LBRACE lst=separated_list(SEMICOLON, stmtordec) RBRACE {}
;

block_stmt:
  | e=expr SEMICOLON                    {Expr(e) |@| $loc}
  | RETURN e=option(expr) SEMICOLON     {Return(e) |@| $loc}
  | b=block  {Block(b) |@| $loc}
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
                                            While(e2, Block(
                                              [(Stmt(st)|@| $loc); 
                                                Stmt(Expr(e3)|@| $loc)|@| $loc])|@| $loc
                                              (*Block(body@[Stmt(Expr(e3)|@| $loc) |@| $loc]) |@| $loc*)
                                            ) |@| $loc
                                          )|@| $loc
                                        ]) |@| $loc}
  | st=block_stmt                   {st}
;



expr:
  |re=rexpr {re}
  |le=lexpr {le}
;

lexpr:
  | id=ID {AccVar(id) |@| $loc}
  | LPAREN lexpr RPAREN {}
  | TIMES lexpr {AccDeref(e) |@| $loc}
  | TIMES aexpr {AccDeref(e) |@| $loc}
  | lexpr LBRACK expr RBRACK {AccIndex(a, e1) |@| $loc}
;

rexpr:
  | ae=aexpr {ae}
  | le=lexpr ASSIGN e=expr {Assign(a, e) |@| $loc}
  | NOT expr {UnaryOp(not, e)}
  | MINUS e=expr %prec UMINUS {UnaryOp(Neg, e)}
  | e1=expr bop=binaryop e2=expr {BinaryOp(bop, e1, e2)}
  | id=ID LPAREN l=separated_list(COMMA, expr) RPAREN
    {Call(id, l) |@| $loc}
;

binaryop:
  | PLUS        {Add}
  | MINUS       {Sub}
  | TIMES       {Mult}
  | DIV         {Div}
  | MOD         {Mod}
  | LESS        {Less}
  | GREATER     {Greater}
  | LEQ         {Leq}
  | GEQ         {Geq}
  | EQ          {Eq}
  | NEQ         {Neq}
  | L_OR        {Or}
  | L_AND       {And}

;

aexpr:
  | i=LINT                              {ILiteral(i) |@| $loc}
  | c=LCHAR                             {CLiteral(c) |@| $loc}
  | TRUE                                {BLiteral(true) |@| $loc}
  | FALSE                               {BLiteral(false) |@| $loc}
  | NULL                                {}
  | LPAREN re=rexpr RPAREN              {re}
  | AND lexpr                           {Addr(a) |@| $loc}    
;



