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
  
%}

/* Tokens declarations TODO Remember to add null*/


%token EOF
%token ASSIGN
%token IF ELSE RETURN FOR WHILE INT CHAR VOID BOOL TRUE FALSE NULL
%token PLUS MINUS TIMES DIV MOD AND
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
%nonassoc NOT AND
%nonassoc LBRACK


/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* Grammar specification */

program:
  | l=list(topdecl) EOF               {Prog(l)}
  | EOF                               {Prog([])}
;

topdecl:
  | tp=typ id=ID LPAREN fd=separated_list(COMMA, funvar) LBRACE b=list(stmtordec) RBRACE
                                      {Fundecl({typ=tp; fname=id; formals=fd; body=(Block(b)|@| $loc)}) |@| $loc}
  | vd=vardec SEMICOLON               {vd |@| $loc}
;

typ:
  | INT   {TypI}
  | CHAR  {TypC}
  | BOOL  {TypB}
  | VOID  {TypV}
;

funvar:
  | tp=typ id=ID LBRACK i=option(LINT) RBRACK {(TypA(tp, i), id)}
  | tp=typ TIMES id=ID                {(TypP(tp), id)}
  | tp=typ id=ID                      {(tp, id)}

vardec:
  | tp=typ id=ID LBRACK i=option(LINT) RBRACK {Vardec(TypA(tp, i), id)}
  | tp=typ TIMES id=ID                {Vardec(TypP(tp), id)}
  | tp=typ id=ID                      {Vardec(tp, id)}
;

dec:
  | tp=typ id=ID LBRACK i=option(LINT) RBRACK {Dec(TypA(tp, i), id)}
  | tp=typ TIMES id=ID                {Dec(TypP(tp), id)}
  | tp=typ id=ID                      {Dec(tp, id)}
;

stmtordec:
  | dc=dec SEMICOLON               {dc |@| $loc}
  | st=stmt                        {Stmt(st) |@| $loc}
;

stmt:
  | IF LPAREN cond=expr RPAREN st1=stmt ELSE st2=stmt            
                                        {If(cond, st1, st2) |@| $loc}
  | WHILE LPAREN cond=expr RPAREN LBRACE body=list(stmtordec) RBRACE
                                        {While(cond, Block(body)|@| $loc) |@| $loc}
  | e=expr SEMICOLON                    {Expr(e) |@| $loc}
  | RETURN e=option(expr) SEMICOLON     {Return(e) |@| $loc}
  | LBRACE body=list(stmtordec) RBRACE  {Block(body) |@| $loc}


;



expr:
  | a=access ASSIGN e=expr              {Assign(a, e) |@| $loc}
  | a=access                            {Access(a) |@| $loc}
  | AND a=access                        {Addr(a) |@| $loc}
  | i=LINT                              {ILiteral(i) |@| $loc}
  | c=LCHAR                             {CLiteral(c) |@| $loc}
  | TRUE                                {BLiteral(true) |@| $loc}
  | FALSE                               {BLiteral(false) |@| $loc}
  | NOT e=expr                          {UnaryOp(Not, e) |@| $loc}
  | MINUS e=expr                        {UnaryOp(Neg, e) |@| $loc}
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

access:
  | id=ID                               {AccVar(id) |@| $loc}  
  | TIMES e=expr                        {AccDeref(e) |@| $loc}
  | a=access LBRACK e1=expr RBRACK      {AccIndex(a, e1) |@| $loc}
;

