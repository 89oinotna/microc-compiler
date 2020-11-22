/*
* MicroC Parser specification
*/

%{
    open Ast

    (* Define here your utility functions *)


%}

/* Tokens declarations */


%token EOF
%token ASSIGN
%token IF ELSE RETURN FOR WHILE INT CHAR VOID NULL BOOL TRUE FALSE
%token PLUS MINUS TIMES DIV MOD AND
%token EQ NEQ LESS GREATER LEQ GEQ L_OR L_AND NOT
%token LPAREN RPAREN LBRACE RBRACE LBRACK RBRACK
%token <string>ID
%token <int>LINT
%token <char>LCHAR
%token SEMICOLON COLON COMMA


/* Precedence and associativity specification */
%right ASSIGN
%left L_OR
%left L_AND
%left EQ NEQ
%nonassoc GREATER LESS LEQ GEQ
%left PLUS MINUS
%left TIMES DIV MOD
%nonassoc NOT AND


/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* Grammar specification */

program:
  | list(topdecl)=l EOF               {Prog(l)}
  | EOF                               {Prog([])}
;

topdecl:
  | tp=typ id=ID LPAREN fd=separated_list(COMMA, vd=vardec) RPAREN LBRACE body=block RBRACE 
                                      {Fundecl(tp, id, fd, body)}
  | vd=vardec SEMICOLON               {Vardec(vd)}
;

typ:
  | INT   {TypI}
  | CHAR  {TypC}
  | BOOL  {TypB}
  | VOID  {TypV}
;

vardec:
  | tp=typ id=ID LBRACK i=option(LINT) RBRACK {TypA(tp, i), id}
  | tp=typ TIMES id=ID                {TypP(tp), id}
  | tp=typ id=ID                      {tp, id}
;

block:
  | l=list(stmtordec)  {l}
;

stmtordec:
  | dc=vardec SEMICOLON               {Dec(dc)}
  | st=stmt                           {Stmt(st)}
;

stmt:
  | IF LPAREN cond=expr RPAREN LBRACE body_if=block RBRACE ELSE LBRACE body_else=block RBRACE            
                                      {If(cond, body_if, body_else)}
  | WHILE LPAREN cond=expr RPAREN LBRACE body=block RBRACE
                                      {While(cond, body)}
  | e=expr SEMICOLON                  {Expr(e)}
  | RETURN e=option(expr) SEMICOLON   {Return(e)}
  | LBRACE body=block RBRACE          {Block(body)}
;

expr:
  | a=access                            {Access(a)}
  | a=access ASSIGN e=expr              {Assign(a, e)}
  | AND a=access                        {Addr(a)}
  | i=LINT                              {ILiteral(i)}
  | c=LCHAR                             {CLiteral(c)}
  | TRUE                                {BLiteral(true)}
  | FALSE                               {BLiteral(false)}
  | NOT e=expr                          {UnaryOp(Not, e)}
  | MINUS e=expr                        {UnaryOp(Minus, e)}
  | e1 = expr PLUS e2 = expr
    { BinaryOp(Add, e1, e2) }
  | e1 = expr MINUS e2 = expr
    { BinaryOp(Sub, e1, e2) }
  | e1 = expr TIMES e2 = expr
    { BinaryOp(Mult, e1, e2) }
  | e1 = expr DIV e2 = expr
    { BinaryOp(Div, e1, e2) }
  | e1 = expr MOD e2 = expr
    { BinaryOp(Mod, e1, e2) }
  | e1 = expr LESS e2 = expr
    { BinaryOp(Less, e1, e2) }
  | e1 = expr GREATER e2 = expr
    { BinaryOp(Greater, e1, e2) }
  | e1 = expr LEQ e2 = expr
    { BinaryOp(Leq, e1, e2) }
  | e1 = expr GEQ e2 = expr
    { BinaryOp(Geq, e1, e2) }
  | e1 = expr EQ e2 = expr
    { BinaryOp(Equal, e1, e2) }
  | e1 = expr NEQ e2 = expr
    { BinaryOp(Equal, e1, e2) }
  | e1 = expr L_OR e2 = expr
    { BinaryOp(Or, e1, e2) }
  | e1 = expr L_AND e2 = expr
    { BinaryOp(And, e1, e2) }
  | id=ID LPAREN l=separated_list(expr) RLPAREN
    {Call(id, l)}
;

access:
  | id=ID
  | TIMES id=ID
  | id=ID LRBRACK e=expr RBRACK


