{
    open Parser
  (*| '\''                   {read_char lexbuf}*)
    exception Lexing_error of string
    exception Char_error
    let create_hashtable size init =
        let tbl = Hashtbl.create size in
        List.iter (fun (key, data) -> Hashtbl.add tbl key data) init;
        tbl

    let keyword_table =
    create_hashtable 12 [
        ("if", IF);
        ("else", ELSE);
        ("return", RETURN);
        ("for", FOR);
        ("while", WHILE);
        ("int", INT);
        ("char", CHAR);
        ("void", VOID);
        ("NULL", NULL);
        ("bool", BOOL);
        ("true", TRUE);
        ("false", FALSE);
        ("do", DO)
    ]

    let read_char c=if c.[0]=='\\' then 
    match c.[1] with
    | '\\' -> '\\'
    | 'n' -> '\n'
    | 'b' -> '\b'
    | 't' -> '\t'
    | 'r' -> '\r'
    | _ -> raise Char_error
    else c.[0]




}

let digit = ['0'-'9']
let one_to_nine = ['1'-'9']
let int = (one_to_nine digit*) | '0'
let char=['a'-'z' 'A'-'Z' '0'-'9']
let id = ['a'-'z' 'A'-'Z' '_']['_' 'a'-'z' 'A'-'Z' '0'-'9']*

rule token = parse
  | int as inum            {
                            let num = int_of_string inum in
			                        LINT(num)
                           }
  | id as word             {
                            try
                              Hashtbl.find keyword_table word
                              
                            with Not_found ->  ID(word)
                           }
  
  |"'" ([^'\\'] | ('\\' ('\\' | 'n' | 'b' | 't' | 'r'))) as c "'" {try LCHAR(read_char c)
                                                                    with
                                                                    |Char_error -> Util.raise_lexer_error lexbuf ("Illegal character " ^  c)}
  | "/*"                   {read_comment 0 lexbuf}
  | "//"                   {read_comment 1 lexbuf}
  | ';'                    { SEMICOLON }
  | "++"                   { INC }
  | '+'                    { PLUS }
  | "--"                   { DEC }
  | '-'                    { MINUS }
  | '*'                    { TIMES }
  | '/'                    { DIV }
  | '%'                    { MOD }    
  | '='                    { ASSIGN }
  | "+="                   { ADDASS }
  | "-="                   { SUBASS }
  | "/="                   { DIVASS }
  | "%="                   { MODASS }
  | "*="                   { MULTASS }
  | "=="                   { EQ } 
  | "!="                   { NEQ } 
  | '<'                    { LESS }
  | '>'                    { GREATER }
  | "<="                   { LEQ }
  | ">="                   { GEQ }
  | "&&"                   { L_AND }
  | "||"                   { L_OR }
  | '!'                    { NOT }
  | '&'                    { AND }
  | ':'                    { COLON  }
  | ','                    { COMMA  }
  | '{'                    { LBRACE }
  | '}'                    { RBRACE }
  | '['                    { LBRACK }
  | ']'                    { RBRACK }
  | '('                    { LPAREN }
  | ')'                    { RPAREN }
  | [' ' '\t']             { token lexbuf }
  | '\n' | '\r'                   { Lexing.new_line lexbuf; token lexbuf }
  | eof                    { EOF }
  | _ as c           { Util.raise_lexer_error lexbuf ("Illegal character " ^ Char.escaped c) }

and read_comment tp = parse
  | eof                     { if tp=0 then 
                                Util.raise_lexer_error lexbuf ("Comments not closed") 
                              else 
                                EOF }
  |"*/"                     {if tp=0 then token lexbuf else read_comment tp lexbuf}      
  | '\n'                    {if tp=0 then read_comment tp lexbuf else token lexbuf}
  | _                       {read_comment tp lexbuf}



  
