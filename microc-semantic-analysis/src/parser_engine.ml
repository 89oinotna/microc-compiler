let parse lexbuf =
  try
    Parser.program Scanner.token lexbuf
  with
| Parser.Error -> Util.raise_syntax_error lexbuf (Lexing.lexeme lexbuf);;
