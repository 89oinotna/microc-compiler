type ttype =
  | Tint
  | Tbool
  | Tchar
  | Tvoid
  | Tarr of ttype * ttype
  | Tptr of ttype
  | Tfun of ttype * ttype
  | Treturn of ttype
