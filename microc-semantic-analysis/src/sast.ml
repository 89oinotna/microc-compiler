type ttype =
  | Tint
  | Tbool
  | Tchar
  | Tvoid
  | Tarr of ttype * ttype * int option
  | Tptr of ttype
  | Tfun of ttype * ttype
  | Treturn of ttype
  [@@deriving show]