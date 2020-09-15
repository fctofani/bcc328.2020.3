(* absyn.ml *)

type symbol = Symbol.symbol
[@@deriving show]

(* AST annotated with its type *)
type 'a typed = 'a * Type.ty option ref
[@@deriving show]

type exp = exp_basic typed
[@@deriving show]

and exp_basic =
  | BoolExp       of bool
  | IntExp        of int
  | StringExp     of string
  | RealExp       of float
  | NegativeExp   of lexp
  | BinaryExp     of (lexp * binary_op * lexp)
  | IfExp         of (lexp * lexp * lexp option)
  | WhileExp      of (lexp * lexp)
  | BreakExp
  | ExpSeq        of lexp list
  | CallExp       of symbol * lexp list
  | VarExp        of lvar
  | LetExp        of ldec list * lexp
  | AssignExp     of lvar * lexp
  [@@deriving show]

and binary_op =
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  | Power
  | Equal
  | NotEqual
  | GreaterThan
  | GreaterEqual
  | LowerThan
  | LowerEqual
  | And
  | Or
  [@@deriving show]

and var =
  | SimpleVar     of Symbol.symbol
  [@@deriving show]

and dec =
  | VarDec of vardec typed
  [@@deriving show]

and vardec = Symbol.symbol * Symbol.symbol option * lexp
  [@@deriving show]

and lexp = exp Location.loc  (* exp anotated with a location *)
  [@@deriving show]

and lvar = var Location.loc
  [@@deriving show]

and ldec = dec Location.loc
  [@@deriving show]

(* Annotate an ast with a dummy type representation *)
let dummyt ast = (ast, ref None)
