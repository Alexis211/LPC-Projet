
(* Syntaxe abstraite pour mini-C++ *)

(* rien à voir pour l'instant *)

type ident = string

type binop =
	| Equal | NotEqual
	| Lt | Le | Gt | Ge
	| Add | Sub | Mul | Div | Modulo
	| Land | Lor

type unop =
	| PreIncr | PostIncr | PreDecr | PostDecr
	| Ref | Deref
	| Not
	| Minus | Plus

type expr =
	| EBinop of expr * binop * expr
	| EUnary of unop * expr
	| EAssign of expr * expr
	| EIntConst of int
	| EBoolConst of bool
	| EThis
	| ENull
	| EMem of expr * ident

