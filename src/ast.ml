(*
	Langages de Programmation et Compilation (J.-C. Filliatre)
	2013-2014
	Alex AUVOLAT

	AST for Mini-C++
*)

module Sset = Set.Make(String)
let type_names = ref Sset.empty

type ident = string
type tident = string

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

type var_type =
	| TVoid
	| TInt
	| TPtr of var_type
	| TRef of var_type
	| TIdent of tident

type expression =
	| EInt of int
	| EBool of bool
	| ENull
	| EIdent of ident
	| EAssign of expression * expression
	| ECall of expression * expression list
	| EUnary of unop * expression
	| EBinary of expression * binop * expression

type statement =
	| SEmpty
	| SExpr of expression
	| SIf of expression  * statement * statement
	| SWhile of expression * statement
	| SFor of expression list * expression option * expression list * statement
	| SBlock of block
	| SReturn of expression option
	| SDeclare of ident * var_type * expression option
and block = statement list

type proto = {
	p_name : ident;
	p_ret_type : var_type;
	p_args : (ident * var_type) list;
}

type declaration =
	| DGlobal of (ident * var_type)
	| DFunction of (proto * block)

type program = declaration list
