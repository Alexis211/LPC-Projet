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

type loc = Lexing.position * Lexing.position

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

type expression = {
	e_loc: loc;
	e_desc: expr_desc }
and expr_desc =
	| EInt of int
	| EBool of bool
	| ENull
	| EThis
	| EIdent of ident
  | EQIdent of tident * ident (* class * member name *)         
	| EAssign of expression * expression
	| ECall of expression * expression list
	| EUnary of unop * expression
	| EBinary of expression * binop * expression
	| EMember of expression * ident
	| ENew of tident * expression list

type str_expression = {
	se_loc: loc;
	se_desc : se_desc }
and se_desc =
	| SEExpr of expr_desc
	| SEStr of string

type statement = {
	s_loc: loc;
	s_desc: s_desc }
and s_desc =
	| SEmpty
	| SExpr of expression
	| SIf of expression  * statement * statement
	| SWhile of expression * statement
	| SFor of expression list * expression option * expression list * statement
	| SBlock of block
	| SReturn of expression option
	| SDeclare of var_type * ident
	| SDeclareAssignExpr of var_type * ident * expression
	| SDeclareAssignConstructor of var_type * ident * tident * expression list
			(* Type of variable, variable name, constructor class name, constructor arguments *)
	| SWriteCout of str_expression list
and block = statement list

type proto = {
	p_loc : loc;
	p_name : ident;	
	p_class : tident option; (* p_class = none : standalone function *)
	p_ret_type : var_type option; (* p_class = some and p_ret_type = none : constructor *)
	p_args : (var_type * ident) list;
}

type cls_mem =
	| CVar of var_type * ident
	| CMethod of proto * bool (* is method virtual *)

type cls = {
	c_name : tident;
	c_supers : tident list option;
	c_members : cls_mem list;
}

type declaration = {
	d_loc : loc;
	d_desc : decl_desc; }
and decl_desc =
	| DGlobal of (var_type * ident)
	| DFunction of (proto * block)
	| DClass of cls

type program = declaration list
