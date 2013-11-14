
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
and str_expr =
	| SEExpr of expr
	| SEStr of string
and instr =
	| IEmpty
	| IExpr of expr
	| IIf of expr * instr * instr
	| IWhile of expr * instr
	| IFor of expr list * expr option * expr list * instr
	| IBlock of block
	| IStdCoutWrite of str_expr list
	| IReturn of expr option
	| IDeclVar of ty_expr * ident * expr option
	| IDeclVarAssignConstruct of ty_expr * ident * ident * expr list
and block = instr list

and ty_expr =
	| TVoid
	| TInt
	| TId of ident
	| TPtr of ty_expr
	| TRef of ty_expr
and var =
	| VId of ident
	| VClsMem of ident * ident

type proto = 
	| PConstructor of constructor_proto
	| PFunction of function_proto
and constructor_proto = {
	cc_class : ident;
	cc_args : arg list;
}
and function_proto = {
	f_type : ty_expr;
	f_name : var;
	f_args : arg list;
}
and arg = {
	arg_ty : ty_expr;
	arg_name : ident;
}
and var_decl = ty_expr * ident

type cls = {
	c_name : ident;
	c_supers : ident list;
	c_vars : var_decl list;
	c_protos : proto list;
}

type program = {
	p_classes : cls list;
	p_vars : var_decl list;
	p_functions : (proto * block) list; (* class methods included in here *)
}
