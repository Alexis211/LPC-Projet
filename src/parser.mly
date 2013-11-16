(*
	Langages de Programmation et Compilation (J.-C. Filliatre)
	2013-2014
	Alex AUVOLAT

	Parser for Mini-C++
*)

%{
	open Ast

	type var =
		| VId of ident
		| VPtr of var
		| VRef of var
	let rec reverse_var bt v = match v with
		| VId(i) -> i, bt
		| VPtr(vv) -> let id, ty = reverse_var bt vv in id, TPtr(ty)
		| VRef(vv) -> let id, ty = reverse_var bt vv in id, TRef(ty)
%}

%token <int> INTVAL
%token <string> STRVAL
%token <string> IDENT
%token <string> TIDENT

(* this is stupid *)
%token INCLUDE_IOSTREAM STD_COUT

(* keywords *)
%token CLASS ELSE FALSE FOR IF INT NEW NULL PUBLIC RETURN
%token THIS TRUE VIRTUAL VOID WHILE

(* operators *)
%token ASSIGN LOR LAND EQ NE LT LE GT GE PLUS MINUS
%token TIMES DIV MOD NOT INCR DECR REF
%token LPAREN RPAREN RARROW DOT

(* other symbols *)
%token SEMICOLON COLON DOUBLECOLON LFLOW LBRACE RBRACE COMMA EOF


(* operator priority *)
%right ASSIGN
%left LOR
%left LAND
%left EQ NE
%left LT LE GT GE
%left PLUS MINUS
%left TIMES DIV MOD
%right UNARY
%left RARROW DOT LPAREN

%start <Ast.program> prog

%%

prog:
	INCLUDE_IOSTREAM?
	decls = declaration*
	EOF
	{ List.flatten decls }
;

declaration:
|	ident = typed_var
	LPAREN args = typed_var* RPAREN
	b = block
	{ [ DFunction({p_ret_type = snd ident; p_name = fst ident; p_args = args}, b) ] }
|	vars = typed_vars
	SEMICOLON
	{ List.map (fun k -> DGlobal(k)) vars }
;

typed_var:
|	b = base_type
	x = var
	{ reverse_var b x }
;

typed_vars:
|	b = base_type
	x = separated_nonempty_list(COMMA, var)
	{ List.map (reverse_var b) x }
;

base_type:
|	VOID { TVoid }
|	INT	{ TInt }
|	t = TIDENT { TIdent(t) }
;

var:
|	t = IDENT { VId(t) }
|	TIMES v = var { VPtr(v) }
|	REF v = var { VRef(v) }
;

block:
|	LBRACE
	i = statement*
	RBRACE
	{ i }
;

statement:
|	SEMICOLON
	{ SEmpty }
|	e = expression SEMICOLON { SExpr(e) }
|	IF LPAREN c = expression RPAREN s = statement
	{ SIf(c, s, SEmpty) }
|	IF LPAREN c = expression RPAREN s = statement ELSE t = statement
	{ SIf(c, s, t) }
|	WHILE LPAREN c = expression RPAREN s = statement
	{ SWhile(c, s) }
|	FOR LPAREN k = separated_list(COMMA, expression) SEMICOLON
	c = expression? SEMICOLON 
	r = separated_list(COMMA, expression) RPAREN
	b = statement
	{ SFor(k, c, r, b) }
|	b = block
	{ SBlock (b) }
|	RETURN e = expression? SEMICOLON
	{ SReturn (e) }
|	k = typed_var v = preceded(ASSIGN, expression)? SEMICOLON
	{ SDeclare(fst k, snd k, v) }
;

expression:
|	NULL { ENull }
|	i = INTVAL { EInt(i) }
|	TRUE { EBool(true) }
|	FALSE { EBool(false) }
|	i = IDENT { EIdent(i) }
|	e1 = expression ASSIGN e2 = expression { EAssign(e1, e2) }
|	b = binop { b }
|	a = unop { a }
|	LPAREN e = expression RPAREN { e }
;

binop:
|	a = expression EQ b = expression { EBinary(a, Equal, b) }
|	a = expression NE b = expression { EBinary(a, NotEqual, b) }
|	a = expression LAND b = expression { EBinary(a, Land, b) }
|	a = expression LOR b = expression { EBinary(a, Lor, b) }
|	a = expression GT b = expression { EBinary(a, Gt, b) }
|	a = expression GE b = expression { EBinary(a, Ge, b) }
|	a = expression LT b = expression { EBinary(a, Lt, b) }
|	a = expression LE b = expression { EBinary(a, Le, b) }
|	a = expression PLUS b = expression { EBinary(a, Add, b) }
|	a = expression MINUS b = expression { EBinary(a, Sub, b) }
|	a = expression TIMES b = expression { EBinary(a, Mul, b) }
|	a = expression DIV b = expression { EBinary(a, Div, b) }
|	a = expression MOD b = expression { EBinary(a, Modulo, b) }
;

unop:
|	NOT e = expression { EUnary(Not, e) } %prec UNARY
|	MINUS e = expression { EUnary(Minus, e) } %prec UNARY
|	PLUS e = expression { EUnary(Plus, e) } %prec UNARY
|	REF e = expression { EUnary(Ref, e) } %prec UNARY
|	TIMES e = expression { EUnary(Deref, e) } %prec UNARY
|	INCR e = expression { EUnary(PreIncr, e) } %prec UNARY
|	e = expression INCR { EUnary(PostIncr, e) }
|	DECR e = expression { EUnary(PreDecr, e) } %prec UNARY
|	e = expression DECR { EUnary(PostDecr, e) }
;
