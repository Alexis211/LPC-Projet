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
|	k = common_statement { k }
|	IF LPAREN c = expression RPAREN s = statement
	{ SIf(c, s, SEmpty) }
|	IF LPAREN c = expression RPAREN s = no_if_statement ELSE t = statement
	{ SIf(c, s, t) }
|	WHILE LPAREN c = expression RPAREN s = statement
	{ SWhile(c, s) }
|	FOR LPAREN k = separated_list(COMMA, expression) SEMICOLON
	c = expression? SEMICOLON 
	r = separated_list(COMMA, expression) RPAREN
	b = statement
	{ SFor(k, c, r, b) }
;

no_if_statement:
|	WHILE LPAREN c = expression RPAREN s = no_if_statement
	{ SWhile(c, s) }
|	FOR LPAREN k = separated_list(COMMA, expression) SEMICOLON
	c = expression? SEMICOLON 
	r = separated_list(COMMA, expression) RPAREN
	b = no_if_statement
	{ SFor(k, c, r, b) }
|	c = common_statement { c }
;

common_statement:
|	SEMICOLON
	{ SEmpty }
|	e = expression SEMICOLON { SExpr(e) }
|	b = block
	{ SBlock (b) }
|	RETURN e = expression? SEMICOLON
	{ SReturn (e) }
|	k = typed_var v = preceded(ASSIGN, expression)? SEMICOLON
	{ SDeclare(fst k, snd k, v) }
;

expression:
|	e1 = expression ASSIGN e2 = expression { EAssign(e1, e2) }
|	a = expression b = binop c = expression { EBinary(a, b, c) }
|	a = expression LPAREN arg = separated_list(COMMA, expression) RPAREN { ECall(a, arg) }
|	a = unop { a }
;

primary:
|	NULL { ENull }
|	i = INTVAL { EInt(i) }
|	TRUE { EBool(true) }
|	FALSE { EBool(false) }
|	i = IDENT { EIdent(i) }
|	LPAREN e = expression RPAREN { e }
;

%inline binop:
|	EQ {Equal }
|	NE { NotEqual }
|	LAND { Land }
|	LOR { Lor }
|	GT { Gt }
|	GE { Ge }
|	LT { Lt }
|	LE { Le }
|	PLUS { Add }
|	MINUS { Sub }
|	TIMES { Mul }
|	DIV { Div }
|	MOD { Modulo }
;

unop:
|	e = lunop { e }
|	e = unop INCR { EUnary(PostIncr, e) }
|	e = unop DECR { EUnary(PostDecr, e) }
;

lunop:
|	NOT e = lunop { EUnary(Not, e) }
|	MINUS e = lunop { EUnary(Minus, e) }
|	PLUS e = lunop { EUnary(Plus, e) }
|	REF e = lunop { EUnary(Ref, e) }
|	TIMES e = lunop { EUnary(Deref, e) }
|	INCR e = lunop { EUnary(PreIncr, e) }
|	DECR e = lunop { EUnary(PreDecr, e) }
|	e = primary { e }
;
