
%{
	open Ast

	module Sset = Set.Make(String)

	let type_names = ref Sset.empty
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

%start <unit> prog

%%

prog:
	INCLUDE_IOSTREAM?
	decls = declaration*
	EOF
		{ () }
;

declaration:
| 	d = decl_vars
	{ d }
| 	d = decl_class
	{ d }
|	p = proto
	b = block
	{ () }
;

decl_vars:
|	t = ty
	vars = separated_nonempty_list(COMMA, var)
	SEMICOLON
	{ () }
;

decl_class:
|	CLASS i = IDENT
	s = supers?
	LBRACE
	PUBLIC COLON
	m = member*
	RBRACE SEMICOLON
	{ () }
;

supers:
|	COLON
	s = separated_nonempty_list(COMMA, preceded(PUBLIC, TIDENT))
	{ s }
;

member:
|	d = decl_vars
	{ () }
|	v = boption(VIRTUAL)
	p = proto
	{ () }
;

proto:
|	t = ty
	qv = qvar
	LPAREN args = separated_list(COMMA, argument) RPAREN
	{ () }
|	qi = TIDENT
	LPAREN args = separated_list(COMMA, argument) RPAREN
	{ () }
|	qa = TIDENT DOUBLECOLON
	qb = TIDENT
	LPAREN args = separated_list(COMMA, argument) RPAREN
	{ () }
;

ty:
|	VOID
	{ () }
|	INT
	{ () }
|	i = TIDENT
	{ i }
;

argument:
|	t = ty
	v = var
	{ () }
;

var:
|	i = IDENT
	{ () }
|	TIMES v = var
	{ () }
|	REF v = var
	{ () }
;

qvar:
|	qi = qident
	{ qi }
|	TIMES v = qvar
	{ () }
|	REF v = qvar
	{ () }
;

qident:
|	i = IDENT
	{ () }
|	i = IDENT DOUBLECOLON j = IDENT
	{ () }
;

expression:
|	i = INTVAL { EIntConst(i) }
|	THIS { EThis }
|	FALSE { EBoolConst(false) }
|	TRUE { EBoolConst(true) }
|	NULL { ENull }
|	q = qident { () }
|	TIMES expression { EUnary(Deref, e) } %prec UNARY
|	e1 = expression DOT e2 = IDENT { () }
|	e1 = expression RARROW e2 = IDENT { () }
|	e1 = expression ASSIGN e2 = expression { () }
|	f = expression LPAREN
	a = separated_list(COLON, expression)
	{ () }
|	NEW c = IDENT LPAREN
	a = separated_list(COLON, expression)
	{ () }
|	INCR e = expression { EUnary(PreIncr, e) } %prec UNARY
|	DECR e = expression { EUnary(PreDecr, e) } %prec UNARY
|	e = expression INCR { EUnary(PostIncr, e) } %prec UNARY
|	e = expression DECR { EUnary(PostDecr, e) } %prec UNARY
|	REF e = expression { EUnary(Ref, e) } %prec UNARY
|	NOT e = expression { EUnary(Not, e) } %prec UNARY
|	MINUS e = expression { EUnary(Minus, e) } %prec UNARY
|	PLUS e = expression { EUnary(Plus, e) } %prec UNARY
|	e1 = expression
	o = operator
	e2 = expression
	{ EBinop(e1, o, e2) }
|	LPAREN e = expression RPAREN { e }
;

operator:
|	EQ { Equal }
|	NE { NotEqual }
|	LT	{ Lt }
|	LE	{ Le }
|	GT	{ Gt }
|	GE	{ Ge }
|	PLUS { Add }
|	MINUS { Sub }
|	TIMES { Mul }
|	DIV { Div }
|	MOD { Modulo }
|	LAND { Land }
|	LOR { Lor }
;

instruction:
|	SEMICOLON
	{ () }
|	e = expression SEMICOLON
	{ () }
|	t = ty
	v = var
	ASSIGN e = expression? SEMICOLON
	{ IDeclVar(t, v, e) }
|	t = ty
	v = var
	ASSIGN cl = TIDENT
	LPAREN e = separated_list(COMMA, expression) RPAREN
	SEMICOLON
	{ IDeclVarAssignConstruct (t, v, cl, e) }
|	IF LPAREN e = expression RPAREN i = instruction 
	{ IIf(e, i, IEmpty) }
|	IF LPAREN e = expression RPAREN i1 = instruction
	ELSE i2 = instruction 
	{ IIf(e, i1, i2) }
|	WHILE LPAREN e = expression RPAREN i = instruction
	{ IWhile(e, i) }
|	FOR LPAREN
	start = separated_list(COMMA, expression) SEMICOLON
	cond = expression? SEMICOLON
	loop = separated_list(COMMA, expression) RPAREN
	i = instruction
	{ IFor(start, cond, loop, i) } 
|	b = block
	{ IBlock(b) }
|	STD_COUT
	e = preceded(LFLOW, expr_str)+
	SEMICOLON
	{ IStdCoutWrite(e) }
|	RETURN e = expression? SEMICOLON
	{ IReturn(e) }
;

expr_str:
|	e = expression
	{ SEExpr(e) }
|	s = STRVAL
	{ SEStr(s) }
;

block:
|	LBRACE
	i = instruction*
	RBRACE
	{ i }
;
