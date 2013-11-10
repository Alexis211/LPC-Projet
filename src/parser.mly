
%{
	open Ast

	module Sset = Set.Make(String)

	let type_names = ref Sset.empty
%}

%token <int> INTVAL
%token <string> STRVAL
%token <string> IDENT
%token <string> TIDENT

/* this is stupid */
%token INCLUDE_IOSTREAM

/* keywords */
%token CLASS ELSE FALSE FOR IF INT NEW NULL PUBLIC RETURN
%token THIS TRUE VIRTUAL VOID WHILE

/* operators */
%token ASSIGN LOR LAND EQ NE LT LE GT GE PLUS MINUS
%token TIMES DIV MOD NOT INCR DECR REF
%token LPAREN RPAREN RARROW DOT

/* other symbols */
%token SEMICLON COLON DOUBLECOLON LFLOW LBRACE RBRACE


/* operator priority */
%right ASSIGN
%left LOR
%left LAND
%left EQ NE
%left LT LE GT GE
%left PLUS MINUS
%left TIMES DIV MOD
/* opérateurs unaires associatifs à droite */
%left RARROW DOT LPAREN

%start prog

%type <unit> prog

%%

prog:
	INCLUDE_IOSTREAM?
	decls = declaration*
	EOF
		{ () }
;

declaration:
| 	d = decl_var
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
;

decl_class:
|	CLASS i = IDENT
	s = supers?
	LBRACE
	PUBLIC COLON
	m = members*
	RBRACE SEMICOLON
	{ () }
;

supers:
|	COLON
	s = separated_nonempty_list(COMMA, super_id)
	{ s }
;

super_id:
|	PUBLIC i = TIDENT
	{ i }
;

member:
|	d = decl_vars
	{ () }
|	v = VIRTUAL?
	p = proto
	{ () }
;

proto:
|	t = ty
	qv = qvar
	LPAREN args = separated_list(COMMA, argument) RPAREN
	{ () }
|	qi = TIDENT
	LPAREN args = separated_list(COMMA, arg) RPAREN
	{ () }
|	qa = TIDENT DOUBLECOLON
	qb = TIDENT
	LPAREN args = separated_list(COMMA, arg) RPAREN
	{ () }
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
|	TIMES expression { EUnary(Deref, e) }
|	e1 = expression DOT e2 = IDENT { () }
|	e1 = expression RARROW e2 = IDENT { () }
|	e1 = expression ASSIGN e2 = expression { () }
|	f = expression LPAREN
	a = separated_list(COLON, expression)
	{ () }
|	NEW c = IDENT LPAREN
	a = separated_list(COLON, expression)
	{ () }
|	INCR e = expression { EUnary(PreIncr, e) }
|	DECR e = expression { EUnary(PreDecr, e) }
|	e = expression INCR { EUnary(PostIncr, e) }
|	e = expression DECR { EUnary(PostDecr, e) }
|	REF e = expression { EUnary(Ref, e) }
|	NOT e = expression { EUnary(Not, e) }
|	MINUS e = expression { EUnary(Minus, e) }
|	PLUS e = expression { EUnary(Plus, e) }
|	e1 = expression
	o = operator
	e2 = expression
	{ EBinop(e1, o, e2) }
|	LPAREN e = expression RPAREN { e }
;

operator:
|	EQ { Equal }
|	NEQ { NotEqual }
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
