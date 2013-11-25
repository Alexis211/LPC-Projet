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
	
	(* return type, name *)
	let rec reverse_var bt v = match v with
		| VId(i) -> bt, i
		| VPtr(vv) -> let ty, id = reverse_var bt vv in TPtr(ty), id
		| VRef(vv) -> let ty, id = reverse_var bt vv in TRef(ty), id
	
	(* return type, class, name *)
	let rec reverse_qvar bt (v, cl) =
		let ty, na = reverse_var bt v in
		ty, cl, na
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
%nonassoc LPAREN

%start <Ast.program> prog

%%

prog:
	INCLUDE_IOSTREAM?
	decls = declaration*
	EOF
	{ List.flatten decls }
;

declaration:
|	p = proto
	b = block
	{ [ DFunction(p, b) ] }
|	vars = typed_vars
	SEMICOLON
	{ List.map (fun k -> DGlobal(k)) vars }
|	n = cls
	s = supers? LBRACE PUBLIC COLON
	m = member* RBRACE SEMICOLON
	{
		[ DClass({
			c_name = n;
			c_supers = s;
			c_members = List.flatten m;
		}) ]
	}
;

cls:
	CLASS n = IDENT
	{
		type_names := Sset.add n !type_names;
		n
	}
;

supers:
	COLON s = separated_nonempty_list(COMMA, preceded(PUBLIC, TIDENT)) { s }
;

member:
|	k = typed_vars SEMICOLON
	{ List.map (fun (x, y) -> CVar(x, y)) k }
|	p = cls_proto SEMICOLON
	{ [ CMethod(p) ] }
|	VIRTUAL p = cls_proto SEMICOLON
	{ [ CVirtualMethod(p) ] }
;

cls_proto:
|	ident = typed_var
	LPAREN args = separated_list(COMMA, typed_var) RPAREN
	{ {
		p_ret_type = Some(fst ident);
		p_name = snd ident;
		p_class = None;
		p_args = args;
		p_loc = $startpos, $endpos } }
|	cls = TIDENT
	LPAREN args = separated_list(COMMA, typed_var) RPAREN
	{ {p_ret_type = None;
		p_name = cls;
		p_class = Some cls;
		p_args = args;
		p_loc = $startpos, $endpos } }
;

proto:
|	ident = typed_qvar
	LPAREN args = separated_list(COMMA, typed_var) RPAREN
	{
		let ty, cl, na = ident in
		{ p_ret_type = Some ty; p_name = na; p_class = cl; p_args = args; p_loc = $startpos, $endpos } }
|	cls = TIDENT DOUBLECOLON cls2 = TIDENT
	LPAREN args = separated_list(COMMA, typed_var) RPAREN
	{
		{p_ret_type = None; p_name = cls2; p_class = Some cls; p_args = args; p_loc = $startpos, $endpos}
	}
;

base_type:
|	VOID { TVoid }
|	INT	{ TInt }
|	t = TIDENT { TIdent(t) }
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

var:
|	t = IDENT { VId(t) }
|	TIMES v = var { VPtr(v) }
|	REF v = var { VRef(v) }
;

typed_qvar:
|	b = base_type
	x = qvar
	{ reverse_qvar b x }
;

qvar:
|	c = TIDENT DOUBLECOLON t = IDENT { VId(t), Some(c) }
|	t = IDENT { VId(t), None }
|	TIMES v = qvar { VPtr(fst v), snd v }
|	REF v = qvar { VRef(fst v), snd v }
;

block:
|	LBRACE
	i = statement*
	RBRACE
	{ i }
;

statement:
|	d = statement_desc { { s_loc = $startpos, $endpos; s_desc = d } }
;
statement_desc:
|	k = common_statement { k }
|	IF LPAREN c = expression RPAREN s = statement
	{ SIf(c, s, { s_loc = $startpos, $endpos; s_desc = SEmpty}) }
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
|	d = no_if_statement_desc { { s_loc = $startpos, $endpos; s_desc = d } }
;
no_if_statement_desc:
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
|	k = typed_var SEMICOLON
	{ SDeclare(fst k, snd k) }
|	k = typed_var ASSIGN v = expression SEMICOLON
	{ SDeclareAssignExpr(fst k, snd k, v) }
|	k = typed_var ASSIGN cls = TIDENT LPAREN args = separated_list(COMMA, expression) RPAREN SEMICOLON
	{ SDeclareAssignConstructor(fst k, snd k, cls, args) }
|	STD_COUT
	a = nonempty_list(preceded(LFLOW, str_expression))
	SEMICOLON
	{ SWriteCout(a) }
;

expression:
|	e = expression_desc
	{ { e_loc = $startpos, $endpos; e_desc = e } }
|	l = lunop { l }
;
expression_desc:
|	e1 = expression ASSIGN e2 = expression { EAssign(e1, e2) }
|	a = expression b = binop c = expression { EBinary(a, b, c) }
|	a = expression LPAREN arg = separated_list(COMMA, expression) RPAREN { ECall(a, arg) }
|	NEW c = TIDENT LPAREN args = separated_list(COMMA, expression) RPAREN { ENew(c, args) }
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

primary:
|	LPAREN e = expression RPAREN
	{ { e_loc = $startpos, $endpos; e_desc = e.e_desc } }
|	k = primary_desc
	{ { e_loc = $startpos, $endpos; e_desc = k } }
;
primary_desc:
|	NULL { ENull }
|	THIS { EThis }
|	i = INTVAL { EInt(i) }
|	TRUE { EBool(true) }
|	FALSE { EBool(false) }
|	i = IDENT { EIdent(i) }
|	a = primary RARROW b = IDENT
	{ EMember(
		{ e_loc = $startpos, $endpos; e_desc = EUnary(Deref, a)}
		, b) }
|	a = primary DOT b = IDENT
	{ EMember(a, b) }
;

runop:
|	e = runop_desc { { e_loc = $startpos, $endpos; e_desc = e } }
|	p = primary { p }
;
runop_desc:
|	e = runop INCR { EUnary(PostIncr, e) }
|	e = runop DECR { EUnary(PostDecr, e) }
;

lunop:
|	e = lunop_desc
	{ { e_loc = $startpos, $endpos; e_desc = e } }
|	k = runop { k }
;
lunop_desc:
|	NOT e = lunop { EUnary(Not, e) }
|	MINUS e = lunop { EUnary(Minus, e) }
|	PLUS e = lunop { EUnary(Plus, e) }
|	REF e = lunop { EUnary(Ref, e) }
|	TIMES e = lunop { EUnary(Deref, e) }
|	INCR e = lunop { EUnary(PreIncr, e) }
|	DECR e = lunop { EUnary(PreDecr, e) }
;

str_expression:
|	e = expression { { se_loc = e.e_loc; se_desc = SEExpr(e.e_desc) } }
|	s = STRVAL { { se_loc = $startpos, $endpos; se_desc = SEStr(s) } }
;
