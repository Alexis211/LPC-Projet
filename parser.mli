
type token =
	(* KEYWORDZ *)
	| CLASS
	| ELSE
	| FALSE
	| FOR
	| IF
	| INT
	| NEW
	| NULL
	| PUBLIC
	| RETURN
	| THIS
	| TRUE
	| VIRTUAL
	| VOID
	| WHILE
	(* IDENTZ *)
	| IDENT of string
	(* OPERATORZ, by precedence *)
	| ASSIGN
	| LOR
	| LAND
	| EQ
	| NE
	| LT
	| LE
	| GT
	| GE
	| PLUS
	| MINUS
	| TIMES
	| DIV
	| MOD
	| NOT
	| INCR
	| DECR
	| REF
	(* and also : unary dereference, plus, minus *)
	| LPAREN
	| RPAREN
	| RARROW
	| DOT
	(* OTHER SYMBOLZ *)
	| SEMICOLON
	| DOUBLECOLON
	| LFLOW
	| LBRACE
	| RBRACE
	(* DATAZ *)
	| INTVAL of int
	| STRVAL of string
