
(*
	Analysateur lexicographiquep pour maxi-C++
*)

{
	open Lexing
	open Parser
	
	exception Lexing_error of string

	let keywordz_l = [
		"class",	CLASS;
		"else",		ELSE;
		"false",	FALSE;
		"for",		FOR;
		"if",		IF;
		"int",		INT;
		"new",		NEW;
		"NULL",		NULL;
		"public",	PUBLIC;
		"return",	RETURN;
		"this",		THIS;
		"true",		TRUE;
		"virtual",	VIRTUAL;
		"void",		VOID;
		"while",	WHILE;
		]
	
	let id_or_kwd =
		let h = Hashtbl.create 20 in
		List.iter (fun (s, t) -> Hashtbl.add h s t) keywordz_l;
		fun s ->
			try Hashtbl.find h s with _ -> 
				if Ast.Sset.mem s !Ast.type_names
					then TIDENT s
					else IDENT s

	let newline lexbuf =
		let pos = lexbuf.lex_curr_p in
		lexbuf.lex_curr_p <- 
			{ pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = ('_' | alpha) ('_' | alpha | digit)*
let octal = ['0'-'7']
let hexa = ['0'-'9' 'a'-'f' 'A'-'F']

rule token = parse
	| [' ' '\t']+			{ token lexbuf }
	| '\n'					{ newline lexbuf; token lexbuf }
	| ident as id			{ id_or_kwd id }
	| "//"					{ short_comment lexbuf; token lexbuf }
	| "/*"					{ long_comment lexbuf; token lexbuf }
	| "#include <iostream>" { INCLUDE_IOSTREAM }		(* nasty hack #1 *)
	| "std::cout" { STD_COUT }							(* nasty hack #2 *)
	| "std::endl" { STRVAL("\n") }						(* nasty hack #3 *)
	| "0x" (hexa+ as n)		{ INTVAL(int_of_string("0x" ^ n)) }
	| ['1'-'9'] digit* as n	{ INTVAL(int_of_string(n)) }
	| '0' (octal+ as n)		{ INTVAL(int_of_string("0o" ^ n)) }
	| "0"					{ INTVAL(0) }
	| digit ('_' | alpha | digit)+
		{ raise (Lexing_error "Missing separators") }
	| "\""					{ STRVAL(strval "" lexbuf) }
	| "="					{ ASSIGN }
	| "||"					{ LOR }
	| "&&"					{ LAND }
	| "=="					{ EQ }
	| "!="					{ NE }
	| "<"					{ LT }
	| "<="					{ LE }
	| ">"					{ GT }
	| ">="					{ GE }
	| "+"					{ PLUS }
	| "-"					{ MINUS }
	| "*"					{ TIMES }
	| "/"					{ DIV }
	| "%"					{ MOD }
	| "!"					{ NOT }
	| "++"					{ INCR }
	| "--"					{ DECR }
	| "&"					{ REF }
	| "("					{ LPAREN }
	| ")"					{ RPAREN }
	| "->"					{ RARROW }
	| "."					{ DOT }
	| ";"					{ SEMICOLON }
	| "::"					{ DOUBLECOLON }
	| ":"					{ COLON }
	| "<<"					{ LFLOW }
	| "{"					{ LBRACE }
	| "}"					{ RBRACE }
	| ","					{ COMMA }
	| eof					{ EOF }
	| _ as c
		{ raise 
			(Lexing_error
				("illegal character: " ^ String.make 1 c)) }
and strval s = parse
	| "\""					{ s }
	| "\\\\"				{ strval (s ^ "\\") lexbuf }
	| "\\\""				{ strval (s ^ "\"") lexbuf }
	| "\\n"					{ strval (s ^ "\n") lexbuf }
	| "\\t"					{ strval (s ^ "\t") lexbuf }
	| "\\x" (hexa hexa as x)
		{ strval (s ^ 
			(String.make 1 (char_of_int (int_of_string("0x" ^ x)))))
			lexbuf }
	| "\\"
		{ raise (Lexing_error "Invalid escape sequence") }
	| '\n'					{ raise (Lexing_error "Invalid character (newline) in string litteral.") }
	| _ as c				{ strval (s ^ (String.make 1 c)) lexbuf }
	| eof					{ raise (Lexing_error "Unfinished string") }
and short_comment = parse
	| '\n'					{}
	| _						{ short_comment lexbuf }
	| eof					{}
and long_comment = parse
	| "*/"					{}
	| _						{ long_comment lexbuf }
	| eof					{ raise (Lexing_error "Unclosed comment") }
	
