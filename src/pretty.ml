(*
	PRETTY PRINTER
	These functions enable the dumping of an AST
	Used for debugging the parser.
*)


open Parser
open Ast

let token_str = function
	| CLASS -> "class"
	| ELSE -> "else"
	| FALSE -> "false"
	| FOR -> "for"
	| IF -> "if"
	| INT -> "int"
	| NEW -> "new"
	| NULL -> "NULL"
	| PUBLIC -> "public"
	| RETURN -> "return"
	| THIS -> "this"
	| TRUE -> "true"
	| VIRTUAL -> "virtual"
	| VOID -> "void"
	| WHILE -> "while"
	| IDENT(s) -> "'"^s^"'"
	| TIDENT(s) -> "\""^s^"\""
	| ASSIGN -> "="
	| LOR -> "||"
	| LAND -> "&&"
	| EQ -> "=="
	| NE -> "!="
	| LT -> "<"
	| LE -> "<="
	| GT -> ">"
	| GE -> ">="
	| PLUS -> "+"
	| MINUS -> "-"
	| TIMES -> "*"
	| DIV -> "/"
	| MOD -> "%"
	| NOT -> "!"
	| INCR -> "++"
	| DECR -> "--"
	| REF -> "&"
	(* and also : unary dereference, plus, minus *)
	| LPAREN -> "("
	| RPAREN -> ")"
	| RARROW -> "->"
	| DOT -> "."
	(* OTHER SYMBOLZ *)
	| SEMICOLON -> ";"
	| DOUBLECOLON -> "::"
	| LFLOW -> "<<"
	| LBRACE -> "{"
	| RBRACE -> "}"
	| COMMA -> ","
	| COLON -> ":"
	(* DATAZ *)
	| INTVAL(i) -> "#" ^ (string_of_int i)
	| STRVAL(s) -> "`" ^ s ^ "`"
	(* STUPIDITIEZS *)
	| STD_COUT -> "std::cout"
	| INCLUDE_IOSTREAM -> "#include <iostream>"
	| EOF -> "end."

let print_tok t =
	print_string ((token_str t) ^ "\n")

let csl f l =
	List.fold_left (fun x t -> (if x = "" then "" else x ^ ", ") ^ (f t)) "" l

(* printing AST's *)

let binop_str = function
	| Equal -> "==" | NotEqual -> "!=" | Lt -> "<" | Le -> "<="
	| Gt -> ">" | Ge -> ">=" | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
	| Modulo -> "%" | Land -> "&&" | Lor -> "||"
let unop_str = function
	| PreIncr -> "++." | PostIncr -> ".++" | PreDecr -> "--." | PostDecr -> ".--"
	| Ref -> "&" | Deref -> "*" | Not -> "!" | Minus -> "-" | Plus -> "+"
let rec var_type_str = function
	| TVoid -> "void" | TInt -> "int" | TIdent(i) -> i
	| TPtr(k) -> "*" ^ (var_type_str k)
	| TRef(k) -> "&" ^ (var_type_str k)
let rec expr_string e = match e.e_desc with
	| EInt(i) -> string_of_int i
	| EBool(b) -> (if b then "true" else "false")
	| ENull -> "NULL"
	| EThis -> "this"
	| EIdent(i) -> i
	| EAssign(k, p) -> "(" ^ (expr_string k) ^ " = " ^ (expr_string p) ^ ")"
	| ECall(e, f) -> (expr_string e) ^ "(" ^ (csl expr_string f) ^ ")"
	| EUnary(e, f) -> (unop_str e) ^ (expr_string f)
	| EBinary(e1, o, e2) -> "(" ^ (expr_string e1) ^ " " ^ (binop_str o) ^ " " ^ (expr_string e2) ^ ")"
	| EMember(e1, x) -> "(" ^ (expr_string e1) ^ ")." ^ x
	| ENew(c, arg) -> "new " ^ c ^ " (" ^ (csl expr_string arg) ^ ")"

let rec print_stmt l x =
	for i = 1 to l do print_string " " done;
	match x.s_desc with 
	| SEmpty -> print_string ";\n"
	| SExpr(e) -> print_string ((expr_string e) ^ "\n")
	| SIf(e, a, b) -> print_string ("if " ^ (expr_string e) ^ "\n");
		print_stmt (l+1) a;
		for i = 1 to l do print_string " " done;
		print_string "else\n";
		print_stmt (l+1) b
	| SWhile(e, a) -> print_string ("while " ^ (expr_string e) ^ "\n");
		print_stmt (l+1) a;
	| SFor(i, c, f, s) -> print_string 
		("for " ^ 
			(List.fold_left (fun x k -> x ^ ", " ^ (expr_string k)) "" i) ^ "; " ^
			(match c with | None -> "" | Some(a) -> expr_string a) ^ "; " ^
			(List.fold_left (fun x k -> x ^ ", " ^ (expr_string k)) "" f) ^ "\n");
		print_stmt (l+1) s
	| SBlock(b) -> print_block l b
	| SReturn(None) -> print_string "return\n"
	| SReturn(Some k) -> print_string ("return " ^ (expr_string k) ^ "\n")
	| SDeclare(t, i) -> print_string (i ^ " : " ^ (var_type_str t) ^ "\n")
	| SDeclareAssignExpr(t, i, e) -> print_string (i ^ " : " ^ (var_type_str t) ^ " = " ^ (expr_string e) ^ "\n")
	| SDeclareAssignConstructor(t, i, c, a) -> print_string
		(i ^ " : " ^ (var_type_str t) ^ " = " ^ c ^ "(" ^
			(csl expr_string a) ^ ")\n")
	| SWriteCout(k) -> print_string ("std::cout" ^
		(List.fold_left (fun x k -> x ^ " << " ^ (match k.se_desc with
				| SEExpr(e) -> expr_string {e_loc = k.se_loc; e_desc = e}
				| SEStr("\n") -> "std::endl" | SEStr(s) -> "`" ^ s ^ "`")) "" k) ^ "\n")
and print_block n b =
	let prefix = String.make n ' ' in
	print_string (prefix ^ "{\n");
	List.iter
		(fun s -> print_stmt (n+1) s)
		b;
	print_string (prefix ^ "}\n")

let proto_str p =
	(match p.p_class with | Some c -> c ^ "::" | None -> "") ^ p.p_name
		^ " (" ^ (csl (fun (t, i) -> i ^ " : " ^ (var_type_str t)) p.p_args)
		^ ") : " ^ (match p.p_ret_type with | Some k -> var_type_str k | None -> "constructor")

let print_class_decl c =
	print_string ("class " ^ c.c_name ^ 
		(match c.c_supers with | None -> "" | Some(s) -> " : " ^
		(List.fold_left (fun x t -> x ^ " public " ^ t) "" s)) ^ " {\n");
	List.iter (function
		| CVar(t, i) -> print_string (" " ^ i ^ " : " ^ (var_type_str t) ^ "\n")
		| CMethod(p, v) -> print_string ((if v then " virtual " else " ") ^ (proto_str p) ^ "\n")
		) c.c_members;
	print_string "}\n"

let print_prog p =
	List.iter (fun k -> match k.d_desc with
		| DGlobal(t, i) -> print_string ("decl " ^ i ^ " : " ^ (var_type_str t) ^ "\n")
		| DFunction(p, b) -> print_string (proto_str p ^"\n");
			print_block 0 b
		| DClass(c) -> print_class_decl c
		) p

