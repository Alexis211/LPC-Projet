(*
	PRETTY PRINTER
	These functions enable the dumping of an AST
	Used for debugging the parser.
*)


open Parser
open Typing
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
	List.fold_left 
	  (fun x t -> (if x = "" then "" else x ^ ", ") ^ (f t)) "" l

(* printing AST's *)

let binop_str = function
	| Equal -> "==" | NotEqual -> "!=" | Lt -> "<" | Le -> "<="
	| Gt -> ">" | Ge -> ">=" | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/"
	| Modulo -> "%" | Land -> "&&" | Lor -> "||"
let unop_str = function
	| PreIncr -> "++." | PostIncr -> ".++" | PreDecr -> "--." | PostDecr -> ".--"
	| Ref -> "&" | Deref -> "*" | Not -> "!" | Minus -> "-" | Plus -> "+"
let rec var_type_str = function
	| T_Void -> "void" | T_Int -> "int"
	| TPoint(k) -> "*" ^ (var_type_str k)
	| TClass s -> ""
	| Typenull -> "NULL"
let rec expr_string e = match e.te_desc with
	| TEInt(i) -> string_of_int i
	| TENull -> "NULL"
	| TEThis -> "this"
	| TEIdent(i) -> i
	| TEAssign(k, p) -> "(" ^ (expr_string k) ^ " = " ^ (expr_string p) ^ ")"
	| TECallFun(i, f) -> i ^ "(" ^ (csl expr_string f) ^ ")"
(* ici, le second ast a changé par rapport au premier *)
	| TEUnary(e, f) -> (unop_str e) ^ (expr_string f)
	| TEBinary(e1, o, e2) -> "(" ^ (expr_string e1) ^ " " ^ (binop_str o) ^ " " ^ (expr_string e2) ^ ")"
(*	| TEMember(e1, x) -> "(" ^ (expr_string e1) ^ ")." ^ x
	| TENew(c, arg) -> "new " ^ c ^ " (" ^ (csl expr_string arg) ^ ")"*)
	| _ -> ""

let rec print_stmt l x =
	for i = 1 to l do print_string " " done;
	match x.ts_desc with 
	| TSEmpty -> print_string ";\n"
	| TSExpr(e) -> print_string ((expr_string e) ^ "\n")
	| TSIf(e, a, b) -> print_string ("if " ^ (expr_string e) ^ "\n");
		print_stmt (l+1) a;
		for i = 1 to l do print_string " " done;
		print_string "else\n";
		print_stmt (l+1) b
	| TSWhile(e, a) -> print_string ("while " ^ (expr_string e) ^ "\n");
		print_stmt (l+1) a;
	| TSFor(i, c, f, s) -> print_string 
		("for " ^ 
			(List.fold_left (fun x k -> x ^ ", " ^ (expr_string k)) "" i) ^ "; " ^
			(match c with | None -> "" | Some(a) -> expr_string a) ^ "; " ^
			(List.fold_left (fun x k -> x ^ ", " ^ (expr_string k)) "" f) ^ "\n");
		print_stmt (l+1) s
	| TSBlock(b) -> print_block l b
	| TSReturn(None) -> print_string "return\n"
	| TSReturn(Some k) -> print_string ("return " ^ (expr_string k) ^ "\n")
	| TSDeclare((ty,b), i) -> let addr = (if b then "&" else "") in
				  print_string (addr ^ i ^ " : " ^ (var_type_str ty) ^ "\n")
	| TSDeclareAssignExpr((ty,b), i, e) -> let addr = (if b then "&" else "") in
					  print_string (addr ^ i ^ " : " ^ (var_type_str ty) ^ " = " ^ (expr_string e) ^ "\n")
	| TSDeclareAssignConstructor(t, i, c, a) -> () (*print_string
		(i ^ " : " ^ (var_type_str t) ^ " = " ^ c ^ "(" ^
							 (csl expr_string a) ^ ")\n")*)
	| TSWriteCout(k) -> print_string ("std::cout" ^
					     (List.fold_left (fun x k -> x ^ " << " ^ (match k with
					       | TSEExpr e -> expr_string e
					       | TSEStr("\n") -> "std::endl" 
					       | TSEStr s -> "`" ^ s ^ "`")) "" k) ^ "\n")

and print_block n b =
  let prefix = String.make n ' ' in
  print_string (prefix ^ "{\n");
	List.iter
		(fun s -> print_stmt (n+1) s)
		b;
	print_string (prefix ^ "}\n")

let proto_str p =
  (match p.tp_class with | Some c -> c ^ "::" | None -> "") ^ p.tp_name
  ^ " (" ^ (csl 
	      (fun ((ty,b), i) ->  let addr = (if b then "&" else "") in
				   addr ^ i ^ " : " ^ (var_type_str ty)
	      )
	      p.tp_args)
  ^ ") : " ^ (match p.tp_ret_type with | Some (ty,b) -> var_type_str ty | None -> "constructor")

(*let print_class_decl c =
	print_string ("class " ^ c.c_name ^ 
		(match c.c_supers with | None -> "" | Some(s) -> " : " ^
		(List.fold_left (fun x t -> x ^ " public " ^ t) "" s)) ^ " {\n");
	List.iter (function
		| CVar(t, i) -> print_string (" " ^ i ^ " : " ^ (var_type_str t) ^ "\n")
		| CMethod(p) -> print_string (" " ^ (proto_str p) ^ "\n")
		| CVirtualMethod(p) -> print_string (" virtual " ^ (proto_str p) ^ "\n")
		) c.c_members;
	print_string "}\n"*)

let print_prog p =
	List.iter (function
		| TDGlobal((ty,b),i) -> let addr = (if b then "&" else "") in
					print_string ("decl " ^ addr ^ i ^ " : " ^ (var_type_str ty) ^ "\n")
		| TDFunction(p,b) -> print_string (proto_str p ^"\n");
			print_block 0 b
		| TDClass(c) -> () (* print_class_decl c  *)
		| TDNothing -> ()
		) 
	  p

