(*
	PRETTY PRINTER
	These functions enable the dumping of an AST
	Used for debugging the parser.
*)


open Parser
open Typing
open Ast

let repl_nl s =
	let k = ref "" in
	for i = 0 to String.length s - 1 do
		if s.[i] = '\n' then
			k := !k ^ "\\n"
		else
			k := !k ^ (String.make 1 s.[i])
	done; !k

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
	| TClass s -> s
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
	| TEMember(e1, i) -> "(" ^ (expr_string e1) ^ ")@" ^ (string_of_int i)
	| TENew(c, proto, arg) -> "new " ^ c.tc_name
			^ (match proto with | None -> "" | Some p -> " ." ^ p.tp_unique_ident)
			 ^ " (" ^ (csl expr_string arg) ^ ")"
	| TECallVirtual(exp, pos1, pos2, args) ->
		"(" ^ (expr_string exp) ^ ")@" ^ (string_of_int pos1) ^ "#" ^  (string_of_int pos2) ^ "(" ^ (csl expr_string args) ^ ")"

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
	| TSDeclareAssignConstructor(t, i, _, c, a) -> () (*print_string
		(i ^ " : " ^ (var_type_str t) ^ " = " ^ c ^ "(" ^
							 (csl expr_string a) ^ ")\n")*)
	| TSWriteCout(k) -> print_string ("std::cout" ^
					     (List.fold_left (fun x k -> x ^ " << " ^ (match k with
					       | TSEExpr e -> expr_string e
					       | TSEStr("\n") -> "std::endl" 
					       | TSEStr s -> "\"" ^ (repl_nl s) ^ "\"")) "" k) ^ "\n")

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
  	^ "  ." ^ p.tp_unique_ident
  	^ (match p.tp_virtual with | None -> "" | Some (k, l) -> " @" ^ (string_of_int k) ^ "#" ^ (string_of_int l))

let print_class_decl c =
	print_string ("class " ^ c.tc_name ^ " (size : " ^ (string_of_int c.tc_size) ^ ") {\n");
	print_string " members:\n";
	Smap.iter (fun name (t, pos) -> print_string ("  " ^ name ^ " : " ^ (var_type_str t)
				^ " @" ^ (string_of_int pos) ^ "\n")) c.tc_members;
	print_string " methods:\n";
	List.iter(fun p -> print_string ("  " ^ (proto_str p) ^ "\n")) c.tc_methods;
	print_string " hier:\n";
  let rec print_hier s =
    print_string ("    @" ^ (string_of_int s.h_pos) ^" : " ^ s.h_class ^ "\n");
	  List.iter 
      (fun (i, p) -> print_string ("      #" ^ (string_of_int i) ^ ": ." ^ (p.tp_unique_ident) ^ "\n"))
          s.h_vtable;
    List.iter print_hier s.h_supers
  in print_hier c.tc_hier;
	print_string "}\n"

let print_prog p =
	List.iter (function
		| TDGlobal(ty,i) -> 
					print_string ("decl " ^ i ^ " : " ^ (var_type_str ty) ^ "\n")
		| TDFunction(p,b) -> print_string (proto_str p ^"\n");
			print_block 0 b
		| TDClass(c) -> 
			print_class_decl c
		) 
	p.prog_decls

