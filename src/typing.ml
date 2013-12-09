open Ast

(* Gestion des erreurs *)
exception Error of string
exception LocError of loc * string
let ty_assert x k = if not x then raise (Error (k))
let ty_error k = raise (Error (k))
let err_add_loc loc f =
	try f()
	with
		| Error(k) -> raise (LocError(loc, k))
		| LocError(_, _) as e -> raise e
		| Assert_failure (k, a, b) -> raise (LocError (loc,
			"(unexpected) Assertion failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
		| Not_found -> raise (LocError (loc, "(unexpected) Not found"))
		| Invalid_argument(k) -> raise (LocError (loc, "(unexpected) Invalid argument: "^k))
		| Match_failure(k, a, b) -> raise (LocError (loc,
			"(unexpected) Match failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
		| _ -> raise (LocError (loc, "(unexpected) Other error"))

(* AST typés *)

module Smap = Map.Make(String)

type typ =
  | T_Int
  | Typenull
  | T_Void
  | TClass of tident
  | TPoint of typ

type type_ref = typ * bool 
(* type d'une variable, avec ref? *)

type texpression = {
  te_loc: loc;
  te_desc: texpr_desc;
  type_expr : typ*bool*bool; (* Type, référence?, valeur gauche? *)
}
and texpr_desc =
  | TEInt of int
  | TENull
  | TEThis
  | TEIdent of ident
  | TEAssign of texpression * texpression
  | TECallFun of ident * texpression list (* changé : te -> ident *)
  | TECallMethod of texpression * ident * texpression list (* changé : te -> ident *)
  | TEUnary of unop * texpression
  | TEBinary of texpression * binop * texpression
  | TEMember of texpression * ident
  | TENew of tcls * tproto option * texpression list

and tstr_expression =
	| TSEExpr of texpression
	| TSEStr of string


and tstatement = {
	ts_loc: loc;
	ts_desc: ts_desc;
	}
and ts_desc =
	| TSEmpty
	| TSExpr of texpression
	| TSIf of texpression  * tstatement * tstatement
	| TSWhile of texpression * tstatement
	| TSFor of texpression list * texpression option * texpression list * tstatement
	| TSBlock of tblock
	| TSReturn of texpression option
	| TSDeclare of type_ref * ident
	| TSDeclareAssignExpr of type_ref * ident * texpression
	| TSDeclareAssignConstructor of type_ref * ident * tident * texpression list (* a faire *)
(* Type of variable, variable name, constructor class name, constructor arguments *)
	| TSWriteCout of tstr_expression list
and tblock = tstatement list

and tproto = {
	tp_virtual : bool;	(* only used for class methods *)
	tp_loc : loc;
	tp_name : ident;	
	tp_class : tident option; (* p_class = none : standalone function *)
	tp_ret_type : type_ref option; (* p_class = some and p_ret_type = none : constructor *)
	tp_args : (type_ref * ident) list;
}

and tcls = {
	tc_name : tident;
	tc_supers : tident list;
	tc_members : typ Smap.t;
	tc_methods : tproto list;
}

type env = {
	e_globals : typ Smap.t;
	e_funs : tproto list;
	e_classes : tcls Smap.t;
}
and benv = {
	b_pe : env;
	b_locals : type_ref Smap.t;
	b_class : tcls option;
}


type tdeclaration =
	| TDGlobal of (typ * ident)
	| TDFunction of (tproto * tblock)
	| TDClass of tcls

type tprogram = {
	prog_decls : tdeclaration list;
	prog_env : env;
}

(* Quelques fonctions utiles : *)

let find_v i env =
  try Smap.find i env.e_globals with Not_found -> ty_error ("No such global variable: " ^ i)

let rec bf env t =
  let rec aux = function			(* true si bien formé *)
	  | T_Int -> true
	  | TClass n ->
		Smap.mem n env.e_classes
	  | TPoint t -> aux t
	  | _ -> false
	in aux t

let num = function
  | T_Int -> true
  | Typenull -> true
  | TPoint _ -> true
  | _ -> false
(* !! modifier si on peut pas être un type num peut pas aller
avec une ref *)

let build_type_or_ref vt = (* vt -> typ,bool = tr, true si ref *)
  let rec see = function
    | TPtr vt -> TPoint (see vt)
    | TVoid -> T_Void
    | TInt -> T_Int
    | TRef _ -> ty_error ("Unexpected reference type - no pionters on references allowed")
    | TIdent tid -> TClass tid
  in
  match vt with
    | TRef (TRef vt) -> ty_error ("Double references not allowed") (* ... *)
    | TRef vt -> (see vt),true (* indique qu'il s'agit d'une ref *)
    | vt -> (see vt),false

let rec subtype_d env a b = match a, b with (* returns distance *)
	| T_Int, T_Int -> true, 0
	| T_Void, T_Void -> true, 0
	| Typenull, TPoint(_) -> true, 0
	| TPoint(ka), TPoint(kb) -> subtype_d env ka kb
	| TClass(i), TClass(j) ->
		if i = j then true, 0
		else begin try let c = Smap.find i env.e_classes in
			begin let d = ref None in
			List.iter (fun s -> match subtype_d env (TClass s) (TClass j) with
				| false, _ -> ()
				| true, n -> d := match !d with | None -> Some n | Some d -> Some (if d < n then d else n))
				c.tc_supers;
			match !d with
			| Some d -> true, d+1
			| None -> false, 0
			end
		with | Not_found -> false, 0 end
	| _ -> false, 0
let subtype env a b = fst (subtype_d env a b)


(* pour la surcharge de fonctions *)
let closest_proto env arg_type_list fun_list =
	let p = ref None in
	List.iter (fun f ->
		let proto = f in
		try
		let k = List.fold_left2
			(fun d (t_a, t_a_ref) (t_p, t_p_ref) -> match d with
				| None -> None
				| Some d ->
					if t_p_ref && (not t_a_ref) then None else
					match subtype_d env t_a t_p with
					| false, _ -> None
					| true, d_a -> Some (d + d_a))
			(Some 0) arg_type_list (List.map fst proto.tp_args) in
		match k with
		| None -> ()
		| Some d -> match !p with
			| None -> p := Some(d, f)
			| Some(dd, _) -> if (d < dd) then p := Some(d, f)
							else if (d = dd) then ty_error "Ambiguous overload"
		with Invalid_argument _ -> ()) fun_list;
	match !p with
	| None -> None
	| Some(_, f) -> Some f
	

(* -------------------------------------------- *)
(* On passe aux choses sérieuses *)

let rec type_expr env e = (* expression -> texpression *)
  err_add_loc e.e_loc (fun () ->
    let d,(ty,b1,b2) = compute_type env e in
    { te_loc = e.e_loc; te_desc = d; type_expr = (ty,b1,b2) } )

and get_expr0 env e = (* expression -> texpression,(ty,b1,b2) *)
  let te = type_expr env e in
  (te,te.type_expr)

and get_expr env e = (* expression -> texpression,(ty,b) *)
  let te = type_expr env e in
  let (ty,b,_) = te.type_expr in
  (te,(ty,b))

and compute_type env e =
	let e_this = 
		{	te_loc = e.e_loc;
			te_desc = TEThis;
			type_expr = TClass(match env.b_class with | Some c -> c.tc_name | None -> "#"), false, true } in
	match e.e_desc with (* expression -> te_desc,(typ,ref?,left?) *)
    | EInt n -> TEInt n, (T_Int,false,false) 
    (* false, : pas une ref, pas une val gauche*)
    | EBool b -> let n = (if b then 1 else 0) in
		 TEInt n, (T_Int,false,false)
    | ENull -> TENull, (Typenull,false,false)
    | EIdent i -> 
		begin try
			let t, r = Smap.find i env.b_locals in
			TEIdent i, (t, r, true)
		with Not_found ->
			try match env.b_class with
			| Some k -> let ty = Smap.find i k.tc_members in
				TEMember(e_this, i),
				 (ty, false, true)
			| None -> raise Not_found
		with Not_found ->
			try let t = Smap.find i env.b_pe.e_globals in
			TEIdent i, (t, false, true)
		with Not_found -> ty_error ("Undeclared identifier: " ^ i)
		end
    | EAssign (e1,e2) -> let te1,(ty1,r3,b3) = get_expr0 env e1 in
			 let te2,(ty2,_,_) = get_expr0 env e2 in
			 ty_assert (b3 || r3) "Can only assign to lvalue";
			 ty_assert (num ty1) "Cannot assign to non-numeric type (pointer type is numeric)";
			 ty_assert (subtype env.b_pe ty2 ty1) "Incompatible types in assign";
			 		(* type num et ref compatibles ?*)
			 (TEAssign (te1,te2) ),(ty1,false,false)
    | EUnary (op,e) -> let te,(ty,b1,b2) = get_expr0 env e in
		       (match op with
			 | PreIncr | PostIncr | PreDecr | PostDecr ->
			   ty_assert (b2 = true) "Can only increment/decrement lvalue";
			   ty_assert (ty = T_Int) "Can only increment/decrement integers";
			   TEUnary(op,te),(T_Int,b1,false)
			 | Plus | Minus | Not ->
			   ty_assert (ty = T_Int) "Can only apply unary plus/minus/not to integers";
			   TEUnary(op,te),(T_Int,false,false)
			 | Ref ->
			   ty_assert b2 "Can only reference lvalues";
			   TEUnary(op,te),(TPoint ty,false,false) (* verif *)
			 | Deref ->
			   let t = (match ty with
			     | TPoint t -> t
			     | _ -> ty_error "Can only dereference pointer"   ) in
			   TEUnary(op,te), (t,false,true)
		       )
    | EBinary (e1,op,e2) -> let te1,(ty1,_,b1) = get_expr0 env e1 in
			    let te2,(ty2,_,b2) = get_expr0 env e2 in
			    (match op with
			      | Equal | NotEqual -> 
					ty_assert ((subtype env.b_pe ty1 ty2) || (subtype env.b_pe ty2 ty1)) 
						"Can only apply == or != to two values of compatible type";
					ty_assert (num ty1) "Can only apply == or != to pointers"
			      | Lt | Le | Gt | Ge
			      | Add | Sub | Mul | Div | Modulo
			      | Land | Lor ->
					ty_assert (ty1 = T_Int) "Left operand of binop is not integer";
					ty_assert (ty2 = T_Int) "Right operand of binop is not integer"
			    ); (* vérifs *)
			    TEBinary(te1,op,te2),(T_Int,false,false)
    | ECall (e,e_list) ->
		(* TODO : look also within parent classes *)
			let obj, name, candidates = (match e.e_desc with
			    | EIdent i ->
					let funs = List.filter (fun p -> p.tp_name = i) env.b_pe.e_funs in
					begin match env.b_class with
					| None -> None, i, funs
					| Some k ->
						begin match List.filter (fun p -> p.tp_name = i) k.tc_methods with
						| [] -> None, i, funs
						| l -> Some e_this, i, l
						end
					end
				| EMember(e, i) ->
					let e = type_expr env e in
					let c = match e.type_expr with
					| TClass(k), a, b when a || b ->
						begin try Smap.find k env.b_pe.e_classes with
							Not_found -> ty_error ("Unknown class " ^ k ^ " (should not happen)") end
					| _ -> ty_error "Invalid argument type for method call (not a class, or not a lvalue)"
					in
					Some e, i, List.filter (fun p -> p.tp_name = i) (c.tc_methods)
			    | _ -> ty_error "Calling something that is neither a function nor a method") in
			let args_values = List.map (get_expr0 env) e_list in
			let tproto = match candidates with
			| [] -> ty_error ("No such function: " ^ name)
			| l ->
				(* handle overload *)
			  let args_types = List.map (fun (e, (t, r, l)) -> t, r||l) args_values in
			  let f = closest_proto env.b_pe args_types candidates in
			  begin match f with
			  | None -> ty_error "No corresponding function"
			  | Some(p) -> p
			  end
			in
			  (* vérif ici pour adresse/valeur, ici on test seulement
				 que ce sont les mêmes types, pas d'adressage de pris en compte *)
			  let l_te = List.map fst args_values in 
			  (* que les te de e_list*)
			  let ty,b = match tproto.tp_ret_type with
				| None -> assert false (* no return type only happens for constructors, and
											constructors cannot be called as functions *)
				| Some (ty,b) -> ty,b in
			  TECallFun(name,l_te),(ty,b,false)
    | EMember _ -> ty_error "Not implemented (member)"
    | ENew (cls_name, args) -> 
		begin try let c = Smap.find cls_name env.b_pe.e_classes in
			let args_values = List.map (get_expr0 env) args in
			  let args_types = List.map (fun (e, (t, r, l)) -> t, r||l) args_values in
			let candidates = List.filter (fun p -> p.tp_ret_type = None) c.tc_methods in
			match candidates with
			| [] ->
				ty_assert (args = []) "Only default constructor exists and it has 0 arguments";
				TENew(c, None, []), (TPoint(TClass(cls_name)), false, false)
			| _ ->
				let proto = closest_proto env.b_pe args_types candidates in
				match proto with
				| Some (p) ->
					(* closest_proto makes sure the prototypes match, no problem here *)
					let l_te = List.map fst args_values in
					TENew(c, Some p, l_te), (TPoint(TClass(cls_name)), false, false)
				| None -> ty_error "No matching prototype"
		with
		| Not_found -> ty_error ("No such class: " ^ cls_name)
		end
    | EThis -> ty_error "Not implemented (this)"


(* Statements *)

let rec type_stm ret_type env s = 
	err_add_loc s.s_loc (fun () ->
		let d, ty = compute_type_stm ret_type env s in
		{ ts_loc = s.s_loc; ts_desc = d }, ty)

and compute_type_stm ret_type env s = match s.s_desc with (* statement -> ts_desc,stm_type *)
  | SEmpty -> TSEmpty,env
  | SExpr e -> let te,(ty,_) = get_expr env e in (* verif ty est bien typé *)
	       (TSExpr te) , env
  | SBlock b -> build_block ret_type env b
  | SReturn None -> 
  	let ty, ref = ret_type in
	ty_assert (ty = T_Void) "Function must return non-void value";
  	(TSReturn None) , env
  | SReturn (Some e0) ->  let te,(ty,r) = get_expr env e0 in
  		let rty, rref = ret_type in
  				ty_assert (rty = ty) "Invalid return type";
				ty_assert (if rref then r else true) "Function must return reference";
			  TSReturn (Some te), env 
  | SIf (e,s1,s2) ->  let te,(ty,_) = get_expr env e in
		      let ts1,ty1 = type_stm ret_type env s1 in (* vérifs règle *)
		      let ts2,ty2 = type_stm ret_type env s2 in
		      ty_assert (ty = T_Int) "Condition in if statement must be integer";
		      (TSIf (te,ts1,ts2)) , env		    
  | SFor (el1,eopt,el3,s) -> let tel1 = List.map (type_expr env) el1 in (* et fait les vérifs pr e1 et e3 ? *)
			     let tel3 = List.map (type_expr env) el3 in
			     let teopt = (match eopt with
			       | None -> None
			       | Some e -> let te,(ty,_) = get_expr env e in
					   ty_assert (ty = T_Int) "Condition in for statement must be integer";
					   Some te) 
			     in
			     ignore( type_stm ret_type env s );  (* vérifie i *)
			     let ts, _ = type_stm ret_type env s in (* fait le truc d'avant aussi *)
			     TSFor (tel1,teopt,tel3,ts) , env
  (* traduire règles restantes du for*)
  | SWhile(e,s) -> let ts,tys = type_stm ret_type env s in
		   let te,(ty,_) = get_expr env e in
		      ty_assert (ty = T_Int) "Condition in if statement must be integer";
		   TSWhile(te,ts),env
  (* pq while n'est pas dans les règles données ? *)
  | SDeclare(vt,i) -> let ty,b = build_type_or_ref vt in
		      ty_assert (bf env.b_pe ty) "Malformed type";
		      ty_assert (not (Smap.mem i env.b_locals) ) "Variable redefinition";
		      let env0 =
			  {	b_pe = env.b_pe;
			  	b_locals = Smap.add i (ty,b) env.b_locals;
				b_class = env.b_class } in
		      TSDeclare( (ty,b) ,i) , env0
  | SDeclareAssignExpr(vt,i,e) -> let ty,b = build_type_or_ref vt in
				  ty_assert (bf env.b_pe ty) "Malformed type";
				  ty_assert (not (Smap.mem i env.b_locals)) "Variable redefinition";
				  let te,(tye,r,l) = get_expr0 env e in
				  ty_assert (if b  then r || l else true) "Can only assigne lvalue/reference to reference type var";
				  ty_assert (subtype env.b_pe tye ty) "Invalid data type for assign.";
				  let env0 = 
				  {	b_pe = env.b_pe;
				  	b_locals = Smap.add i (ty,b) env.b_locals;
					b_class = env.b_class } in
				  TSDeclareAssignExpr( (ty,b) ,i,te) , env0
  | SWriteCout(str_e_list) -> 
    let args = 
      List.map
	(fun e -> match e.se_desc with
	  | SEExpr e0 -> let te,(ty,_) = get_expr env {e_loc = e.se_loc; e_desc = e0} in 
			 ty_assert (ty = T_Int) "Expected integer or string in cout<<"; TSEExpr te
	  | SEStr s -> TSEStr(s) (* osef *)  
	)
	str_e_list 
    in
    TSWriteCout(args) , env
  | SDeclareAssignConstructor(vt,i,ti,e_l) -> ty_error "TODO"
		    
and build_block ret_type env b = (* utilisé ds compute_type_stm et def_global_fun *)
  let two_stms (env,l) s =
    let ts,env2 = type_stm ret_type env s in
    (env2,(ts::l)) in
  let ty_final,ts_list = List.fold_left two_stms (env,[]) b in 
  (* verif si b bien typé (règle i1;i2) et construit le te-block*)
  TSBlock (List.rev ts_list),env

and get_block ret_type env b =
  match fst (build_block ret_type env b) with
    | TSBlock tb -> tb
    | _ -> assert false

(* Déclarations de fonction *)

let parse_args env a =
	let args = List.map
		(fun (t, i) ->
			let t, r = build_type_or_ref t in
			ty_assert (bf env t) ("Malformed argument type for argument " ^ i ^ ".");
			(t, r), i)
		a in
	let rec aux = function
		| [] -> ()
		| p::q -> ty_assert (not (List.mem p q)) ("Argument name appears twice : " ^ p); aux q
	in aux (List.map snd args);
	args
 
let get_fun env p b = (* p : proto   b : block -> tp, tb, env2*)
  assert (p.p_class = None);
  let name = p.p_name in
  let ty_args = parse_args env p.p_args in
  (* Check there is not already a function with similar prototype *)
  let args_type = List.map fst ty_args in
  ty_assert (not (List.exists
	(fun p -> p.tp_name = name && (List.map fst p.tp_args) = args_type) env.e_funs))
	("Redefinition of function: " ^ name);

  let ret_type = build_type_or_ref
  (match p.p_ret_type with
	| Some k -> k
	| None -> ty_error "Internal error (function with no return type)" ) in

  (* Add to env *)
  let tproto = { tp_loc = p.p_loc ; tp_name = name ; tp_class = None ; tp_virtual = false ;
		 tp_ret_type = Some ret_type ; tp_args = ty_args; } in
  let env2 = 
		{	e_globals = env.e_globals;
			e_funs = tproto::(env.e_funs);
			e_classes = env.e_classes; } in
  (* Build local env *)
  let locales = List.fold_left (* tr = (ty,ref?) *)
	(fun envir (tr,i) -> Smap.add i tr envir)
	Smap.empty
	ty_args
  in (* contexte ds l'instruction *)
  let contexte = { b_pe = env2; b_locals = locales; b_class = None } in
  let tb = get_block ret_type contexte b in (* vérif instructions typées*)
  tproto,tb, env2

(* Déclarations de classes *)

let rec compute_tclass env c = 
	let name = c.c_name in
	ty_assert (not (Smap.mem name env.e_classes)) ("Redeclaration of class " ^name^".");
	let supers = match c.c_supers with | None -> [] | Some k -> k in
	List.iter (fun n ->
		ty_assert (Smap.mem n env.e_classes)
				("Super " ^ n ^ " does not exist or is not a class.")) supers;
	let cls_tmp = {tc_name = name; tc_supers = supers; tc_members = Smap.empty; tc_methods = [] } in
	let t_env = {
		e_globals = env.e_globals;
		e_funs = env.e_funs;
		e_classes = (Smap.add name cls_tmp env.e_classes); } in
	let mem, meth = List.fold_left
		(fun (mem, meth) n -> match n with
			| CVar(t, i) ->
				let t, r = build_type_or_ref t in
				ty_assert (not r) "Class members cannot be references.";
				ty_assert (bf t_env t) ("Malformed type for member " ^ i ^ ".");
				ty_assert (t <> TClass(name)) "Class cannot contain itself as a member.";
				ty_assert (not (Smap.mem i mem)) ("Redefinition of class member " ^ i ^ " in class " ^ name ^ ".");
				(Smap.add i t mem, meth)
			| CMethod(p) ->
				let m = err_add_loc p.p_loc (fun () -> (build_method t_env name meth false p)) in
				mem, m::meth
			| CVirtualMethod(p) ->
				let m = err_add_loc p.p_loc (fun () -> (build_method t_env name meth true p)) in
				mem, m::meth
		) (Smap.empty, []) c.c_members in
	{	tc_name = name;
		tc_supers = supers;
		tc_members = mem;
		tc_methods = meth; }
and build_method env cls_name cls_mems virt proto =
	ty_assert (proto.p_class = None) "Overqualification in prototype.";
	ty_assert (proto.p_ret_type <> None || proto.p_name = cls_name) "Invalid name for constructor";
	(* Make sure prototype is well formed *)
	let args = parse_args env proto.p_args in
	(* TODO Make sure method is compatible with parents and other declarations *)
	(* Check return type *)
	let ret_type = match proto.p_ret_type with
		| Some k -> Some (build_type_or_ref k)
		| None -> None in
	{	tp_virtual = virt;
		tp_loc = proto.p_loc;
		tp_name = proto.p_name;
		tp_class = Some(cls_name);
		tp_ret_type = ret_type;
		tp_args = args;
	}

let get_method env proto block = 	(* return : TDFunction *)
	match proto.p_class with
	| None -> assert false
	| Some(cls_name) ->
	try let c = Smap.find cls_name env.e_classes in
		let args = parse_args env proto.p_args in
		let ret_type = match proto.p_ret_type with
			| Some k -> Some (build_type_or_ref k)
			| None -> None in
		(* Find prototype in class *)
		begin try let cproto = List.find 
				(fun p -> p.tp_args = args && p.tp_ret_type = ret_type && p.tp_name = proto.p_name) c.tc_methods
			in
			let locals = List.fold_left
				(fun env (tr, i) -> Smap.add i tr env) Smap.empty args in
			let contexte = {
				b_pe = env;
				b_locals = locals;
				b_class = Some c; } in
			let tb = get_block (match ret_type with | None -> T_Void, false | Some k -> k) contexte block in
			{	tp_virtual = cproto.tp_virtual;
				tp_loc = proto.p_loc;
				tp_name = proto.p_name;
				tp_class = proto.p_class;
				tp_ret_type = ret_type;
				tp_args = args }, tb
		with
		| Not_found -> ty_error ("Implementation corresponds to no declared method of class " ^ cls_name)
		end
	with
	| Not_found -> ty_error (cls_name ^ " is not defined.")
	
(* Partie générique *)

let compute_decl env d = 
	err_add_loc (d.d_loc) (fun () ->
		match d.d_desc with
		  | DGlobal(t,i) -> let tr, r = build_type_or_ref t in
				ty_assert (bf env tr) ("Malformed type for global var " ^ i);
				ty_assert (not r) "Global cannot be reference";
		  		ty_assert (not (Smap.mem i env.e_globals)) ("Redeclaration of " ^ i);
				ty_assert (not (List.exists (fun p -> p.tp_name = i) env.e_funs)) ("Redeclaration of: " ^ i ^ ", was previously a function");
				(TDGlobal(tr,i)) , 
				{	e_globals = (Smap.add i tr env.e_globals);
					e_funs = env.e_funs;
					e_classes = env.e_classes }
		  (* on voudrait une liste de ident pr decl plsr en meme temps *)
		  | DFunction (p,b) ->
		  	ty_assert (not (Smap.mem p.p_name env.e_globals)) ("Redeclaration of: " ^ p.p_name ^ ", was previously a global variable");
		  	begin match p.p_class with
			| None ->
				let tp, tb, env2 = get_fun env p b in
				TDFunction(tp, tb), env2
			| Some _ ->
				let tp, tb = get_method env p b in
				(TDFunction(tp, tb)), env(* env is not modified *)
			end
		  | DClass c ->
		  	let tc = compute_tclass env c in
		  	(TDClass tc),
			{	e_globals = env.e_globals;
				e_funs = env.e_funs;
				e_classes = Smap.add c.c_name tc env.e_classes; }
		  )

let prog p =
  let decls, env = (
    List.fold_left 
      (fun (decls, env) decl ->
	  	let decl_p, env2 = compute_decl env decl in
		decl_p::decls, env2)
      ([],{ e_globals = Smap.empty; e_funs = []; e_classes = Smap.empty })
      p
  ) in
  { prog_decls = decls; prog_env = env }





