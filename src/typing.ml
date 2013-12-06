open Ast

(* Gestion des erreurs *)
exception LocError of loc * string
exception Error of string
let ty_assert x k = if not x then raise (Error (k))
let ty_error k = raise (Error (k))
let err_add_loc loc f =
	try f()
	with
		| Error(k) -> raise (LocError(loc, k))
		| LocError(_, _) as e -> raise e
		| Assert_failure (k, a, b) -> raise (LocError (loc, "Assertion failure : "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
		| Not_found -> raise (LocError (loc, "Not found"))
		| Invalid_argument(k) -> raise (LocError (loc, "Invalid argument "^k))
		| _ -> raise (LocError (loc, "Unexpected error"))

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
  | TENew of tident * texpression list

type tstr_expression =
	| TSEExpr of texpression
	| TSEStr of string


type tstatement = {
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
	| TSDeclareAssignConstructor of var_type * ident * tident * texpression list (* a faire *)
(* Type of variable, variable name, constructor class name, constructor arguments *)
	| TSWriteCout of tstr_expression list
and tblock = tstatement list

and tproto = {
	tp_loc : loc;
	tp_name : ident;	
	tp_class : tident option; (* p_class = none : standalone function *)
	tp_ret_type : type_ref option; (* p_class = some and p_ret_type = none : constructor *)
	tp_args : (type_ref * ident) list;
}

type decl_ident = (* type d'un identifieur *)
  | Var of type_ref
  | Fun of tproto * tblock
and env = decl_ident Smap.t (* string -> decl_ident *)

type tcls_mem =
	| TCVar of var_type * ident
	| TCMethod of tproto
	| TCVirtualMethod of tproto

type tcls = {
	tc_name : tident;
	tc_supers : tident list option;
	tc_members : tcls_mem list;
}

type tdeclaration =
	| TDGlobal of (type_ref * ident)
	| TDFunction of (tproto * tblock)
	| TDClass of tcls
	| TDNothing

type tprogram = tdeclaration list

(* Quelques fonctions utiles : *)

let find_v i env =
  match Smap.find i env with
    | Var tr -> tr
    | _ -> ty_error ("Not a variable : " ^ i)

let find_f i env =
  match Smap.find i env with
    | Fun (p,t) -> (p,t)
	| _ -> ty_error ("Not a function : " ^ i)


let rec bf = function			(* true si bien formé *)
  | T_Int -> true
  | TClass _ -> true
  | TPoint t -> bf t
  | _ -> false

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

let rec subtype a b = match a, b with
	| T_Int, T_Int -> true
	| T_Void, T_Void -> true
	| Typenull, TPoint(_) -> true
	| TPoint(ka), TPoint(kb) -> subtype ka kb
	| TClass(i), TClass(j) -> ty_error "Classes not implemented (in subtype a b)"
	| _ -> false


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

and compute_type env e = match e.e_desc with (* expression -> te_desc,(typ,ref?,left?) *)
    | EInt n -> TEInt n, (T_Int,false,false) 
    (* false, : pas une ref, pas une val gauche*)
    | EBool b -> let n = (if b then 1 else 0) in
		 TEInt n, (T_Int,false,false)
    | ENull -> TENull, (Typenull,false,false)
    | EIdent i -> 
      (try let ty,b = find_v i env in (* pb avec (i,bool) *)
	  ty_assert (bf ty) "Malformed type"; (* règle champs p4 *)
	   TEIdent i,(ty,b,true)
       with Not_found -> ty_error ("Unknown identifier " ^ i)
      )
    | EAssign (e1,e2) -> let te1,(ty1,r3,b3) = get_expr0 env e1 in
			 let te2,(ty2,_,_) = get_expr0 env e2 in
			 ty_assert (b3 || r3) "Can only assign to lvalue";
			 ty_assert (num ty1) "Cannot assign to non-numeric type (pointer type is numeric)";
			 ty_assert (subtype ty2 ty1) "Incompatible types in assign";
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
					ty_assert (ty1 = ty2) "Can only apply == or != to two values of same type";
					ty_assert (num ty1) "Can only apply == or != to pointers"
			      | Lt | Le | Gt | Ge
			      | Add | Sub | Mul | Div | Modulo
			      | Land | Lor ->
					ty_assert (ty1 = T_Int) "Left operand of binop is not integer";
					ty_assert (ty2 = T_Int) "Right operand of binop is not integer"
			    ); (* vérifs *)
			    TEBinary(te1,op,te2),(T_Int,false,false)
    | ECall (e,e_list) -> let name = (match e.e_desc with
			    | EIdent i -> i
			    | _ -> ty_error "Calling something that is not a function") in
			  let tproto,tblock = find_f name env in (* chope la fonction *)
			  let args_proto = List.map fst tproto.tp_args in 
			  let args_values = List.map (get_expr0 env) e_list in
			  begin try
			  	List.iter2 
					(fun arg ty_proto ->
						let _,(ty,r,l) = arg in
						let pty,pr = ty_proto in
						ty_assert (if pr then r || l else true) "Expected referencable value as argument";
						ty_assert (subtype ty pty) "Invalid argument type"
					) args_values args_proto
			  with
			  | Invalid_argument _ -> ty_error "Incorrect arity for function call"
			  end;
			  (* vérif ici pour adresse/valeur, ici on test seulement
			     que ce sont les mêmes types, pas d'adressage de pris en compte *)
			  let l_te = List.map fst args_values in 
			  (* que les te de e_list*)
			  let ty,b = match tproto.tp_ret_type with
			    | None -> assert false (* no return type only happens for constructors, and
											constructors cannot be called as functions *)
			    | Some (ty,b) -> ty,b in
			  TECallFun(name,l_te),(ty,b,false)
    | EMember _ -> ty_error "Not implemented"
    | ENew _ -> ty_error "Not implemented"
    | EThis -> ty_error "Not implemented"


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
				ty_assert (if rref then r else false) "Function must return reference";
  			
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
		      ty_assert (bf ty) "Malformed type";
		      ty_assert (not (Smap.mem i env) ) "Variable redefinition";
		      let env0 = Smap.add i (Var (ty,b)) env in
		      TSDeclare( (ty,b) ,i) , env0
  | SDeclareAssignExpr(vt,i,e) -> let ty,b = build_type_or_ref vt in
				  ty_assert (bf ty) "Malformed type";
				  ty_assert (not (Smap.mem i env)) "Variable redefinition";
				  let te,(tye,r,l) = get_expr0 env e in
				  ty_assert (if b  then r || l else true) "Can only assigne lvalue/reference to reference type var";
				 (* assert tye<ty;*)
				  let env0 = Smap.add i (Var (ty,b) ) env in
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
  | SDeclareAssignConstructor(vt,i,ti,e_l) -> TSEmpty,env (* a faire *)
		    
and build_block ret_type env b = (* utilisé ds compute_type_stm et def_global_fun *)
  let two_stms (env,l) s =
    let ts,ty = type_stm ret_type env s in
    (ty,(ts::l)) in
  let ty_final,ts_list = List.fold_left two_stms (env,[]) b in 
  (* verif si b bien typé (règle i1;i2) et construit le te-block*)
  TSBlock (List.rev ts_list),env

and get_block ret_type env b =
  match fst (build_block ret_type env b) with
    | TSBlock tb -> tb
    | _ -> assert false

(* Autres *)
 
let get_fun env p b = (* p : proto   b : block -> name,Fun( ...)*)
  let name = p.p_name in
  let ty_args = 
    List.map (* liste des arguments tr*ident *)
      (fun (vt,i) -> let tr = build_type_or_ref vt in
		     (tr,i)              )
      p.p_args
  in
(* vérif que les xi sont distincts, enlever '&' possible
pour traiter les ref, en fait fait quand on appelle sur proto.p_args *)
  let ids = List.map snd p.p_args in (* juste les ident*)
  let aux = function
  	| [] -> ()
	| p::q -> ty_assert (not (List.mem p q)) ("Argument name appears twice : " ^ p)
  in aux ids;
  List.iter (fun ((ty,_),_) -> assert( bf ty ) ) ty_args; 
(* types st bf*)
  let ret_type = build_type_or_ref (match p.p_ret_type with | Some k -> k | None -> assert false (* not implemented *) ) in
  let contexte = List.fold_left (* tr = (ty,ref?) *)
    (fun envir (tr,i) -> Smap.add i (Var tr) envir)
    env
    ty_args
  in (* contexte ds l'instruction *)
  let tb = get_block ret_type contexte b in (* vérif instructions typées*)
  let tproto = { tp_loc = p.p_loc ; tp_name = name ; tp_class = None ;
		 tp_ret_type = Some ret_type ; tp_args = ty_args; }
  in
  name,tproto,tb

let compute_decl env d = 
	err_add_loc (d.d_loc) (fun () ->
		match d.d_desc with
		  | DGlobal(t,i) -> let tr = build_type_or_ref t in
				ty_assert (bf (fst tr)) ("Malformed type for global var " ^ i);
		  		ty_assert (not (Smap.mem i env)) ("Redeclaration of " ^ i);
					(TDGlobal(tr,i)) , (Smap.add i (Var tr) env)
		  (* on voudrait une liste de ident pr decl plsr en meme temps *)
		  | DFunction (p,b) -> let name,tp,tb = get_fun env p b in
		  				ty_assert (not (Smap.mem name env)) ("Redeclaration of " ^ name);
					   (TDFunction (tp,tb) ) , (Smap.add name (Fun (tp,tb)) env)
		  | DClass c -> ty_error "Not implemented : classes" (* TODO *)
		  )

let prog p =
  let l = (
    List.fold_left 
      (fun list decl  -> let (td,env) = List.hd list in
			 (compute_decl env decl)::list         )
      [(TDNothing,Smap.empty)]
      p
  ) in
  List.map fst l





