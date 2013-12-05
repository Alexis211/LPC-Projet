open Ast

(* Gestion des erreurs *)
exception LocError of loc * string
exception Error of string
let er_ident i = raise (Error ("Unknown identifier " ^ i))
let er_ident_loc i loc = raise (LocError (loc, "Unknown identifier " ^ i))
let er_not_a_variable i = raise (Error ("Expected '"^i^"' to be a variable"))
let er_not_a_function i = raise (Error ("Expected '"^i^"' to be a function"))
let er_tident_use () = raise (Error ("Er_tident_use"))
let er_double_ref () = raise (Error ("Er_double_ref"))
let er_ref_use ()= raise (Error ("Er_ref_use"))
let er_not_implemented () = raise (Error ("Not implemented"))
let ty_assert x k = if not x then raise (Error (k))
let ty_error k = raise (Error (k))

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

type mem = (* type d'une expression *)
  | Var of type_ref
  | Fun of tproto * tblock
  | Env of stmt (* statement type *)
and stmt = mem Smap.t (* string -> env *)

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
    | _ -> er_not_a_variable i

let find_f i env =
  match Smap.find i env with
    | Fun (p,t) -> (p,t)
	| _ -> er_not_a_function i

let same_type t1 t2 = (* types mem *)
  let tr1 = (match t1 with
    | Var (typ,_) -> typ
	| _ -> er_not_a_variable "") in
  let tr2 = (match t2 with
   | Var (typ,_) -> typ
   | _ -> er_not_a_variable "") in
  tr1 = tr2

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
    | TRef _ -> er_ref_use()
    | TIdent tid -> TClass tid
  in
  match vt with
    | TRef (TRef vt) -> er_double_ref() (* ... *)
    | TRef vt -> (see vt),true (* indique qu'il s'agit d'une ref *)
    | vt -> (see vt),false

(* -------------------------------------------- *)
(* On passe aux choses sérieuses *)

let rec type_expr env e = (* expression -> texpression *)
  try 
    let d,(ty,b1,b2) = compute_type env e in
    { te_loc = e.e_loc; te_desc = d; type_expr = (ty,b1,b2) }
  with
  	| Error(k) -> raise (LocError(e.e_loc, k))
	| LocError(_, _) as e -> raise e
    | _ -> raise (LocError (e.e_loc,"Other error"))

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
       with Not_found -> er_ident i
      )
    | EAssign (e1,e2) -> let te1,(ty1,_,b3) = get_expr0 env e1 in
			 let te2,(ty2,_,_) = get_expr0 env e2 in
			 ty_assert (b3 = true) "Can only assign to lvalue";
			 ty_assert (num ty1) "Cannot assign to non-numeric type (pointer type is numeric)";
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
			   TEUnary(op,te), (t,true,false)
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
			    | _ -> failwith "Not a function") in
			  let tproto,tblock = find_f name env in (* chope la fonction *)
			  let args = List.map (fun ((ty,_),_) -> ty) tproto.tp_args in (* pas adressage pris en compte *)
			  let l = List.map (get_expr env) e_list in
			  let tab = Array.of_list args in
			  List.iteri 
			    (fun j (te,(ty0,b)) -> 
			      ty_assert (ty0 = tab.(j)) "Invalid type for function argument" )
			    l ;
			  (* vérif ici pour adresse/valeur, ici on test seulement
			     que ce sont les mêmes types, pas d'adressage de pris en compte *)
			  let l_te = List.map fst l in 
			  (* que les te de e_list*)
			  let ty = match tproto.tp_ret_type with
			    | None -> T_Void
			    | Some (ty,b) -> ty in
			  TECallFun(name,l_te),(ty,false,false)
    | EMember _ -> TEInt 0, (T_Int,false,false)
    | ENew _ -> TEInt 0, (T_Int,false,false)
    | EThis -> TEInt 0, (T_Int,false,false)


(* Statements *)

let rec type_stm env s = 
  let d, ty = compute_type_stm env s in
  { ts_loc = s.s_loc; ts_desc = d }, ty

and compute_type_stm env s = match s.s_desc with (* statement -> ts_desc,stm_type *)
  | SEmpty -> TSEmpty,env
  | SExpr e -> let te,(ty,_) = get_expr env e in (* verif ty est bien typé *)
	       (TSExpr te) , env
  | SBlock b -> build_block env b
  | SReturn None -> (TSReturn None) , env
  | SReturn (Some e0) ->  let te,(ty,_) = get_expr env e0 in
			  TSReturn (Some te), env 
  | SIf (e,s1,s2) ->  let te,(ty,_) = get_expr env e in
		      let ts1,ty1 = type_stm env s1 in (* vérifs règle *)
		      let ts2,ty2 = type_stm env s2 in
		      assert (ty = T_Int);
		      (TSIf (te,ts1,ts2)) , env		    
  | SFor (el1,eopt,el3,s) -> let tel1 = List.map (type_expr env) el1 in (* et fait les vérifs pr e1 et e3 ? *)
			     let tel3 = List.map (type_expr env) el3 in
			     let teopt = (match eopt with
			       | None -> None
			       | Some e -> let te,(ty,_) = get_expr env e in
					   assert (ty = T_Int);
					   Some te) 
			     in
			     ignore( type_stm env s );  (* vérifie i *)
			     let ts, _ = type_stm env s in (* fait le truc d'avant aussi *)
			     TSFor (tel1,teopt,tel3,ts) , env
  (* traduire règles restantes du for*)
  | SWhile(e,s) -> let ts,tys = type_stm env s in
		   let te,(ty,_) = get_expr env e in
		   TSWhile(te,ts),env
  (* pq while n'est pas dans les règles données ? *)
  | SDeclare(vt,i) -> let ty,b = build_type_or_ref vt in
		      assert (bf ty);
		      assert (not (Smap.mem i env) );
		      let env0 = Smap.add i (Var (ty,b)) env in
		      TSDeclare( (ty,b) ,i) , env0
  | SDeclareAssignExpr(vt,i,e) -> let ty,b = build_type_or_ref vt in
				  assert (bf ty);
				  assert (not (Smap.mem i env));
				  let te,(tye,_) = get_expr env e in
				 (* assert tye<ty;*)
				  let env0 = Smap.add i (Var (ty,b) ) env in
				  TSDeclareAssignExpr( (ty,b) ,i,te) , env0
  | SWriteCout(str_e_list) -> 
    let args = 
      List.map
	(fun e -> match e.se_desc with
	  | SEExpr e0 -> let te,(ty,_) = get_expr env {e_loc = e.se_loc; e_desc = e0} in 
			 assert (ty = T_Int); TSEExpr te
	  | SEStr s -> TSEStr(s) (* osef *)  
	)
	str_e_list 
    in
    TSWriteCout(args) , env
  | SDeclareAssignConstructor(vt,i,ti,e_l) -> TSEmpty,env (* a faire *)
		    
and build_block env b = (* utilisé ds compute_type_stm et def_global_fun *)
  let two_stms (env,l) s =
    let ts,ty = type_stm env s in
    (ty,(ts::l)) in
  let ty_final,ts_list = List.fold_left two_stms (env,[]) b in 
  (* verif si b bien typé (règle i1;i2) et construit le te-block*)
  TSBlock (List.rev ts_list),env

and get_block env b =
  match fst (build_block env b) with
    | TSBlock tb -> tb
    | _ -> failwith "Pas possible"

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
  let n = List.length p.p_args in
  let ids = Array.of_list( List.map snd p.p_args ) in (* juste les ident*)
  for i = 0 to n-2 do
    for j = i+1 to n-1 do
      assert (String.compare ids.(i) ids.(j) = 0) (* compare 2 à 2 *)
    done;
  done;
  List.iter (fun ((ty,_),_) -> assert( bf ty ) ) ty_args; 
(* types st bf*)
  let contexte = List.fold_left (* tr = (ty,ref?) *)
    (fun envir (tr,i) -> Smap.add i (Var tr) envir)
    env
    ty_args
  in (* contexte ds l'instruction *)
  let tb = get_block contexte b in (* vérif instructions typées*)
  let tproto = { tp_loc = p.p_loc ; tp_name = name ; tp_class = None ;
		 tp_ret_type = None ; tp_args = ty_args; }
  in
  name,tproto,tb

let compute_decl env = function
  | DGlobal(t,i) -> let tr = build_type_or_ref t in
		    (TDGlobal(tr,i)) , (Smap.add i (Var tr) env)
  (* on voudrait une liste de ident pr decl plsr en meme temps *)
  | DFunction (p,b) -> let name,tp,tb = get_fun env p b in
		       (TDFunction (tp,tb) ) , (Smap.add name (Fun (tp,tb)) env)
  | DClass c -> er_not_implemented() (* TODO *)

let prog p =
  let l = (
    List.fold_left 
      (fun list decl  -> let (td,env) = List.hd list in
			 (compute_decl env decl)::list         )
      [(TDNothing,Smap.empty)]
      p
  ) in
  List.map fst l





