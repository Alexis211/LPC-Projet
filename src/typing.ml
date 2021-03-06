open Ast

(* Gestion des erreurs *)
exception Error of string
exception LocError of loc * string
exception NoCorrespondingPrototype
exception AmbiguousOverload
let ty_assert x k = if not x then raise (Error (k))
let ty_error k = raise (Error (k))
let err_add_loc loc f =
    try f()
    with
        | Error(k) -> raise (LocError(loc, k))
        | LocError(_, _) as e -> raise e
        | NoCorrespondingPrototype -> raise (LocError (loc, "No corresponding prototype"))
        | AmbiguousOverload -> raise (LocError (loc, "Ambiguous overload"))
        | Assert_failure (k, a, b) -> raise (LocError (loc,
            "(unexpected) Assertion failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
        | Not_found -> raise (LocError (loc, "(unexpected) Not found"))
        | Invalid_argument(k) -> raise (LocError (loc, "(unexpected) Invalid argument: "^k))
        | Match_failure(k, a, b) -> raise (LocError (loc,
            "(unexpected) Match failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
        | Stack_overflow -> raise (LocError (loc, "(unexpected) Stack overflow"))
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
  | TECallFun of ident * (texpression * bool) list * bool (* changé : te -> ident *)
    (* calls to non-virtual methods are compiled using TECallFun, with the object cons'ed at
        the begining of the arguments expression list *)
    (* for each argument, bool is is argument passed by reference ? *)
    (* final bool : is returned value a reference ? *)
  | TECallVirtual of texpression * int * (texpression * bool) list * bool
    (* object * index in vtable * arguments * is return value a reference? *)
  | TEUnary of unop * texpression
  | TEBinary of texpression * binop * texpression
  | TEMember of texpression * int   (* object * position of member *)
  | TEPointerCast of texpression * int   (* object * position of member *)
  | TENew of tcls * ident * (texpression * bool) list

and tstr_expression =
    | TSEExpr of texpression
    | TSEStr of string


and tstatement =
    | TSEmpty
    | TSExpr of texpression
    | TSIf of texpression  * tstatement * tstatement
    | TSWhile of texpression * tstatement
    | TSFor of texpression list * texpression option * texpression list * tstatement
    | TSBlock of tblock
    | TSReturn of texpression option
    | TSDeclare of typ * ident
    | TSDeclareAssignExpr of type_ref * ident * texpression
    | TSDeclareAssignConstructor of tcls * ident * ident * (texpression * bool) list
(* Class name of variable, variable name, constructor name, constructor arguments *)
    | TSWriteCout of tstr_expression list
and tblock = tstatement list

and tproto = {
    tp_virtual : (tcls_hier * int) option;    (* only used for class methods ; if none then not virtual *)
    tp_name : ident;    
    tp_unique_ident : ident;    (* label de la fonction dans le code assembleur *)
    tp_class : tident option; (* p_class = none : standalone function *)
    tp_ret_type : type_ref option; (* p_class = some and p_ret_type = none : constructor *)
    tp_args : (type_ref * ident) list;
}

and tcls_supers = tcls_hier list
and tcls_hier = {
    h_class : tident;
    mutable h_pos : int;
    mutable h_vtable : (int * tproto) list; (* only to be muted during class definition parsing *)
    h_supers : tcls_supers
}

and tcls = {
    tc_name : tident;
    tc_size : int;
    tc_hier : tcls_hier;
        (* tous les supers à tous les niveaux, plus la classe actuelle *)
    tc_members : (typ * int) Smap.t;    (* type du membre * position du membre dans les données de l'objet *)
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
    prog_main : ident;
}

(* Quelques fonctions utiles : *)

let tproto_numbering = ref 1
let tproto_unique_number () =
    let k = !tproto_numbering in
    tproto_numbering := k + 1;
    string_of_int k

let get_c env i =
  try Smap.find i env.e_classes with Not_found -> ty_error ("No such class: " ^ i)

let rec bf env t =
  let rec aux = function            (* true si bien formé *)
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
    | TRef _ -> ty_error ("Unexpected reference type - no pointers on references allowed")
    | TIdent tid -> TClass tid
  in
  match vt with
    | TRef (TRef vt) -> ty_error ("Double references not allowed") (* ... *)
    | TRef vt -> (see vt),true (* indique qu'il s'agit d'une ref *)
    | vt -> (see vt),false

let rec subtype env a b = match a, b with
    | T_Int, T_Int -> true
    | T_Void, T_Void -> true
    | Typenull, TPoint(_) -> true
    | TPoint(TPoint(TClass(_))), TPoint(TPoint(_)) -> false
    | TPoint(ka), TPoint(kb) -> subtype env ka kb
    | TClass(i), TClass(j) ->
        let c = get_c env i in
        let rec find_in_hier h =
          h.h_class = j ||
          (List.length (List.filter find_in_hier h.h_supers) = 1)
        in find_in_hier c.tc_hier
    | _ -> false

let relative_class_position env i j =
  let c = get_c env i in
  let rec find_in_hier h =
    h.h_class = j ||
    (List.length (List.filter find_in_hier h.h_supers) = 1)
  and get_in_hier h =
    if h.h_class = j
      then h.h_pos
      else match List.filter find_in_hier h.h_supers with
        | [a] -> get_in_hier a
        | _ -> assert false
  in get_in_hier c.tc_hier

let rec upcast env exp dt =   (* présupposé : exp.type_expr <= dt *)
  match exp.type_expr, dt with
  | (T_Int, _, _), T_Int -> exp
  | (T_Void, _, _), T_Void -> exp
  | (Typenull, _, _), TPoint(_) -> exp
  | (TClass(i), a, b), TClass(j) when a||b ->
    begin match relative_class_position env i j with
    | 0 -> exp
    | pos ->
        { type_expr = (TClass(j), false, true); te_loc = exp.te_loc;
          te_desc = TEMember(exp, pos) }
    end
  | (TPoint(TClass(i)), a, b), TPoint(TClass(j)) ->
    begin match relative_class_position env i j with
    | 0 -> exp
    | pos ->
        { type_expr = (TPoint(TClass(j)), false, true); te_loc = exp.te_loc;
          te_desc = TEPointerCast(exp, pos) }
    end
  | (TPoint(ka), _, _), TPoint(kb) -> exp
  | _ -> assert false

let type_size env t = match t with
    | T_Int | Typenull | TPoint(_) -> 4
    | T_Void -> 0
    | TClass(c) -> let c = get_c env c in c.tc_size

(* pour la surcharge de fonctions *)
let possible_protos env arg_type_list fun_list =
    List.filter
        (fun proto ->
            try List.for_all2
                (fun (t_a, t_a_ref) (t_p, t_p_ref) ->
                    if t_p_ref && (not t_a_ref) then false else
                    subtype env t_a t_p)
                arg_type_list (List.map fst proto.tp_args)
            with Invalid_argument _ -> false)
        fun_list
let closest_proto env arg_type_list fun_list =
    match possible_protos env arg_type_list fun_list with
    | [] -> raise NoCorrespondingPrototype
    | [p] -> p
    | _ -> raise AmbiguousOverload
let find_protos_in_class env cls name =
  let rec aux s =
    match List.filter (fun p -> p.tp_name = name) (get_c env s.h_class).tc_methods with
    | [] ->
      List.fold_left (fun q r ->
            match q, (aux r) with | [], l -> l | l, [] -> l | _, _ -> raise AmbiguousOverload) [] s.h_supers
    | k -> k
  in aux (get_c env cls).tc_hier


let find_cls_mem env cls_name mem_name =
    let rec aux s =
      begin try let mty, mi = Smap.find mem_name (get_c env s.h_class).tc_members in
        Some (mty, mi + s.h_pos)
      with Not_found -> 
        List.fold_left (fun q r ->
          match q, (aux r) with
          | Some l, None -> Some l
          | None, Some l -> Some l
          | None, None -> None
          | _, _ -> ty_error ("Ambiguous reference to member " ^ mem_name)) None s.h_supers
      end
    in match aux (get_c env cls_name).tc_hier with
    | Some k -> k
    | None -> raise Not_found

let find_cls_superclass env cls_name superclass =
    let rec aux s =
        if s.h_class = superclass then
            Some s
        else
            List.fold_left (fun q r ->
                match q, aux r with
                | Some l, None | None, Some l -> Some l
                | None, None -> None
                | _, _ -> ty_error ("Ambiguous reference to superclass " ^ superclass))
                None s.h_supers
    in match aux (get_c env cls_name).tc_hier with
    | Some k -> k
    | None -> raise Not_found


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
    let ttype = (TClass(match env.b_class with | Some c -> c.tc_name | None -> "#")) in
    let e_this = 
    {   te_loc = e.e_loc;
        te_desc = TEThis;
        type_expr = TPoint(ttype), false, true } in
    let e_this_not_ptr =
    {   te_loc = e.e_loc;
        te_desc = TEUnary(Deref, e_this);
        type_expr = ttype, false, true; } in
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
            | Some k -> let mty, mi = find_cls_mem env.b_pe k.tc_name i in
                TEMember(e_this_not_ptr, mi),
                 (mty, false, true)
            | None -> raise Not_found
        with Not_found ->
            try let t = Smap.find i env.b_pe.e_globals in
            TEIdent i, (t, false, true)
        with Not_found -> ty_error ("Undeclared identifier: " ^ i)
        end
    | EQIdent(c, i) ->
        begin match env.b_class with
        | Some k ->
            let sc = try find_cls_superclass env.b_pe k.tc_name c
                with Not_found -> ty_error (c ^ " is no superclass of current class " ^ k.tc_name) in
            let mty, mi = find_cls_mem env.b_pe sc.h_class i in
                TEMember(e_this_not_ptr, mi + sc.h_pos), (mty, false, true)
        | None -> ty_error "Qualified identifier invalid in function belonging to no class."
        end
    | EAssign (e1,e2) -> let te1,(ty1,r3,b3) = get_expr0 env e1 in
             let te2,(ty2,_,_) = get_expr0 env e2 in
             ty_assert (b3 || r3) "Can only assign to lvalue";
             ty_assert (num ty1) "Cannot assign to non-numeric type (pointer type is numeric)";
             ty_assert (subtype env.b_pe ty2 ty1) "Incompatible types in assign";
                    (* type num et ref compatibles ?*)
             (TEAssign (te1,upcast env.b_pe te2 ty1) ),(ty1,false,false)
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
                    ty_assert (num ty1) "Can only apply == or != to pointers";
                    let te1 = if subtype env.b_pe ty1 ty2 then upcast env.b_pe te1 ty2 else te1 in
                    let te2 = if subtype env.b_pe ty2 ty1 then upcast env.b_pe te2 ty1 else te2 in
                    TEBinary(te1,op,te2),(T_Int,false,false)
                  | Lt | Le | Gt | Ge
                  | Add | Sub | Mul | Div | Modulo
                  | Land | Lor ->
                    ty_assert (ty1 = T_Int) "Left operand of binop is not integer";
                    ty_assert (ty2 = T_Int) "Right operand of binop is not integer";
                    TEBinary(te1,op,te2),(T_Int,false,false)
                )
    | ECall (e,e_list) ->
            let args_values = List.map (get_expr0 env) e_list in
            let args_types = List.map (fun (e, (t, r, l)) -> t, r||l) args_values in

            let obj, tproto = (match e.e_desc with
                | EIdent i ->
                    let funs = List.filter (fun p -> p.tp_name = i) env.b_pe.e_funs in
                    begin match env.b_class with
                    | None -> None, closest_proto env.b_pe args_types funs
                    | Some k ->
                        begin try 
                            let proto = closest_proto env.b_pe args_types (find_protos_in_class env.b_pe k.tc_name i) in
                            let upcasted =
                                  upcast env.b_pe e_this_not_ptr
                                     (TClass (match proto.tp_class with | None -> assert false | Some k -> k)) in
                            Some upcasted, proto
                        with NoCorrespondingPrototype ->
                            None, closest_proto env.b_pe args_types funs
                        end
                    end
                | EMember(e, i) ->
                    let e = type_expr env e in
                    begin match e.type_expr with
                    | TClass(k), a, b when a || b ->
                        let proto = closest_proto env.b_pe args_types (find_protos_in_class env.b_pe k i) in
                        let upcasted =
                              upcast env.b_pe e
                                 (TClass (match proto.tp_class with | None -> assert false | Some k -> k)) in
                        Some upcasted, proto
                    | _ -> ty_error "Invalid argument type for method call (not a class, or not a lvalue)"
                    end
                | EQIdent(c, i) ->
                    begin match env.b_class with
                    | Some k ->
                        let sc = try find_cls_superclass env.b_pe k.tc_name c
                            with Not_found -> ty_error (c ^ " is no superclass of current class " ^ k.tc_name) in
                        let proto = closest_proto env.b_pe args_types (find_protos_in_class env.b_pe sc.h_class i) in
                        let upcasted =
                            upcast env.b_pe e_this_not_ptr
                                (TClass (match proto.tp_class with | None -> assert false | Some k -> k)) in
                        Some upcasted, proto
                    | None -> ty_error "Qualified identifier in a function belonging to no class."
                    end
                | _ -> ty_error "Calling something that is neither a function nor a method") in
          let l_te = List.map fst args_values in 
          let l_te = List.map2 (fun k ((ty, r), _) -> upcast env.b_pe k ty, r) l_te tproto.tp_args in
          let ty,b = match tproto.tp_ret_type with
            | None -> ty_error "Constructor cannot be called as function"
            | Some (ty,b) -> ty,b in
          begin match tproto.tp_virtual, obj with
          | None, None -> 
                TECallFun(tproto.tp_unique_ident,l_te,b),(ty,b,false)
          | None, Some(obj)->
                TECallFun(tproto.tp_unique_ident,(obj, true)::l_te,b),(ty,b,false)
          | Some(hier, idx), Some(obj) ->
                TECallVirtual(upcast env.b_pe obj (TClass hier.h_class), idx, l_te,b),(ty,b,false)
          | _ -> ty_error "(should not happen) Virtual function applied to no object..."
          end
    | EMember (e, id) ->
        let e, (ty, r, l) = get_expr0 env e in
        begin match ty with
        | TClass(c_name) ->
            begin try let mty, mi = find_cls_mem env.b_pe c_name id in
                TEMember(e, mi), (mty, false, true)
            with | Not_found -> ty_error ("Class " ^ c_name ^ " has no member " ^ id)
            end
        | _ -> ty_error "Cannot get member of expression that is not a class"
        end
    | ENew (cls_name, args) -> 
        let c = get_c env.b_pe cls_name in
        let args_values = List.map (get_expr0 env) args in
          let args_types = List.map (fun (e, (t, r, l)) -> t, r||l) args_values in
        let candidates = List.filter (fun p -> p.tp_ret_type = None) c.tc_methods in
        begin match candidates with
        | [] -> assert false (* default constructor should always be in list *)
        | _ ->
            let p = closest_proto env.b_pe args_types candidates in
            (* closest_proto makes sure the prototypes match, no problem here *)
            let l_te = List.map fst args_values in
            let l_te = List.map2 (fun k ((ty, r), _) -> upcast env.b_pe k ty, r) l_te p.tp_args in
            TENew(c, p.tp_unique_ident, l_te), (TPoint(TClass(cls_name)), false, false)
        end
    | EThis -> 
        begin match env.b_class with
        | Some c -> TEThis, (TPoint(TClass(c.tc_name)), false, true)
        | None -> ty_error "Cannot use this outside of method"
        end


(* Statements *)

let rec type_stm ret_type env s = 
    err_add_loc s.s_loc (fun () -> compute_type_stm ret_type env s)

and compute_type_stm ret_type env s = match s.s_desc with (* statement -> ts_desc,stm_type *)
  | SEmpty -> TSEmpty,env
  | SExpr e -> let te,(ty,_) = get_expr env e in (* verif ty est bien typé *)
           (TSExpr te) , env
  | SBlock b -> build_block ret_type env b
  | SReturn None -> 
    let ty, ref = ret_type in
    ty_assert (ty = T_Void) "Function must return non-void value";
    (TSReturn None) , env
  | SReturn (Some e0) ->  let te,(ty,r,l) = get_expr0 env e0 in
        let rty, rref = ret_type in
                ty_assert (rty = ty) "Invalid return type";
                ty_assert (if rref then r||l else true) "Function must return reference";
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
              ty_assert (ty = T_Int) "Condition in while statement must be integer";
           TSWhile(te,ts),env
  (* pq while n'est pas dans les règles données ? *)
  | SDeclare(vt,i) -> let ty,b = build_type_or_ref vt in
              ty_assert (bf env.b_pe ty) "Malformed type";
              ty_assert (not b) "Reference must be assigned at declaration";
              ty_assert (not (Smap.mem i env.b_locals) ) "Variable redefinition";
              let env0 = { env with b_locals = Smap.add i (ty,b) env.b_locals } in
              TSDeclare( ty ,i) , env0
  | SDeclareAssignExpr(vt,i,e) -> let ty,b = build_type_or_ref vt in
          ty_assert (bf env.b_pe ty) "Malformed type";
          ty_assert (not (Smap.mem i env.b_locals)) "Variable redefinition";
          let te,(tye,r,l) = get_expr0 env e in
          ty_assert (if b  then r || l else true) "Can only assigne lvalue/reference to reference type var";
          ty_assert (subtype env.b_pe tye ty) "Invalid data type for assign.";
          let env0 = { env with b_locals = Smap.add i (ty,b) env.b_locals } in
          TSDeclareAssignExpr( (ty,b) ,i,upcast env.b_pe te ty) , env0
  | SDeclareAssignConstructor(vt,i,ti,e_l) ->
        let ty, b = build_type_or_ref vt in
        ty_assert (bf env.b_pe ty) "Malformed type";
        ty_assert (not (Smap.mem i env.b_locals)) "Variable redefinition";
        ty_assert (not b) "Cannot have reference on a newly created object";
        ty_assert (ty = (TClass ti)) "Invalid type for constructor";
        let c = get_c env.b_pe ti in
        let args_values= List.map (get_expr0 env) e_l in
          let args_types = List.map (fun (e, (t, r, l)) -> t, r||l) args_values in
        let candidates = List.filter (fun p -> p.tp_ret_type = None) c.tc_methods in
        begin match candidates with
        | [] -> assert false (* ... *)
        | _ ->
            let p = closest_proto env.b_pe args_types candidates in
            (* closest_proto makes sure the prototypes match, no problem here *)
            let l_te = List.map fst args_values in
            let l_te = List.map2 (fun k ((ty, r), _) -> upcast env.b_pe k ty, r) l_te p.tp_args in
            let env0 = { env with b_locals = Smap.add i (ty,b) env.b_locals } in
            TSDeclareAssignConstructor(c, i, p.tp_unique_ident, l_te), env0
        end
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
    in
        aux (List.map snd args);
        args
 
let get_fun env p b = (* p : proto   b : block -> tp, tb, env2*)
  assert (p.p_class = None);
  let name = p.p_name in
  let args = parse_args env p.p_args in
  (* Check there is not already a function with similar prototype *)
  let args_types = List.map fst args in
  ty_assert (not (List.exists
    (fun p -> p.tp_name = name && (List.map fst p.tp_args) = args_types) env.e_funs))
    ("Redefinition of function: " ^ name);

  let ret_type = build_type_or_ref
  (match p.p_ret_type with
    | Some k -> k
    | None -> ty_error "Internal error (function with no return type)" ) in

  (* Add to env *)
  let tproto = {
        tp_name = name ;
        tp_unique_ident = name ^ (tproto_unique_number());
        tp_class = None ;
        tp_virtual = None ;
        tp_ret_type = Some ret_type ;
        tp_args = args; } in
  let env2 = { env with e_funs = tproto::(env.e_funs) } in
  (* Build local env *)
  let locales = List.fold_left (* tr = (ty,ref?) *)
    (fun envir (tr, i) -> Smap.add i tr envir)
    Smap.empty
    args
  in (* contexte ds l'instruction *)
  let contexte = { b_pe = env2; b_locals = locales; b_class = None } in
  let tb = get_block ret_type contexte b in (* vérif instructions typées*)
  tproto,tb, env2

(* Déclarations de classes *)

let compute_tclass env c = 
    let cls_name = c.c_name in
    ty_assert (not (Smap.mem cls_name env.e_classes)) ("Redeclaration of class " ^cls_name^".");
    (* artifice pour que la classe en train d'être définie puisse être utilisée par elle-même *)
    let forward_def = {
        tc_name = cls_name;
        tc_size = 0;
        tc_hier = { h_class = cls_name; h_pos = 0; h_vtable = []; h_supers = [] } ;
        tc_members = Smap.empty; tc_methods = []; } in
    let forward_env = { env with e_classes = (Smap.add cls_name forward_def env.e_classes); } in

    let super_list = match c.c_supers with | None -> [] | Some l -> l in

    let hier, used =
      let rec move_super diff s =
        { s with
          h_pos = s.h_pos + diff;
          h_supers = List.map (move_super diff) s.h_supers }
      in
      let sup, used = List.fold_left
        (fun (sup, u) n -> let c = get_c env n in
          (move_super u c.tc_hier)::sup, u + c.tc_size) ([], 4) super_list in
      { h_class = cls_name;
        h_pos = 0;
        h_vtable = [];
        h_supers = sup }, used
    in

    let (mem, mem_u), meth = List.fold_left
        (fun ((mem, mem_u), meth) n -> match n with
            | CVar(t, i) ->
                let t, r = build_type_or_ref t in
                ty_assert (not r) "Class members cannot be references.";
                ty_assert (bf forward_env t) ("Malformed type for member " ^ i ^ ".");
                ty_assert (t <> TClass(cls_name)) "Class cannot contain itself as a member.";
                ty_assert (not (Smap.mem i mem)) ("Redefinition of class member " ^ i ^ " in class " ^ cls_name ^ ".");
                let size = type_size env t in 
                ((Smap.add i (t, mem_u) mem, mem_u + size), meth)
            | CMethod(proto, virt) ->
                let m = err_add_loc proto.p_loc (fun () ->
                    ty_assert (proto.p_class = None) "Overqualification in prototype.";
                    ty_assert (proto.p_ret_type <> None || proto.p_name = cls_name) "Invalid name for constructor";
                    (* Make sure prototype is well formed *)
                    let args = parse_args forward_env proto.p_args in
                    let args_types = List.map fst args in
                    (* Make sure method is compatible with other declarations in this class *)
                    ty_assert (not (List.exists
                            (fun p -> p.tp_name = proto.p_name && (List.map fst p.tp_args) = args_types) meth))
                        ("Redefinition of function " ^ proto.p_name ^ " with same argument types.");
                    (* Check return type *)
                    let ret_type = match proto.p_ret_type with
                        | Some k -> Some (build_type_or_ref k)
                        | None -> None in

                    (* Build primitive proto *)
                    let tproto = 
                    {   tp_virtual = None;
                        tp_name = proto.p_name;
                        tp_unique_ident = proto.p_name ^ (tproto_unique_number()) ;
                        tp_class = Some(cls_name);
                        tp_ret_type = ret_type;
                        tp_args = args;
                    } in

                    (*  If method is redefined from a virtual method of a parent class,
                            it becomes virtual with same offset
                        If method is redefined from a virtual method of several parent classes,
                            update vtables for all these parent classes, use any as virtual
                            class for this class.
                        Else if method is virtual, it gets new offset !
                        Else method is not virtual, everything is simple. *)
                    let rec check_in_super (s:tcls_hier) =
                      let c_proto =
                        try
                          let (pos, proto) = List.find
                            (fun (_, p) -> p.tp_name = proto.p_name && (List.map fst p.tp_args) = args_types && p.tp_virtual <> None)
                            s.h_vtable in
                          ty_assert (proto.tp_ret_type = ret_type)
                            "Redefinition of virtual method must be done with same return type.";
                          let new_proto = { tproto with tp_virtual = Some(s, pos) } in
                          s.h_vtable <- (pos, new_proto)::(List.remove_assoc pos s.h_vtable);
                          Some (s, pos)
                        with | Not_found -> None
                      in
                        
                      List.fold_left (fun k s ->
                            match check_in_super s with
                            | None -> k
                            | r -> r)
                          c_proto s.h_supers
                    in
                    match check_in_super hier with
                    | None -> if virt then 
                          (*  allocate new spot in vtable of this object *)
                          let pos = List.fold_left (fun n (x, _) -> max n (x+4)) 0 hier.h_vtable in
                          let proto = { tproto with tp_virtual = Some (hier, pos) } in
                          hier.h_vtable <- (pos, proto)::hier.h_vtable;
                          proto
                        else tproto
                    | some_super -> { tproto with tp_virtual = some_super }
                ) in
                (mem, mem_u), m::meth
        ) ((Smap.empty, used), []) c.c_members in
    (* make sure class has default constructor *)
    let meth = 
      if List.exists (fun p -> p.tp_ret_type = None && p.tp_name = cls_name) meth
        then meth
        else
          { tp_virtual = None;
            tp_name = cls_name;
            tp_unique_ident = cls_name ^ "0";
            tp_class = Some cls_name;
            tp_ret_type = None;
            tp_args = [] }::meth
    in
    (* if vtable is empty, remove it *)
    let mem, mem_u =
      if hier.h_vtable = [] then
        let rec mv_h h =
          h.h_pos <- h.h_pos - 4;
          List.iter mv_h h.h_supers
        in
          List.iter mv_h hier.h_supers;
        Smap.map (fun (ty, pos) -> (ty, pos-4)) mem, mem_u - 4
      else
        mem, mem_u
    in
    {   tc_name = cls_name;
        tc_size = mem_u;
        tc_hier = hier;
        tc_members = mem;
        tc_methods = meth; }

let get_method env proto block =    (* return : TDFunction *)
    match proto.p_class with
    | None -> assert false
    | Some(cls_name) ->
    try let c = get_c env cls_name in
        let args = parse_args env proto.p_args in
        let args_types = List.map fst args in
        let ret_type = match proto.p_ret_type with
            | Some k -> Some (build_type_or_ref k)
            | None -> None in
        (* Find prototype in class *)
        begin try let cproto = List.find 
                (fun p -> (List.map fst p.tp_args) = args_types
                    && p.tp_ret_type = ret_type
                    && p.tp_name = proto.p_name) c.tc_methods
            in
            let locals = List.fold_left
                (fun env (ty, i) -> Smap.add i ty env) Smap.empty args in
            let contexte = {
                b_pe = env;
                b_locals = locals;
                b_class = Some c; } in
            let tb = get_block (match ret_type with | None -> T_Void, false | Some k -> k) contexte block in
                { cproto with tp_args = args }, tb
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
                { env with e_globals = (Smap.add i tr env.e_globals); }
          (* on voudrait une liste de ident pr decl plsr en meme temps *)
          | DFunction (p,b) ->
            begin match p.p_class with
            | None ->
                ty_assert (not (Smap.mem p.p_name env.e_globals)) ("Redeclaration of: " ^ p.p_name ^ ", was previously a global variable");
                let tp, tb, env2 = get_fun env p b in
                TDFunction(tp, tb), env2
            | Some _ ->
                let tp, tb = get_method env p b in
                (TDFunction(tp, tb)), env (* env is not modified *)
            end
          | DClass c ->
            let tc = compute_tclass env c in
            (TDClass tc),
            { env with e_classes = Smap.add c.c_name tc env.e_classes; }
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
  let p = try List.find
        (fun tp -> tp.tp_class = None && tp.tp_name = "main"
                && tp.tp_args = [] && tp.tp_ret_type = Some (T_Int,false))
        env.e_funs
    with Not_found -> ty_error "No correct main function in program." in
  { prog_decls = List.rev decls; prog_env = env; prog_main = p.tp_unique_ident }





