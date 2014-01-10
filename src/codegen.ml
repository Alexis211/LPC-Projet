open Mips
open Typing

exception Very_bad_error of string

(* Environnement pour accéder aux variables *)
type whereis_var =
  | VGlobal
  | VStack of int (* position relative à $fp *)
  | VStackByRef of int

type cg_env = {
  c_penv : env;     (* environnement du programme (Typing.env) : contient les informations de types *)
  c_names : whereis_var Smap.t;
  c_ret_ref : bool; (* le résultat est-il renvoyé par référence ? *)
  c_fp_used : int;  (* nombre d'octets sous $fp utilisés par la fonction *)
}

let globals_env = ref Smap.empty        (* variables globales *)

let strings = Hashtbl.create 12 (* string -> label *)

(* Identifiants uniques pour les machins - essentiellement labels *)
let id =
  let last = ref 0 in
  fun prefix -> (last := !last + 1; prefix ^ (string_of_int !last))


(* La génération de code à proprement parler !

    La valeur d'une expression est générée dans le registre a0, la pile est utilisée
    pour les calculs intermédiaires.

    Le plus possible, le générateur de code enregistre dans a0 non pas la valeur
    de l'expression mais l'adresse où cette valeur est stockée en mémoire. Évidemment,
    une telle adresse n'existe que pour les expressions qui sont typées comme des
    références ou des lvalues (c'est essentiellement la même chose).
    
    La fonction cr effectue donc, dans le cas où on a l'addresse et non pas la valeur,
    la lecture mémoire requise pour accéder à la valeur en question.
 *)

let cr a = if a then lw a0 areg (0, a0) else nop (* conditionnally read *)

(* Convention : doit garder $sp invariant *)
let rec gen_expr env e = match e.te_desc with
  | TEInt(k) -> li a0 k, false
  | TENull -> move a0 zero, false
  | TEThis -> (* convention : this est toujours le premier argument de la fonction, c'est-à-dire
                    celui qui est pushé en dernier. on connait donc toujours son adresse *)
    lw a0 areg (8, fp), false
  | TEIdent(i) ->
    begin match Smap.find i env.c_names with
    | VGlobal -> la a0 alab i, true
    | VStack(i) -> la a0 areg (i, fp), true
    | VStackByRef(i) -> lw a0 areg (i, fp), true
    end
  | TEAssign(e1, e2) ->
    let t1, ae1 = gen_expr env e1 in
    assert ae1;
    let t2, ae2 = gen_expr env e2 in
    t1 ++ push a0 ++ t2 ++ cr ae2 ++ pop a1 ++ sw a0 areg (0, a1), false
  | TECallFun(id, args, b) ->
    let code = List.fold_left
      (fun code (arg, byref) ->
        let c, r = gen_expr env arg in
        assert (r || not byref);
        c ++ cr (r && not byref) ++ push a0 ++ code) nop args in
    code ++ jal id ++ popn (4 * (List.length args)), b
  | TECallVirtual(obj, fi, args, b) ->
    let code = List.fold_left
      (fun code (arg, byref) ->
        let c, r = gen_expr env arg in
        assert (r || not byref);
        c ++ cr (r && not byref) ++ push a0 ++ code) nop args in
    let code2, a = gen_expr env obj in
    assert a;
    code ++ code2 ++ push a0 ++ lw a0 areg (0, a0) ++ lw a0 areg (fi, a0)
      ++ jalr a0 ++ popn (4 * (1 + List.length args)), b
  | TEUnary (x, e) ->
    let t, a = gen_expr env e in
    begin match x with
    | Ast.Deref -> t ++ cr a, true
    | Ast.Ref -> assert a; t, false
    | Ast.Plus -> t ++ cr a, false
    | Ast.Minus -> t ++ cr a ++ neg a0 a0, false
    | Ast.Not -> t ++ cr a ++ not_ a0 a0, false
    | Ast.PreIncr -> assert a;
        t ++ lw a1 areg (0, a0) ++ add a1 a1 oi 1 ++ sw a1 areg (0, a0), true
    | Ast.PreDecr -> assert a;
        t ++ lw a1 areg (0, a0) ++ sub a1 a1 oi 1 ++ sw a1 areg (0, a0), true
    | Ast.PostIncr -> assert a;
        t ++ move a1 a0 ++ lw a2 areg(0, a1) ++ move a0 a2
          ++ add a2 a2 oi 1 ++ sw a2 areg(0, a1), false
    | Ast.PostDecr -> assert a;
        t ++ move a1 a0 ++ lw a2 areg(0, a1) ++ move a0 a2
          ++ sub a2 a2 oi 1 ++ sw a2 areg(0, a1), false
    end
  | TEBinary(e1, op, e2) ->
    let t1, ae1 = gen_expr env e1 in
    let t2, ae2 = gen_expr env e2 in
    let t1 = t1 ++ cr ae1 in
    let t2 = t2 ++ cr ae2 in
    (
      match op with
      | Ast.Add -> t1 ++ push a0 ++ t2 ++ pop a1 ++ add a0 a1 oreg a0
      | Ast.Sub -> t1 ++ push a0 ++ t2 ++ pop a1 ++ sub a0 a1 oreg a0
      | Ast.Mul -> t1 ++ push a0 ++ t2 ++ pop a1 ++ mul a0 a1 oreg a0
      | Ast.Div -> t1 ++ push a0 ++ t2 ++ pop a1 ++ div a0 a1 oreg a0
      | Ast.Modulo -> t1 ++ push a0 ++ t2 ++ pop a1 ++ rem a0 a1 oreg a0
      | Ast.Equal -> t1 ++ push a0 ++ t2 ++ pop a1 ++ seq a0 a1 a0
      | Ast.NotEqual -> t1 ++ push a0 ++ t2 ++ pop a1 ++ sne a0 a1 a0
      | Ast.Lt -> t1 ++ push a0 ++ t2 ++ pop a1 ++ slt a0 a1 a0
      | Ast.Le -> t1 ++ push a0 ++ t2 ++ pop a1 ++ sle a0 a1 a0
      | Ast.Gt -> t1 ++ push a0 ++ t2 ++ pop a1 ++ sgt a0 a1 a0
      | Ast.Ge -> t1 ++ push a0 ++ t2 ++ pop a1 ++ sge a0 a1 a0
      | Ast.Land -> 
        let lazy_lbl = id "_lazy" in
        t1 ++ beqz a0 lazy_lbl ++ t2 ++ label lazy_lbl ++ sne a0 a0 zero
      | Ast.Lor -> 
        let lazy_lbl = id "_lazy" in
        t1 ++ bnez a0 lazy_lbl ++ t2 ++ label lazy_lbl ++ sne a0 a0 zero
    ), false
  | TEMember(e, i) ->
    let c, a = gen_expr env e in
    if i <> 0 then begin
      assert a;
      c ++ la a0 areg (i, a0), true
    end else
      c, a
  | TEPointerCast(e, i) ->
    let c, a = gen_expr env e in
    c ++ cr a ++ (if i = 0 then nop else la a0 areg (i, a0)), false
  | TENew(cls, constr, args) ->
    let args_code = List.fold_left
      (fun code (arg, byref) ->
        let c, r = gen_expr env arg in
        assert (r || not byref);
        c ++ cr (r && not byref) ++ push a0 ++ code) nop args in
    let alloc = li v0 9 ++ li a0 cls.tc_size ++ syscall in
    args_code ++ alloc ++ push v0 ++ jal constr  
      ++ pop a0 ++ popn (4 * List.length args), false
    

let rec gen_stmt env = function
  | TSEmpty -> nop, env
  | TSExpr(e) ->
    comment "expr" ++ (fst (gen_expr env e)), env
  | TSIf(cond, s1, s2) ->
    let c, a = gen_expr env cond in
    let l_else = id "_cond_then" in
    let l_end = id "_cond_end" in
    let c_then, _ = gen_stmt env s1 in
    let c_else, _ = gen_stmt env s2 in
    comment "if" ++ c ++ cr a ++ beqz a0 l_else ++ c_then ++ b l_end ++
      label l_else ++ c_else ++ label l_end, env
  | TSWhile(cond, body) ->
    let c, a = gen_expr env cond in
    let l_begin = id "_while_begin" in
    let l_cond = id "_while_cond" in
    let c_body, _ = gen_stmt env body in
    comment "while" ++ b l_cond ++ label l_begin ++ c_body ++
      label l_cond ++ c ++ cr a ++ bnez a0 l_begin, env
  | TSFor(before, cond, after, body) ->
    let l_begin = id "_for_begin" in
    let l_cond = id "_for_cond" in
    let c_before = List.fold_left
      (fun code expr -> let c, _ = gen_expr env expr in code ++ c) nop before in
    let c_after = List.fold_left
      (fun code expr -> let c, _ = gen_expr env expr in code ++ c) nop after in
    let c_cond = match cond with
      | None -> b l_begin
      | Some x -> let c, a = gen_expr env x in
        c ++ cr a ++ bnez a0 l_begin in
    let c_body, _ = gen_stmt env body in
    comment "for" ++ c_before ++ b l_cond ++ label l_begin ++ c_body ++ c_after ++ label l_cond
      ++ c_cond, env
  | TSBlock(b) ->
    let c = gen_block env b in
    comment "block" ++ c, env
  | TSReturn (None) ->
    comment "return" ++ b "_return", env
  | TSReturn (Some e) ->
    let c, a = gen_expr env e in
    assert (a || not env.c_ret_ref);
    comment "return" ++ c ++ cr (not env.c_ret_ref && a) ++ b "_return", env
  | TSDeclare (ty, id) ->
    let s = type_size env.c_penv ty in
    let new_fp_used = env.c_fp_used + s in
    let pos = - new_fp_used in
    let code = match ty with
    | TClass(i) ->
      let c = get_c env.c_penv i in
      let cproto = List.find (fun p -> p.tp_ret_type = None && p.tp_name =  i && p.tp_args = []) c.tc_methods in
      sub sp sp oi s ++
      la a0 areg (pos, fp) ++
      push a0 ++
      jal cproto.tp_unique_ident
    | _ -> push zero
    in
    comment ("declare " ^ id) ++ code,
    { env with
      c_names = Smap.add id (VStack pos) env.c_names;
      c_fp_used = new_fp_used }
  | TSDeclareAssignConstructor(cls, id, constr, args) ->
    let new_fp_used = env.c_fp_used + cls.tc_size in
    let pos = - new_fp_used in
    let code =
      let args_code = List.fold_left
        (fun code (arg, byref) ->
          let c, r = gen_expr env arg in
          assert (r || not byref);
          c ++ cr (r && not byref) ++ push a0 ++ code) nop args in
      sub sp sp oi cls.tc_size ++ args_code ++ la a0 areg(pos, fp) ++ push a0 ++ jal constr ++
          popn (4 * (List.length args + 1))
    in
    comment ("declare " ^ id) ++ code,
    { env with
      c_names = Smap.add id (VStack pos) env.c_names;
      c_fp_used = new_fp_used; }
  | TSDeclareAssignExpr ((ty, r), id, e) ->
    let s = if r then 4 else type_size env.c_penv ty in
    assert (s = 4);
    let new_fp_used = env.c_fp_used + 4 in
    let pos = - new_fp_used in
    let code, a = gen_expr env e in
    assert (a || not r);
    comment ("declare " ^ id) ++ sub sp sp oi 4 ++ code ++ cr (a && not r) ++ sw a0 areg (pos, fp),
    { env with
      c_names = Smap.add id (if r then VStackByRef pos else VStack pos) env.c_names;
      c_fp_used = new_fp_used }
  | TSWriteCout(sl) ->
    let text1 = List.fold_left
      (fun text s ->
        match s with
        | TSEExpr(e) ->
          let t, a = gen_expr env e in
          text ++ t ++ cr a ++  li v0 1 ++ syscall
        | TSEStr(s) ->
          let l =
            if Hashtbl.mem strings s then
              Hashtbl.find strings s
            else
              let l = id "_s" in
              Hashtbl.add strings s l; l
          in
            text ++ la a0 alab l ++ li v0 4 ++ syscall) (nop) sl in
    comment "cout<<..." ++ text1, env
and gen_block env b =
  let text, fin_env =
    List.fold_left (fun (t, e) s ->
        let tt, e = gen_stmt e s in
          t ++ tt, e)
      (nop, env) b
  in
    let n = (fin_env.c_fp_used - env.c_fp_used) in
    text ++ (if n = 0 then nop else popn n)

let gen_decl tenv decl = match decl with
  | TDGlobal(ty, id) ->
    globals_env := Smap.add id VGlobal !globals_env;
    let bytes = type_size tenv ty in
    nop, (label id) ++ (dword (let rec a n = if n > 0 then 0::(a (n-4)) else [] in a bytes))
  | TDFunction(proto, block) ->
    let names, _ = List.fold_left 
            (fun (env, p) ((ty, r), id) -> 
              Smap.add id (if r then VStackByRef p else VStack p) env, p + (type_size tenv ty)) 
            (!globals_env, (match proto.tp_class with | None -> 8 | Some k -> 12)) proto.tp_args in
    let env = {
        c_penv = tenv;
        c_names = names;
        c_ret_ref = (match proto.tp_ret_type with | None -> false | Some(_, r) -> r);
        c_fp_used = 0;
      } in
    let code_for_constructor = match proto.tp_ret_type with
      | Some _ -> nop
      | None -> let cls_name = (match proto.tp_class with | Some k -> k | None -> assert false) in
        lw v0 areg (8, fp) ++ jal ("_c_" ^ cls_name) in
    let code_for_virtual = match proto.tp_virtual with
      | Some (c, _) when c.h_pos <> 0 ->
        lw a0 areg (8, fp) ++ la a0 areg (-c.h_pos, a0) ++ sw a0 areg (8, fp)
      | _ -> nop
    in
    let text = gen_block env block in 
    label proto.tp_unique_ident ++
    push fp ++ push ra ++ move fp sp ++ code_for_constructor ++ code_for_virtual ++
    text ++ b "_return", nop
  | TDClass(c) ->
    (* Call default constructor of parent classes *)
    let code_parents = List.fold_left
      (fun code parent ->
          let cn = parent.h_class in
          let c = get_c tenv cn in
          let proto = List.find (fun p -> p.tp_ret_type = None && p.tp_args = [] && p.tp_name = cn) c.tc_methods in
          code ++ lw v0 areg(0, sp) ++ la v0 areg(parent.h_pos, v0) ++push v0 ++ jal proto.tp_unique_ident ++ popn 4)
      nop c.tc_hier.h_supers in
    let code_parents = if code_parents <> nop then push v0 ++ code_parents ++ pop v0 else nop in
    (* Build vtables and build constructor *)
    let rec make_vtables hh =
      (* calculate vtable contents *)
      let vtable_size = List.fold_left (fun k (p, _) -> max k (p+4)) 0 hh.h_vtable in
      let vtable_as_array = Array.make (vtable_size / 4) "_nothing" in
      List.iter (fun (p, s) -> vtable_as_array.(p/4) <- s.tp_unique_ident) hh.h_vtable;
      let vt_l = Array.to_list vtable_as_array in
      (* code for vtable initialization *)
      let vtable =
        if vt_l = [] 
          then nop 
          else label ("_vt_" ^ c.tc_name ^ "_as_" ^ hh.h_class) ++ address vt_l in
      let constructor_code = 
        if vt_l = []
          then sw zero areg (hh.h_pos, v0)
          else la a0 alab ("_vt_" ^ c.tc_name ^ "_as_" ^ hh.h_class)
            ++ sw a0 areg (hh.h_pos, v0) in
      (* code for subclasses initialization *)
      List.fold_left
          (fun (vt, cc) sup ->
            let mvt, mcc = make_vtables sup in
            vt ++ mvt, cc ++ mcc)
          (vtable, constructor_code) hh.h_supers
    in
    let vtables, vtable_init_code = make_vtables c.tc_hier in
    let init_code_proper = Smap.fold
      (fun _ (ty, pos) code ->
        (match ty with
          | TClass(s) ->
            let cs = get_c tenv s in
            let proto = List.find (fun p -> p.tp_ret_type = None && p.tp_args = [] && p.tp_name = s) cs.tc_methods in
            push v0 ++
              la a0 areg (pos, v0) ++ push a0 ++
               jal proto.tp_unique_ident ++ popn 4 ++ pop v0
          | _ -> sw zero areg (pos, v0)
        ) ++ code) c.tc_members nop 
    in
      label (c.tc_name ^ "0") ++ lw v0 areg (0, sp) ++ label ("_c_" ^ c.tc_name) 
          ++ push ra ++ code_parents ++ vtable_init_code ++ init_code_proper ++ pop ra ++ jr ra, vtables


let generate p =
  try 
    let text, data = List.fold_left (fun (text, data) decl ->
        let more_text, more_data = gen_decl p.prog_env decl in
        text ++ more_text, data ++ more_data) (nop, nop) p.prog_decls in
    let text =
      label "main"
        ++ jal p.prog_main
        ++ li v0 10 ++ syscall
        ++ label "_return" ++ move sp fp ++ pop ra ++ pop fp
        ++ label "_nothing" ++ jr ra
        ++ text in
    let str = Hashtbl.fold
      (fun str lbl data -> data ++ label lbl ++ asciiz str)
      strings nop in
    { text = text;
      data = data ++ str }
  with
  | Assert_failure (k, a, b) -> raise (Very_bad_error (
        "(unexpected) Assertion failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
  | Not_found -> raise (Very_bad_error ("(unexpected) Not found"))
  | Invalid_argument(k) -> raise (Very_bad_error ("(unexpected) Invalid argument: "^k))
  | Match_failure(k, a, b) -> raise (Very_bad_error (
      "(unexpected) Match failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
  | Stack_overflow -> raise (Very_bad_error ("(unexpected) Stack overflow"))
  | _ -> raise (Very_bad_error ("(unexpected) Other error"))
