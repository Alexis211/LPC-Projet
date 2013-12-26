open Mips
open Typing

exception Very_bad_error of string

(* Environnement pour accéder aux variables *)
type whereis_var =
  | VGlobal
  | VStack of int (* position relative à $fp *)
  | VStackByRef of int

type cg_env = {
  c_penv : env;
  c_names : whereis_var Smap.t;
  c_ret_ref : bool;
  c_fp_used : int;
}

let globals_env = ref Smap.empty

let strings = Hashtbl.create 12 (* string -> label *)

(* Identifiants uniques pour les machins - essentiellement labels *)
let id =
  let last = ref 0 in
  fun prefix -> (last := !last + 1; prefix ^ (string_of_int !last))


(* Génération de code des machins *)

let cr r a = if a then lw r areg (0, r) else nop (* conditionnally read *)

let use_regs = [ a0; a1; a2; a3; t0; t1; t2; t3 ]
let spare_reg = v0
let spare_reg2 = v1

(* Convention : doit garder $sp invariant ; renvoie le résultat dans le premier registre de free_regs *)
let rec gen_expr env free_regs save_regs e =
  (* register management *)
  let r = List.hd free_regs in (* register where to put result *)
  let more = List.tl free_regs in
  let code_save_regs = List.fold_left
    (fun code r -> push r ++ code) nop save_regs in
  let code_restore_regs = List.fold_left
    (fun code r -> code ++ pop r) nop save_regs in
  (* the generator... *)
  match e.te_desc with
  | TEInt(k) -> li r k, false
  | TENull -> move r zero, false
  | TEThis -> (* convention : this is always the last-pushed argument *)
    lw r areg (8, fp), false
  | TEIdent(i) ->
    begin match Smap.find i env.c_names with
    | VGlobal -> la r alab i, true
    | VStack(i) -> la r areg (i, fp), true
    | VStackByRef(i) -> lw r areg (i, fp), true
    end
  | TEAssign(e1, e2) ->
    let t2, ae2 = gen_expr env free_regs save_regs e2 in
    let t2 = t2 ++ cr r ae2 in
    begin match more with
    | [] ->
      let t1, ae1 = gen_expr env free_regs save_regs e1 in
      assert ae1;
      t1 ++ push r ++ t2 ++ pop spare_reg ++ sw r areg (0, spare_reg), false
    | b::_ ->
      let t1, ae1 = gen_expr env more (r::save_regs) e1 in
      assert ae1;
      t2 ++ t1 ++ sw r areg (0, b), false
    end
  | TECallFun(id, args, b) ->
    let code = List.fold_left
      (fun code (arg, byref) ->
        let c, addr = gen_expr_a0 env arg in
        assert (addr || not byref);
        c ++ cr a0 (addr && not byref) ++ push a0 ++ code) nop args in
    code_save_regs ++ code ++ jal id ++ popn (4 * (List.length args))
      ++ (if r <> a0 then move r a0 else nop) ++ code_restore_regs, b
  | TECallVirtual(obj, fi, args, b) ->
    let code = List.fold_left
      (fun code (arg, byref) ->
        let c, addr = gen_expr_a0 env arg in
        assert (addr || not byref);
        c ++ cr a0 (addr && not byref) ++ push a0 ++ code) nop args in
    let code2, a = gen_expr_a0 env obj in
    assert a;
    code_save_regs
      ++ code ++ code2 ++ push a0 ++ lw a0 areg (0, a0) ++ lw a0 areg (fi, a0)
      ++ jalr a0 ++ popn (4 * (1 + List.length args))
      ++ (if r <> a0 then move r a0 else nop) ++ code_restore_regs, b
  | TEUnary (x, e) ->
    let t, a = gen_expr env free_regs save_regs e in
    begin match x with
    | Ast.Deref -> t ++ cr r a, true
    | Ast.Ref -> assert a; t, false
    | Ast.Plus -> t ++ cr r a, false
    | Ast.Minus -> t ++ cr r a ++ neg r r, false
    | Ast.Not -> t ++ cr r a ++ not_ r r, false
    | Ast.PreIncr -> assert a; t ++ lw spare_reg areg (0, r) ++ add spare_reg spare_reg oi 1 ++ sw spare_reg areg (0, r), true
    | Ast.PreDecr -> assert a; t ++ lw spare_reg areg (0, r) ++ sub spare_reg spare_reg oi 1 ++ sw spare_reg areg (0, r), true
    | Ast.PostIncr -> assert a; t ++ move spare_reg r ++ lw spare_reg2 areg(0, spare_reg) ++ move r spare_reg2 ++
          add spare_reg2 spare_reg2 oi 1 ++ sw spare_reg2 areg(0, spare_reg), false
    | Ast.PostDecr -> assert a; t ++ move spare_reg r ++ lw spare_reg2 areg(0, spare_reg) ++ move r spare_reg2 ++
          sub spare_reg2 spare_reg2 oi 1 ++ sw spare_reg2 areg(0, spare_reg), false
    end
  | TEBinary(e1, op, e2) when op <> Ast.Lor && op <> Ast.Land ->
    let rb, precode = match more with
    | [] ->
      let t1, ae1 = gen_expr env free_regs save_regs e1 in
      let t2, ae2 = gen_expr env free_regs save_regs e2 in
      let t1 = t1 ++ cr r ae1 in
      let t2 = t2 ++ cr r ae2 in
      spare_reg, t2 ++ push r ++ t1 ++ pop spare_reg
    | b::_ ->
      let t1, ae1 = gen_expr env free_regs save_regs e1 in
      let t2, ae2 = gen_expr env more (r::save_regs) e2 in
      let t1 = t1 ++ cr r ae1 in
      let t2 = t2 ++ cr b ae2 in
      b, t1 ++ t2
    in
    precode ++ (match op with
      | Ast.Add -> add r r oreg rb
      | Ast.Sub -> sub r r oreg rb
      | Ast.Mul -> mul r r oreg rb
      | Ast.Div -> div r r oreg rb
      | Ast.Modulo -> rem r r oreg rb
      | Ast.Equal -> seq r r rb
      | Ast.NotEqual -> sne r r rb
      | Ast.Lt -> slt r r rb
      | Ast.Le -> sle r r rb
      | Ast.Gt -> sgt r r rb
      | Ast.Ge -> sge r r rb
      | _ -> assert false
    ), false
  | TEBinary(e1, op, e2) (* when op = Ast.Lor || op = Ast.Land *) ->
    let t1, ae1 = gen_expr env free_regs save_regs e1 in
    let t2, ae2 = gen_expr env free_regs save_regs e2 in
    let t1 = t1 ++ cr r ae1 in
    let t2 = t2 ++ cr r ae2 in
    let lazy_lbl = id "_lazy" in
    t1 ++ (if op = Ast.Lor then bnez r lazy_lbl else beqz r lazy_lbl) ++ t2 ++ label lazy_lbl ++ sne r r zero, false
  | TEMember(e, i) ->
    let c, a = gen_expr env free_regs save_regs e in
    if i <> 0 then begin
      assert a;
      c ++ la r areg (i, r), true
    end else
      c, a
  | TEPointerCast(e, i) ->
    let c, a = gen_expr env free_regs save_regs e in
    c ++ cr r a ++ (if i = 0 then nop else la r areg (i, r)), false
  | TENew(cls, constr, args) ->
    let args_code = List.fold_left
      (fun code (arg, byref) ->
        let c, addr = gen_expr_a0 env arg in
        assert (addr || not byref);
        c ++ cr a0 (addr && not byref) ++ push a0 ++ code) nop args in
    let alloc = li v0 9 ++ li a0 cls.tc_size ++ syscall in
    code_save_regs ++ args_code ++ alloc ++ push v0 ++ jal constr  
      ++ pop r ++ popn (4 * List.length args) ++ code_restore_regs, false

and gen_expr_a0 env = gen_expr env use_regs []
    

let rec gen_stmt env = function
  | TSEmpty -> nop, nop, env
  | TSExpr(e) ->
    comment "expr" ++ (fst (gen_expr_a0 env e)), nop, env
  | TSIf(cond, s1, s2) ->
    let c, a = gen_expr_a0 env cond in
    let l_else = id "_cond_then" in
    let l_end = id "_cond_end" in
    let c_then, d_then, _ = gen_stmt env s1 in
    let c_else, d_else, _ = gen_stmt env s2 in
    comment "if" ++ c ++ cr a0 a ++ beqz a0 l_else ++ c_then ++ b l_end ++
      label l_else ++ c_else ++ label l_end, d_then ++ d_else, env
  | TSWhile(cond, body) ->
    let c, a = gen_expr_a0 env cond in
    let l_begin = id "_while_begin" in
    let l_cond = id "_while_cond" in
    let c_body, d_body, _ = gen_stmt env body in
    comment "while" ++ b l_cond ++ label l_begin ++ c_body ++
      label l_cond ++ c ++ cr a0 a ++ bnez a0 l_begin, d_body, env
  | TSFor(before, cond, after, body) ->
    let l_begin = id "_for_begin" in
    let l_cond = id "_for_cond" in
    let c_before = List.fold_left
      (fun code expr -> let c, _ = gen_expr_a0 env expr in code ++ c) nop before in
    let c_after = List.fold_left
      (fun code expr -> let c, _ = gen_expr_a0 env expr in code ++ c) nop after in
    let c_cond = match cond with
      | None -> b l_begin
      | Some x -> let c, a = gen_expr_a0 env x in
        c ++ cr a0 a ++ bnez a0 l_begin in
    let c_body, d_body, _ = gen_stmt env body in
    comment "for" ++ c_before ++ b l_cond ++ label l_begin ++ c_body ++ c_after ++ label l_cond
      ++ c_cond, d_body, env
  | TSBlock(b) ->
    let c, d = gen_block env b in
    comment "block" ++ c, d, env
  | TSReturn (None) ->
    comment "return" ++ b "_return", nop, env
  | TSReturn (Some e) ->
    let c, a = gen_expr_a0 env e in
    assert (a || not env.c_ret_ref);
    comment "return" ++ c ++ cr a0 (not env.c_ret_ref && a) ++ b "_return", nop, env
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
    comment ("declare " ^ id) ++ code, nop, {
      c_penv = env.c_penv;
      c_names = Smap.add id (VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_fp_used = new_fp_used }
  | TSDeclareAssignConstructor(cls, id, constr, args) ->
    let new_fp_used = env.c_fp_used + cls.tc_size in
    let pos = - new_fp_used in
    let code =
      let args_code = List.fold_left
        (fun code (arg, byref) ->
          let c, addr = gen_expr_a0 env arg in
          assert (addr || not byref);
          c ++ cr a0 (addr && not byref) ++ push a0 ++ code) nop args in
      sub sp sp oi cls.tc_size ++ args_code ++ la a0 areg(pos, fp) ++ push a0 ++ jal constr ++
          popn (4 * (List.length args + 1))
    in
    comment ("declare " ^ id) ++ code, nop, {
      c_penv = env.c_penv;
      c_names = Smap.add id (VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_fp_used = new_fp_used; }
  | TSDeclareAssignExpr ((ty, ref), id, e) ->
    let s = if ref then 4 else type_size env.c_penv ty in
    assert (s = 4);
    let new_fp_used = env.c_fp_used + 4 in
    let pos = - new_fp_used in
    let code, a = gen_expr_a0 env e in
    assert (a || not ref);
    comment ("declare " ^ id) ++ sub sp sp oi 4 ++ code ++ cr a0 (a && not ref) ++ sw a0 areg (pos, fp), nop, {
      c_penv = env.c_penv;
      c_names = Smap.add id (if ref then VStackByRef pos else VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_fp_used = new_fp_used }
  | TSWriteCout(sl) ->
    let text1, data1 = List.fold_left
      (fun (text, data) s ->
        match s with
        | TSEExpr(e) ->
          let t, a = gen_expr_a0 env e in
          text ++ t ++ cr a0 a ++  li v0 1 ++ syscall, data
        | TSEStr(s) ->
          let l, d =
            if Hashtbl.mem strings s then
              Hashtbl.find strings s, nop
            else
              let l = id "_s" in Hashtbl.add strings s l;
              l, label l ++ asciiz s
          in
            text ++ la a0 alab l ++ li v0 4 ++ syscall, data ++ d) (nop, nop) sl in
    comment "cout<<..." ++ text1, data1, env
and gen_block env b =
  let text, data, fin_env =
    List.fold_left (fun (t, d, e) s ->
        let tt, dd, e = gen_stmt e s in
          t ++ tt, d ++ dd, e)
      (nop, nop, env) b
  in
    let n = (fin_env.c_fp_used - env.c_fp_used) in
    text ++ (if n = 0 then nop else popn n), data

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
    let text, data = gen_block env block in 
    label proto.tp_unique_ident ++
    push fp ++ push ra ++ move fp sp ++ code_for_constructor ++ code_for_virtual ++
    text ++ b "_return", data
  | TDClass(c) ->
    let calls_something = ref false in
    (* Call default constructor of parent classes *)
    let code_parents = List.fold_left
      (fun code parent ->
          let cn = parent.h_class in
          let c = get_c tenv cn in
          let proto = List.find (fun p -> p.tp_ret_type = None && p.tp_args = [] && p.tp_name = cn) c.tc_methods in
          calls_something := true;
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
          then nop
          else la a0 alab ("_vt_" ^ c.tc_name ^ "_as_" ^ hh.h_class)
            ++ sw a0 areg (hh.h_pos, v0) in
      (* code for subclasses vtable initialization *)
      List.fold_left
          (fun (vt, cc) sup ->
            let mvt, mcc = make_vtables sup in
            vt ++ mvt, cc ++ mcc)
          (vtable, constructor_code) hh.h_supers
    in
    let vtables, vtable_init_code = make_vtables c.tc_hier in
    (* Initialize members *)
    let init_code_proper = Smap.fold
      (fun _ (ty, pos) code ->
        (match ty with
          | TClass(s) ->
            let cs = get_c tenv s in
            let proto = List.find (fun p -> p.tp_ret_type = None && p.tp_args = [] && p.tp_name = s) cs.tc_methods in
            calls_something := true;
            push v0 ++
              la a0 areg (pos, v0) ++ push a0 ++
               jal proto.tp_unique_ident ++ popn 4 ++ pop v0
          | _ -> sw zero areg (pos, v0)
        ) ++ code) c.tc_members nop 
    in (* Put it all together *)
      label (c.tc_name ^ "0") ++ lw v0 areg (0, sp) ++ label ("_c_" ^ c.tc_name) 
          ++ (if !calls_something then push ra else nop)
          ++ code_parents ++ vtable_init_code ++ init_code_proper
          ++ (if !calls_something then pop ra else nop) ++ jr ra, vtables


let generate p =
  try 
    let text, data = List.fold_left (fun (text, data) decl ->
        let more_text, more_data = gen_decl p.prog_env decl in
        text ++ more_text, data ++ more_data) (nop, nop) p.prog_decls in
    let text =
      label "main" ++ jal p.prog_main ++
      li v0 10 ++ syscall ++
      label "_return" ++ move sp fp ++ pop ra ++ pop fp ++
      label "_nothing" ++ jr ra ++
      text in
    { text = text;
      data = data }
  with
  | Assert_failure (k, a, b) -> raise (Very_bad_error (
        "(unexpected) Assertion failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
  | Not_found -> raise (Very_bad_error ("(unexpected) Not found"))
  | Invalid_argument(k) -> raise (Very_bad_error ("(unexpected) Invalid argument: "^k))
  | Match_failure(k, a, b) -> raise (Very_bad_error (
      "(unexpected) Match failure: "^k^" at "^(string_of_int a)^":"^(string_of_int b)))
  | Stack_overflow -> raise (Very_bad_error ("(unexpected) Stack overflow"))
  | _ -> raise (Very_bad_error ("(unexpected) Other error"))
