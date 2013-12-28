open Mips
open Typing

exception Very_bad_error of string

(* Convention pour les registres :
  - a0, a1, a2, a3 : contiennent les (éventuels) 4 premiers arguments de la fonction
  - v0 : contient la valeur de retour des fonctions (rien de particulier pour un constructeur)
  - v0-v1, t0-t9, s0-s1 : utilisés pour les calculs
  Tous les registres doivent être sauvés par l'appellant
  Les registres a0, a1, a2, a3 sont susceptibles d'être modifiés par la fonction appellée.
    **sauf dans le cas où a0 représente this** !!
*)

(* Environnement pour accéder aux variables *)
type whereis_var =
  | VGlobal
  | VStack of int (* position relative à $fp *)
  | VStackByRef of int
  | VRegister of register
  | VRegisterByRef of register

type cg_env = {
  c_penv : env;
  c_names : whereis_var Smap.t;
  c_ret_ref : bool;
  c_ret_lbl : string;
  c_fp_used : int;
  c_save_regs : register list;
}

let env_push n e =
  let kk = e.c_fp_used + n in
  { c_penv = e.c_penv;
    c_names = e.c_names;
    c_ret_ref = e.c_ret_ref;
    c_ret_lbl = e.c_ret_lbl;
    c_fp_used = kk;
    c_save_regs = e.c_save_regs }, -kk

let globals_env = ref Smap.empty

let strings = Hashtbl.create 12 (* string -> label *)

(* Identifiants uniques pour les machins - essentiellement labels *)
let id =
  let last = ref 0 in
  fun prefix -> (last := !last + 1; prefix ^ (string_of_int !last))


let rec expr_does_call e = match e.te_desc with
  | TEInt _ | TENull | TEThis | TEIdent _ -> false
  | TEAssign(a, b) -> expr_does_call a || expr_does_call b
  | TECallFun (_, _, _) -> true
  | TECallVirtual (_, _, _, _) -> true
  | TEUnary (_, e) -> expr_does_call e
  | TEBinary (a, _, b) -> expr_does_call a || expr_does_call b
  | TEMember (e, _) -> expr_does_call e
  | TEPointerCast(e, _) -> expr_does_call e
  | TENew(_, _, _) -> true
let rec stmt_does_call = function
  | TSEmpty | TSReturn(None) -> false
  | TSExpr(e) -> expr_does_call e
  | TSIf (e, sa, sb) -> expr_does_call e || stmt_does_call sa || stmt_does_call sb
  | TSWhile(e, s) -> expr_does_call e || stmt_does_call s
  | TSFor(e, f, g, s) -> (List.exists expr_does_call e) || (match f with | None -> false | Some k -> expr_does_call k)
          || (List.exists expr_does_call g) || stmt_does_call s
  | TSBlock(k) -> List.exists stmt_does_call k
  | TSReturn(Some k) -> expr_does_call k
  | TSDeclare(TClass _, _) -> true
  | TSDeclare (_, _) -> false
  | TSDeclareAssignExpr(_, _, e) -> expr_does_call e
  | TSDeclareAssignConstructor(_, _, _, _) -> true
  | TSWriteCout(l) -> List.exists (function | TSEExpr e -> expr_does_call e | TSEStr _ -> false) l


(* Génération de code des machins *)

type expr_type =
  | Addr  (* top register contains address of value *)
  | AddrByReg of int * register (* value at int(register) *)
  | Copy  (* top register contains copy of value *)
  | Value of register (* other register is home to the value *)

let cla r a = match a with
  | Addr -> nop
  | AddrByReg(x, rg) -> la r areg (x, rg)
  | _ -> assert false
let cr r a = match a with     (* conditionnally read *)
  | Addr -> lw r areg (0, r)
  | AddrByReg(x, rg) -> lw r areg (x, rg)
  | Copy -> nop
  | Value(k) -> if r <> k then move r k else nop
let crb r q a = match a with
  | Value k when q = nop -> nop, k
  | _ -> q ++ cr r a, r

let use_regs = [ v0; v1; t0; t1; t2; t3; t4; t5; t6; t7; t8; t9 ]
let spare_reg = s0
let spare_reg2 = s1

let saver env save_regs =
  let sc, lc, env2 = List.fold_left
    (fun (code, more_code, env) r ->
      let new_fp_used = env.c_fp_used + 4 in
      let pos = - new_fp_used in
      code ++ sw r areg (pos, fp), lw r areg (pos, fp) ++ more_code,
      { c_penv = env.c_penv;
        c_names = Smap.map
          (function
            | VRegister k when k = r -> VStack (pos)
            | VRegisterByRef k when k = r -> VStackByRef(pos)
            | a -> a) env.c_names;
        c_ret_ref = env.c_ret_ref;
        c_ret_lbl = env.c_ret_lbl;
        c_fp_used = new_fp_used;
        c_save_regs = (List.filter (fun k -> k <> r) env.c_save_regs) }
    )
    (nop, nop, env) save_regs
  in 
    sc, lc, env2

(* Convention :
    doit garder $sp invariant ; renvoie le résultat dans le premier registre de free_regs
    on doit toujours avoir lors d'un appel à cette fonction, $fp - env.c_fp_used = $sp
*)
let rec gen_expr env free_regs save_regs e =
  (* register management *)
  let r = List.hd free_regs in (* register where to put result *)
  let more = List.tl free_regs in
  (* the generator... *)
  match e.te_desc with
  | TEInt(k) -> li r k, Copy
  | TENull -> move r zero, Copy
  | TEThis -> (* convention : this is always the first argument, so in a0 *)
    begin match Smap.find "this" env.c_names with
    | VRegister(k) when k <> r -> nop, Value k
    | VStack(i) -> lw r areg (i, fp), Copy
    | _ -> assert false
    end
  | TEIdent(i) ->
    begin match Smap.find i env.c_names with
    | VGlobal -> la r alab i, Addr
    | VStack(i) -> nop, AddrByReg(i, fp)
    | VStackByRef(i) -> lw r areg (i, fp), Addr
    | VRegister(k) -> nop, Value k
    | VRegisterByRef(k) when k <> r -> move r k, Addr
    | _ -> assert false
    end
  | TEAssign(e1, e2) ->
    begin match more with
    | [] ->
      let t1, ae1 = gen_expr env free_regs save_regs e1 in
      let env2, tspot = env_push 4 env in
      let t2, ae2 = gen_expr env2 free_regs save_regs e2 in
      let t2 = t2 ++ cr r ae2 in
      begin match ae1 with
      | Addr -> t1 ++ sw r areg (tspot, fp) ++ t2 ++ lw spare_reg areg (tspot, fp) ++ sw r areg (0, spare_reg), Copy
      | AddrByReg (x, rg) when t1 = nop -> t2 ++ sw r areg (x, rg), Copy
      | Value k when t1 = nop && k <> r -> t2 ++ move k r, Copy
      | _ -> assert false
      end
    | b::_ ->
      let t1, ae1 = gen_expr env more (r::save_regs) e1 in
      let t2, ae2 = gen_expr env free_regs save_regs e2 in
      let t2 = t2 ++ cr r ae2 in
      begin match ae1 with
      | Addr -> t2 ++ t1 ++ sw r areg (0, b), Copy
      | AddrByReg (x, rg) when t1 = nop -> t2 ++ sw r areg (x, rg), Copy
      | Value k when t1 = nop && k <> r -> t2 ++ move k r, Copy
      | _ -> assert false
      end
    end
  | TECallFun(id, args, b) ->
    let code_save_regs, code_restore_regs, env_regs_saved = saver env save_regs in
    let args_code, _, env_args = code_for_args env_regs_saved args [ a0; a1; a2; a3 ] in
    code_save_regs ++ args_code ++ la sp areg (-env_args.c_fp_used, fp) ++ jal id
      ++ (if r <> v0 then move r v0 else nop) ++ code_restore_regs,
    if b then Addr else Copy
  | TECallVirtual(obj, fi, args, b) ->
    let code_save_regs, code_restore_regs, env_regs_saved = saver env save_regs in
    let args_code, sr, env_args = code_for_args env_regs_saved args [ a1; a2; a3 ] in
    let code2, a = gen_expr env_args (a0::use_regs) sr obj in
    code_save_regs
      ++ args_code ++ code2 ++ cla a0 a ++ lw v0 areg (0, a0) ++ lw v0 areg (fi, v0)
      ++ la sp areg (-env_args.c_fp_used, fp) ++ jalr v0
      ++ (if r <> v0 then move r v0 else nop) ++ code_restore_regs, if b then Addr else Copy
  | TEUnary (x, e) ->
    let t, a = gen_expr env free_regs save_regs e in
    begin match x with
    | Ast.Deref -> 
      begin match a with
      | Value r when t = nop -> nop, AddrByReg (0, r)
      | _ -> t ++ cr r a, Addr
      end
    | Ast.Ref -> t ++ cla r a, Copy
    | Ast.Plus -> t ++ cr r a, Copy
    | Ast.Minus -> t ++ cr r a ++ neg r r, Copy
    | Ast.Not -> t ++ cr r a ++ not_ r r, Copy
    | Ast.PreIncr -> 
      begin match a with
      | Addr -> t ++ lw spare_reg areg (0, r) ++ add spare_reg spare_reg oi 1 ++ sw spare_reg areg (0, r), Addr
      | AddrByReg (k, rg) when t = nop -> lw r areg (k, rg) ++ add r r oi 1 ++ sw r areg (k, rg), Copy
      | Value v when t = nop && v <> r -> add v v oi 1 ++ move r v, Copy
      | _ -> assert false
      end
    | Ast.PreDecr ->
      begin match a with
      | Addr -> t ++ lw spare_reg areg (0, r) ++ sub spare_reg spare_reg oi 1 ++ sw spare_reg areg (0, r), Addr
      | AddrByReg (k, rg) when t = nop -> lw r areg (k, rg) ++ sub r r oi 1 ++ sw r areg (k, rg), Copy
      | Value v when t = nop && v <> r -> sub v v oi 1 ++ move r v, Copy
      | _ -> assert false
      end
    | Ast.PostIncr -> 
      begin match a with
      | Addr -> t ++ move spare_reg r ++ lw spare_reg2 areg(0, spare_reg) ++ move r spare_reg2 ++
          add spare_reg2 spare_reg2 oi 1 ++ sw spare_reg2 areg(0, spare_reg), Copy
      | AddrByReg (k, rg) when t = nop ->
          lw r areg (k, rg) ++ add spare_reg r oi 1 ++ sw spare_reg areg (k, rg), Copy
      | Value v when t = nop && v <> r -> move r v ++ add v v oi 1, Copy
      | _ -> assert false
      end
    | Ast.PostDecr ->
      begin match a with
      | Addr -> t ++ move spare_reg r ++ lw spare_reg2 areg(0, spare_reg) ++ move r spare_reg2 ++
          sub spare_reg2 spare_reg2 oi 1 ++ sw spare_reg2 areg(0, spare_reg), Copy
      | AddrByReg (k, rg) when t = nop ->
          lw r areg (k, rg) ++ sub spare_reg r oi 1 ++ sw spare_reg areg (k, rg), Copy
      | Value v when t = nop && v <> r -> move r v ++ sub v v oi 1, Copy
      | _ -> assert false
      end
    end
  | TEBinary(e1, op, e2) when op <> Ast.Lor && op <> Ast.Land ->
    let rs, rb, precode = match more with
    | [] ->
      let env2, tspot = env_push 4 env in
      let t1, ae1 = gen_expr env2 free_regs save_regs e1 in
      let t2, ae2 = gen_expr env free_regs save_regs e2 in
      let t1 = t1 ++ cr r ae1 in
      let t2 = t2 ++ cr r ae2 in
      r, spare_reg, t2 ++ sw r areg (tspot, fp) ++ t1 ++ lw spare_reg areg (tspot, fp)
    | b::_ ->
      let t1, ae1 = gen_expr env free_regs save_regs e1 in
      let t2, ae2 = gen_expr env more (r::save_regs) e2 in
      let t1, rs = crb r t1 ae1 in
      let t2, rb = crb b t2 ae2 in
      rs, rb, t1 ++ t2
    in
    precode ++ (match op with
      | Ast.Add -> add r rs oreg rb
      | Ast.Sub -> sub r rs oreg rb
      | Ast.Mul -> mul r rs oreg rb
      | Ast.Div -> div r rs oreg rb
      | Ast.Modulo -> rem r rs oreg rb
      | Ast.Equal -> seq r rs rb
      | Ast.NotEqual -> sne r rs rb
      | Ast.Lt -> slt r rs rb
      | Ast.Le -> sle r rs rb
      | Ast.Gt -> sgt r rs rb
      | Ast.Ge -> sge r rs rb
      | _ -> assert false
    ), Copy
  | TEBinary(e1, op, e2) (* when op = Ast.Lor || op = Ast.Land *) ->
    let t1, ae1 = gen_expr env free_regs save_regs e1 in
    let t2, ae2 = gen_expr env free_regs save_regs e2 in
    let t1 = t1 ++ cr r ae1 in
    let t2 = t2 ++ cr r ae2 in
    let lazy_lbl = id "_lazy" in
    t1 ++ (if op = Ast.Lor then bnez r lazy_lbl else beqz r lazy_lbl) ++ t2 ++ label lazy_lbl ++ sne r r zero, Copy
  | TEMember(e, i) ->
    let c, a = gen_expr env free_regs save_regs e in
    if i <> 0 then begin
      match a with
      | Addr -> c ++ la r areg (i, r), Addr
      | AddrByReg (k, rg) when c = nop -> nop, AddrByReg (k + i, rg)
      | _ -> assert false
    end else
      c, a
  | TEPointerCast(e, i) ->
    let c, a = gen_expr env free_regs save_regs e in
    c ++ cr r a ++ (if i = 0 then nop else la r areg (i, r)), Copy
  | TENew(cls, constr, args) ->
    let code_save_regs, code_restore_regs, env_regs_saved = saver env save_regs in
    let args_code, _, env_args = code_for_args env_regs_saved args [ a1; a2; a3 ] in
    code_save_regs ++ args_code
      ++ li v0 9 ++ li a0 cls.tc_size ++ syscall ++ move a0 v0
      ++ la sp areg (-env_args.c_fp_used, fp) ++ jal constr ++ (if r <> a0 then move r a0 else nop)
      ++ code_restore_regs, Copy
and code_for_args env arg_list regs =
  let stack_use = max 0 (4 * (List.length arg_list - List.length regs)) in
  let kenv, _ = env_push stack_use env in
  let code, _, sr, u = List.fold_left
    (fun (code, r, sr, u) (arg, byref) ->
      match r with
      | [] ->
        let c, addr = gen_expr kenv use_regs [] arg in
        if byref then (
          c ++ cla v0 addr ++ sw v0 areg (-kenv.c_fp_used + u, fp) ++ code, r, sr, u+4
        ) else (
          let c, freg = crb v0 c addr in
          c ++ sw freg areg (-kenv.c_fp_used + u, fp) ++ code, r, sr, u+4
        )
      | reg::more_regs ->
        let c, addr = gen_expr kenv (reg::use_regs) sr arg in
        code ++ c ++ (if not byref then cr reg addr else cla reg addr), more_regs, reg::sr, u
    ) (nop, regs, [], 0) arg_list
  in code, sr, kenv
  

let gen_expr_v0 env = gen_expr env use_regs env.c_save_regs
    

let rec gen_stmt env = function
  | TSEmpty -> nop, nop, env
  | TSExpr(e) ->
    comment "expr" ++ (fst (gen_expr_v0 env e)), nop, env
  | TSIf(cond, s1, s2) ->
    let c, a = gen_expr_v0 env cond in
    let l_else = id "_cond_else" in
    let l_end = id "_cond_end" in
    let c_then, d_then, _ = gen_stmt env s1 in
    let c_else, d_else, _ = gen_stmt env s2 in
    comment "if" ++ c ++ cr v0 a ++ beqz v0 l_else ++ c_then ++ b l_end ++
      label l_else ++ c_else ++ label l_end, d_then ++ d_else, env
  | TSWhile(cond, body) ->
    let c, a = gen_expr_v0 env cond in
    let l_begin = id "_while_begin" in
    let l_cond = id "_while_cond" in
    let c_body, d_body, _ = gen_stmt env body in
    comment "while" ++ b l_cond ++ label l_begin ++ c_body ++
      label l_cond ++ c ++ cr v0 a ++ bnez v0 l_begin, d_body, env
  | TSFor(before, cond, after, body) ->
    let l_begin = id "_for_begin" in
    let l_cond = id "_for_cond" in
    let c_before = List.fold_left
      (fun code expr -> let c, _ = gen_expr_v0 env expr in code ++ c) nop before in
    let c_after = List.fold_left
      (fun code expr -> let c, _ = gen_expr_v0 env expr in code ++ c) nop after in
    let c_cond = match cond with
      | None -> b l_begin
      | Some x -> let c, a = gen_expr_v0 env x in
        c ++ cr v0 a ++ bnez v0 l_begin in
    let c_body, d_body, _ = gen_stmt env body in
    comment "for" ++ c_before ++ b l_cond ++ label l_begin ++ c_body ++ c_after ++ label l_cond
      ++ c_cond, d_body, env
  | TSBlock(b) ->
    let c, d = gen_block env b in
    comment "block" ++ c, d, env
  | TSReturn (None) ->
    comment "return" ++ b env.c_ret_lbl, nop, env
  | TSReturn (Some e) ->
    let c, a = gen_expr_v0 env e in
    assert (a = Addr || not env.c_ret_ref);
    comment "return" ++ c ++ (if not env.c_ret_ref then cr v0 a else nop) ++ b env.c_ret_lbl, nop, env
  | TSDeclare (ty, id) ->
    let s = type_size env.c_penv ty in
    let env2, pos = env_push s env in
    let code = match ty with
    | TClass(i) ->
      let c = get_c env.c_penv i in
      let cproto = List.find (fun p -> p.tp_ret_type = None && p.tp_name =  i && p.tp_args = []) c.tc_methods in
      let code_save_regs, code_restore_regs, env_regs_saved = saver env2 env.c_save_regs in
      code_save_regs ++
      la a0 areg (pos, fp) ++
      la sp areg (-env_regs_saved.c_fp_used, fp) ++
      jal cproto.tp_unique_ident ++ code_restore_regs
    | _ -> sw zero areg (pos, fp)
    in
    comment ("declare " ^ id) ++ code, nop, {
      c_penv = env.c_penv;
      c_names = Smap.add id (VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_ret_lbl = env.c_ret_lbl;
      c_fp_used = env2.c_fp_used;
      c_save_regs = env.c_save_regs }
  | TSDeclareAssignConstructor(cls, id, constr, args) ->
    let env2, pos = env_push cls.tc_size env in
    let code =
      let code_save_regs, code_restore_regs, env_regs_saved = saver env2 env.c_save_regs in
      let args_code, _, env_args = code_for_args env_regs_saved args [ a1; a2; a3 ] in
      code_save_regs ++ args_code ++ la a0 areg(pos, fp) 
        ++ la sp areg (-env_args.c_fp_used, fp) ++ jal constr ++
        code_restore_regs
    in
    comment ("declare " ^ id) ++ code, nop, {
      c_penv = env.c_penv;
      c_names = Smap.add id (VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_ret_lbl = env.c_ret_lbl;
      c_save_regs = env.c_save_regs;
      c_fp_used = env2.c_fp_used; }
  | TSDeclareAssignExpr ((ty, ref), id, e) ->
    let s = if ref then 4 else type_size env.c_penv ty in
    assert (s = 4);
    let env2, pos = env_push 4 env in
    let code, a = gen_expr_v0 env2 e in
    comment ("declare " ^ id) ++ code ++ (if not ref then cr v0 a else cla v0 a) ++ sw v0 areg (pos, fp), nop,
    { c_penv = env.c_penv;
      c_names = Smap.add id (if ref then VStackByRef pos else VStack pos) env.c_names;
      c_ret_ref = env.c_ret_ref;
      c_ret_lbl = env.c_ret_lbl;
      c_fp_used = env2.c_fp_used;
      c_save_regs = env.c_save_regs }
  | TSWriteCout(sl) ->
    let save_code, restore_code, env2 = saver env (if List.mem a0 env.c_save_regs then [a0] else []) in
    let text1, data1 = List.fold_left
      (fun (text, data) s ->
        match s with
        | TSEExpr(e) ->
          let t, a = gen_expr env2 (a0::use_regs) (env2.c_save_regs) e in
          text ++ t ++ cr a0 a ++ li v0 1 ++ syscall, data
        | TSEStr(s) ->
          let l, d =
            if Hashtbl.mem strings s then
              Hashtbl.find strings s, nop
            else
              let l = id "_s" in Hashtbl.add strings s l;
              l, label l ++ asciiz s
          in
            text ++ la a0 alab l ++ li v0 4 ++ syscall, data ++ d) (nop, nop) sl in
    comment "cout<<..." ++ save_code ++ text1 ++ restore_code, data1, env
and gen_block env b =
  let text, data, fin_env =
    List.fold_left (fun (t, d, e) s ->
        let tt, dd, e = gen_stmt e s in
          t ++ tt, d ++ dd, e)
      (nop, nop, env) b
  in
    text, data

let gen_decl tenv decl = match decl with
  | TDGlobal(ty, id) ->
    globals_env := Smap.add id VGlobal !globals_env;
    let bytes = type_size tenv ty in
    nop, (label id) ++ (dword (let rec a n = if n > 0 then 0::(a (n-4)) else [] in a bytes))
  | TDFunction(proto, block) ->
    let regs_for_args = match proto.tp_class with | None -> [ a0; a1; a2; a3 ] | Some k -> [ a1; a2; a3 ] in
    let env0 = match proto.tp_class with | None -> !globals_env | Some _ -> Smap.add "this" (VRegister a0) !globals_env in
    let names, _, free_regs = List.fold_left 
            (fun (env, p, regs) ((ty, r), id) -> 
              let s = (if r then 4 else type_size tenv ty) in
              assert (s = 4);
              match regs with
              | reg::more_regs ->
                Smap.add id (if r then VRegisterByRef reg else VRegister reg) env, p, more_regs
              | _ -> Smap.add id (if r then VStackByRef p else VStack p) env, p + 4, regs
            )
            (env0, 0, regs_for_args) proto.tp_args in
    let env = {
      c_penv = tenv;
      c_names = names;
      c_ret_ref = (match proto.tp_ret_type with | None -> false | Some(_, r) -> r);
      c_ret_lbl = "_return_" ^ proto.tp_unique_ident;
      c_fp_used = 8;
      c_save_regs = List.filter (fun r -> not (List.mem r free_regs)) [a0; a1; a2; a3];
      } in
    let save_code, unsave_code, env2 = saver env (List.filter (fun x -> x <> a0 || proto.tp_class = None) env.c_save_regs) in
    let code_for_constructor, does_calls = match proto.tp_ret_type with
      | Some _ -> nop, (List.exists stmt_does_call block)
      | None -> let cls_name = (match proto.tp_class with | Some k -> k | None -> assert false) in
        la sp areg (-8, fp) ++ jal (cls_name ^ "0"), true in
    let code_for_virtual = match proto.tp_virtual with
      | Some (c, _) when c.h_pos <> 0 ->
        la a0 areg (-c.h_pos, a0)
      | _ -> nop
    in
    if does_calls 
      then
        let text, data = gen_block env2 block in 
        label proto.tp_unique_ident
        ++ sw fp areg (-4, sp) ++ sw ra areg (-8, sp) ++ move fp sp
        ++ code_for_virtual ++ save_code ++ code_for_constructor ++ text ++ label env.c_ret_lbl
        ++ move sp fp ++ lw fp areg (-4, sp) ++ lw ra areg (-8, sp) ++ jr ra, data
      else
        let text, data = gen_block env block in 
        label proto.tp_unique_ident
        ++ sw fp areg (-4, sp) ++ move fp sp
        ++ code_for_virtual ++ text ++ label env.c_ret_lbl
        ++ move sp fp ++ lw fp areg (-4, sp) ++ jr ra, data
  | TDClass(c) ->
    let calls_something = ref false in
    (* Call default constructor of parent classes *)
    let code_parents = List.fold_left
      (fun code parent ->
          let cn = parent.h_class in
          let c = get_c tenv cn in
          let proto = List.find (fun p -> p.tp_ret_type = None && p.tp_args = [] && p.tp_name = cn) c.tc_methods in
          calls_something := true;
          code ++ (if parent.h_pos <> 0 then la a0 areg(parent.h_pos, a0) else nop)
            ++ jal proto.tp_unique_ident ++ (if parent.h_pos <> 0 then lw a0 areg (-12, fp) else nop)
      )
      nop c.tc_hier.h_supers in
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
          else la a1 alab ("_vt_" ^ c.tc_name ^ "_as_" ^ hh.h_class)
            ++ sw a1 areg (hh.h_pos, a0) in
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
              (if pos <> 0 then la a0 areg (pos, a0) else nop)
                ++ la sp areg (-12, fp)
                ++ jal proto.tp_unique_ident ++ (if pos <> 0 then lw a0 areg (-12, fp) else nop)
          | _ -> sw zero areg (pos, a0)
        ) ++ code) c.tc_members nop 
    in (* Put it all together *)
      label (c.tc_name ^ "0")
          ++ (if !calls_something then 
                sw fp areg (-4, sp) ++ move fp sp ++
                sw ra areg (-8, fp) ++ sw a0 areg (-12, fp) ++ la sp areg (-12, fp)
              else nop)
          ++ code_parents ++ vtable_init_code ++ init_code_proper
          ++ (if !calls_something then
                lw ra areg (-8, fp) ++ move sp fp ++ lw fp areg (-4, sp)
              else nop)
          ++ jr ra, vtables


let generate p =
  try 
    let text, data = List.fold_left (fun (text, data) decl ->
        let more_text, more_data = gen_decl p.prog_env decl in
        text ++ more_text, data ++ more_data) (nop, nop) p.prog_decls in
    let text =
      label "main" ++ jal p.prog_main ++
      li v0 10 ++ syscall ++
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
