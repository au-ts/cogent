(*
 * Copyright 2017, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)
theory GraphLangCompare

imports "../cogent/isa/TypeTrackingSemantics"
  "../../verification/l4v/tools/asmrefine/GraphLangLemmas"

begin

primrec
  variable_of_lit :: "lit \<Rightarrow> variable"
where
    "variable_of_lit (LU8 w) = VarWord8 w"
  | "variable_of_lit (LU16 w) = VarWord16 w"
  | "variable_of_lit (LU32 w) = VarWord32 w"
  | "variable_of_lit (LU64 w) = VarWord64 w"
  | "variable_of_lit (LBool b) = VarBool b"

primrec
  lit_of_variable :: "variable \<Rightarrow> lit"
where
    "lit_of_variable (VarWord8 w) = LU8 w"
  | "lit_of_variable (VarWord16 w) = LU16 w"
  | "lit_of_variable (VarWord32 w) = LU32 w"
  | "lit_of_variable (VarWord64 w) = LU64 w"
  | "lit_of_variable (VarBool w) = LBool w"

fun dec :: "nat \<Rightarrow> string"
where
  "dec n = (if n < 10 then [''0123456789'' ! n]
    else dec (n div 10) @ dec (n mod 10))"

lemmas dec_simps_safe[simp]
    = split_if[where P="op = (dec n)" for n, THEN iffD1, OF dec.simps]
declare dec.simps[simp del]

definition
  "record_field_names n = dec n"

lemma dec_empty[simp]:
  "dec n \<noteq> []"
  apply (induct n rule: dec.induct)
  apply (subst dec.simps)
  apply simp
  done

lemmas empty_dec[simp] = not_sym[OF dec_empty]

lemma set_dec:
  "set (dec n) \<subseteq> set ''0123456789''"
  apply (induct n rule: dec.induct)
  apply (subst dec.simps)
  apply (simp add: nth_Cons')
  done

lemma inj_dec_lemma:
  "dec x = dec y \<longrightarrow> x = y"
proof (induct x arbitrary: y rule: dec.induct)
  case (1 n)
  have P: "\<And>x y. x < 10 \<longrightarrow> y < 10 \<longrightarrow> ((''0123456789'' ! x = ''0123456789'' ! y) = (x = y))"
    by (simp add: nth_Cons')
  show ?case
    apply (subst dec.simps[where n=n])
    apply (subst dec.simps[where n=y])
    apply (clarsimp simp: P dest!: "1.hyps"[rule_format, rotated])
    apply (metis  div_mod_equality[where c="0", simplified])
    done
qed

definition
  "naming_scheme xs y zs = (xs @ (case y of Some i \<Rightarrow> ''@'' @ dec i | _ \<Rightarrow> [])
    @ (concat (map (op # (CHR ''.'')) zs)))"

lemma append_cut:
  "as @ bs = cs @ ds
    \<Longrightarrow> (bs = [] \<or> hd bs = x)
    \<Longrightarrow> (ds = [] \<or> hd ds = x)
    \<Longrightarrow> (x \<notin> set as)
    \<Longrightarrow> (x \<notin> set cs)
    \<Longrightarrow> as = cs \<and> bs = ds"
  apply (induct as arbitrary: cs)
   apply (case_tac cs, simp_all)
  apply (case_tac cs, auto)
  done

lemma naming_scheme_inj:
  "naming_scheme xs y zs = naming_scheme xs' y' zs'
    \<Longrightarrow> set xs \<inter> set ''.@'' = {}
    \<Longrightarrow> set xs' \<inter> set ''.@'' = {}
    \<Longrightarrow> xs = xs' \<and> y = y' \<and> concat (map (op # CHR ''.'') zs) = concat (map (op # CHR ''.'') zs')"
  apply (clarsimp simp: naming_scheme_def)
  apply (simp only: append_assoc[symmetric])
  apply (drule_tac x="CHR ''.''" in append_cut)
      apply (cases zs, simp_all)[1]
     apply (cases zs', simp_all)[1]
    apply (clarsimp dest!: set_dec[THEN subsetD])
   apply (clarsimp dest!: set_dec[THEN subsetD])
  apply clarsimp
  apply (drule_tac x="CHR ''@''" in append_cut)
  apply (auto split: option.split option.split_asm
              dest!: inj_dec_lemma[rule_format])
  done

lemma naming_scheme_inj_eq:
  "set xs \<inter> set ''.@'' = {}
    \<Longrightarrow> set xs' \<inter> set ''.@'' = {}
    \<Longrightarrow> ((naming_scheme xs y zs = naming_scheme xs' y' zs')
      = (xs = xs' \<and> y = y' \<and> concat (map (op # CHR ''.'') zs) = concat (map (op # CHR ''.'') zs')))"
  by (auto dest: naming_scheme_inj, simp add: naming_scheme_def)

locale update_sem_32 = update_sem abs_typing
    for abs_typing :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> 'l set \<Rightarrow> _"
  + fixes encode_ptr :: "'l \<Rightarrow> word32"
      and encode_abs :: "'a \<Rightarrow> word32"
      and \<xi> \<Xi>
    assumes encode_ptr_inj: "inj encode_ptr"
and u_progress:
 "\<Xi>, [], \<Gamma> \<turnstile> c : \<tau>
    \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>r, w\<rangle>
    \<Longrightarrow> \<exists>! st. (\<xi>, \<gamma> \<turnstile> (\<sigma>,c) \<Down>! st)"
and ctx_wf: "proc_ctx_wellformed \<Xi>" "\<xi> matches-u \<Xi>"

begin

primrec
  uval_fields :: "('f, 'a, 'l) uval \<Rightarrow> variable list"
  and uval_fields_xs :: "(('f, 'a, 'l) uval \<times> repr) list \<Rightarrow> variable list"
  and uval_fields_prod :: "(('f, 'a, 'l) uval \<times> repr) \<Rightarrow> variable list"
where
    "uval_fields (UPrim lit) = [variable_of_lit lit]"
  | "uval_fields (UPtr addr _) = [VarWord32 (encode_ptr addr)]"
  | "uval_fields UUnit = []"
  | "uval_fields (UFunction f args) = []"
  | "uval_fields (UAFunction f args) = []"
  | "uval_fields (UAbstract ab) = [VarWord32 (encode_abs ab)]"
  | "uval_fields (USum x y z) = []"
  | "uval_fields (UProduct x y) = uval_fields x @ uval_fields y"
  | "uval_fields (URecord flds) = uval_fields_xs flds"
  | "uval_fields_xs [] = []"
  | "uval_fields_xs (v # vs) = (uval_fields_prod v @ uval_fields_xs vs)"
  | "uval_fields_prod (x, y) = uval_fields x"

primrec
  var_fields :: "string \<Rightarrow> repr \<Rightarrow> string list"
  and var_fields_xs :: "nat \<Rightarrow> string \<Rightarrow> repr list \<Rightarrow> string list"
where
    "var_fields nm RUnit = []"
  | "var_fields nm (RPrim _) = [nm]"
  | "var_fields nm (RProduct t u) = (var_fields (nm @ ''.1'') t @ var_fields (nm @ ''.2'') u)"
  | "var_fields nm RFun = []"
  | "var_fields nm (RCon _ _) = [nm]"
  | "var_fields nm (RSum _) = []"
  | "var_fields nm (RPtr _) = [nm]"
  | "var_fields nm (RRecord flds) = var_fields_xs 0 nm flds"
  | "var_fields_xs num nm [] = []"
  | "var_fields_xs num nm (r # rs)
    = var_fields (nm @ ''.'' @ record_field_names num) r @ var_fields_xs (Suc num) nm rs"

definition
  var_fields_tup :: "(string \<times> repr) \<Rightarrow> string list"
where
  "var_fields_tup = case_prod var_fields"

definition
  var_fields_opt :: "(string \<times> COGENT.type option) \<Rightarrow> string list"
where
  "var_fields_opt x = (case x of (nm, Some typ) \<Rightarrow> var_fields nm (type_repr typ) | _ \<Rightarrow> [])"

abbreviation (input)
  "var_fields' nm t \<equiv> var_fields nm (type_repr t)"

lemma var_fields_opt_simps[simp]:
  "var_fields_opt (nm, Some t) = var_fields' nm t"
  "var_fields_opt (nm, None) = []"
  by (simp_all add: var_fields_opt_def)

definition
  "mem st == var_mem ''Mem'' st"

(* FIXME: move to CommonOps *)
definition
 "store_word16 (addr :: word32) (w :: word16)
    = heap_update_list addr (rev (word_rsplit w))"

definition
 "load_word16 (addr :: word32) memory
    = (word_rcat (rev (heap_list memory 2 addr)) :: word16)"

definition
 "store_word64 (addr :: word32) (w :: word64)
    = heap_update_list addr (rev (word_rsplit w))"

definition
 "load_word64 (addr :: word32) memory
    = (word_rcat (rev (heap_list memory 8 addr)) :: word64)"

definition
  "load_inner addr_t m == case addr_t of (addr, Num U8) \<Rightarrow> VarWord8 (load_word8 addr m)
    | (addr, Num U16) \<Rightarrow> VarWord16 (load_word16 addr m)
    | (addr, Num U32) \<Rightarrow> VarWord32 (load_word32 addr m)
    | (addr, Num U64) \<Rightarrow> VarWord64 (load_word64 addr m)
    | (addr, Bool) \<Rightarrow> VarBool (load_word32 addr m \<noteq> 0)
    | _ \<Rightarrow> VarBool False"

definition
  "load addr_t = load_inner addr_t o mem"

definition
  "save_inner addr v m == case v of VarWord8 w8 \<Rightarrow> store_word8 addr w8 m
    | VarWord16 w \<Rightarrow> store_word16 addr w m
    | VarWord32 w \<Rightarrow> store_word32 addr w m
    | VarWord64 w \<Rightarrow> store_word64 addr w m
    | VarBool b \<Rightarrow> store_word32 addr (if b then 1 else 0) m
    | _ \<Rightarrow> m"

primrec
  mem_sz :: "repr \<Rightarrow> nat"
  and mem_sz_xs :: "repr list  \<Rightarrow> nat"
where
    "mem_sz RUnit = 0"
  | "mem_sz (RPrim prim_t) = (case prim_t of Num U8 \<Rightarrow> 1
      | Num U16 \<Rightarrow> 2 | Num U32 \<Rightarrow> 4 | Num U64 \<Rightarrow> 8
      | _ \<Rightarrow> 4)"
  | "mem_sz (RProduct t u) = mem_sz t + mem_sz u"
  | "mem_sz (RFun) = 0"
  | "mem_sz (RCon _ _) = 4" (* FIXME assuming ADTs single var *)
  | "mem_sz (RSum _) = 0"
  | "mem_sz (RPtr _) = 4"
  | "mem_sz (RRecord flds) = mem_sz_xs flds"
  | "mem_sz_xs [] = 0"
  | "mem_sz_xs (r # rs) = mem_sz r + mem_sz_xs rs"

definition
  "addr_t_dom addr_t == {fst addr_t ..+ mem_sz (RPrim (snd addr_t))}"

primrec
  var_mem_fields :: "addr \<Rightarrow> repr \<Rightarrow> (addr \<times> prim_type) list"
  and var_mem_fields_xs :: "addr \<Rightarrow> repr list \<Rightarrow> (addr \<times> prim_type) list"
where
    "var_mem_fields addr RUnit = []"
  | "var_mem_fields addr (RPrim prim_t) = [(addr, prim_t)]"
  | "var_mem_fields addr (RProduct t u) = (var_mem_fields addr t @ var_mem_fields (addr + of_nat (mem_sz t)) u)"
  | "var_mem_fields addr RFun = []"
  | "var_mem_fields addr (RPtr _) = [(addr, Num U32)]"
  | "var_mem_fields addr (RCon _ _) = [(addr, Num U32)]" (* FIXME assuming ADTs single var *)
  | "var_mem_fields addr (RSum _) = []"
  | "var_mem_fields addr (RRecord flds) = var_mem_fields_xs addr flds"
  | "var_mem_fields_xs addr [] = []"
  | "var_mem_fields_xs addr (r # rs)
    = var_mem_fields addr r @ var_mem_fields_xs (addr + of_nat (mem_sz r)) rs"

definition
  heap_rel_inner :: "('f, 'a, 'l) store \<Rightarrow> (word32 \<Rightarrow> word8) \<Rightarrow> bool"
where
  "heap_rel_inner \<sigma> m = ((\<forall>(ptr, v) \<in> graph_of \<sigma>.
        map (\<lambda>addr. load_inner addr m) (var_mem_fields (encode_ptr ptr) (uval_repr_deep v))
            = uval_fields v)
    \<and> (\<forall>ptr ptr' v v'. ptr \<noteq> ptr' \<longrightarrow> \<sigma> ptr = Some v \<longrightarrow> \<sigma> ptr' = Some v'
        \<longrightarrow> (\<forall>addr addr'. addr \<in> set (var_mem_fields (encode_ptr ptr) (uval_repr_deep v))
            \<and> addr' \<in> set (var_mem_fields (encode_ptr ptr') (uval_repr_deep v'))
            \<longrightarrow> addr_t_dom addr \<inter> addr_t_dom addr' = {})))"

definition
  heap_rel :: "('f, 'a, 'l) store \<Rightarrow> state \<Rightarrow> bool"
where
  "heap_rel \<sigma> st = heap_rel_inner \<sigma> (mem st)"

definition
  do_prim :: "prim_op \<Rightarrow> variable list \<Rightarrow> variable"
where
  "do_prim opr xs = variable_of_lit (eval_prim_op opr (map (lit_of_variable) xs))"

definition
  load_wrapper :: "(state \<Rightarrow> word32) \<Rightarrow> repr \<Rightarrow> (state \<Rightarrow> variable) list"
where
  "load_wrapper ptr t = map (\<lambda>(offs, tp) st. load (ptr st + offs, tp) st) (var_mem_fields 0 t)"

definition
  load_wrapper2 :: "(state \<Rightarrow> variable) \<Rightarrow> repr \<Rightarrow> (state \<Rightarrow> variable) list"
where
  "load_wrapper2 ptr t = load_wrapper (\<lambda>st. case ptr st of VarWord32 addr \<Rightarrow> addr | _ \<Rightarrow> 0) t"

definition
  lit_var_acc :: "string \<Rightarrow> prim_type \<Rightarrow> state \<Rightarrow> variable"
where
  "lit_var_acc nm lt st \<equiv> case lt of Num U8 \<Rightarrow> VarWord8 (var_word8 nm st)
    | Num U16 \<Rightarrow> VarWord16 (var_word16 nm st)
    | Num U32 \<Rightarrow> VarWord32 (var_word32 nm st)
    | Num U64 \<Rightarrow> VarWord64 (var_word64 nm st)
    | Bool \<Rightarrow> VarBool (var_bool nm st)
    | _ \<Rightarrow> var_acc nm st"

definition
  var_acc_fields :: "string \<Rightarrow> repr \<Rightarrow> (state \<Rightarrow> variable) list"
where
  "var_acc_fields nm r = map (\<lambda>(nm', (_, ltyp)). lit_var_acc nm' ltyp)
        (zip (var_fields nm r) (var_mem_fields 0 r))"

abbreviation(input)
  "var_acc_fields' nm type \<equiv> var_acc_fields nm (type_repr type)"

primrec
  accs_of_atom :: "bool \<Rightarrow> 'f expr \<Rightarrow> (string \<times> COGENT.type option) list \<Rightarrow> ((state \<Rightarrow> variable) list \<times> repr) option"
  and accs_of_atom_xs :: "'f expr list \<Rightarrow> (string \<times> COGENT.type option) list \<Rightarrow> ((state \<Rightarrow> variable) list \<times> repr list) option"
  and accs_of_atom_xs2 :: "'f expr list \<Rightarrow> (string \<times> COGENT.type option) list \<Rightarrow> ((state \<Rightarrow> variable) list \<times> repr list) option"
where
    "accs_of_atom b (Var n) vs = (case vs ! n of (nm, Some tp) \<Rightarrow> Some (var_acc_fields' nm tp, type_repr tp))"
  | "accs_of_atom b (Prim opr es) vs = map_option (\<lambda>(accs, rs). ([\<lambda>st. do_prim opr (map (\<lambda>acc. acc st) accs)],
      RPrim (snd (prim_op_type opr)))) (accs_of_atom_xs es vs)"
  | "accs_of_atom b (Lit lit) vs = Some ([\<lambda>_. variable_of_lit lit], RPrim (lit_type lit))"
  | "accs_of_atom b (Cast nty e) vs = (case accs_of_atom False e vs of None \<Rightarrow> None
        | Some (v, _) \<Rightarrow> Some ([\<lambda>st. variable_of_lit (the (cast_to nty (lit_of_variable (hd v st))))],
            RPrim (Num nty)))"
  | "accs_of_atom b (Tuple t u) vs = (case (accs_of_atom False t vs, accs_of_atom False u vs)
    of (Some (xs, r), Some (ys, r')) \<Rightarrow> Some (xs @ ys, RProduct r r') | _ \<Rightarrow> None)"
  | "accs_of_atom b (Member f ix) vs = (case accs_of_atom False f vs of
        Some (accs, RRecord fs) \<Rightarrow> Some (take (length (var_fields [] (fs ! ix)))
            (drop (length (var_fields_xs 0 [] (take ix fs))) accs), fs ! ix)
      | Some (accs, RPtr r) \<Rightarrow> (case (accs, r, b) of ([acc], RRecord fs, True)
                 \<Rightarrow> Some (take (length (var_fields [] (fs ! ix)))
            (drop (length (var_fields_xs 0 [] (take ix fs))) (load_wrapper2 acc (RRecord fs))), fs ! ix)
          | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)"
  | "accs_of_atom b Unit vs = Some ([], RUnit)"
  | "accs_of_atom b (Promote nty x) vs = map_option (\<lambda>(accs, rs). (accs, type_repr (TSum nty))) (accs_of_atom False x vs)"
  | "accs_of_atom b (Put x ix y) vs = (case (accs_of_atom False x vs, accs_of_atom False y vs)
    of (Some (xs, RRecord fs), Some (ys, r)) \<Rightarrow> Some (take (length (var_fields_xs 0 [] (take ix fs))) xs
        @ ys @ drop (length (var_fields_xs 0 [] (take (Suc ix) fs))) xs, RRecord fs)
     | _ \<Rightarrow> None
    )"
  | "accs_of_atom b (If x y z) vs = None
    (* this isn't currently needed, and enabling it requires a somewhat painful induction
(case (accs_of_atom False x vs, accs_of_atom False y vs,
        accs_of_atom False z vs) of (Some ([x], RBool), Some (ys, r), Some (zs, r'))
            \<Rightarrow> (if r = r' \<and> length ys = length zs then Some
                (map (\<lambda>(y, z) st. if x st = VarBool True then y st else z st) (zip ys zs), r)
            else None)
      | _ \<Rightarrow> None) *)"
  | "accs_of_atom b (Struct f xs) vs = map_option (\<lambda>(xs, rs). (xs, RRecord rs)) (accs_of_atom_xs2 xs vs)"
  | "accs_of_atom b (Let x y) vs = None"
  | "accs_of_atom b (App x y) vs = None"
  | "accs_of_atom b (Take x y z) vs = None"
  | "accs_of_atom b (Split x y) vs = None"
  | "accs_of_atom b (Case x y z w) vs = None"
  | "accs_of_atom b (Esac x) vs = None"
  | "accs_of_atom b (LetBang is x y) vs = None"
  | "accs_of_atom b (Con x y z) vs = None"
  | "accs_of_atom b (Fun f ts) vs = None"
  | "accs_of_atom b (AFun f ts) vs = None"
  | "accs_of_atom_xs [] vs = Some ([], [])"
  | "accs_of_atom_xs (e # es) vs = (case (accs_of_atom False e vs, accs_of_atom_xs es vs)
    of (Some (xs, r), Some (ys, rs)) \<Rightarrow> Some (xs @ ys, r # rs) | _ \<Rightarrow> None)"
  | "accs_of_atom_xs2 [] vs = Some ([], [])"
  | "accs_of_atom_xs2 (e # es) vs = (case (accs_of_atom False e vs, accs_of_atom_xs2 es vs)
    of (Some (xs, r), Some (ys, rs)) \<Rightarrow> Some (xs @ ys, r # rs) | _ \<Rightarrow> None)"

lemma accs_of_atom_xs2[simp]:
  "accs_of_atom_xs2 = accs_of_atom_xs"
  by (intro ext, induct_tac x, simp_all)

definition
  "graph_state_match vars tps args hp st
      = (heap_rel hp st
          \<and> length vars = length tps
          \<and> length args = length tps
          \<and> (\<forall>i < length tps. tps ! i = None \<or> type_repr (the (tps ! i)) = snd (vars ! i))
          \<and> (\<forall>i < length tps. acc_vars (var_fields_tup (vars ! i)) st = uval_fields (args ! i)))"

definition
  "relates GGamma gfun_name (typ :: poly_type) cogent_expr
    = (\<exists>gfun. GGamma gfun_name = Some gfun
      \<and> (\<forall>tr nn st hp arg. tr \<in> exec_trace GGamma gfun_name \<and> tr 0 = Some [(nn, st, gfun_name)]
           \<and> graph_state_match [(''a@0'', type_repr (fst (snd typ)))] [None] [arg] hp st
           \<and> (\<exists>rs ws. \<Xi>, hp \<turnstile> [arg] matches [Some (fst (snd typ))] \<langle>rs, ws\<rangle>)
        \<longrightarrow> (\<exists>hp' fin st'. u_sem \<xi> [arg] (hp, cogent_expr) (hp', fin)
            \<and> trace_end tr = Some [(Ret, st', gfun_name)]
            \<and> graph_state_match [(''ret'', type_repr (snd (snd typ)))] [None] [fin] hp' st')))"

definition
  "naming_cond' vars N = (distinct vars
           \<and> (\<forall>v \<in> set vars. \<exists>nm y. y \<in> N \<and> v = naming_scheme nm y []
              \<and> set nm \<inter> set ''.@'' = {}))"

definition
  "naming_cond vars N = naming_cond' vars (Some ` N)"

definition
  "graph_chunk GGamma t\<Gamma> gfun_name vars cogent_expr ep fin_typ N R
    = (\<forall>tr i st hp args fin hp'.
           tr \<in> exec_trace GGamma gfun_name \<and> tr i = Some [(NextNode ep, st, gfun_name)]
           \<and> graph_state_match vars (snd t\<Gamma>) args hp st
           \<and> (u_tt_sem_pres \<Xi> \<xi> args [] t\<Gamma> fin_typ (hp, cogent_expr) (hp', fin))
           \<and> naming_cond (map fst vars) {..< N}
        \<longrightarrow> (\<exists>st' i. tr i = Some [(R, st', gfun_name)]
            \<and> graph_state_match ((''ret'', type_repr fin_typ) # vars)
                (Some fin_typ # replicate (length vars) None) (fin # args) hp' st'))"

lemmas graph_chunkI = graph_chunk_def[THEN iffD2, rule_format]
lemmas graph_chunkD = graph_chunk_def[THEN iffD1, simplified imp_conjL, rule_format]

lemma relates_from_graph_chunk:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> graph_chunk GGamma (TT, [Some (fst (snd typ))]) gfun_name
        [(''a@0'', type_repr (fst (snd typ)))] cogent_expr (entry_point gfun) (snd (snd typ)) 1 Ret
    \<Longrightarrow> ttyping \<Xi> [] (TT, [Some (fst (snd typ))]) cogent_expr (snd (snd typ))
    \<Longrightarrow> relates GGamma gfun_name typ cogent_expr"
  apply (clarsimp simp add: relates_def)
  apply (frule exec_trace_init, clarsimp)
  apply (frule ttyping_imp_typing)
  apply (clarsimp simp: graph_state_match_def)
  apply (frule(1) u_progress)
  apply clarsimp
  apply (frule(2) intermediate_preservation[OF ctx_wf(1) _ ctx_wf(2),
    where \<Gamma>="(TT, [Some (fst (snd typ))])", simplified])
  apply (drule(2) graph_chunkD[where args="[arg]" for arg])
     apply (simp add: graph_state_match_def)
    apply assumption
   apply (simp add: naming_cond_def naming_cond'_def image_def)
   apply (rule_tac x="''a''" in exI, simp add: naming_scheme_def)
   apply fastforce
  apply clarsimp
  apply (frule_tac i=i in exec_trace_step_cases)
  apply (clarsimp simp: trace_end_eq_Some exec_trace_def
                        all_exec_graph_step_cases)
  apply (clarsimp simp: graph_state_match_def all_less_Suc_eq, blast)
  done

lemma list_all2_weaken:
  "list_all2 P xs ys \<Longrightarrow> \<forall>(x,y) \<in> set (zip xs ys). P x y \<longrightarrow> Q x y \<Longrightarrow> list_all2 Q xs ys"
  apply (induct xs ys rule: list_all2_induct)
   apply simp
  apply clarsimp
  done

lemma map_zip_takes:
  "map fst (zip xs ys) = take (length ys) xs"
  "map snd (zip ys xs) = take (length ys) xs"
  "map (\<lambda>(x, y). f x) (zip xs ys) = map f (take (length ys) xs)"
  "map (\<lambda>(x, y). f y) (zip ys xs) = map f (take (length ys) xs)"
  "map (f o fst) (zip xs ys) = map f (take (length ys) xs)"
  "map (f o snd) (zip ys xs) = map f (take (length ys) xs)"
  "map (\<lambda>x. f (fst x)) (zip xs ys) = map f (take (length ys) xs)"
  "map (\<lambda>x. f (snd x)) (zip ys xs) = map f (take (length ys) xs)"
  apply (induct xs arbitrary: ys, simp_all)
     apply ((case_tac ys, simp_all)[1])+
  done

lemma exec_cogent_unique_wrapper:
  "\<xi>, \<gamma> \<turnstile> (\<sigma>, cogent_expr) \<Down>! (\<sigma>', v)
    \<Longrightarrow> \<xi>, \<gamma> \<turnstile> (\<sigma>, cogent_expr) \<Down>! (\<sigma>'', v')
    \<Longrightarrow> ttyping \<Xi> [] (TT, \<Gamma>) cogent_expr \<tau>
    \<Longrightarrow> \<exists>rs ws. \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>rs, ws\<rangle>
    \<Longrightarrow> graph_state_match vars \<Gamma>' \<gamma> \<sigma> st
    \<Longrightarrow> \<sigma>'' = \<sigma>' \<and> v' = v"
  using u_progress[where c=cogent_expr and \<tau>=\<tau> and \<Gamma>=\<Gamma> and \<gamma>=\<gamma> and \<sigma>=\<sigma>]
  apply (clarsimp simp: graph_state_match_def dest!: ttyping_imp_typing)
  apply auto
  done

lemma lit_of_variable_of_lit:
  "lit_of_variable (variable_of_lit l) = l"
  by (cases l, simp_all)

lemma split_simple_weakening:
  "Kn \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
    \<Longrightarrow> list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) \<Gamma>0 \<Gamma>
    \<Longrightarrow> list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) \<Gamma>0 \<Gamma>1
        \<and> list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) \<Gamma>0 \<Gamma>2"
  apply (induct arbitrary: \<Gamma>0 rule: split.induct)
   apply clarsimp
  apply (clarsimp simp: list_all2_Cons2)
  apply (erule split_comp.cases, simp_all)
  done

lemma uval_fields_length:
  "length (uval_fields (uv :: ('f, 'a, 'l) uval)) = length (var_fields nm (uval_repr_deep uv))"
  "length (uval_fields_xs (uvs :: (('f, 'a, 'l) uval \<times> repr) list))
    = length (var_fields_xs n nm (map (uval_repr_deep o fst) uvs))"
  "length (uval_fields_prod (uvp :: (('f, 'a, 'l) uval \<times> repr)))
    = length (var_fields nm (uval_repr_deep (fst uvp)))"
  by (induct uv and uvs and uvp arbitrary: nm and n nm and nm,
    simp_all add: Product_Type.split_def HOL.Let_def)

lemma uval_fields_length_Nil:
  "length (uval_fields uv) = length (var_fields [] (uval_repr_deep uv))"
  "length (uval_fields_xs uvs) = length (var_fields_xs 0 [] (map (uval_repr_deep o fst) uvs))"
  by (metis uval_fields_length)+

lemma length_var_fields_const1[simp]:
  "length (var_fields (s # ss) repr) = length (var_fields [] repr)"
  "length (var_fields_xs n (s # ss) reprs) = length (var_fields_xs n [] reprs)"
  by (induct repr and reprs arbitrary: s ss and n s ss, simp_all)

lemma length_var_fields_const2[simp]:
  "length (var_fields_xs (Suc n) ss reprs) = length (var_fields_xs 0 [] reprs)"
  apply (induct reprs arbitrary: n ss, simp_all)
  apply (case_tac ss, simp_all add: length_var_fields_const1)
  done

lemma uval_fields_xs_split:
  "ix < length fs
    \<Longrightarrow> uval_fields (fst (fs ! ix))
    = take (length (var_fields [] (uval_repr_deep (fst (fs ! ix)))))
        (drop (length (var_fields_xs 0 [] (map (uval_repr_deep o fst) (take ix fs))))
            (uval_fields_xs fs))"
  apply (induct fs arbitrary: ix, simp_all)
  apply (case_tac ix)
   apply (clarsimp simp: uval_fields_length_Nil)
  apply (clarsimp simp: uval_fields_length_Nil)
  done

lemma uval_fields_xs_update:
  "ix < length fs
    \<Longrightarrow> uval_fields_xs (fs[ix := (val, rep)])
        = take (length (var_fields_xs 0 [] (map (uval_repr_deep o fst) (take ix fs)))) (uval_fields_xs fs)
            @ uval_fields val @ drop (length (var_fields_xs 0 [] (map (uval_repr_deep o fst) (take (Suc ix) fs)))) (uval_fields_xs fs)"
  apply (induct fs arbitrary: ix, simp_all)
  apply (case_tac ix)
   apply (clarsimp simp: uval_fields_length_Nil)
  apply (clarsimp simp: uval_fields_length_Nil)
  done

lemma map_eq_map_list_all2:
  "(map f xs = map g ys) = (list_all2 (\<lambda>x y. f x = g y) xs ys)"
  apply (induct xs arbitrary: ys, simp_all)
  apply (case_tac ys, simp_all)
  done

lemma var_mem_fields_offs_induct:
  "map (\<lambda>(offs,t). (ptr + offs, t)) (var_mem_fields ptr' r) = (var_mem_fields (ptr + ptr') r)"
  "map (\<lambda>(offs,t). (ptr + offs, t)) (var_mem_fields_xs ptr' rs) = (var_mem_fields_xs (ptr + ptr') rs)"
  by (induct r and rs arbitrary: ptr ptr' and ptr ptr', simp_all add: field_simps)

lemmas var_mem_fields_offs = var_mem_fields_offs_induct[where ptr'=0, symmetric, simplified]

lemma heap_relD:
  "hp ptr = Some v
    \<Longrightarrow> heap_rel hp st
    \<Longrightarrow> acc st = VarWord32 (encode_ptr ptr)
    \<Longrightarrow> uval_fields v = map (\<lambda>acc. acc st) (load_wrapper2 acc (uval_repr_deep v))"
  apply (clarsimp simp: heap_rel_def heap_rel_inner_def)
  apply (drule bspec, erule graph_ofI, clarsimp)
  apply (simp add: load_wrapper_def load_wrapper2_def o_def Product_Type.split_def load_def
                   var_mem_fields_offs[where ptr="encode_ptr ptr"])
  done

lemma uval_typing_record_length:
  "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> length fs = length \<tau>s"
  by (induct fs arbitrary: r w \<tau>s, auto)

lemma uval_typing_record_uval_repr_deep:
  "\<Xi>, \<sigma> \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> map (uval_repr_deep o fst) fs = map (type_repr o fst) \<tau>s"
  by (induct fs arbitrary: r w \<tau>s, auto simp: type_repr_uval_repr_deep)

lemma uval_fields_xs_eq_concat:
  "uval_fields_xs xs = concat (map (uval_fields o fst) xs)"
  by (induct xs, auto)

lemma length_var_mem_fields[simp]:
  "length (var_mem_fields ptr r) = length (var_fields [] r)"
  "length (var_mem_fields_xs ptr rs) = length (var_fields_xs 0 [] rs)"
  by (induct r and rs arbitrary: ptr and ptr, simp_all)

lemma var_acc_fields_is_var_accs_induct:
  "map (\<lambda>v. var_acc v st') (var_fields x (uval_repr_deep (uv :: ('f, 'a, 'l) uval))) = uval_fields uv
    \<Longrightarrow> map (\<lambda>acc. acc st') (map (\<lambda>(nm', (_, ltyp)). lit_var_acc nm' ltyp)
        (zip (var_fields x (uval_repr_deep uv)) (var_mem_fields j (uval_repr_deep uv))))
    = uval_fields uv"
  "map (\<lambda>v. var_acc v st') (var_fields_xs i x (map (uval_repr_deep o fst) (uvs :: (('f, 'a, 'l) uval \<times> repr) list))) = uval_fields_xs uvs
    \<Longrightarrow> map (\<lambda>acc. acc st') (map (\<lambda>(nm', (_, ltyp)). lit_var_acc nm' ltyp)
        (zip (var_fields_xs i x (map (uval_repr_deep o fst) uvs)) (var_mem_fields_xs j (map (uval_repr_deep o fst) uvs))))
    = uval_fields_xs uvs"
  "map (\<lambda>v. var_acc v st') (var_fields x (uval_repr_deep (fst uvp))) = uval_fields_prod uvp
    \<Longrightarrow> map (\<lambda>acc. acc st') (map (\<lambda>(nm', (_, ltyp)). lit_var_acc nm' ltyp)
        (zip (var_fields x (uval_repr_deep (fst uvp))) (var_mem_fields j (uval_repr_deep (fst uvp)))))
    = uval_fields_prod (uvp :: (('f, 'a, 'l) uval \<times> repr))"
  unfolding var_acc_fields_def
  apply (induct uv and uvs and uvp arbitrary: x j and i j x and x j,
    simp_all add: uval_fields_length[symmetric] var_acc_fields_def
           split: Product_Type.prod.split_asm)
    apply (case_tac lit, simp_all add: lit_var_acc_def var_bool_def var_word8_def
        var_word16_def var_word32_def var_word64_def)
  done

lemma var_acc_fields_is_var_accs:
  "map (\<lambda>v. var_acc v st') (var_fields x (uval_repr_deep uv)) = uval_fields uv
    \<Longrightarrow> map (\<lambda>acc. acc st') (var_acc_fields x (uval_repr_deep uv)) = uval_fields uv"
  unfolding var_acc_fields_def
  by (erule var_acc_fields_is_var_accs_induct)

lemma accs_of_atom_sem:
  "\<xi>, \<gamma> \<turnstile> st \<Down>! res
    \<Longrightarrow> accs_of_atom P (snd st) vars = Some (accs, repr)
    \<Longrightarrow> list_all2 (\<lambda>arg (nm, ty). ty = None \<or> (acc_vars (var_fields_opt (nm, ty)) st' = uval_fields arg
        \<and> uval_repr_deep arg = type_repr (the ty))) \<gamma> vars
    \<Longrightarrow> \<exists>\<Gamma>. list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) (map snd vars) \<Gamma>
        \<and> \<Xi>, [], \<Gamma> \<turnstile> snd st : \<tau> \<and> (P \<longrightarrow> (\<exists>rs ws. \<Xi>, fst st \<turnstile> \<gamma> matches \<Gamma> \<langle>rs, ws\<rangle>)
            \<and> proc_ctx_wellformed \<Xi> \<and> \<xi> matches-u \<Xi>)
    \<Longrightarrow> heap_rel (fst st) st'
    \<Longrightarrow> fst res = fst st \<and> uval_fields (snd res) = map (\<lambda>acc. acc st') accs
        \<and> uval_repr_deep (snd res) = repr \<and> type_repr \<tau> = repr"
  "\<xi>, \<gamma> \<turnstile>* ast \<Down>! ares
    \<Longrightarrow> accs_of_atom_xs (snd ast) vars = Some (accs, reprs)
    \<Longrightarrow> list_all2 (\<lambda>arg (nm, ty). ty = None \<or> (acc_vars (var_fields_opt (nm, ty)) st' = uval_fields arg
        \<and> uval_repr_deep arg = type_repr (the ty))) \<gamma> vars
    \<Longrightarrow> \<exists>\<Gamma>. list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) (map snd vars) \<Gamma>
        \<and> \<Xi>, [], \<Gamma> \<turnstile>* snd ast : \<tau>s
    \<Longrightarrow> heap_rel (fst ast) st'
    \<Longrightarrow> fst ares = fst ast \<and> concat (map uval_fields (snd ares)) = map (\<lambda>acc. acc st') accs
        \<and> map uval_repr_deep (snd ares) = reprs \<and> map type_repr \<tau>s = reprs"
proof (induct arbitrary: accs \<tau> repr P and accs \<tau>s reprs rule: u_sem_u_sem_all.inducts)
  case (u_sem_var \<xi> \<gamma> \<sigma> i) thus ?case
    apply clarsimp
    apply (erule typing.cases, simp_all, clarsimp)
    apply (frule weakening_nth, simp)
    apply (erule weakening_comp.cases, simp_all add: COGENT.empty_def, clarsimp)
    apply (clarsimp simp: list_all2_conv_all_nth)
    apply (drule spec, drule(1) mp)+
    apply (clarsimp simp: acc_vars_def o_def eq_commute COGENT.empty_def nth_map)
    apply (case_tac "\<Gamma>' ! i", simp_all, clarsimp)
    apply (frule var_acc_fields_is_var_accs[OF sym])
    apply simp
    done
next
  case (u_sem_prim \<xi> \<gamma> \<sigma> as \<sigma>' as' p accs)
  have P: "\<exists>ts. map uval_repr_deep as' = map (type_repr o TPrim) ts
    \<Longrightarrow> \<exists>lits. as' = map UPrim lits"
    apply (induct as', simp_all)
    apply clarsimp
    apply (case_tac a, simp_all add: Product_Type.split_def HOL.Let_def)
    apply (metis list.map)
    done
  from u_sem_prim.prems show ?case
    apply clarsimp
    apply (erule typing.cases, simp_all, clarsimp)
    apply (frule(1) u_sem_prim.hyps[simplified], blast, simp, clarsimp)
    apply (frule P[OF exI, OF sym])
    apply clarsimp
    apply (drule sym[where s="concat xs" for xs], simp)
    apply (clarsimp simp: do_prim_def eval_prim_u_def o_def lit_of_variable_of_lit)
    apply (erule eval_prim_op_lit_type)
    apply (rule map_inj_on[where f=RPrim, OF _ inj_onI], simp_all add: o_def)
    done
next
  case (u_sem_cast \<xi> \<gamma> \<sigma> e \<sigma>' l \<tau> l' accs \<tau>') 
    from u_sem_cast.prems show ?case
    apply (clarsimp split: option.split_asm)
    apply (erule typing.cases, simp_all, clarsimp)
    apply (frule(1) u_sem_cast.hyps[simplified], blast, simp, clarsimp)
    apply (erule upcast_valid_cast_to, erule sym)
    apply (metis Option.option.sel lit_of_variable_of_lit u_sem_cast.hyps)
    done
next
  case u_sem_promote thus ?case
    apply clarsimp
    apply (erule typing.cases, simp_all, clarsimp)
    apply blast
    done
next
  case u_sem_tuple from u_sem_tuple.prems show ?case
    apply (clarsimp split: option.split_asm elim!: typing_tupleE)
    apply (drule(1) split_simple_weakening)
    apply (drule u_sem_tuple.hyps[simplified], simp_all, fastforce)+
    done
next
  case (u_sem_if \<xi> \<gamma> \<sigma> x \<sigma>' b) from u_sem_if.prems show ?case
    apply (clarsimp split: option.split_asm list.split_asm
                    elim!: typing_ifE split: split_if_asm)
    done (* restore if if-case in accs_of_atom is needed 
    apply (drule(1) split_simple_weakening)
    apply (drule u_sem_if.hyps[simplified], simp_all, fastforce)
    apply (clarsimp dest!: sym[where s="VarBool b"])
    apply (rule u_sem_if.hyps(4)[where accs="if b then x else y"
        and repr="if b then x' else y'" and P=False for x y x' y', elim_format])
     apply (fastforce split: split_if, simp_all, fastforce)
    apply (clarsimp simp: o_def Product_Type.split_def
                          map_zip_takes(3-)[where f="\<lambda>acc. acc st" for st])
    done *)
next
  case (u_sem_member \<xi> \<gamma> \<sigma> e \<sigma>' fs ix accs \<tau> repr')
  from u_sem_member.prems show ?case
    apply clarsimp
    apply (clarsimp split: option.split_asm
                    elim!: typing_memberE)
    apply (frule u_sem_member.hyps[simplified], simp, blast, simp)
    apply (clarsimp split: repr.split_asm)
    apply (case_tac s, simp_all)
    apply (clarsimp simp: list_all2_conv_all_nth
                          uval_fields_xs_split take_map drop_map
                   dest!: map_eq_map_list_all2[THEN iffD1])
    apply (metis fst_conv)
    done
next
  case (u_sem_memb_b \<xi> \<gamma> \<sigma> e \<sigma>' addr repr fs ix accs \<tau> repr')
  note pres = preservation(1)[where \<tau>s=Nil and K=Nil, simplified, OF _ _ _ u_sem_memb_b.hyps(1)]
  from u_sem_memb_b.prems u_sem_memb_b.hyps(3) show ?case
    apply (clarsimp split: option.split_asm
                    elim!: typing_memberE)
    apply (frule u_sem_memb_b.hyps[simplified], simp, blast, simp)
    apply (clarsimp split: repr.split_asm bool.split_asm)
    apply (frule(1) heap_relD, erule sym)
    apply (frule(3) pres)
    apply clarsimp
    apply (erule u_t_ptrE, simp_all)
     apply clarsimp
     apply (frule uval_typing_record_length)
     apply (frule uval_typing_record_uval_repr_deep)
     apply (clarsimp simp: uval_fields_xs_split take_map[symmetric])
     apply (clarsimp simp: list_all2_conv_all_nth o_def Product_Type.split_def
                           drop_map
                    dest!: map_eq_map_list_all2[THEN iffD1])

    apply clarsimp
    apply (frule uval_typing_record_length)
    apply (frule uval_typing_record_uval_repr_deep)
    apply (clarsimp simp: uval_fields_xs_split take_map[symmetric])
    apply (clarsimp simp: list_all2_conv_all_nth o_def Product_Type.split_def
                          drop_map
                   dest!: map_eq_map_list_all2[THEN iffD1])
    done
next
  case u_sem_struct
  from u_sem_struct.prems show ?case
    apply (clarsimp split: option.split_asm repr.split_asm elim!: typing_structE)
    apply (frule u_sem_struct.hyps[simplified], simp, blast, simp)
    apply (clarsimp simp: map_zip_takes uval_fields_xs_eq_concat)
    done
next
  case u_sem_put
  from u_sem_put.prems show ?case
    apply (clarsimp split: option.split_asm repr.split_asm elim!: typing_putE)
    apply (drule(1) split_simple_weakening)
    apply (drule u_sem_put.hyps[simplified], simp, blast, simp)
    apply (drule u_sem_put.hyps[simplified], simp, blast, simp)
    apply clarsimp
    done
next
  case u_sem_put_ub
  from u_sem_put_ub.prems show ?case
    apply (clarsimp split: option.split_asm repr.split_asm elim!: typing_putE)
    apply (drule(1) split_simple_weakening)
    apply (drule u_sem_put_ub.hyps[simplified], simp, blast, simp)
    apply (drule u_sem_put_ub.hyps[simplified], simp, blast, simp)
    apply (case_tac s, simp_all)[1]
    apply (clarsimp simp: list_all2_conv_all_nth uval_fields_xs_update
                          take_map drop_map map_update
      dest!: map_eq_map_list_all2[THEN iffD1]
      intro!: list_helper)
    apply (metis fst_conv)
    done
next
  case u_sem_all_cons from u_sem_all_cons.prems show ?case
    apply (clarsimp split: option.split_asm elim!: typing_all_consE)
    apply (drule(1) split_simple_weakening)
    apply (drule u_sem_all_cons.hyps[simplified], simp_all, fastforce)+
    done

qed auto

lemma simple_weakening_matches_ptrs:
  "list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) \<Gamma>0 \<Gamma>
    \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>0 \<langle>rs, ws\<rangle>
    \<Longrightarrow> \<exists>rs' ws'. rs' \<subseteq> rs \<and> ws' \<subseteq> ws \<and> \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>rs', ws'\<rangle>"
  apply (induct arbitrary: \<gamma> rs ws rule: list_all2_induct)
   apply auto[1]
  apply clarsimp
  apply (erule matches_ptrs_consE)
   apply clarsimp
  apply clarsimp
  apply atomize
  apply (elim allE, drule(1) mp)
  apply clarsimp
  apply (erule disjE)
   apply simp
   apply (intro exI conjI[rotated], assumption)
    apply blast
   apply blast
  apply simp
  apply (intro exI conjI[rotated], erule(1) matches_ptrs_some)
  apply auto
  done

lemma accs_of_atom_graph_state_match_weaken:
  "accs_of_atom P x (zip (map fst vars) \<Gamma>) = Some (accs, repr)
    \<Longrightarrow> graph_state_match vars \<Gamma> \<gamma> \<sigma> st
    \<Longrightarrow> \<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma> \<langle>rs, ws\<rangle>
    \<Longrightarrow> \<xi>, \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)
    \<Longrightarrow> \<Xi>, [], \<Gamma>w \<turnstile> x : \<tau>
    \<Longrightarrow> list_all2 (\<lambda>tp tp'. tp' = None \<or> tp' = tp) \<Gamma> \<Gamma>w
    \<Longrightarrow> \<sigma>' = \<sigma> \<and> uval_fields uv = map (\<lambda>acc. acc st) accs
        \<and> uval_repr_deep uv = type_repr \<tau>
        \<and> type_repr \<tau> = repr"
  apply (clarsimp simp: graph_state_match_def)
  apply (frule(1) simple_weakening_matches_ptrs, clarsimp)
  apply (drule accs_of_atom_sem[where st'=st], simp)
     apply (clarsimp simp: list_all2_conv_all_nth var_fields_tup_def
                           Product_Type.split_def)
     apply (drule spec, drule(1) mp)+
     apply (rule ccontr, clarsimp)
     apply (fastforce dest: matches_ptrs_proj_single' type_repr_uval_repr_deep)[1]
    apply (rule_tac x=\<Gamma>w in exI, fastforce simp: ctx_wf)
   apply simp+
  done

lemmas accs_of_atom_graph_state_match
    = accs_of_atom_graph_state_match_weaken[where \<Gamma>=\<Gamma> and \<Gamma>w=\<Gamma>,
        simplified list_all2_same, simplified]
    for \<Gamma>

lemma accs_of_atom_tt_sem:
  "accs_of_atom P x (zip (map fst vars) (snd \<Gamma>)) = Some (accs, repr)
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> \<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)
    \<Longrightarrow> \<sigma>' = \<sigma> \<and> uval_fields uv = map (\<lambda>acc. acc st) accs
        \<and> repr = uval_repr_deep uv"
  apply (erule u_tt_sem_pres.cases, simp_all, clarsimp)
  apply (drule(4) accs_of_atom_graph_state_match)
  apply simp
  done

lemma graph_state_match_ttsplit_inner:
  "graph_state_match vars \<Gamma> \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit_inner Kn sps wk \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> graph_state_match vars \<Gamma>1 \<gamma> \<sigma> st
        \<and> graph_state_match vars \<Gamma>2 \<gamma> \<sigma> st"
  by (clarsimp simp: graph_state_match_def ttsplit_def ttsplit_inner_def)

lemma graph_state_match_ttsplit_Nil:
  "graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit Kn \<Gamma> sps [] \<Gamma>1 ys \<Gamma>2
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>1) \<gamma> \<sigma> st"
  "graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit Kn \<Gamma> sps xs \<Gamma>1 [] \<Gamma>2
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>2) \<gamma> \<sigma> st"
  by (auto simp: ttsplit_def dest: graph_state_match_ttsplit_inner)

lemma var_acc_var_upd:
  "var_acc nm (var_upd nm' v st) = (if nm = nm' then v else var_acc nm st)"
  by (simp add: var_acc_def var_upd_def split: state.split)

lemma var_acc_save_vals:
  "length nms = length vals \<Longrightarrow> distinct nms
    \<Longrightarrow> var_acc nm (save_vals nms vals st) = (case map_of (zip nms vals) nm
        of None \<Rightarrow> var_acc nm st | Some v \<Rightarrow> v)"
  apply (induct arbitrary: st rule: list_induct2, simp_all add: save_vals_def)
  apply (simp add: var_acc_var_upd cong: option.case_cong)
  apply (clarsimp split: option.split dest!: map_of_SomeD in_set_zip1)
  done

lemma uval_typing_fields_length:
  "\<Xi>, \<sigma> \<turnstile> uv :u \<tau> \<langle>rs, ws\<rangle>
    \<Longrightarrow> length (var_fields' nm \<tau>) = length (uval_fields uv)"
  using type_repr_uval_repr_deep uval_fields_length
  by metis

lemma save_vals_append:
  "length nms = length vs
    \<Longrightarrow> save_vals (nms @ nms2) (vs @ vs2) st
        = save_vals nms2 vs2 (save_vals nms vs st)"
  by (simp add: save_vals_def)

lemma save_vals_commute:
  "set nms \<inter> set nms2 = {}
    \<Longrightarrow> save_vals nms vs (save_vals nms2 vs2 st) = save_vals nms2 vs2 (save_vals nms vs st)"
  apply (simp add: save_vals_def)
  apply (rule fold_commute_apply)
  apply clarsimp
  apply (rule sym, rule fold_commute)
  apply (clarsimp simp: var_upd_def intro!: ext split: state.split)
  apply (auto dest: in_set_zip1)
  done

lemma acc_vars_save_vals:
  "length nms = length vs \<Longrightarrow> distinct nms
    \<Longrightarrow> acc_vars nms (save_vals nms vs st)
        = vs"
  apply (induct rule: list_induct2, simp_all add: acc_vars_def upd_vars_def)
  apply (simp add: var_acc_save_vals)
  apply (erule trans[rotated])
  apply (rule map_cong[OF refl])
  apply (auto split: option.split)
  done

lemma acc_vars_upd_vars:
  "length nms = length accs \<Longrightarrow> distinct nms
    \<Longrightarrow> acc_vars nms (upd_vars (zip nms accs) st)
        = map (\<lambda>acc. acc st) accs"
  by (simp add: upd_vars_def acc_vars_save_vals map_zip_takes)

lemma acc_vars_save_vals_diff:
  "set nms \<inter> set nms' = {}
    \<Longrightarrow> acc_vars nms (save_vals nms' vals st) = acc_vars nms st"
  apply (induct nms, simp_all add: acc_vars_def upd_vars_def save_vals_def)
  apply (rule_tac Q="\<lambda>x. fst x \<in> set nms'" in fold_invariant)
    apply (auto simp: var_acc_var_upd image_def dest: in_set_zip1)
  done

lemma acc_vars_upd_vars_diff:
  "set nms \<inter> fst ` set upds = {}
    \<Longrightarrow> acc_vars nms (upd_vars upds st) = acc_vars nms st"
  unfolding upd_vars_def
  by (rule acc_vars_save_vals_diff, auto)

lemmas var_acc_upd_vars_diff
    = acc_vars_upd_vars_diff[where nms="[nm]" for nm, unfolded acc_vars_def, simplified]

lemma zip_eq_map:
  "zip xs ys = map (\<lambda>i. (xs ! i, ys ! i)) [0 ..< min (length xs) (length ys)]"
  by (clarsimp simp: list_eq_iff_nth_eq)

lemma naming_scheme_glom:
  "naming_scheme nm i xs @ CHR ''.'' # ys
    = naming_scheme nm i (xs @ [ys])"
  by (cases xs, simp_all add: naming_scheme_def)

lemma record_field_names_extended_inj:
  "record_field_names i @ concat (map (op # CHR ''.'') xs)
     = record_field_names j @ concat (map (op # CHR ''.'') ys)
    \<Longrightarrow> i = j \<and> concat (map (op # CHR ''.'') xs) = concat (map (op # CHR ''.'') ys)"
  apply (drule append_cut[where x="CHR ''.''"])
      apply (cases xs, simp_all)
     apply (cases ys, simp_all)
    apply (clarsimp simp: record_field_names_def dest!: set_dec[THEN subsetD])
   apply (clarsimp simp: record_field_names_def dest!: set_dec[THEN subsetD])
  apply (clarsimp simp: record_field_names_def dest!: inj_dec_lemma[rule_format])
  done

lemma distinct_var_fields_naming:
  assumes nm: "set nm \<inter> set ''.@'' = {}"
  shows
  "distinct (var_fields (naming_scheme nm i xs) repr)
    \<and> set (var_fields (naming_scheme nm i xs) repr) \<subseteq> {zs. \<exists>ys. zs = naming_scheme nm i (xs @ ys)}"
  "distinct (var_fields_xs n (naming_scheme nm i xs) reprs)
    \<and> set (var_fields_xs n (naming_scheme nm i xs) reprs)
        \<subseteq> {zs. \<exists>j ys. j \<ge> n \<and> zs = naming_scheme nm i (xs @ [record_field_names j] @ ys)}"
proof (induct repr and reprs arbitrary: xs and n xs)
  case (RProduct r1 r2)
  thus ?case
    apply (clarsimp simp: naming_scheme_glom)
    apply (auto dest!: RProduct.hyps[THEN conjunct2, THEN subsetD]
                       naming_scheme_inj[OF _ nm nm])
    done
next
  case (Cons_repr3 r rs)
  thus ?case
    apply (clarsimp simp: naming_scheme_glom)
    apply (auto simp: naming_scheme_inj_eq[OF nm nm]
                dest!: Cons_repr3.hyps[THEN conjunct2, THEN subsetD]
                       record_field_names_extended_inj
               )
     apply (metis order_refl)
    apply (metis Suc_leD)
    done
qed (simp_all add: exI[where x=Nil], fastforce)

lemma distinct_var_fields_naming2:
  "set nm \<inter> set ''.@'' = {}
    \<Longrightarrow> distinct (var_fields_tup (naming_scheme nm i xs, r))"
  by (simp_all add: distinct_var_fields_naming var_fields_tup_def)

lemma distinct_var_fields_opt:
  "set nm \<inter> set ''.@'' = {}
    \<Longrightarrow> distinct (var_fields_opt (naming_scheme nm i xs, \<tau>))"
  by (cases \<tau>, simp_all add: distinct_var_fields_naming)

lemma set_var_fields_naming_scheme:
  "set nm \<inter> set ''.@'' = {}
    \<Longrightarrow> set (var_fields_tup (naming_scheme nm i as, r))
        \<subseteq> {xs. \<exists>ys. xs = naming_scheme nm i (as @ ys)}"
  by (simp_all add: var_fields_tup_def distinct_var_fields_naming)

lemma distinct_naming_var_fields:
  "\<not> (nm, i) = (nm', j) \<Longrightarrow> set nm \<inter> set ''.@'' = {}
    \<Longrightarrow> set nm' \<inter> set ''.@'' = {}
    \<Longrightarrow> set (var_fields_tup (naming_scheme nm i as, r))
    \<inter> set (var_fields_tup (naming_scheme nm' j cs, r')) = {}"
  apply (rule ccontr, clarsimp elim!: nonemptyE)
  apply (drule subsetD[OF set_var_fields_naming_scheme, rotated], simp)+
  apply (auto dest: naming_scheme_inj)
  done

lemma mem_naming_scheme:
  "(naming_scheme nm i ys = ''Mem'')
    = (nm = ''Mem'' \<and> i = None \<and> ys = [])"
  apply (rule iffI[rotated], simp_all add: naming_scheme_def)
  apply (cases i, simp_all)
   apply (cases ys, simp_all)
   apply (drule_tac f="\<lambda>xs. CHR ''.'' \<in> set xs" in arg_cong)
   apply simp
  apply (drule_tac f="\<lambda>xs. CHR ''@'' \<in> set xs" in arg_cong)
  apply simp
  done

lemmas mem_naming_schemes[simp]
    = mem_naming_scheme mem_naming_scheme[THEN trans[OF eq_commute]]

lemma naming_cond_distinct':
  "naming_cond' (map fst vars) N \<Longrightarrow> ''Mem'' \<notin> set (map fst vars)
    \<Longrightarrow> distinct (concat (map var_fields_tup vars) @ [''Mem''])"
  apply (clarsimp simp: naming_cond'_def)
  apply (induct vars)
   apply simp
  apply (clarsimp simp: distinct_var_fields_naming2)
  apply (simp only: Int_UN_distrib UNION_empty_conv)
  apply (intro conjI ballI)
   apply clarsimp
   apply (frule(1) bspec, erule exE)
   apply clarsimp
   apply (rule distinct_naming_var_fields)
     apply (auto simp: image_def)[3]
  apply (auto dest: set_var_fields_naming_scheme[THEN subsetD, rotated])
  done

lemma naming_cond_distinct:
  "naming_cond (map fst vars) N
    \<Longrightarrow> distinct (concat (map var_fields_tup vars) @ [''Mem''])"
  unfolding naming_cond_def
  apply (rule naming_cond_distinct', assumption)
  apply (clarsimp simp: naming_cond'_def)
  apply (auto dest: set_var_fields_naming_scheme[THEN subsetD, rotated])
  done

lemma graph_state_match_extend_argument':
  "graph_state_match vars \<Gamma> \<gamma> \<sigma> st
    \<Longrightarrow> vals = uval_fields new_v
    \<Longrightarrow> distinct (concat (map var_fields_tup ((new_nm, r') # vars)) @ [''Mem''])
    \<Longrightarrow> length (uval_fields new_v) = length (var_fields new_nm r)
    \<Longrightarrow> r = type_repr t
    \<Longrightarrow> r' = r
    \<Longrightarrow> graph_state_match ((new_nm, r') # vars) (Some t # \<Gamma>) (new_v # \<gamma>)
        \<sigma> (save_vals (var_fields new_nm r) vals st)"
  apply (clarsimp simp: graph_state_match_def)
  apply (clarsimp simp: forall_less_Suc_eq var_fields_tup_def)
  apply (subst acc_vars_save_vals, simp_all)
  apply (rule conjI)
   apply (clarsimp simp: heap_rel_def mem_def var_mem_def var_acc_save_vals)
   apply (auto split: option.split dest: in_set_zip1)[1]
  apply (clarsimp simp: var_fields_opt_def Product_Type.split_def)
  apply (subst acc_vars_save_vals_diff, simp_all)
  apply (clarsimp simp: acc_vars_def)
  apply (simp only: Int_UN_distrib UNION_empty_conv)
  apply (drule bspec, rule_tac n=i in nth_mem, simp)+
  apply (case_tac "vars ! i", simp add: Int_commute)
  done

lemmas graph_state_match_extend_argument
    = graph_state_match_extend_argument'[OF _ _ naming_cond_distinct]

lemma naming_cond_extend_argument':
  "naming_cond' vars Ns
    \<Longrightarrow> naming_cond' new_nms Ns'
    \<Longrightarrow> Ns \<inter> Ns' = {}
    \<Longrightarrow> Ns \<union> Ns' \<subseteq> Ns''
    \<Longrightarrow> naming_cond' (new_nms @ vars) Ns''"
  apply (clarsimp simp: naming_cond'_def ball_Un)
  apply safe
    apply (drule(1) bspec)+
    apply (auto simp: naming_scheme_inj_eq)[1]
   apply blast
  apply (drule(1) bspec)+
  apply clarsimp
  apply (intro exI conjI[rotated], simp+, blast)
  done

lemma naming_cond_extend_argument:
  "naming_cond vars {..< N}
    \<Longrightarrow> naming_cond new_nms {n}
    \<Longrightarrow> N \<le> n
    \<Longrightarrow> naming_cond (new_nms @ vars) {..< Suc n}"
  unfolding naming_cond_def
  by (auto elim: naming_cond_extend_argument')

lemmas naming_cond_extend1_argument
    = naming_cond_extend_argument[where new_nms="[new_nm]" for new_nm, simplified]

lemma naming_cond_drop:
  "naming_cond vars N
    \<Longrightarrow> naming_cond (drop n vars) N"
  by (clarsimp simp: naming_cond_def naming_cond'_def dest!: in_set_dropD)

lemma graph_state_match_memupd_argument:
  "graph_state_match vars \<Gamma> args \<sigma> st
    \<Longrightarrow> heap_rel \<sigma>' (save_vals [''Mem''] m st)
    \<Longrightarrow> naming_cond (map fst vars) N
    \<Longrightarrow> graph_state_match vars \<Gamma> args \<sigma>' (save_vals [''Mem''] m st)"
  apply (frule naming_cond_distinct)
  apply (clarsimp simp: graph_state_match_def)
  apply (auto simp add: in_set_zip acc_vars_save_vals_diff)
  done

lemma length_var_fields_const:
  "length (var_fields nm repr) = length (var_fields nm' repr)"
  "length (var_fields_xs n nm reprs) = length (var_fields_xs n' nm' reprs)"
  using length_var_fields_const1 length_var_fields_const2
    nat.nchotomy list.nchotomy
  by metis+

lemma sublist_take_all:
  "{..< length xs} \<subseteq> St \<Longrightarrow> sublist xs St = xs"
proof (induct xs arbitrary: St)
  case Nil show ?case by simp
next
  case (Cons x xs) from Cons.prems show ?case
    by (auto simp add: sublist_Cons intro!: Cons.hyps)
qed

lemma sublist_take_none:
  "{..< length xs} \<inter> St = {} \<Longrightarrow> sublist xs St = []"
proof (induct xs arbitrary: St)
  case Nil show ?case by simp
next
  case (Cons x xs) from Cons.prems show ?case
    by (auto simp add: sublist_Cons intro!: Cons.hyps)
qed

lemma ttsplit_inner_set_names_sublist:
  "ttsplit_inner Kn sps wk \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> (\<exists>k. concat (map var_fields_opt (zip vars \<Gamma>1))
        = sublist (concat (map var_fields_opt (zip vars \<Gamma>))) k)
    \<and> (\<exists>k. concat (map var_fields_opt (zip vars \<Gamma>2))
        = sublist (concat (map var_fields_opt (zip vars \<Gamma>))) k)"
proof (induct \<Gamma> arbitrary: \<Gamma>1 \<Gamma>2 sps vars)
  case Nil thus ?case by (clarsimp simp: ttsplit_inner_def)
next
  case (Cons t \<Gamma> \<Gamma>1 \<Gamma>2 sps vars)

  have subl:
    "\<And>xs ys zs k. \<exists>k'. xs @ sublist ys k = sublist (xs @ ys) k'"
    apply (clarsimp simp: sublist_append)
    apply (rule_tac x="{j. j < length xs \<or> j - length xs \<in> k}" in exI)
    apply simp
    apply (rule sublist_take_all[symmetric], clarsimp)
    done

  have subl_none:
    "\<And>xs ys zs k. \<exists>k'. sublist ys k = sublist (xs @ ys) k'"
    apply (clarsimp simp: sublist_append)
    apply (rule_tac x="{j. j \<ge> length xs \<and> j - length xs \<in> k}" in exI)
    apply simp
    apply (rule sublist_take_none, auto)
    done

  from Cons(2)
  obtain t' t'' \<Gamma>1' \<Gamma>2' sp sps' where "\<Gamma>1 = t' # \<Gamma>1'" and "\<Gamma>2 = t'' # \<Gamma>2'"
    and "sps = sp # sps'"
    and "ttsplit_inner Kn sps' wk \<Gamma> \<Gamma>1' \<Gamma>2'" and "ttsplit_inner Kn [sp] wk [t] [t'] [t'']"
    by (clarsimp simp: ttsplit_inner_def length_Suc_conv forall_less_Suc_eq)

  thus ?case
    apply (cases vars, simp_all, clarsimp)
    apply (drule_tac vars=list in Cons(1))
    apply (auto simp: ttsplit_inner_def intro!: subl subl_none)
    done
qed

lemma graph_chunkD2_helper:
  "\<exists>st' i. tr i = Some [(R, st', gfun_name)]
        \<and> graph_state_match ((''ret'', type_repr fin_typ) # vars) (Some fin_typ # ns) (finv # args) hp' st'
    \<Longrightarrow> \<exists>st' i. tr i = Some [(R, st', gfun_name)]
        \<and> graph_state_match ((''ret'', type_repr fin_typ) # drop dn vars) (Some fin_typ # drop dn ns) (finv # drop dn args) hp' st'"
  apply (clarsimp simp: graph_state_match_def forall_less_Suc_eq)
  apply (intro exI conjI, assumption, simp_all)
  done

lemmas graph_chunkD2 = graph_chunkD[THEN graph_chunkD2_helper]

lemma graph_chunk_Let_App:
  assumes rel: "relates GGamma fname (args, inp_typ, out_typ) cfun2"
      "ttyping \<Xi> [] (TT, [Some inp_typ]) cfun2 out_typ"
      "function_inputs gfun2 = (var_fields' ''a@0'' inp_typ @ [''Mem''])"
      "function_outputs gfun2 = (var_fields' ''ret'' out_typ @ [''Mem''])"
  assumes facts:
    "GGamma gfun_name = Some gfun"
    "function_graph gfun n = Some (Call (NextNode n') fname call_args call_rets)"
    "GGamma fname = Some gfun2"
    "length args = length (function_inputs gfun2)"
    "accs_of_atom False arg (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>)))) = Some (accs, repr)"
    "call_args = accs @ [var_acc ''Mem'']"
    "call_rets = var_fields' new_nm out_typ @ [''Mem'']"
    "N \<le> n" "naming_cond new_nms {n}" "new_nms = [new_nm]"
    "graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name ((new_nm, type_repr out_typ) # vars) y n' fin_ty (Suc n) R"
  shows "graph_chunk GGamma \<Gamma> gfun_name vars (Let (App (Fun cfun2 []) arg) y) n fin_ty N R"
proof -

  note preservation = preservation(1)[where \<tau>s=Nil and K=Nil,
    OF _ ctx_wf(1) _ ctx_wf(2), simplified]

  { fix x \<sigma> \<sigma>' y st i args tr Kn sps \<Gamma>1 \<Gamma>2
    assume inner_prems: "\<xi>, [x] \<turnstile> (\<sigma>, cfun2) \<Down>! (\<sigma>', y)"
       "uval_fields x = map (\<lambda>acc. acc st) accs"
       "trace_drop_n i 1 tr \<in> exec_trace GGamma fname"
       "trace_drop_n i 1 tr 0 = Some [(NextNode (entry_point gfun2),
          init_vars (function_inputs gfun2) (accs @ [var_acc ''Mem'']) st, fname)]"
       "y \<notin> set args \<or> True \<Longrightarrow> graph_state_match vars (snd \<Gamma>) args \<sigma> st"
       "naming_cond (map fst vars) {..< N}"
       "ttsplit_inner Kn sps True (snd \<Gamma>) \<Gamma>1 \<Gamma>2"
       "\<exists>rs ws. \<Xi>, \<sigma> \<turnstile> x :u inp_typ \<langle>rs, ws\<rangle>"

    from inner_prems have matches_ptrs:
      "\<exists>rs ws. \<Xi>, \<sigma> \<turnstile> [x] matches [Some inp_typ] \<langle>rs, ws\<rangle>"
      using matches_ptrs_some matches_ptrs.matches_ptrs_empty
      by fastforce

    from inner_prems have len: "length (var_fields' ''a@0'' inp_typ) = length accs"
      by (clarsimp simp add: uval_typing_fields_length)

    have nc: "naming_cond (map fst [(''a@0'', type_repr inp_typ)]) {..< 1}"
      by (simp add: naming_cond_def naming_cond'_def naming_scheme_def
                    Bex_def[symmetric])
    note ncd = naming_cond_distinct[OF nc]

    have nc': "naming_cond (new_nm # map fst vars) {..< Suc n}"
      using naming_cond_extend1_argument inner_prems facts
      by metis

    from inner_prems len ncd have init:
      "graph_state_match [(''a@0'', type_repr inp_typ)] [None] [x] \<sigma>
        (init_vars (function_inputs gfun2) (accs @ [var_acc ''Mem'']) st)"
      apply (clarsimp simp: graph_state_match_def rel init_vars_def
                            heap_rel_def mem_def var_mem_def save_vals_append)
      apply (clarsimp simp: var_acc_save_vals acc_vars_save_vals_diff
                            acc_vars_save_vals var_fields_tup_def)
      done

    hence exec: "\<exists>st'. trace_end (trace_drop_n i 1 tr) = Some [(Ret, st', fname)] \<and>
                 graph_state_match [(''ret'', type_repr out_typ)] [None] [y] \<sigma>' st'"
      using rel matches_ptrs inner_prems
      apply (clarsimp simp: relates_def)
      apply (elim allE, drule mp, (erule conjI)+)
       apply blast
      apply (metis exec_cogent_unique_wrapper)
      done

    hence return: "\<exists>st'. trace_end (trace_drop_n i 1 tr) = Some [(Ret, st', fname)] \<and>
                 graph_state_match ((new_nm, type_repr out_typ) # vars) (Some out_typ # \<Gamma>2) (y # args) \<sigma>'
                   (return_vars (function_outputs gfun2)
                       (var_fields new_nm (type_repr out_typ) @ [''Mem'']) st' st)"
      using inner_prems nc' rel(3-) matches_ptrs
      apply (clarsimp simp: return_vars_def acc_vars_def)
      apply (frule(1) graph_state_match_ttsplit_inner, clarsimp)
      apply (simp add: save_vals_append length_var_fields_const)
      apply (frule preservation[rotated],
          (rule ttyping_imp_typing rel facts ctx_wf | simp)+)
      apply (rule graph_state_match_memupd_argument,
          erule graph_state_match_extend_argument, simp_all)
        apply (clarsimp simp: graph_state_match_def heap_rel_def mem_def
                              var_mem_def acc_vars_def var_fields_tup_def)
       apply (clarsimp simp: uval_typing_fields_length)
      apply (clarsimp simp: graph_state_match_def heap_rel_def mem_def
                              var_mem_def var_acc_save_vals)
      done
  }
  note inner = this

  show ?thesis using facts
    apply (clarsimp intro!: graph_chunkI)
    apply (erule u_tt_sem_pres.cases, simp_all)
     apply (clarsimp simp: composite_anormal_expr_def)
    apply (frule split_follow_typing_tree)
    apply (clarsimp simp: Pair_fst_snd_eq)
    apply (erule u_tt_sem_pres.cases[where ?a7.0="(\<sigma>, App f x)" for \<sigma> f x], simp_all)
    apply (erule u_sem.cases, simp_all, clarsimp)
     apply (auto elim: u_sem.cases)[1]
    apply clarsimp
    apply (erule u_sem.cases[where ?a3.0="(\<sigma>, Fun f ts)" for \<sigma> f ts], simp_all)
    apply (erule typing_appE, clarsimp)
    apply (clarsimp simp: Pair_fst_snd_eq)
    apply (frule accs_of_atom_graph_state_match_weaken)
         apply (erule(1) graph_state_match_ttsplit_Nil)
        apply assumption+
     apply (erule split_simple_weakening[where \<Gamma>0=v and \<Gamma>=v for v, THEN conjunct2])
     apply (simp add: list_all2_same)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (frule(2) preservation[where e=arg, rotated])
    apply (clarsimp simp: ttsplit_def Pair_fst_snd_eq)
    apply (erule typing_funE, clarsimp)
    apply (frule(4) exec_trace_drop_n)
    apply (frule(4) trace_drop_n_init)
    apply (drule(6) inner)
sorry (* multiple types for function body issue
     apply blast
    apply clarsimp
    apply (frule(5) trace_end_trace_drop_n_Some, clarsimp)
    apply (frule(2) graph_chunkD, simp_all)
  done
*)
qed

lemma graph_state_match_ttsplit_triv:
  "graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit_triv \<Gamma> [] \<Gamma>1 ys \<Gamma>2
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>1) \<gamma> \<sigma> st"
  "graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit_triv \<Gamma> xs \<Gamma>1 [] \<Gamma>2
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>2) \<gamma> \<sigma> st"
  by (auto simp: graph_state_match_def ttsplit_triv_def)

lemma forall_less_sum_conv:
  "(\<forall>i < n + (m :: nat). P i) = ((\<forall>i < n. P i) \<and> (\<forall>i < m. P (n + i)))"
  by (induct m, auto simp add: all_less_Suc_eq)

lemma graph_chunk_Let:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> new_tt_types \<Gamma> = [Some new_t]
    \<Longrightarrow> new_names = [new_nm]
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>)))) = Some (accs, repr)
    \<Longrightarrow> length accs = length (var_fields' new_nm new_t)
    \<Longrightarrow> upds = zip (var_fields' new_nm new_t) accs
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((new_nm, type_repr new_t) # vars) y n' fin_ty (Suc n) R
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Let x y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (erule u_tt_sem_pres.cases, simp_all)
   apply (clarsimp simp: composite_anormal_expr_def)
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq)
  apply (frule(1) naming_cond_extend1_argument, simp)
  apply (frule(1) graph_state_match_ttsplit_Nil(1))
  apply (drule(2) accs_of_atom_tt_sem)
  apply (clarsimp simp: K_def ttsplit_def upd_vars_def)
  apply (frule(1) graph_state_match_ttsplit_inner, clarsimp)
  apply (drule(2) graph_chunkD2[where i="Suc i" and dn = 1 for i,
          where args = "arg # args" for arg args])
     apply (simp, erule graph_state_match_extend_argument,
            simp_all add: map_zip_takes)
  done

lemma graph_state_match_ttsplit_bang_nilkind:
  "graph_state_match vars (snd \<Gamma>) \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit_bang is sps [] \<Gamma> [] \<Gamma>1 ys \<Gamma>2
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> (\<exists>k. [] \<turnstile>  t :\<kappa>  k)
    \<Longrightarrow> graph_state_match vars (snd \<Gamma>1) \<gamma> \<sigma> st"
  apply (simp_all add: graph_state_match_def ttsplit_bang_def ttsplit_bang_inner_def)
  apply (safe | simp_all)+
     apply (case_tac "\<Gamma>b ! i", simp_all)
     apply (drule_tac x=a in spec, drule mp, metis nth_mem)
     apply (clarsimp simp: bang_type_repr)
     apply auto
  done

lemma graph_state_match_ttsplit_bang_inner:
  "graph_state_match vars \<Gamma> \<gamma> \<sigma> st
    \<Longrightarrow> ttsplit_bang_inner Kn sps \<Gamma> \<Gamma>1 \<Gamma>2
    \<Longrightarrow> graph_state_match vars \<Gamma>2 \<gamma> \<sigma> st"
  by (clarsimp simp: ttsplit_bang_inner_def graph_state_match_def)

lemma length_var_acc_fields[simp]:
  "length (var_acc_fields s r)
      = length (var_fields [] r)"
  by (simp add: var_acc_fields_def length_var_fields_const[where nm=s and nm'=Nil])

lemma graph_state_match_LetBang_merge:
  "graph_state_match vars \<Gamma> args hp st
    \<Longrightarrow> graph_state_match ((nm, t) # vars) (optT # ns) (finv # args) hp' st'
    \<Longrightarrow> graph_state_match vars \<Gamma> args hp' st'"
  by (clarsimp simp: graph_state_match_def forall_less_Suc_eq)

lemma graph_chunk_LetBang:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') [])
    \<Longrightarrow> function_graph gfun (Suc n) = Some (Basic (NextNode n'') upds)
    \<Longrightarrow> new_tt_types \<Gamma> = [Some new_t]
    \<Longrightarrow> new_names = [new_nm]
    \<Longrightarrow> upds = zip (var_fields new_nm (type_repr new_t)) (var_acc_fields ''ret'' (type_repr new_t))
    \<Longrightarrow> graph_chunk GGamma (fst (follow_typing_tree \<Gamma>)) gfun_name vars x n' new_t N (NextNode (Suc n))
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((new_nm, type_repr new_t) # vars) y n'' fin_ty (Suc (Suc n)) R
    \<Longrightarrow> naming_cond new_names {Suc n} \<Longrightarrow> N \<le> Suc n
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (LetBang is x y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases upd_vars_def[where upds=Nil]
                        save_vals_def K_def)
  apply (frule u_tt_sem_pres_type_wellformed)
  apply (erule u_tt_sem_pres.cases, simp_all)
   apply (clarsimp simp: composite_anormal_expr_def)
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq)
  apply (drule(2) graph_chunkD, simp_all)
   apply (erule(1) graph_state_match_ttsplit_bang_nilkind)
   apply simp
  apply clarsimp
  apply (frule_tac i=ia in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases K_def upd_vars_def
                        map_zip_takes length_var_fields_const[where nm=new_nm and nm'=Nil])
  apply (frule u_tt_sem_pres_preservation[where \<tau>=new_t, OF _ _ ctx_wf], simp)
  apply (clarsimp dest!: type_repr_uval_repr_deep[symmetric])
  apply (subst(asm) var_acc_fields_is_var_accs)
   apply (clarsimp simp: graph_state_match_def forall_less_Suc_eq
                         acc_vars_def var_fields_tup_def)
  apply (clarsimp simp: ttsplit_bang_def)
  apply (frule(1) naming_cond_extend1_argument, simp)
  apply (drule(1) graph_state_match_LetBang_merge)
  apply (frule(1) graph_state_match_ttsplit_bang_inner)
  apply (drule(2) graph_chunkD2[where dn=1],
    simp_all, erule graph_state_match_extend_argument,
      simp_all add: uval_fields_length_Nil length_var_fields_const)
  done

lemma save_vals_nms_append:
  "length vals = length nms + length nms'
    \<Longrightarrow> distinct (nms @ nms')
    \<Longrightarrow> save_vals (nms @ nms') vals st
        = save_vals nms (take (length nms) vals) (save_vals nms' (drop (length nms) vals) st)"
  apply (clarsimp simp: upd_vars_def save_vals_def zip_append1)
  apply (rule fold_commute_apply)
  apply clarsimp
  apply (rule sym, rule fold_commute)
  apply (clarsimp simp: var_upd_def intro!: ext split: state.split)
  apply (auto dest: in_set_zip1)
  done

lemma upd_vars_zip_append:
  "length accs = length nms + length nms'
    \<Longrightarrow> distinct (nms @ nms')
    \<Longrightarrow> upd_vars (zip (nms @ nms') accs) st = upd_vars (zip nms (take (length nms) (map (\<lambda>acc st'. acc st) accs)))
        (upd_vars (zip nms' (drop (length nms) accs)) st)"
  apply (clarsimp simp: upd_vars_def zip_append1 map_zip_takes)
  apply (subst save_vals_nms_append, simp_all add: take_map o_def)
  done

lemma naming_cond_distinct_wtyps:
  "naming_cond vnames N
    \<Longrightarrow> distinct (concat (map var_fields_tup (zip vnames \<Gamma>)) @ [''Mem''])"
  apply (rule naming_cond_distinct[where N=N])
  apply (simp add: naming_cond_def map_zip_takes)
  apply (simp add: naming_cond'_def)
  apply (auto dest: in_set_takeD)
  done

lemma graph_chunk_Split:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> new_tt_types \<Gamma> = [Some t, Some u]
    \<Longrightarrow> new_names = [t_nm, u_nm]
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>)))) = Some (accs, repr)
    \<Longrightarrow> length accs = length (var_fields' t_nm t) + length (var_fields' u_nm u)
    \<Longrightarrow> upds = zip (var_fields' t_nm t @ var_fields' u_nm u) accs
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((t_nm, type_repr t) # (u_nm, type_repr u) # vars) y n' fin_ty (Suc n) R
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Split x y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (erule u_tt_sem_pres.cases, simp_all)
   apply (clarsimp simp: composite_anormal_expr_def)
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq)
  apply (drule(1) naming_cond_extend_argument, simp)
  apply (frule_tac \<Gamma>="[type_repr t, type_repr u]" in naming_cond_distinct_wtyps)
  apply (frule_tac n=1 and vars="[t_nm, u_nm] @ ?a" in naming_cond_drop)
  apply (frule u_tt_sem_pres_preservation[OF _ _ ctx_wf], simp)
  apply (frule(1) graph_state_match_ttsplit_Nil(1))
  apply (drule(2) accs_of_atom_tt_sem)
  apply (clarsimp simp: K_def ttsplit_def)
  apply (erule u_t_productE)
  apply (frule(1) graph_state_match_ttsplit_inner, clarsimp)
  apply (simp add: upd_vars_def map_zip_takes)
  apply (subst(asm) save_vals_nms_append, simp, (auto simp: var_fields_tup_def)[1])
  apply (simp add: uval_typing_fields_length upd_vars_def map_zip_takes)
  apply (drule(2) graph_chunkD2[where dn=2 and i="Suc i" for i, where args = "tv # uv # args" for tv uv args])
    apply (simp, rule graph_state_match_extend_argument,
      erule graph_state_match_extend_argument,
      simp_all add: uval_typing_fields_length drop_map[symmetric] map_zip_takes
  )
   apply (simp_all add: append_eq_conv_conj drop_map take_map o_def)
  done

lemma graph_chunk_If:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Cond (NextNode n') (NextNode n'') cond)
    \<Longrightarrow> accs_of_atom False cond' (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>)))) = Some (accs, repr)
    \<Longrightarrow> accs = [VarBool o cond]
    \<Longrightarrow> graph_chunk GGamma (fst (follow_typing_tree_triv (snd (follow_typing_tree \<Gamma>)))) gfun_name vars x n' fin_ty N R
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree_triv (snd (follow_typing_tree \<Gamma>)))) gfun_name vars y n'' fin_ty N R
    
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (If cond' x y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (erule u_tt_sem_pres.cases, simp_all)
   apply (clarsimp simp: composite_anormal_expr_def)
  apply (frule split_follow_typing_tree(1))
  apply (frule split_follow_typing_tree(2))
  apply (clarsimp simp: Pair_fst_snd_eq)
  apply (drule accs_of_atom_tt_sem, erule(1) graph_state_match_ttsplit_Nil, simp+)
  apply clarsimp
  apply (drule(1) graph_state_match_ttsplit_Nil(2))
  apply (auto elim: graph_chunkD[where i="Suc i" for i, simplified]
             split: split_if_asm elim: graph_state_match_ttsplit_triv)
  done

lemma var_fields_match_xs_nth:
  "uval_fields_xs flds = acc_vars (var_fields_xs i nm (map (type_repr o fst) \<tau>s)) st
    \<Longrightarrow> map (uval_repr_deep o fst) flds = map (type_repr o fst) \<tau>s
    \<Longrightarrow> ix < length flds
    \<Longrightarrow> uval_fields (fst (flds ! ix)) = acc_vars
        (var_fields (nm @ ''.'' @ record_field_names (i + ix)) (type_repr (fst (\<tau>s ! ix)))) st
        \<and> uval_repr_deep (fst (flds ! ix)) = type_repr (fst (\<tau>s ! ix))"
  apply (induct flds arbitrary: i ix \<tau>s, simp_all)
  apply (clarsimp simp: acc_vars_def)
  apply (subst(asm) append_eq_append_conv)
   apply (simp add: uval_fields_length_Nil)
  apply (case_tac ix, simp_all)
  done

lemma save_record_horror:
  "save_vals
               (take (min (length (var_fields_xs 0 [] (map (uval_repr_deep \<circ> fst) fs)) -
                           length (var_fields_xs 0 [] (take ix (map (uval_repr_deep \<circ> fst) fs))))
                       (length (var_fields [] (uval_repr_deep (fst (fs ! ix))))))
                 (var_fields fld_nm (uval_repr_deep (fst (fs ! ix)))) @
                take (length (var_fields_xs 0 [] (map (uval_repr_deep \<circ> fst) fs)))
                 (var_fields_xs 0 rec_nm (map (uval_repr_deep \<circ> fst) fs)))
               (take (length (var_fields [] (uval_repr_deep (fst (fs ! ix)))))
                 (drop (length (var_fields_xs 0 [] (take ix (map (uval_repr_deep \<circ> fst) fs))))
                   (uval_fields_xs fs)) @
                take (length (var_fields_xs 0 rec_nm (map (uval_repr_deep \<circ> fst) fs)))
                 (uval_fields_xs fs))
               st
      = save_vals (var_fields fld_nm (uval_repr_deep (fst (fs ! ix)))) (uval_fields (fst (fs ! ix)))
          (save_vals (var_fields_xs 0 rec_nm (map (uval_repr_deep o fst) fs)) (uval_fields_xs fs) st)"
  sorry

lemma var_fields_match_xs_nth_Rec:
  "uval_fields_xs flds = acc_vars (var_fields' nm (TRecord \<tau>s Unboxed)) st
    \<Longrightarrow>  RRecord (map (uval_repr_deep \<circ> fst) flds) = type_repr (TRecord \<tau>s Unboxed)
    \<Longrightarrow> ix < length flds
    \<Longrightarrow> uval_fields (fst (flds ! ix)) = acc_vars
        (var_fields (nm @ ''.'' @ record_field_names ix) (type_repr (fst (\<tau>s ! ix)))) st
        \<and> uval_repr_deep (fst (flds ! ix)) = type_repr (fst (\<tau>s ! ix))"
  apply simp
  apply (drule var_fields_match_xs_nth[where ix=ix, unfolded o_def], simp_all add: o_def)
  done

lemma graph_chunk_Take_ub:
  notes type_repr.simps[simp del]
  shows
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>)))) = Some (accs, RRecord rs)
    \<Longrightarrow> new_tt_types \<Gamma> = [Some fty, Some (TRecord fs' Unboxed)]
    \<Longrightarrow> ix < length rs \<and> length fs' = length rs \<and> fs' ! ix = (fty, taken)
    \<Longrightarrow> type_repr (fst (fs' ! ix)) = rs ! ix
    \<Longrightarrow> new_names = [fld_nm, rec_nm]
    \<Longrightarrow> upds = zip (var_fields' fld_nm fty) (take (length (var_fields [] (rs ! ix)))
            (drop (length (var_fields_xs 0 [] (take ix rs))) accs))
        @ zip (var_fields' rec_nm (TRecord fs' Unboxed)) accs
    \<Longrightarrow> type_repr (TRecord fs' Unboxed) = RRecord rs
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((fld_nm, type_repr fty) # (rec_nm, RRecord rs) # vars) y n' fin_ty (Suc n) R
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Take x ix y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases K_def)
  apply (erule u_tt_sem_pres.cases, simp_all)
    apply (clarsimp simp: composite_anormal_expr_def)
   apply (clarsimp simp: ttsplit_def)
  apply clarsimp
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq upd_vars_def map_zip_takes
                        length_var_fields_const take_all[OF eq_imp_le] o_def)
  apply (drule(1) naming_cond_extend_argument, simp)
  apply (frule_tac \<Gamma>="[type_repr fty, RRecord rs]" in naming_cond_distinct_wtyps)
  apply (frule_tac n=1 and vars="[fld_nm, rec_nm] @ ?vs" in naming_cond_drop)
  apply (frule(1) graph_state_match_ttsplit_Nil)
  apply (drule(2) accs_of_atom_tt_sem)
  apply clarsimp
  apply (drule sym[where t="map f accs" for f])
  apply (frule trans[OF _ uval_fields_length_Nil(2),
      OF arg_cong[where f=length]], simp(no_asm_use))
  apply (clarsimp simp: take_map[symmetric] drop_map[symmetric]
                        length_var_fields_const(1)[where nm=fld_nm and nm'=Nil]
                        save_record_horror)
  apply (clarsimp simp: K_def ttsplit_def upd_vars_def map_zip_takes
              simp del: uval_repr_deep.simps)
  apply (frule(1) graph_state_match_ttsplit_inner, clarsimp simp: o_def)
  apply (drule(2) graph_chunkD2[where dn=2 and i="Suc i" for i,
      where args = "x # y # args" for x y args],
    simp, rule graph_state_match_extend_argument,
    erule graph_state_match_extend_argument[where r="RRecord rs" for rs, simplified],
    simp_all add: acc_vars_def length_var_fields_const uval_fields_length_Nil o_def)
  done

lemma length_load_wrapper[simp]:
  "length (load_wrapper ptr r) = length (var_fields [] r)"
  by (simp add: load_wrapper_def)

lemma var_fields_load_match_xs_nth:
  "uval_fields_xs flds = map (\<lambda>acc. acc st) (load_wrapper ptr (RRecord rs))
    \<Longrightarrow> map (uval_repr_deep o fst) flds = rs
    \<Longrightarrow> ix < length flds
    \<Longrightarrow> r = rs ! ix
    \<Longrightarrow> uval_fields (fst (flds ! ix)) = map (\<lambda>acc. acc st)
            (load_wrapper (\<lambda>st. ptr st + of_nat (mem_sz_xs (take ix rs))) r)"
  apply (induct flds arbitrary: ptr ix rs, simp_all)
  apply (clarsimp simp: load_wrapper_def o_def Product_Type.split_def)
  apply (subst(asm) append_eq_append_conv)
   apply (simp add: uval_fields_length)
  apply (case_tac ix, simp_all)
  apply (atomize, clarsimp)
  apply (simp add: var_mem_fields_offs[where ptr="of_nat n" for n]
                   Product_Type.split_def)
  apply (drule spec, drule mp, clarsimp simp: field_simps, rule refl)
  apply (clarsimp simp: field_simps)
  done

lemma graph_state_match_take:
  "graph_state_match vars \<Gamma> args hp st
    \<Longrightarrow> hp p = Some (URecord flds)
    \<Longrightarrow> ix < length flds
    \<Longrightarrow> encode_ptr p = ptr st
    \<Longrightarrow> \<Xi>, hp \<turnstile> UPtr p (RRecord rs) :u TRecord ts Writable \<langle>rset, wset\<rangle>
    \<Longrightarrow> uval_fields (fst (flds ! ix)) = map (\<lambda>acc. acc st)
            (load_wrapper (\<lambda>st. ptr st + of_nat (mem_sz_xs (take ix rs))) (rs ! ix))"
  apply (erule u_t_ptrE, simp_all, clarsimp)
  apply (clarsimp simp: graph_state_match_def)
  apply (frule(1) heap_relD[OF _ _ refl, where hp=hp and st=st])
  apply (frule type_repr_uval_repr_deep)
  apply (rule var_fields_load_match_xs_nth, simp_all)
   apply (simp add: load_wrapper2_def o_def Product_Type.split_def
                    load_wrapper_def)
  apply clarsimp
  done

lemma graph_chunk_Take_b:
  notes type_repr.simps[simp del]
  shows
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>))))
        = Some ([\<lambda>st. VarWord32 (ptr st)], RPtr (RRecord rs))
    \<Longrightarrow> new_tt_types \<Gamma> = [Some fty, Some (TRecord fs' Writable)]
    \<Longrightarrow> ix < length rs \<and> length fs' = length rs \<and> fs' ! ix = (fty, taken)
    \<Longrightarrow> type_repr (fst (fs' ! ix)) = rs ! ix
    \<Longrightarrow> new_names = [fld_nm, rec_nm]
    \<Longrightarrow> type_repr (TRecord fs' Writable) = RPtr (RRecord rs)
    \<Longrightarrow> upds = zip (var_fields' fld_nm fty @ var_fields' rec_nm (TRecord fs' Writable))
        (load_wrapper (\<lambda>st. ptr st +
                of_nat (mem_sz_xs (take ix rs))) (type_repr fty)
            @ [\<lambda>st. VarWord32 (ptr st)])
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((fld_nm, type_repr fty) # (rec_nm, RPtr (RRecord rs)) # vars) y n' fin_ty (Suc n) R
    
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Take x ix y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases K_def)
  apply (erule u_tt_sem_pres.cases, simp_all)
    apply (clarsimp simp: composite_anormal_expr_def)
   prefer 2
   apply (clarsimp simp: ttsplit_def)
  apply clarsimp
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq upd_vars_def map_zip_takes
                        length_var_fields_const take_all[OF eq_imp_le] o_def)
  apply (drule(1) naming_cond_extend_argument, simp)
  apply (frule_tac \<Gamma>="[type_repr fty, RPtr (RRecord rs)]" in naming_cond_distinct_wtyps)
  apply (frule_tac n=1 and vars="[fld_nm, rec_nm] @ ?vs" in naming_cond_drop)
  apply (frule(1) graph_state_match_ttsplit_Nil)
  apply (drule(2) accs_of_atom_tt_sem)
  apply (frule u_tt_sem_pres_preservation[where \<Gamma>="fst follow" for follow],
    (simp add: ctx_wf)+)
  apply (clarsimp simp: K_def ttsplit_def upd_vars_def map_zip_takes)
  apply (frule(2) graph_state_match_take[rotated -1, where ptr=ptr and ix=ix], simp_all)
   apply (auto dest!: arg_cong[where f=length] uval_typing_record_length elim!: u_t_ptrE)[1]
  apply (subst(asm) save_vals_nms_append)
    apply (simp add: length_var_fields_const)
   apply (simp add: var_fields_tup_def)
  apply (simp add: length_var_fields_const[where nm="fld_nm" and nm'=Nil])
  apply (frule(1) graph_state_match_ttsplit_inner, clarsimp simp: o_def)
  apply (drule(2) graph_chunkD2[where dn=2 and i="Suc i" for i, where args = "x # y # args" for x y args],
    simp, rule graph_state_match_extend_argument,
    erule graph_state_match_extend_argument[where r="RPtr p" for p, simplified],
    simp_all add: acc_vars_def length_var_fields_const type_repr.simps)[1]
  done

lemma graph_chunk_Take:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>))))
        = Some (accs, repr)
    \<Longrightarrow> new_tt_types \<Gamma> = [Some fty, Some (TRecord fs' sig)]
    \<Longrightarrow> type_repr (TRecord fs' sig) = repr 
    \<Longrightarrow> ix < length fs' \<and> fs' ! ix = (fty, taken)
    \<Longrightarrow> new_names = [fld_nm, rec_nm]
    \<Longrightarrow> sig = Unboxed \<longrightarrow> upds = zip (var_fields' fld_nm fty) (take (length (var_fields [] (type_repr fty)))
            (drop (length (var_fields_xs 0 [] (take ix (map (type_repr o fst) fs')))) accs))
        @ zip (var_fields' rec_nm (TRecord fs' Unboxed)) accs
    \<Longrightarrow> sig \<noteq> Unboxed \<longrightarrow> (\<exists>ptr. upds = zip (var_fields' fld_nm fty @ var_fields' rec_nm (TRecord fs' Writable))
        (load_wrapper (\<lambda>st. ptr st +
                of_nat (mem_sz_xs (take ix (map (type_repr o fst) fs')))) (type_repr fty)
            @ accs) \<and> accs = [\<lambda>st. VarWord32 (ptr st)])
    \<Longrightarrow> type_repr (TRecord fs sig) = type_repr (TRecord fs' sig)
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((fld_nm, type_repr fty) # (rec_nm, type_repr (TRecord fs' sig)) # vars) y n' fin_ty (Suc n) R
    
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Take x ix y) n fin_ty N R
  "
  apply (cases sig)
    apply (clarsimp intro!: graph_chunkI)
    apply (erule u_tt_sem_pres.cases, auto simp: ttsplit_def composite_anormal_expr_def)[1]
   apply (clarsimp)
   apply (erule_tac ptr=ptr in graph_chunk_Take_b, auto simp: o_def)[1]
  apply clarsimp
  apply (erule graph_chunk_Take_ub, auto simp: o_def)
  done

definition
  save_wrapper :: "word32 \<Rightarrow> variable list \<Rightarrow> repr list \<Rightarrow> (word32 \<Rightarrow> word8) \<Rightarrow> (word32 \<Rightarrow> word8)"
where
  "save_wrapper ptr vs rs m = fold (\<lambda>((ptr, _), v) mem. save_inner ptr v mem)
        (zip (var_mem_fields_xs ptr rs) vs) m"

definition
  save_wrapper2 :: "(state \<Rightarrow> variable) \<Rightarrow> word32
    \<Rightarrow> (state \<Rightarrow> variable) list \<Rightarrow> repr \<Rightarrow> state \<Rightarrow> variable"
where
  "save_wrapper2 ptr offs vs r st = VarMem (save_wrapper
    (case ptr st of VarWord32 addr \<Rightarrow> addr + offs | _ \<Rightarrow> 0) (map (\<lambda>acc. acc st) vs)
    [r] (mem st))"

lemmas split_simple_weakening_single
    = split_simple_weakening[where ?\<Gamma>0.0=\<Gamma> and \<Gamma>=\<Gamma> for \<Gamma>,
        simplified list_all2_same, simplified]

lemmas save_vals_cons_split
    = save_vals_append[where nms="[nm]" and ?nms2.0="nm' # nms"
        and vs="[v]" and ?vs2.0="v' # vs" for nm nm' nms v v' vs, simplified]

lemma type_repr_record_list_update:
  "ix < length fs \<Longrightarrow> fst (fs ! ix) = t
    \<Longrightarrow> type_repr (TRecord (fs [ix := (t, False)]) s)
        = type_repr (TRecord fs s)"
  by (cases s, simp_all add: map_update list_helper)

definition
  "lit_type_of_variable v == case v of
    VarWord8 _ \<Rightarrow> Some (Num U8)
  | VarWord16 _ \<Rightarrow> Some (Num U16)
  | VarWord32 _ \<Rightarrow> Some (Num U32)
  | VarWord64 _ \<Rightarrow> Some (Num U64)
  | VarBool _ \<Rightarrow> Some Bool
  | _ \<Rightarrow> None"

lemma load_save_inner_distinct:
  assumes "lit_type_of_variable v = Some lt"
    "addr_t_dom addr_t \<inter> addr_t_dom (addr, lt) = {}"
  shows "load_inner addr_t (save_inner addr v m) = load_inner addr_t m"
proof -
  obtain xs where xs: "save_inner addr v m = heap_update_list addr xs m"
      "length xs = mem_sz (RPrim lt)"
    using assms
    apply (cases v, simp_all add: lit_type_of_variable_def save_inner_def)
       apply (clarsimp simp: store_word8_def)
       apply (erule_tac x="[word]" in meta_allE, simp)
      apply (auto simp: store_word16_def store_word32_def store_word64_def
                        length_word_rsplit_exp_size' word_size)
    done
  from assms xs show ?thesis
    by (auto simp: load_inner_def load_word16_def addr_t_dom_def
                   load_word32_def load_word64_def load_word8_def
                   heap_list_update_disjoint_same Int_commute
                   length_word_rsplit_exp_size' word_size
                   heap_list_update_disjoint_same[where k="Suc 0", simplified]
            split: prod.split prim_type.split num_type.split)
qed

lemma load_save_inner_same:
  "lit_type_of_variable v = Some t
    \<Longrightarrow> load_inner (addr, t) (save_inner addr v m) = v"
  by (auto simp: load_inner_def save_inner_def lit_type_of_variable_def
                 addr_t_dom_def load_word8_def store_word8_def  
                 load_word16_def store_word16_def load_word32_def store_word32_def
                 load_word64_def store_word64_def
                 heap_list_update_eq addr_card_def card_word
                 length_word_rsplit_exp_size' word_size
                 word_rcat_rsplit
          split: prod.split prim_type.split num_type.split variable.split)

lemma load_save_inner_fold_distinct:
  "map (Some o snd o fst) ys = map (lit_type_of_variable o snd) ys
    \<Longrightarrow> \<forall>((addr, t), v) \<in> set ys. addr_t_dom x \<inter> addr_t_dom (addr, t) = {}
    \<Longrightarrow> load_inner x (fold (case_prod (\<lambda>(ptr, _). save_inner ptr)) ys m)
        = load_inner x m"
  apply (rule_tac P="\<lambda>m. load_inner ?x m = ?v" and Q="\<lambda>x. x \<in> set ys"
      in fold_invariant, simp_all)[1]
  apply clarsimp
  apply (drule(1) bspec, clarsimp)
  apply (subst load_save_inner_distinct, auto)
  done

lemma heap_rel_inner_update_fold:
  "heap_rel_inner \<sigma> m
    \<Longrightarrow> \<sigma> p = Some v
    \<Longrightarrow> uval_repr_deep v' = uval_repr_deep v
    \<Longrightarrow> fst ` set xs \<subseteq> set (var_mem_fields (encode_ptr p) (uval_repr_deep v))
    \<Longrightarrow> map (Some o snd o fst) xs = map (lit_type_of_variable o snd) xs
    \<Longrightarrow> (map (\<lambda>addr. load_inner addr m)
     (var_mem_fields (encode_ptr p) (uval_repr_deep v)) = uval_fields v
        \<Longrightarrow> map (\<lambda>addr. load_inner addr (fold (case_prod (\<lambda>(ptr, _). save_inner ptr)) xs m))
     (var_mem_fields (encode_ptr p) (uval_repr_deep v)) =
    uval_fields v')
    \<Longrightarrow> heap_rel_inner (\<sigma>(p \<mapsto> v')) (fold (\<lambda>((ptr, _), v). save_inner ptr v) xs m)"
  apply (clarsimp simp: heap_rel_inner_def dest!: graph_ofD split: split_if_asm)
   apply (drule bspec, erule graph_ofI, clarsimp)
  apply (drule bspec, erule graph_ofI, clarsimp, erule trans[rotated])
  apply (rule map_cong, simp)
  apply (rule load_save_inner_fold_distinct, simp)
  apply clarsimp
  apply (drule subsetD, erule imageI, clarsimp)
  done

lemma load_save_inner_fold_same:
  "map (Some o snd) xs = map lit_type_of_variable ys
    \<Longrightarrow> distinct_prop (\<lambda>x x'. addr_t_dom x \<inter> addr_t_dom x' = {}) xs
    \<Longrightarrow> map (\<lambda>addr. load_inner addr
        (fold (case_prod (\<lambda>(ptr, _). save_inner ptr)) (zip xs ys) m)) xs = ys"
  apply (frule map_eq_map_list_all2[THEN iffD1])
  apply (rotate_tac 2, induct arbitrary: m rule: list_all2_induct)
   apply simp
  apply clarsimp
  apply (subst load_save_inner_fold_distinct)
    apply (simp add: map_zip_takes list_all2_lengthD)
   apply (auto dest: in_set_zip1)[1]
  apply (simp add: load_save_inner_same)
  done

lemma var_mem_fields_xs_split:
  "ix < length flds
    \<Longrightarrow> var_mem_fields_xs ptr flds
        = var_mem_fields_xs ptr (take ix flds)
            @ var_mem_fields (ptr + of_nat (mem_sz_xs (take ix flds))) (flds ! ix)
            @ var_mem_fields_xs (ptr + of_nat (mem_sz_xs (take (Suc ix) flds))) (drop (Suc ix) flds)"
  apply (induct flds arbitrary: ix ptr)
   apply simp
  apply clarsimp
  apply (case_tac ix)
   apply clarsimp
  apply (clarsimp simp: field_simps)
  done

lemma var_mem_fields_uval_fields_types_agree1:
  "map (Some \<circ> snd)
     (var_mem_fields p (uval_repr_deep (uv :: ('f, 'a, 'l) uval))) =
    map lit_type_of_variable (uval_fields uv)"
  "map (Some \<circ> snd)
     (var_mem_fields_xs p (map (uval_repr_deep o fst) (uvs :: (('f, 'a, 'l) uval \<times> repr) list))) =
    map lit_type_of_variable (uval_fields_xs uvs)"
  "map (Some \<circ> snd)
     (var_mem_fields p (uval_repr_deep (fst uvp))) =
    map lit_type_of_variable (uval_fields_prod (uvp :: (('f, 'a, 'l) uval \<times> repr)))"
  apply (induct uv and uvs and uvp arbitrary: p and p and p,
    simp_all add: lit_of_variable_of_lit image_Un split: Product_Type.prod.split)
     apply (case_tac lit, simp_all add: lit_type_of_variable_def)
  done

lemma var_mem_fields_uval_fields_types_agree2:
  "\<forall>x\<in>set (zip (var_mem_fields p (uval_repr_deep v)) (uval_fields v)).
              Some (snd (fst x)) = lit_type_of_variable (snd x)"
  using map_eq_map_list_all2[THEN iffD1,
    OF var_mem_fields_uval_fields_types_agree1(1)]
  by (fastforce simp: list_all2_iff)

lemmas var_mem_fields_uval_fields_types_agree
    = var_mem_fields_uval_fields_types_agree1 var_mem_fields_uval_fields_types_agree2

lemma intvl_sum:
  "{p ..+ x + y} = ({p ..+ x} \<union> {p + of_nat x ..+ y})"
  apply (simp add: intvl_def, safe, simp_all)
    apply (case_tac "k < x")
     apply blast
    apply (drule_tac x="k - x" in spec)
    apply simp
   apply auto[1]
  apply (rule_tac x="x + k" in exI)
  apply simp
  done

lemma var_mem_fields_uval_fields_dom:
  "\<forall>x\<in>set (var_mem_fields p repr).
    addr_t_dom x \<subseteq> {p ..+ mem_sz repr}"
  "\<forall>x\<in>set (var_mem_fields_xs p reprs).
    addr_t_dom x \<subseteq> {p ..+ mem_sz_xs reprs}"
  apply (induct repr and reprs arbitrary: p and p, simp_all)
      apply (simp add: addr_t_dom_def)
     apply (simp add: addr_t_dom_def)
    apply (simp add: addr_t_dom_def)
   apply (simp add: intvl_sum)
   apply blast
  apply (simp add: intvl_sum)
  apply blast
  done

lemma var_mem_fields_distinct:
  "mem_sz (uval_repr_deep uv) < addr_card
    \<Longrightarrow> distinct_prop (\<lambda>x x'. addr_t_dom x \<inter> addr_t_dom x' = {})
        (var_mem_fields p (uval_repr_deep (uv :: ('f, 'a, 'l) uval)))"
  "mem_sz_xs (map (uval_repr_deep o fst) uvs) < addr_card
    \<Longrightarrow> distinct_prop (\<lambda>x x'. addr_t_dom x \<inter> addr_t_dom x' = {})
     (var_mem_fields_xs p (map (uval_repr_deep o fst) (uvs :: (('f, 'a, 'l) uval \<times> repr) list)))"
  "mem_sz (uval_repr_deep (fst uvp)) < addr_card
    \<Longrightarrow> distinct_prop (\<lambda>x x'. addr_t_dom x \<inter> addr_t_dom x' = {})
     (var_mem_fields p (uval_repr_deep (fst (uvp :: (('f, 'a, 'l) uval \<times> repr)))))"
  apply (induct uv and uvs and uvp arbitrary: p and p and p,
    simp_all add: Product_Type.split_def HOL.Let_def distinct_prop_append)
   apply (clarsimp)
   apply (rule disjoint_subset, erule var_mem_fields_uval_fields_dom[rule_format])
   apply (rule disjoint_subset2, erule var_mem_fields_uval_fields_dom[rule_format])
   apply (subst Int_commute, rule init_intvl_disj)
   apply simp
  apply (clarsimp)
  apply (rule disjoint_subset, erule var_mem_fields_uval_fields_dom[rule_format])
  apply (rule disjoint_subset2, erule var_mem_fields_uval_fields_dom[rule_format])
  apply (subst Int_commute, rule init_intvl_disj)
  apply simp
  done

lemma mem_sz_xs_split:
  "ix < length flds \<Longrightarrow> mem_sz_xs flds = mem_sz_xs (take ix flds)
    + mem_sz (flds ! ix) + mem_sz_xs (drop (Suc ix) flds)"
  apply (induct flds arbitrary: ix)
   apply simp
  apply (case_tac ix, simp_all)
  done

lemma var_fields_xs_append:
  "var_fields_xs n s (rs @ rs') = var_fields_xs n s rs @ var_fields_xs (n + length rs) s rs'"
  by (induct rs arbitrary: n, simp_all)

lemma mem_sz_xs_append:
  "mem_sz_xs (xs @ ys) = mem_sz_xs xs + mem_sz_xs ys"
  by (induct xs, simp_all)

lemma var_mem_fields_load_xs_update:
  "ix < length flds
    \<Longrightarrow> uval_repr_deep (fst (flds ! ix)) = uval_repr_deep v
    \<Longrightarrow> mem_sz_xs (map (uval_repr_deep \<circ> fst) flds) < addr_card
    \<Longrightarrow> map (\<lambda>addr. load_inner addr m) (var_mem_fields_xs p (map (uval_repr_deep \<circ> fst) flds))
        = uval_fields_xs flds
    \<Longrightarrow> map (\<lambda>addr. load_inner addr
                 (fold (case_prod (\<lambda>(ptr, _). save_inner ptr))
                   (zip (var_mem_fields
                          (p +
                           of_nat (mem_sz_xs (take ix (map (uval_repr_deep \<circ> fst) flds))))
                          (uval_repr_deep v))
                     (uval_fields v))
                   m))
     (var_mem_fields_xs p (map (uval_repr_deep \<circ> fst) flds)) =
    uval_fields_xs (flds[ix := (v, snd (flds ! ix))])"
  apply (simp add: uval_fields_xs_update
                   mem_sz_xs_split[where ix=ix and flds="map f flds" for f]
                   var_mem_fields_xs_split[where ix=ix and flds="map f flds" for f])
  apply (drule sym[where t="uval_fields_xs flds"])
  apply (simp add: length_var_mem_fields take_map
                   take_Suc_conv_app_nth var_fields_xs_append)
  apply (intro conjI)
    apply (clarsimp simp: take_map)
    apply (rule load_save_inner_fold_distinct)
     apply (simp add: var_mem_fields_uval_fields_types_agree)
    apply clarsimp
    apply (drule in_set_zip1)
    apply (drule var_mem_fields_uval_fields_dom[rule_format])+
    apply (erule disjoint_subset, erule disjoint_subset2)
    apply (subst Int_commute, rule init_intvl_disj)
    apply simp
   apply (simp add: load_save_inner_fold_same var_mem_fields_uval_fields_types_agree
                    var_mem_fields_distinct)
  apply clarsimp
  apply (rule load_save_inner_fold_distinct)
   apply (simp add: var_mem_fields_uval_fields_types_agree)
  apply (clarsimp simp: mem_sz_xs_append)
  apply (drule in_set_zip1)
  apply (drule var_mem_fields_uval_fields_dom[rule_format])+
  apply (erule disjoint_subset, erule disjoint_subset2)
  apply (rule disjoint_subset[OF _ init_intvl_disj])
   apply (simp add: field_simps, rule order_refl)
  apply simp
  done

lemma heap_rel_inner_offset_update:
  "heap_rel_inner \<sigma> m
    \<Longrightarrow> \<sigma> p = Some (URecord flds)
    \<Longrightarrow> ix < length flds
    \<Longrightarrow> uval_repr_deep v = repr
    \<Longrightarrow> uval_repr_deep (fst (flds ! ix)) = repr
    \<Longrightarrow> fs = map (uval_repr_deep o fst) flds
    \<Longrightarrow> mem_sz_xs (map (uval_repr_deep \<circ> fst) flds) < addr_card
    \<Longrightarrow> heap_rel_inner (\<sigma>(p \<mapsto> URecord (flds[ix := (v, snd (flds ! ix))])))
        (save_wrapper (encode_ptr p + of_nat (mem_sz_xs (take ix fs))) (uval_fields v) [repr] m)"
  apply (clarsimp simp: save_wrapper_def)
  apply (rule heap_rel_inner_update_fold, simp_all)
     apply (clarsimp simp: map_update list_helper)
    apply clarsimp
    apply (drule in_set_zip1)
    apply (clarsimp simp: var_mem_fields_xs_split[where ix=ix])
   apply (simp add: var_mem_fields_uval_fields_types_agree)
  apply simp
  apply (rule var_mem_fields_load_xs_update, simp_all)
  done

lemma graph_chunk_Put:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic (NextNode n') upds)
    \<Longrightarrow> accs_of_atom True x (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>))))
        = Some ([ptr], RPtr (RRecord fs))
    \<Longrightarrow> accs_of_atom True y (zip (map fst vars) (snd (fst (follow_typing_tree \<Gamma>))))
        = Some (yaccs, repr')
    \<Longrightarrow> ix < length fs
    \<Longrightarrow> mem_sz_xs fs < addr_card
    \<Longrightarrow> new_names = [new_nm]
    \<Longrightarrow> upds = (zip (var_fields' new_nm (the (hd (new_tt_types \<Gamma>)))) [ptr]) @
        [(''Mem'', save_wrapper2 ptr (of_nat (mem_sz_xs (take ix fs))) yaccs repr')]
    \<Longrightarrow> naming_cond new_names {n} \<Longrightarrow> N \<le> n
    \<Longrightarrow> graph_chunk GGamma (snd (follow_typing_tree \<Gamma>)) gfun_name
        ((new_nm, RPtr (RRecord fs)) # vars) z n' fin_ty (Suc n) R
    
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Let (Put x ix y) z) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases K_def)
  apply (erule u_tt_sem_pres.cases, simp_all)
   apply (clarsimp simp: composite_anormal_expr_def)
  apply clarsimp
  apply (drule(1) naming_cond_extend1_argument, simp)
  apply (erule u_tt_sem_pres.cases[where ?a7.0="(\<sigma>, Put x ix y)" for \<sigma>], simp_all)
  apply (frule split_follow_typing_tree)
  apply (clarsimp simp: Pair_fst_snd_eq upd_vars_def map_zip_takes
                        length_var_fields_const take_all[OF eq_imp_le] o_def)
  apply (erule typing_putE)
  apply (frule(1) graph_state_match_ttsplit_Nil)
  apply (erule u_sem.cases, simp_all)
   apply clarsimp
   apply (drule(4) accs_of_atom_graph_state_match_weaken)
    apply (simp add: split_simple_weakening_single)
   apply clarsimp
   apply (drule(4) accs_of_atom_graph_state_match_weaken)
    apply (simp add: split_simple_weakening_single)
   apply (frule(1) matches_ptrs_split', clarsimp)
   apply (frule(1) preservation(1)[where e=x and \<tau>s=Nil and K=Nil, simplified, rotated -2],
        rule ctx_wf, simp, rule ctx_wf)
   apply (frule(1) preservation(1)[where e=y and \<tau>s=Nil and K=Nil, simplified, rotated -2],
        rule ctx_wf, simp, rule ctx_wf)
   apply (clarsimp simp: ttsplit_def save_vals_append)
   apply (subst(asm) take_all[where n="Suc 0"])
    apply (case_tac s, simp_all)[1]
   apply (frule(1) graph_state_match_ttsplit_inner)
   apply (clarsimp dest!: sym[where s="RPtr r" for r])
   apply (drule(2) graph_chunkD2[where dn=1], simp_all,
     rule graph_state_match_memupd_argument,
     simp_all, erule graph_state_match_extend_argument,
     simp_all add: type_repr_record_list_update heap_rel_def mem_def
                   var_mem_def var_acc_save_vals)
   apply (drule sym[where t="ptr st" for st])
   apply (drule sym[where t="map f yaccs" for f])
   apply (clarsimp simp: save_wrapper2_def)
   apply (erule u_t_ptrE, simp_all)[1]
   apply clarsimp

   apply (rule heap_rel_inner_offset_update, simp_all add: uval_typing_record_length)
      apply (clarsimp simp: graph_state_match_def heap_rel_def)
     apply (frule uval_typing_record_uval_repr_deep)
     apply (clarsimp simp: list_all2_conv_all_nth
                    dest!: map_eq_map_list_all2[THEN iffD1])
    apply (frule uval_typing_record_uval_repr_deep)
    apply (clarsimp simp: list_all2_conv_all_nth
                   dest!: map_eq_map_list_all2[THEN iffD1])
   apply (frule uval_typing_record_uval_repr_deep)
   apply (clarsimp simp: o_def Product_Type.split_def)

  apply clarsimp
  apply (drule(4) accs_of_atom_graph_state_match_weaken)
   apply (simp add: split_simple_weakening_single)
  apply clarsimp
  done

lemma graph_chunk_App_via_Let:
  "new_names = map (id :: string \<Rightarrow> _) new_names
    \<Longrightarrow> graph_chunk GGamma (TyTrSplit (map (\<lambda>_. Some TSK_L) (snd \<Gamma>)) [] (fst \<Gamma>)
            [Some fin_ty] TyTrLeaf, snd \<Gamma>)
        gfun_name vars (Let (App f x) (Var 0)) n fin_ty N R
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (App f x) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (drule let_elaborate_u_tt_sem_pres, simp_all add: ctx_wf)
  apply (erule graph_chunkD[rotated -1, simplified], simp_all)
  done

lemma graph_chunk_Put_via_Let:
  "new_names = map (id :: string \<Rightarrow> _) new_names
    \<Longrightarrow> graph_chunk GGamma (TyTrSplit (map (\<lambda>_. Some TSK_L) (snd \<Gamma>)) [] (fst \<Gamma>)
            [Some fin_ty] TyTrLeaf, snd \<Gamma>)
        gfun_name vars (Let (Put x ix y) (Var 0)) n fin_ty N R
    \<Longrightarrow> graph_chunk GGamma \<Gamma> gfun_name vars (Put x ix y) n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (drule let_elaborate_u_tt_sem_pres, simp_all add: ctx_wf)
  apply (erule graph_chunkD[rotated -1, simplified], simp_all)
  done

lemma naming_cond_ret:
  "naming_cond' [''ret''] {None}"
  by (simp add: naming_cond'_def naming_scheme_def)

lemma naming_cond_final:
  "naming_cond (map fst vars) St
    \<Longrightarrow> naming_cond' (map fst ((''ret'', repr) # vars)) UNIV \<and> ''Mem'' \<notin> set (map fst vars)"
  apply (frule_tac \<Gamma>="map (K (RPtr RUnit)) vars" in naming_cond_distinct_wtyps)
  apply (clarsimp simp: naming_cond_def)
  apply (frule naming_cond_extend_argument'[OF _ naming_cond_ret _ subset_UNIV])
   apply auto[1]
  apply (simp only: zip_map2 zip_same zip_map1)
  apply (auto simp: o_def K_def var_fields_tup_def)
  done

lemma graph_chunk_final_atom:
  "GGamma gfun_name = Some gfun
    \<Longrightarrow> function_graph gfun n = Some (Basic R upds)
    \<Longrightarrow> accs_of_atom False x (zip (map fst vars) \<Gamma>) = Some (accs, repr)
    \<Longrightarrow> new_names = [new_nm]
    \<Longrightarrow> upds = (zip (var_fields' ''ret'' fin_ty) accs)
    \<Longrightarrow> graph_chunk GGamma (TyTrLeaf, \<Gamma>) gfun_name vars x n fin_ty N R
  "
  apply (clarsimp intro!: graph_chunkI)
  apply (drule(2) accs_of_atom_tt_sem[where \<Gamma>="(TyTrLeaf, \<Gamma>)", simplified])
  apply (frule_tac i=i in exec_trace_step_cases, clarsimp)
  apply (clarsimp simp: all_exec_graph_step_cases K_def)
  apply (drule sym[where t="map f accs" for f])
  apply (frule arg_cong[where f=length and x="map f accs" for f], simp(no_asm_use))
  apply (frule u_tt_sem_pres_preservation[OF _ _ ctx_wf], simp)
  apply (clarsimp simp: all_exec_graph_step_cases)
  apply (intro exI conjI, assumption)
  apply (drule type_repr_uval_repr_deep)
  apply (clarsimp simp: upd_vars_def map_zip_takes take_map[symmetric]
                        uval_fields_length_Nil)
  apply (drule_tac repr="type_repr fin_ty" in naming_cond_final, elim conjE)
  apply (frule naming_cond_distinct', simp)
  apply (rule graph_state_match_extend_argument',
    simp_all add: uval_fields_length_Nil graph_state_match_def)
  done

end

end

