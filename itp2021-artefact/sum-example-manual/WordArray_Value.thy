theory WordArray_Value
  imports WordArray_Abstractions

begin

context WordArray begin

type_synonym ('f, 'a) vfoldmapdef = "(char list, vatyp) vabsfuns \<Rightarrow> type \<Rightarrow> ('f, 'a) vval list \<Rightarrow> nat \<Rightarrow> 
                                      nat \<Rightarrow> 'f expr \<Rightarrow> ('f, 'a) vval \<Rightarrow> ('f, 'a) vval \<Rightarrow> 
                                      ('f, 'a) vval \<Rightarrow> bool"

section wordarray_length

definition val_wa_length
  where
  "val_wa_length x y = (\<exists>xs len t. x = VAbstract (VWA (TPrim (Num t)) xs) \<and> y = VPrim (LU32 len) \<and> 
                          length xs = unat len)" 

lemma val_wa_length_rename_monoexpr_correct:
  "\<lbrakk>val_wa_length (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_length v v'"
  apply (clarsimp simp: val_wa_length_def)
  apply (case_tac v; clarsimp)
  done

lemma val_wa_length_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)); val_wa_length v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' (TPrim (Num U32))"
  apply (clarsimp simp:  val_wa_length_def)
  apply (rule val.v_t_prim'; clarsimp)
  done

section wordarray_get

definition val_wa_get
  where
  "val_wa_get x y =
      (\<exists>xs t idx v. x = VRecord [VAbstract (VWA (TPrim (Num t)) xs), VPrim (LU32 idx)] \<and>
       y = VPrim v \<and> lit_type v = Num t \<and> (unat idx < length xs \<longrightarrow> xs ! unat idx = y) \<and> 
       (\<not> unat idx < length xs \<longrightarrow> zero_num_lit t = v))" 

lemma val_wa_get_rename_monoexpr_correct:
  "\<lbrakk>val_wa_get (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_get v v'"
  apply (clarsimp simp: val_wa_get_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  done

lemma val_wa_get_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed); val_wa_get v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' t"
  apply (clarsimp simp: val_wa_get_def)
  apply (erule val.v_t_recordE; clarsimp)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_abstractE; clarsimp simp: wa_abs_typing_v_def)
  apply (rule val.v_t_prim'; clarsimp)
  done

section wordarray_put2

definition val_wa_put2
  where
  "val_wa_put2 x y =
      (\<exists>xs t idx val. x = VRecord [VAbstract (VWA (TPrim (Num t)) xs), VPrim (LU32 idx), VPrim val] \<and>
       lit_type val = Num t \<and> y = VAbstract (VWA (TPrim (Num t)) (xs[unat idx := VPrim val])))" 

lemma val_wa_put2_rename_monoexpr_correct:
  "\<lbrakk>val_wa_put2 (val.rename_val rename' (val.monoval v)) v'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; proc_ctx_wellformed \<Xi>'\<rbrakk>
    \<Longrightarrow> v' = val.rename_val rename' (val.monoval v') \<and> val_wa_put2 v v'"
  apply (clarsimp simp: val_wa_put2_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (case_tac zb; clarsimp)
  done

lemma val_wa_put2_preservation:
  "\<lbrakk>val.vval_typing \<Xi>' v (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b', TPrim (Num U32), Present), (c, t, Present)] Unboxed); val_wa_put2 v v'\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl))"
  apply (clarsimp simp: val_wa_put2_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (erule val.v_t_abstractE)
  apply (rule val.v_t_abstract; clarsimp)
  apply (case_tac "unat idx < length xs"; simp?)
  apply (rule wa_abs_typing_v_update; simp?)
  done

section wordarray_fold_no_break

function val_wa_foldnb_bod :: "(char list, vatyp) vfoldmapdef"
  where
  "val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv res = 
    (if frm < min to (length xs)
      then (\<exists>acc'. (\<xi>\<^sub>v, [(VRecord [xs ! frm, acc, obsv])] \<turnstile> App f (Var 0) \<Down> acc') \<and>
          val_wa_foldnb_bod \<xi>\<^sub>v t xs (Suc frm) to f acc' obsv res)
    else acc = res)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _, _). to - frm)"; clarsimp)
  apply linarith
  done

declare val_wa_foldnb_bod.simps[simp del]

lemma val_wa_foldnb_bod_append:
  "\<lbrakk>to \<le> length xs; val_wa_foldnb_bod \<xi>\<^sub>v t (xs @ [x]) frm to f acc obsv r\<rbrakk>
    \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r"
  apply (induct arbitrary: x 
                rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = x in meta_spec)
   apply clarsimp
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply (clarsimp simp: nth_append)
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_append_incl_to:
  "\<lbrakk>frm < length (xs @ [x]); to > length xs; val_wa_foldnb_bod \<xi>\<^sub>v t (xs @ [x]) frm to f acc obsv r\<rbrakk>
    \<Longrightarrow> \<exists>r'. val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r' \<and> (\<xi>\<^sub>v, [VRecord [x, r', obsv]] \<turnstile> (App f (Var 0)) \<Down> r)"
  apply (induct arbitrary: x
                rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (case_tac "frm = length xs")
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims)
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims)
   apply (clarsimp split: if_splits)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = x in meta_spec)
  apply clarsimp
  apply (rule_tac x = r' in exI)
  apply clarsimp
  apply (subst val_wa_foldnb_bod.simps)
  apply (clarsimp simp: nth_append)
  apply (rule_tac x = acc' in exI)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_step:
  "\<lbrakk>val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r; frm \<le> to; to < length xs; 
    \<xi>\<^sub>v, [VRecord [xs ! to, r, obsv]] \<turnstile> (App f (Var 0)) \<Down> (r')\<rbrakk> 
    \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv r'"
  apply (induct arbitrary: r'
                rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = r' in meta_spec)
   apply clarsimp
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  apply (rule_tac x = r' in exI)
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_to_geq_len:
  "\<lbrakk>val_wa_foldnb_bod \<xi>\<^sub>v t xs frm (length xs) f acc obsv r; length xs \<le> to\<rbrakk> 
    \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r"
  apply (induct rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_to_geq_lenD:
  "\<lbrakk>val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r; length xs \<le> to\<rbrakk> 
    \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>v t xs frm (length xs) f acc obsv r"
  apply (induct rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_back_step':
  "\<lbrakk>val_wa_foldnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv r; length xs < Suc to\<rbrakk>
    \<Longrightarrow> val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r"
  apply (induct rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_foldnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_foldnb_bod_back_step:
  "\<lbrakk>val_wa_foldnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv r; Suc to \<le> length xs; frm < Suc to\<rbrakk>
    \<Longrightarrow> \<exists>r'. val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r' \<and>
        (\<xi>\<^sub>v, [VRecord [xs ! to, r', obsv]] \<turnstile> (App f (Var 0)) \<Down> r)"
  apply (induct rule: val_wa_foldnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_foldnb_bod.elims)
  apply (clarsimp split: if_split_asm)
  apply (erule_tac x = acc' in meta_allE)
  apply clarsimp
  apply (case_tac "frma < to")
   apply clarsimp
   apply (rule_tac x = r' in exI)
   apply clarsimp
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "to = frma")
   apply clarsimp
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = acca in exI; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply linarith
  done


lemma val_wa_foldnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; val_wa_foldnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r; 
    wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; val.vval_typing \<Xi>' acc u; val.vval_typing \<Xi>' obsv v;
    \<Xi>', [], [option.Some (TRecord [(a0, (t, Present)), (a1, (u, Present)), 
      (a2, (v, Present))] Unboxed)] \<turnstile> App f (Var 0) : u; distinct [a0, a1, a2]\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' r u"
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_foldnb_bod_back_step'; simp)
  apply (case_tac "Suc to \<le> frm")
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
  apply (drule val_wa_foldnb_bod_back_step; clarsimp)
  apply (drule_tac x = r' in meta_spec)
  apply (drule val.preservation(1)[of "[]" "[]" _ _ _  \<xi>\<^sub>v, simplified]; simp?)
  apply (clarsimp simp: val.matches_def)
  apply (rule val.v_t_record; simp?)
  apply (rule val.v_t_r_cons1)
   apply (frule wa_abs_typing_v_elims(1); clarsimp)
   apply (drule wa_abs_typing_v_elims(2))
   apply (erule_tac x = to in allE; clarsimp)
   apply (rule val.v_t_prim'; clarsimp)
  apply (rule val.v_t_r_cons1; simp?)
  apply (rule val.v_t_r_cons1; simp?)
  apply (rule val.v_t_r_empty)
  done

lemma val_wa_foldnb_bod_rename_monoexpr_correct:
  "\<lbrakk>val.proc_env_matches \<xi>\<^sub>m \<Xi>'; proc_ctx_wellformed \<Xi>'; 
    value_sem.rename_mono_prog wa_abs_typing_v rename' \<Xi>' \<xi>\<^sub>m \<xi>\<^sub>p;
    val_wa_foldnb_bod \<xi>\<^sub>m t xs frm to (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) 
      (val.rename_val rename' (val.monoval acc )) (val.rename_val rename' (val.monoval obsv)) r;
    is_vval_fun (val.rename_val rename' (val.monoval f)); wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; 
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval acc )) u;
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval obsv)) v;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] \<turnstile>
      App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0) : u; 
    distinct [a0, a1, a2]\<rbrakk>
       \<Longrightarrow> is_vval_fun f \<and> (\<exists>r'. r = val.rename_val rename' (val.monoval r') \<and>
         val_wa_foldnb_bod \<xi>\<^sub>p t xs frm to (vvalfun_to_exprfun f) acc obsv r')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (induct to arbitrary: r)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_foldnb_bod_back_step'; simp)
   apply (drule val_wa_foldnb_bod_to_geq_lenD)
    apply linarith
   apply (drule_tac x = r in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply clarsimp
   apply (rule_tac x = r' in exI; clarsimp)
   apply (rule val_wa_foldnb_bod_to_geq_len; simp?)
   apply (drule_tac to = to in val_wa_foldnb_bod_to_geq_lenD; simp?)
  apply (case_tac "frm \<ge> Suc to")
   apply (clarsimp simp: not_less not_le)
   apply (erule val_wa_foldnb_bod.elims; clarsimp)
   apply (subst val_wa_foldnb_bod.simps; clarsimp)
  apply (drule val_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = r' in meta_spec)
  apply clarsimp
  apply (frule_tac \<gamma> = "[VRecord [xs ! to, r'a, obsv]]" and
      ?\<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      e = "App (vvalfun_to_exprfun f) (Var 0)" and
      v' = r and
      \<tau> = u in val.rename_monoexpr_correct(1); simp?)
     apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
     apply (clarsimp simp: val.matches_def)
     apply (rule val.v_t_record; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (frule wa_abs_typing_v_elims(1); clarsimp)
      apply (drule wa_abs_typing_v_elims(2))
      apply (erule_tac x = to in allE; clarsimp)
      apply (rule val.v_t_prim'; clarsimp)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (drule val_wa_foldnb_bod_preservation; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_r_empty)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (case_tac f; clarsimp)
   apply (case_tac f; clarsimp)
  apply clarsimp
  apply (drule_tac \<xi>\<^sub>v = \<xi>\<^sub>p in val_wa_foldnb_bod_step; simp?)
  apply (rule_tac x = va in exI)
  apply clarsimp
  done

definition val_wa_foldnb
  where
  "val_wa_foldnb \<Xi>' \<xi>\<^sub>v \<tau> x y = (\<exists>xs frm to acc obsv func t u v a0 a1 a2. 
      x = VRecord [VAbstract (VWA t xs), VPrim (LU32 frm), VPrim (LU32 to), func, acc, obsv] \<and> 
      wa_abs_typing_v (VWA t xs) ''WordArray'' [t]  \<and>
      is_vval_fun func \<and> \<tau> = TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
      val.vval_typing \<Xi>' acc u \<and> val.vval_typing \<Xi>' obsv v \<and> distinct [a0, a1, a2] \<and>
      (\<Xi>', [], [option.Some \<tau>] \<turnstile> (App (vvalfun_to_exprfun func) (Var 0)) : u) \<and>
      (val_wa_foldnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) (vvalfun_to_exprfun func) acc obsv y))"

definition val_wa_foldnbp
  where
  "val_wa_foldnbp \<xi>\<^sub>p x y = (\<exists>t xs frm to func acc obsv. 
      x = VRecord [VAbstract (VWA t xs), VPrim (LU32 frm), VPrim (LU32 to), func, acc, obsv] \<and>
      is_vval_fun func \<and> val_wa_foldnb_bod \<xi>\<^sub>p t xs (unat frm) (unat to) (vvalfun_to_exprfun func) acc obsv y)"

section wordarray_map_no_break

function val_wa_mapAccumnb_bod :: "(char list, vatyp) vfoldmapdef"
  where
  "val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv res = 
    (if frm < min to (length xs)
      then (\<exists>v acc'. (\<xi>\<^sub>v, [(VRecord [xs ! frm, acc, obsv])] \<turnstile> App f (Var 0) \<Down> VRecord [v, acc']) \<and>
          val_wa_mapAccumnb_bod \<xi>\<^sub>v t (xs[frm := v]) (Suc frm) to f acc' obsv res)
    else res = VRecord [VAbstract (VWA t xs), acc])"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _, _). to - frm)"; clarsimp)
  apply linarith
  done

declare val_wa_mapAccumnb_bod.simps[simp del]

lemma val_wa_mapAccumnb_bod_to_geq_len:
  "\<lbrakk>val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm (length xs) f acc obsv r; length xs \<le> to\<rbrakk> 
    \<Longrightarrow> val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r"
  apply (induct rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = v in meta_allE)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = v in exI)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_mapAccumnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_mapAccumnb_bod_to_geq_lenD:
  "\<lbrakk>val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r; length xs \<le> to\<rbrakk> 
    \<Longrightarrow> val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm (length xs) f acc obsv r"
  apply (induct rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = v in meta_allE)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = v in exI)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_mapAccumnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_mapAccumnb_bod_step:
  "\<lbrakk>val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv (VRecord [VAbstract (VWA t rxs), racc]); frm \<le> to;
    to < length xs; \<xi>\<^sub>v, [VRecord [xs ! to, racc, obsv]] \<turnstile> (App f (Var 0)) \<Down> VRecord [v, racc']\<rbrakk> 
    \<Longrightarrow> val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv (VRecord [VAbstract (VWA t (rxs[to := v])), racc'])"
  apply (induct arbitrary:rxs racc v racc'
                rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv 
                  "(VRecord [VAbstract (VWA t rxs), racc])"])
  apply clarsimp
  apply (erule val_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (drule_tac x = va in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = rxs in meta_spec)
   apply (drule_tac x = racc in meta_spec)
   apply (drule_tac x = v in meta_spec)
   apply (drule_tac x = racc' in meta_spec)
   apply clarsimp
   apply (subst val_wa_mapAccumnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = va in exI)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_mapAccumnb_bod.simps)
  apply clarsimp
  apply (rule_tac x = v in exI)
  apply (rule_tac x = racc' in exI)
  apply (subst val_wa_mapAccumnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_mapAccumnb_bod_back_step':
  "\<lbrakk>val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv r; length xs < Suc to\<rbrakk>
    \<Longrightarrow> val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r"
  apply (induct rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r]; clarsimp)
  apply (erule val_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
   apply (erule_tac x = v in meta_allE)
   apply (erule_tac x = acc' in meta_allE; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = v in exI)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply (subst val_wa_mapAccumnb_bod.simps)
  apply clarsimp
  done

lemma val_wa_mapAccumnb_bod_back_step:
  "\<lbrakk>val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm (Suc to) f acc obsv (VRecord [VAbstract (VWA t rxs), racc]); 
    Suc to \<le> length xs; frm < Suc to\<rbrakk>
    \<Longrightarrow> \<exists>racc'.
      val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv (VRecord [VAbstract (VWA t (rxs[to := xs ! to])), racc']) \<and>
      (\<xi>\<^sub>v, [VRecord [xs ! to, racc', obsv]] \<turnstile> (App f (Var 0)) \<Down> VRecord [rxs ! to, racc])"
  apply (induct arbitrary: rxs racc
                rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv 
                  "VRecord [VAbstract (VWA t rxs), racc]"])
  apply clarsimp
  apply (erule val_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
  apply (erule_tac x = v in meta_allE)
  apply (erule_tac x = acc' in meta_allE)
  apply (erule_tac x = rxs in meta_allE)
  apply (erule_tac x = racc in meta_allE)
  apply clarsimp
  apply (case_tac "frma < to")
   apply clarsimp
   apply (rule_tac x = racc' in exI)
   apply clarsimp
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
   apply (rule_tac x = v in exI)
   apply (rule_tac x = acc' in exI)
   apply clarsimp
  apply clarsimp
  apply (subgoal_tac "to = frma")
   apply clarsimp
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = acca in exI; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply linarith
  done

lemma val_wa_mapAccumnb_bod_preservation':
  "val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r 
    \<Longrightarrow> \<exists>rxs racc. r = VRecord [VAbstract(VWA t rxs), racc] \<and> length rxs = length xs"
  apply (induct rule: val_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>v t xs frm to f acc obsv r])
  apply (erule val_wa_mapAccumnb_bod.elims; clarsimp split: if_split_asm)
  done

lemma val_wa_mapAccumnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; val.proc_env_matches \<xi>\<^sub>v \<Xi>'; val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs frm to f acc obsv r; 
    wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; val.vval_typing \<Xi>' acc u; val.vval_typing \<Xi>' obsv v;
    \<Xi>', [], [option.Some (TRecord [(a0, (t, Present)), (a1, (u, Present)), 
      (a2, (v, Present))] Unboxed)] \<turnstile> App f (Var 0) : 
      TRecord [(b0, (t, Present)), (b1, (u, Present))] Unboxed; 
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> val.vval_typing \<Xi>' r (TRecord [
      (b0, (TCon ''WordArray'' [t] (Boxed Writable ptrl), Present)),
      (b1, (u, Present))] Unboxed)"
  apply (induct to arbitrary: r)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1; simp?)
    apply (rule val.v_t_abstract; simp)
    apply (drule wa_abs_typing_v_elims(1); clarsimp)
   apply (rule val.v_t_r_cons1; simp?)
   apply (rule val.v_t_r_empty)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp)
  apply (case_tac "Suc to \<le> frm")
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1; simp?)
    apply (rule val.v_t_abstract; simp)
    apply (drule wa_abs_typing_v_elims(1); clarsimp)
   apply (rule val.v_t_r_cons1; simp?)
   apply (rule val.v_t_r_empty)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_back_step; clarsimp)
  apply (drule_tac x = "VRecord [VAbstract (VWA t (rxs[to := xs ! to])), racc']" in meta_spec)
  apply clarsimp
  apply (erule val.v_t_recordE; clarsimp)
  apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_r_emptyE; simp)
   apply (drule_tac e = "App f (Var 0)" and
      v = "VRecord [rxs ! to, racc]" and
      \<gamma> = "[VRecord [xs ! to, racc', obsv]]" and
      \<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" 
      in val.preservation(1)[of "[]" "[]" _ _ _  \<xi>\<^sub>v, simplified]; simp?)
  apply (clarsimp simp: val.matches_def)
  apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
   apply (erule_tac x = to in allE; clarsimp)
   apply (rule val.v_t_prim'; clarsimp)
  apply (rule val.v_t_r_cons1; simp?)
  apply (rule val.v_t_r_cons1; simp?)
    apply (rule val.v_t_r_empty)
   apply (erule val.v_t_recordE; clarsimp)
   apply (erule val.v_t_r_consE; clarsimp)+
   apply (erule val.v_t_r_emptyE; simp)
  apply (rule val.v_t_abstractE; simp)
  apply (rule val.v_t_record; simp)
  apply (rule val.v_t_r_cons1)
   apply (rule val.v_t_abstract; simp?)
   apply (frule wa_abs_typing_v_elims(1); clarsimp)
   apply (clarsimp simp: val.vval_typing.simps[of _ _ "TPrim _", simplified])
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
   apply (drule_tac i = to and v = l and xs = "rxs[to := xs ! to]" in wa_abs_typing_v_update; simp?)
   apply (drule_tac s = "rxs ! to" in sym; clarsimp)
  apply (rule val.v_t_r_cons1; simp?)
  apply (rule val.v_t_r_empty)
  done

lemma val_wa_mapAccumnb_bod_rename_monoexpr_correct:
  "\<lbrakk>val.proc_env_matches \<xi>\<^sub>m \<Xi>'; proc_ctx_wellformed \<Xi>'; 
    value_sem.rename_mono_prog wa_abs_typing_v rename' \<Xi>' \<xi>\<^sub>m \<xi>\<^sub>p;
    val_wa_mapAccumnb_bod \<xi>\<^sub>m t xs frm to (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) 
      (val.rename_val rename' (val.monoval acc )) (val.rename_val rename' (val.monoval obsv)) r;
    is_vval_fun (val.rename_val rename' (val.monoval f)); wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; 
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval acc )) u;
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval obsv)) v;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] \<turnstile>
      App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0) :
      TRecord [(b0, t, Present), (b1, u, Present)] Unboxed; distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
       \<Longrightarrow> is_vval_fun f \<and> (\<exists>r'. r = val.rename_val rename' (val.monoval r') \<and>
         val_wa_mapAccumnb_bod \<xi>\<^sub>p t xs frm to (vvalfun_to_exprfun f) acc obsv r')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (induct to arbitrary: r)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (case_tac "length xs < Suc to")
   apply (drule val_wa_mapAccumnb_bod_back_step'; simp)
   apply (drule val_wa_mapAccumnb_bod_to_geq_lenD)
    apply linarith
   apply (drule_tac x = r in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp?)
   apply clarsimp
   apply (rule_tac x = r' in exI; clarsimp)
   apply (rule val_wa_mapAccumnb_bod_to_geq_len; simp?)
   apply (drule_tac to = to in val_wa_mapAccumnb_bod_to_geq_lenD; simp?)
  apply (case_tac "frm \<ge> Suc to")
  apply (clarsimp simp: not_less not_le)
   apply (erule val_wa_mapAccumnb_bod.elims; clarsimp)
   apply (subst val_wa_mapAccumnb_bod.simps; clarsimp)
  apply (frule val_wa_mapAccumnb_bod_preservation'; clarsimp)
  apply (drule val_wa_mapAccumnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = "VRecord [VAbstract (VWA t (rxs[to := xs ! to])), racc']" in meta_spec)
  apply clarsimp
  apply (case_tac r'; clarsimp)
  apply (case_tac z; clarsimp)
  apply (frule_tac \<gamma> = "[VRecord [xs ! to, za, obsv]]" and
      ?\<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      e = "App (vvalfun_to_exprfun f) (Var 0)" and
      v' = "VRecord [rxs ! to, racc]" and
      \<tau> = "TRecord [(b0, t, Present), (b1, u, Present)] Unboxed" 
      in val.rename_monoexpr_correct(1); simp?)
     apply (clarsimp simp: val.matches_Cons[where xs = "[]" and ys = "[]", simplified])
     apply (clarsimp simp: val.matches_def)
     apply (rule val.v_t_record; simp?)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (frule wa_abs_typing_v_elims(1); clarsimp)
      apply (drule wa_abs_typing_v_elims(2))
      apply (erule_tac x = to in allE; clarsimp)
      apply (rule val.v_t_prim'; clarsimp)
     apply (rule val.v_t_r_cons1; clarsimp?)
      apply (drule val_wa_mapAccumnb_bod_preservation; simp?)
      apply (erule val.v_t_recordE; clarsimp)
      apply (erule val.v_t_r_consE; clarsimp)+
     apply (rule val.v_t_r_cons1; clarsimp?)
     apply (rule val.v_t_r_empty)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (case_tac f; clarsimp)
   apply (case_tac f; clarsimp)
  apply clarsimp
  apply (case_tac va; clarsimp)
  apply (drule_tac \<xi>\<^sub>v = \<xi>\<^sub>p in val_wa_mapAccumnb_bod_step; simp?)
  apply (rule_tac x = "VRecord [VAbstract (VWA t (rxs[to := z])), zb]" in exI)
  apply clarsimp
   apply (frule_tac e = "App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0)" and
      v = "VRecord [val.rename_val rename' (val.monoval z), val.rename_val rename' (val.monoval zb)]" and
      \<gamma> = "[VRecord [xs ! to, val.rename_val rename' (val.monoval za), val.rename_val rename' (val.monoval obsv)]]" and
      \<tau> = "TRecord [(b0, t, Present), (b1, u, Present)] Unboxed" and
      \<Gamma> = "[option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" 
      in val.preservation(1)[of "[]" "[]" _ _ _  \<xi>\<^sub>m, simplified]; simp?)
  apply (clarsimp simp: val.matches_def)
  apply (rule val.v_t_record; simp?)
   apply (rule val.v_t_r_cons1)
    apply (frule wa_abs_typing_v_elims(1); clarsimp)
    apply (drule wa_abs_typing_v_elims(2))
    apply (erule_tac x = to in allE; clarsimp)
    apply (rule val.v_t_prim'; clarsimp)
   apply (rule val.v_t_r_cons1; simp?)
    apply (drule val_wa_mapAccumnb_bod_preservation; simp?)
    apply (erule val.v_t_recordE; clarsimp)
    apply (erule val.v_t_r_consE; clarsimp)+
   apply (rule val.v_t_r_cons1; simp?)
   apply (rule val.v_t_r_empty)
  apply (erule val.v_t_recordE; clarsimp)
   apply (erule val.v_t_r_consE; clarsimp)+
  apply (erule val.v_t_r_emptyE; simp)
  apply (drule wa_abs_typing_v_elims(1); clarsimp)
  apply (erule v_t_primtE; clarsimp)
  apply (case_tac z; clarsimp)
  by (simp add: upd.list_helper)

definition val_wa_mapAccumnb
  where
  "val_wa_mapAccumnb \<Xi>' \<xi>\<^sub>v \<tau>i \<tau>o x y = (\<exists>xs frm to acc obsv func t u v a0 a1 a2 b0 b1. 
      x = VRecord [VAbstract (VWA t xs), VPrim (LU32 frm), VPrim (LU32 to), func, acc, obsv] \<and> 
      wa_abs_typing_v (VWA t xs) ''WordArray'' [t]  \<and>
      is_vval_fun func \<and> \<tau>i = TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
      \<tau>o = TRecord [(b0, t, Present), (b1, u, Present)] Unboxed \<and>
      val.vval_typing \<Xi>' acc u \<and> val.vval_typing \<Xi>' obsv v \<and> distinct [a0, a1, a2] \<and> distinct [b0, b1] \<and>
      (\<Xi>', [], [option.Some \<tau>i] \<turnstile> (App (vvalfun_to_exprfun func) (Var 0)) : \<tau>o) \<and>
      (val_wa_mapAccumnb_bod \<xi>\<^sub>v t xs (unat frm) (unat to) (vvalfun_to_exprfun func) acc obsv y))"

definition val_wa_mapAccumnbp
  where
  "val_wa_mapAccumnbp \<xi>\<^sub>p x y = (\<exists>t xs frm to func acc obsv. 
      x = VRecord [VAbstract (VWA t xs), VPrim (LU32 frm), VPrim (LU32 to), func, acc, obsv] \<and>
      is_vval_fun func \<and> val_wa_mapAccumnb_bod \<xi>\<^sub>p t xs (unat frm) (unat to) (vvalfun_to_exprfun func) acc obsv y)"

end (* of context *)

end