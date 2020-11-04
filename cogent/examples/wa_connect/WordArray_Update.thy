theory WordArray_Update
  imports WordArray_Abstractions

begin

context WordArray begin

type_synonym ('f, 'a, 'l) ufoldmapdef = "(funtyp, abstyp, ptrtyp) uabsfuns \<Rightarrow> ('f, 'a, 'l) store \<Rightarrow>
                                          ptrtyp \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 'f expr \<Rightarrow> 
                                          ('f, 'a, 'l) uval \<Rightarrow> ('f, 'a, 'l) uval \<Rightarrow> ptrtyp set\<Rightarrow>
                                          (('f, 'a, 'l) store \<times> ('f, 'a, 'l) uval) \<Rightarrow> bool"

section wordarray_length

definition upd_wa_length_0
  where
  "upd_wa_length_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p t len arr. x2 = UPtr p (RCon ''WordArray'' [RPrim (Num t)]) \<and>
          x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> y2 = UPrim (LU32 len)))"

lemma upd_wa_length_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    upd_wa_length_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_length_0_def)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def intro!: upd.u_t_prim')
  done

section wordarray_get

definition upd_wa_get_0
  where
  "upd_wa_get_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p idx t len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
          (UPrim (LU32 idx), RPrim (Num U32))] \<and> x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and>
          (idx < len \<longrightarrow> x1 (arr + size_of_num_type t * idx) = option.Some y2) \<and>
            (\<not> idx < len \<longrightarrow> y2 = UPrim (zero_num_lit t))))"

lemma upd_wa_get_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed) r w; upd_wa_get_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' t r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
 apply (clarsimp simp: upd_wa_get_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE[where s = "Boxed ReadOnly _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (rule_tac x = "{}" in exI)+
  apply (frule wa_abs_typing_u_elims(1))
  apply (frule wa_abs_typing_u_elims(5))
  apply (clarsimp simp: upd.frame_id)
  apply (erule_tac x = idx in allE)
  apply (case_tac "idx < len"; clarsimp)
   apply (rule upd.u_t_prim'; clarsimp)+
  apply (case_tac ta; clarsimp intro!: upd.u_t_prim')
  done

section wordarray_put2

definition upd_wa_put2_0
  where
  "upd_wa_put2_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in (\<exists>p idx val t len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
          (UPrim (LU32 idx), RPrim (Num U32)), (val, RPrim (Num t))] \<and>
          x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and>
          y2 = UPtr p (RCon ''WordArray'' [RPrim (Num t)]) \<and>
          (if idx < len 
              then y1 = x1((arr + size_of_num_type t * idx) \<mapsto> val)
              else y1 = x1)))"

lemma upd_wa_put2_preservation:
  "\<lbrakk>upd.uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b, TPrim (Num U32), Present), (c, t, Present)] Unboxed) r w; upd_wa_put2_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl)) r' w' \<and>
      r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE[where s = "Boxed Writable _", simplified])
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule type_repr.elims[where y = "RPrim _", simplified]; clarsimp)
  apply (frule upd.tprim_no_pointers(1); clarsimp)
  apply (frule upd.tprim_no_pointers(2); clarsimp)
  apply (rule_tac x = r in exI)
  apply (rule_tac x = "insert p wa" in exI)
  apply (erule u_t_primtE; clarsimp)
  apply (drule_tac t = "lit_type _" in sym)
  apply (rule conjI)
   apply (rule_tac ptrl = ptrl and a = "UWA (TPrim (Num ta)) len arr" 
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
    apply (clarsimp split: if_split_asm)
    apply (rule wa_abs_typing_u_update; simp)
   apply (frule wa_abs_typing_u_elims(3); clarsimp split: if_splits)
  apply (clarsimp split: if_splits simp: upd.frame_id)
  apply (frule wa_abs_typing_u_elims(3); clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
   apply (rule conjI, clarsimp)
    apply (erule_tac x = idx in allE; clarsimp)+
   apply (rule conjI; clarsimp)
  apply (rule conjI; clarsimp)
  done

section wordarray_fold_no_break

function upd_wa_foldnb_bod :: "(char list, atyp, 32 word) ufoldmapdef"
  where
  "upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s res = (\<exists>t len arr. 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> 
    (\<forall>i<len. \<exists>v. \<sigma> (arr + size_of_num_type t * i) = option.Some v) \<and>
    (if frm < min to len then (\<exists>v acc' \<sigma>' w1 w2. \<sigma> (arr + size_of_num_type t * frm) = option.Some v \<and> 
          (\<xi>\<^sub>u, [(URecord [(v, upd.uval_repr v), (acc, upd.uval_repr acc), 
            (obsv, upd.uval_repr obsv)])] \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>', acc')) \<and>
          frame \<sigma> w1 \<sigma>' w2 \<and> ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {} \<and>
          upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma>' p (frm + 1) to f acc' obsv s res) 
    else (\<sigma>, acc) = res))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _, _,  _). unat to - unat frm)"; clarsimp)
  apply (clarsimp simp: word_less_nat_alt)
  apply (cut_tac n = frm in unat_Suc2; clarsimp)
   apply (cut_tac y = to in word_not_simps(3); clarsimp simp: word_less_nat_alt)
  apply linarith
  done

declare upd_wa_foldnb_bod.simps[simp del]

lemma upd_wa_foldnb_bod_to_geq_len:
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm len f acc obsv s (\<sigma>', r); \<sigma> p = option.Some (UAbstract (UWA t len arr));
    to \<ge> len\<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (subst (asm) upd_wa_foldnb_bod.simps)
  apply (clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule conjI; clarsimp)
    apply (rule_tac x = acc' in exI)
    apply (rule_tac x = \<sigma>' in exI)
    apply clarsimp
    apply (rule_tac x = w1 in exI)
    apply clarsimp
    apply (rule conjI)
     apply (rule_tac x = x in exI; clarsimp)
    apply (clarsimp simp: frame_def)
    apply (erule_tac x = p in allE; clarsimp)
   apply (rule FalseE)
   apply auto[1]
  apply (subst upd_wa_foldnb_bod.simps)
  apply clarsimp
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = \<sigma>' in meta_spec)
  apply clarsimp
  apply (rule_tac x = acc' in exI)
  apply (rule_tac x = \<sigma>' in exI)
  apply clarsimp
  apply (rule_tac x = w1 in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule_tac x = x in exI; clarsimp)
  apply (erule meta_mp)
  apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp)
  done

lemma upd_wa_foldnb_bod_to_geq_lenD:
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r); \<sigma> p = option.Some (UAbstract (UWA t len arr));
    to \<ge> len\<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm len f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (subst (asm) upd_wa_foldnb_bod.simps)
  apply (clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply (rule_tac x = \<sigma>' in exI)
   apply clarsimp
   apply (rule_tac x = w1 in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac x = x in exI; clarsimp)
   apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE; simp)
  apply (case_tac "frm < to")
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply (rule_tac x = \<sigma>' in exI)
   apply clarsimp
   apply (rule_tac x = w1 in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac x = x in exI; clarsimp)
   apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE; simp)
  apply clarsimp
  apply (subgoal_tac "\<not> frm < len")
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
  apply auto
  done

lemma upd_wa_foldnb_bod_step:
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r); 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)); frm \<le> to; to < len; 
    \<sigma> (arr + size_of_num_type t * to) = option.Some v; frame \<sigma>' w1 \<sigma>'' w2; 
    ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {};
    \<xi>\<^sub>u, [URecord [(v, upd.uval_repr v), (r, upd.uval_repr r), (obsv, upd.uval_repr obsv)]] \<turnstile> (\<sigma>', App f (Var 0))\<Down>! (\<sigma>'', r')\<rbrakk> 
    \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (to + 1) f acc obsv s (\<sigma>'', r')"
  apply (induct arbitrary: r  \<sigma>'
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>'''' in meta_spec)
   apply (drule_tac x = b in meta_spec)
   apply (drule_tac x = a in meta_spec)
   apply clarsimp
   apply (subst upd_wa_foldnb_bod.simps)
   apply clarsimp
   apply (rule conjI; clarsimp)
    apply (rule_tac x = acc' in exI)
    apply (rule_tac x = \<sigma>'''' in exI)
    apply clarsimp
    apply (rule_tac x = w1a in exI)
    apply clarsimp
    apply (rule conjI)
     apply (rule_tac x = x in exI; clarsimp)
    apply (case_tac "frma + 1 \<le> toa")
     apply clarsimp
     apply (frule_tac p = pa and w = w1a in valid_ptr_not_in_frame_same; simp?)
     apply (frule_tac p = "arr + size_of_num_type t * toa" and w = w1a in valid_ptr_not_in_frame_same; simp?)
      apply blast
     apply clarsimp
    apply (clarsimp simp: not_le)
    apply (drule_tac i = frma and m = toa in inc_le)
    apply (rule FalseE)
    apply simp
   apply (clarsimp simp: not_less)
   apply (rule FalseE)
   apply (simp add: less_is_non_zero_p1 plus_one_helper2 word_le_not_less)
  apply (erule disjE)
   apply (subst upd_wa_foldnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp)
    apply (rule_tac x = r' in exI)
    apply (rule_tac x = \<sigma>'' in exI)
    apply (subst upd_wa_foldnb_bod.simps; clarsimp)
    apply (rule_tac x = w1 in exI)
    apply clarsimp
    apply (rule conjI)
     apply (rule_tac x = w2 in exI; clarsimp)
    apply (rule_tac x =  t in exI)
    apply (rule_tac x = len in exI)
    apply (rule_tac x = arr in exI)
    apply (rule conjI)
     apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp)
    apply clarsimp
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = va in exI)
    apply (drule_tac p = "arr + size_of_num_type t * i" in valid_ptr_not_in_frame_same; simp?)
    apply blast
   apply (clarsimp simp: not_less)
   apply (meson less_is_non_zero_p1 word_le_not_less word_overflow)
  apply (clarsimp simp: not_less)
  by auto

lemma upd_wa_foldnb_bod_back_step':
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r); 
    \<sigma> p = option.Some (UAbstract (UWA t len arr)); len < to\<rbrakk>
    \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (to - 1) f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_foldnb_bod.induct[of _  \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"]; clarsimp)
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)  
  apply (subst upd_wa_foldnb_bod.simps)
  apply (clarsimp split: if_split_asm)
  apply (rule_tac x = ta in exI)
  apply (rule conjI; clarsimp)
   apply (cut_tac x = frma and n = "toa - 1" in plus_one_helper2; simp)
    apply auto[1]
   apply clarsimp
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply clarsimp
   apply (rule_tac x = acc' in exI)
   apply (rule_tac x = \<sigma>'' in exI)
   apply clarsimp
   apply (rule_tac x = w1 in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac x = x in exI; clarsimp)
   apply (erule meta_mp)
   apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp)
  apply (rule FalseE)
  by (metis (no_types, hide_lams) less_1_simp word_le_less_eq word_not_le)

lemma upd_wa_foldnb_bod_back_step:
  "\<lbrakk>upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f acc obsv s (\<sigma>', r); 1 + to \<le> len; frm < 1 + to; 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr))\<rbrakk>
    \<Longrightarrow> \<exists>\<sigma>'' r'' w1 w2 v. upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>'', r'') \<and> 
        \<sigma> (arr + size_of_num_type t * to) = option.Some v \<and>
        (\<xi>\<^sub>u, [URecord [(v, upd.uval_repr v), (r'', upd.uval_repr r''), 
          (obsv, upd.uval_repr obsv)]] \<turnstile> (\<sigma>'', App f (Var 0))\<Down>! (\<sigma>', r)) \<and>
        frame \<sigma>'' w1 \<sigma>' w2 \<and> ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {}"
  apply (induct arbitrary: \<sigma>' r
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"]; clarsimp)
  apply (erule upd_wa_foldnb_bod.elims)  
  apply (clarsimp split: if_split_asm)
   apply (drule_tac x = len in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>''' in meta_spec)
   apply (drule_tac x = a in meta_spec)
   apply (drule_tac x = b in meta_spec)
   apply clarsimp
   apply (case_tac "frma < to"; clarsimp)
    apply (drule meta_mp)
     apply (metis (no_types, hide_lams) add.commute inc_le plus_le_left_cancel_wrap word_le_less_eq word_le_not_less word_plus_strict_mono_right)
    apply (drule meta_mp)
     apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp)
    apply clarsimp
    apply (rule_tac x = \<sigma>'''' in exI)
    apply (rule_tac x = r'' in exI)
    apply (rule conjI)
     apply (subst upd_wa_foldnb_bod.simps; clarsimp)
     apply (rule_tac x = acc' in exI)
     apply (rule_tac x = \<sigma>''' in exI)
     apply clarsimp
     apply (rule_tac x = w1 in exI)
     apply clarsimp
     apply (rule_tac x = x in exI)
     apply clarsimp
    apply (rule_tac x = w1a in exI)
    apply (rule_tac x = w2 in exI)
    apply (erule_tac x = to in allE; clarsimp)
    apply (erule impE)
     apply (metis (no_types, hide_lams) add.commute less_is_non_zero_p1 plus_one_helper plus_one_helper2 word_neq_0_conv word_not_le)
    apply (rule_tac x = va in exI)
    apply clarsimp
    apply (drule_tac p = "arr + size_of_num_type t * to" in valid_ptr_not_in_frame_same; simp; clarsimp)
    apply (drule_tac x = "arr + size_of_num_type t * to" in orthD1; simp)
    apply (rule disjI2)
    apply (rule_tac x = to in exI)
    apply clarsimp
    apply (metis (no_types, hide_lams) add.commute plus_one_helper2  word_not_le word_not_simps(1))
   apply (subgoal_tac "frma = to")
    apply clarsimp
    apply (subst upd_wa_foldnb_bod.simps; clarsimp simp: add.commute)
    apply (erule upd_wa_foldnb_bod.elims; clarsimp simp: add.commute)
    apply (rule_tac x = w1 in exI)
    apply clarsimp
    apply (rule_tac x = x in exI)
    apply clarsimp
   apply (metis add.commute le_step)
  apply (rule FalseE)
  by auto

lemma upd_wa_foldnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; upd.proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
    upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res);
    \<sigma> p = option.Some (UAbstract (UWA t len arr)); 
    wa_abs_typing_u (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
    upd.uval_typing \<Xi>' \<sigma> acc u rb wb; upd.uval_typing \<Xi>' \<sigma> obsv v rc {};  wb \<inter> rc = {};
    \<Xi>', [], [option.Some (TRecord [
      (b0, t, Present), (b1, u, Present), (b2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
    distinct [b0, b1, b2]\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. upd.uval_typing \<Xi>' \<sigma>' res u r' w' \<and> r' \<subseteq> ({p} \<union> ra \<union> rb \<union> rc) \<and> frame \<sigma> wb \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: upd.frame_id)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_foldnb_bod_back_step'; simp?)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: upd.frame_id)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (drule upd_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply (drule_tac x = r'' in meta_spec)
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(5))
  apply (erule_tac x = to in allE; clarsimp)+
  apply (erule impE)
   apply (cut_tac x = to in word_overflow)
   apply (erule disjE; clarsimp simp: add.commute)
   apply auto[1]
  apply clarsimp
  apply (drule_tac ?\<Gamma> = "[option.Some (TRecord [(b0, TPrim (Num ta), Present), (b1, u, Present),
    (b2, v, Present)] Unboxed)]" and r = "r' \<union> rc" and  w = w' and \<tau> = u in upd.preservation_mono(1); simp?)
   apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
    apply (rule upd.u_t_struct; simp?)
    apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
      apply (rule upd.u_t_prim'; clarsimp)
     apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd.uval_typing_frame(1); simp?)
         apply blast
        apply (rule upd.u_t_r_empty)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (thin_tac "frame _ _ _ _")
      apply (clarsimp simp: frame_def)
      apply (erule_tac x = y in allE; clarsimp)+
      apply (drule_tac x = y in orthD2; simp)
      apply (drule_tac u = obsv and p = y in upd.uval_typing_valid(1)[rotated 1]; simp)
     apply (drule_tac v = r'' in upd.type_repr_uval_repr(1); simp)
    apply clarsimp
   apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
  apply clarsimp
  apply (thin_tac "frame _ _ _ _")
  apply (rule_tac x = r'a in exI)
  apply (rule_tac x = w'a in exI)
  apply clarsimp
  apply (rule conjI, blast)
  apply (rule upd.frame_trans; simp)
  done

definition upd_wa_foldnb
  where
  "upd_wa_foldnb \<Xi>' \<xi>\<^sub>u \<tau> y z = 
    (let (y1, y2) = y
      in (\<exists>p frm to func acc obsv t u v a0 a1 a2 ra wa rb.
        y2 = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
                      (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
                      (func, RFun), (acc, upd.uval_repr acc), (obsv, upd.uval_repr obsv)] \<and>
        (\<exists>len arr. y1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> 
          (\<forall>i<len. \<exists>x. y1 (arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> lit_type x = Num t)) \<and>
        is_uval_fun func \<and> upd.uval_typing \<Xi>' y1 acc u ra wa \<and> upd.uval_typing \<Xi>' y1 obsv v rb {} \<and>
        \<tau> = TRecord [(a0, TPrim (Num t), Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
        distinct [a0, a1, a2] \<and> (\<Xi>', [], [option.Some \<tau>] \<turnstile> (App (uvalfun_to_exprfun func) (Var 0)) : u) \<and>
        upd_wa_foldnb_bod \<xi>\<^sub>u y1 p frm to (uvalfun_to_exprfun func) acc obsv (ra \<union> rb) z))"

section wordarray_map_no_break

function upd_wa_mapAccumnb_bod :: "(char list, atyp, ptrtyp) ufoldmapdef"
  where
  "upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s res = (\<exists>t len arr. 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> 
    (\<forall>i<len. \<exists>v. \<sigma> (arr + size_of_num_type t * i) = option.Some v) \<and>
    (\<forall>i<len. p \<noteq> (arr + size_of_num_type t * i)) \<and>
    (if frm < min to len then 
      (\<exists>v v' acc' \<sigma>' w1 w2. \<sigma> (arr + size_of_num_type t * frm) = option.Some v \<and>
      (\<xi>\<^sub>u, [(URecord [(v, upd.uval_repr v), (acc, upd.uval_repr acc), (obsv, upd.uval_repr obsv)])]
        \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>', URecord [ (v', upd.uval_repr v'), (acc', upd.uval_repr acc')])) \<and>
      frame \<sigma> w1 \<sigma>' w2 \<and> ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {} \<and>
      upd_wa_mapAccumnb_bod \<xi>\<^sub>u (\<sigma>'((arr + size_of_num_type t * frm) \<mapsto> v')) p (frm + 1) to f 
        acc' obsv s res) 
    else res = (\<sigma>, URecord [
      (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])), 
      (acc, upd.uval_repr acc)])))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _, _,  _). unat to - unat frm)"; clarsimp)
  apply (clarsimp simp: word_less_nat_alt)
  apply (cut_tac n = frm in unat_Suc2; clarsimp)
   apply (cut_tac y = to in word_not_simps(3); clarsimp simp: word_less_nat_alt)
  apply linarith
  done

declare upd_wa_mapAccumnb_bod.simps[simp del]

lemma upd_wa_mapAccumnb_bod_to_geq_len:
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm len f acc obsv s (\<sigma>', r); \<sigma> p = option.Some (UAbstract (UWA t len arr));
    to \<ge> len\<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"])
  apply clarsimp
  apply (case_tac "frm \<ge> len")
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp split: if_splits)
   apply (drule_tac x = frma in leD; clarsimp)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (erule upd_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
  apply (drule_tac x = frma in not_le_imp_less; clarsimp)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (drule_tac x = v' in meta_spec)
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply clarsimp
  apply (drule meta_mp)
   apply (drule_tac c = to in order.strict_trans2; simp)
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (frule_tac c = to in order.strict_trans2; simp)
  apply (rule_tac x = v' in exI)
  apply (rule_tac x = acc' in exI)
  apply (rule_tac x = \<sigma>'' in exI)
  apply clarsimp
  apply (rule_tac x = w1 in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule_tac x = x in exI)
   apply clarsimp
  apply (erule meta_impE; simp?)
  apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp)
  done

lemma upd_wa_mapAccumnb_bod_to_geq_lenD:
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r); \<sigma> p = option.Some (UAbstract (UWA t len arr));
    to \<ge> len\<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm len f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"])
  apply clarsimp
 apply (case_tac "frm \<ge> len")
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp split: if_splits)
   apply (drule_tac x = frma in leD; clarsimp)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (erule upd_wa_mapAccumnb_bod.elims)
  apply (clarsimp split: if_split_asm)
  apply (drule_tac x = frma in not_le_imp_less; clarsimp)
  apply (frule_tac c = toa in order.strict_trans2; clarsimp)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (drule_tac x = v' in meta_spec)
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply clarsimp
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (rule_tac x = v' in exI)
  apply (rule_tac x = acc' in exI)
  apply (rule_tac x = \<sigma>'' in exI)
  apply clarsimp
  apply (rule_tac x = w1 in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule_tac x = x in exI)
   apply clarsimp
  apply (erule meta_impE; simp?)
  apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp)
  done

lemma upd_wa_mapAccumnb_bod_preservation':
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s r; \<sigma> p = option.Some (UAbstract (UWA t len arr))\<rbrakk>
    \<Longrightarrow> \<exists>\<sigma>' racc. r = (\<sigma>', URecord [
      (UPtr p (RCon ''WordArray'' [type_repr t]), RPtr (RCon ''WordArray'' [type_repr t])),
      (racc, upd.uval_repr racc)])"
  apply (induct rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s r])
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (drule_tac x = v' in meta_spec)
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = \<sigma>'' in meta_spec)
  apply clarsimp
  apply (drule_tac p = pa in valid_ptr_not_in_frame_same; simp?)
  apply clarsimp
  done

lemma upd_wa_mapAccumnb_bod_step:
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', URecord [rp, (r, repr)]); 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)); frm \<le> to; to < len;
    unat (size_of_num_type t) * unat len \<le> unat (max_word :: ptrtyp);
    \<sigma>' (arr + size_of_num_type t * to) = option.Some v; frame \<sigma>' w1 \<sigma>'' w2; 
    ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {};
    \<xi>\<^sub>u, [URecord [(v, upd.uval_repr v), (r, upd.uval_repr r), (obsv, upd.uval_repr obsv)]] \<turnstile> 
      (\<sigma>', App f (Var 0))\<Down>! (\<sigma>'', URecord [ (v', upd.uval_repr v'), (r', upd.uval_repr r')])\<rbrakk> 
    \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (to + 1) f acc obsv s 
      (\<sigma>''((arr + size_of_num_type t * to) \<mapsto> v'), URecord [rp, (r', upd.uval_repr r')])"
  apply (induct arbitrary: r \<sigma>'
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', URecord [rp, (r, upd.uval_repr r)])"])
  apply clarsimp
  apply (drule_tac x = t in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp split: if_splits)
  apply (rename_tac  \<xi>\<^sub>u \<sigma> p frm to f acc obsv s \<sigma>' va v'a acc' \<sigma>a w1a w2a)
   apply (drule_tac x = v'a in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply (drule_tac x = r in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp)
    apply (rule_tac x = v'a in exI)
    apply (rule_tac x = acc' in exI)
    apply (rule_tac x = \<sigma>a in exI)
    apply clarsimp
    apply (rule_tac x = w1a in exI)
    apply clarsimp
    apply (rule conjI)
     apply (rule_tac x = w2a in exI)
     apply clarsimp
    apply (drule meta_mp)
     apply (drule_tac p = p and w = w1a in valid_ptr_not_in_frame_same; simp)
    apply (drule meta_mp)
     apply (simp add: inc_le)
    apply simp
   apply (rule FalseE)
   apply (simp add: less_is_non_zero_p1 plus_one_helper2)
  apply (rename_tac  \<xi>\<^sub>u \<sigma> p frm to f acc obsv s)
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = \<sigma>'' in exI)
   apply clarsimp
   apply (rule_tac x = w1 in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac x = w2 in exI)
    apply clarsimp
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (rule_tac x = len in exI)
   apply (rule_tac x = arr in exI)
   apply clarsimp
   apply (rule conjI)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (rule_tac x = va in exI)
   apply (drule_tac p = "arr + size_of_num_type t * i" in valid_ptr_not_in_frame_same; simp?)
   apply blast
  apply (erule impE)
   apply (metis (no_types, hide_lams) add.commute dual_order.strict_trans less_le max_word_max word_Suc_le word_le_less_eq word_not_le)
  apply (rule FalseE)
  apply clarsimp
  by auto

lemma upd_wa_mapAccumnb_bod_back_step':
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>', r); 
    \<sigma> p = option.Some (UAbstract (UWA t len arr)); len < to\<rbrakk>
    \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (to - 1) f acc obsv s (\<sigma>', r)"
  apply (induct rule: upd_wa_mapAccumnb_bod.induct[of _  \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', r)"]; clarsimp)
  apply (erule upd_wa_mapAccumnb_bod.elims)
  apply (subst upd_wa_mapAccumnb_bod.simps)
  apply (clarsimp split: if_split_asm)
  apply (rule_tac x = ta in exI)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (rule conjI; clarsimp)
   apply (cut_tac x = frma and n = "toa - 1" in plus_one_helper2; simp)
    apply auto[1]
   apply clarsimp
   apply (drule_tac x = v' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>'' in meta_spec)
   apply (frule_tac p = pa in valid_ptr_not_in_frame_same; simp)
   apply clarsimp
   apply (rule_tac x = v' in exI)
   apply (rule_tac x = acc' in exI)
   apply (rule_tac x = \<sigma>'' in exI)
   apply clarsimp
   apply (rule_tac x = w1 in exI)
   apply clarsimp
   apply (rule_tac x = x in exI; clarsimp)
  apply (rule FalseE)
  apply (metis (no_types, hide_lams) not_less_iff_gr_or_eq word_less_cases)
  done

lemma upd_wa_mapAccumnb_bod_back_step:
  "\<lbrakk>upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f acc obsv s (\<sigma>', URecord [rp, (r, upd.uval_repr r)]);
    unat (size_of_num_type t) * unat len \<le> unat (max_word :: ptrtyp);
    1 + to \<le> len; frm < 1 + to; \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr))\<rbrakk>
    \<Longrightarrow> \<exists>\<sigma>a \<sigma>b r'' w1 w2 v v'.
      upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv s (\<sigma>a, URecord [rp, (r'', upd.uval_repr r'')]) \<and>
      \<sigma> (arr + size_of_num_type t * to) = option.Some v \<and>
      (\<xi>\<^sub>u, [URecord [(v, upd.uval_repr v), (r'', upd.uval_repr r''), (obsv, upd.uval_repr obsv)]] 
        \<turnstile> (\<sigma>a, App f (Var 0))\<Down>! (\<sigma>b, URecord [(v', upd.uval_repr v'), (r, upd.uval_repr r)])) \<and> 
      \<sigma>' = \<sigma>b((arr + size_of_num_type t * to) \<mapsto> v') \<and> frame \<sigma>a w1 \<sigma>b w2 \<and> 
      ({p} \<union> s \<union> {arr + size_of_num_type t * i | i. i < len}) \<inter> w1 = {}"
  apply (induct arbitrary: \<sigma>' r
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f acc obsv s "(\<sigma>', URecord [rp, (r, upd.uval_repr r)])"]; clarsimp)
  apply (erule upd_wa_mapAccumnb_bod.elims)
  apply (drule_tac x = t in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (clarsimp split: if_split_asm)
   apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f acc obsv s \<sigma>' v v' acc' \<sigma>1 w1 w2)
   apply (drule_tac x = v' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>1 in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (drule_tac x = r in meta_spec)
   apply clarsimp
   apply (case_tac "frm < to"; clarsimp)
    apply (drule meta_mp)
     apply (metis (no_types, hide_lams) add.commute inc_le plus_le_left_cancel_wrap word_le_less_eq word_le_not_less word_plus_strict_mono_right)
    apply (drule meta_mp)
     apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp)
    apply clarsimp
    apply (rule_tac x = \<sigma>a in exI)
    apply (rule_tac x = \<sigma>b in exI)
    apply (rule_tac x = r'' in exI)
    apply (rule conjI)
     apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
     apply (rule_tac x = v' in exI)
     apply (rule_tac x = acc' in exI)
     apply (rule_tac x = \<sigma>1 in exI)
     apply clarsimp
     apply (rule_tac x = w1 in exI)
     apply clarsimp
     apply (rule_tac x = w2 in exI)
     apply clarsimp
    apply (rule_tac x = w1a in exI)
    apply (rule_tac x = w2a in exI)
    apply (rule_tac x = va in exI)
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp split: if_splits)
     apply (drule_tac a = frm and b = to in word_mult_cancel_left_bounded[rotated 2]; simp?)
       apply (metis (no_types, hide_lams) add.commute less_imp_le plus_one_helper2 word_not_le word_not_simps(1))
      apply (erule disjE)
       apply (case_tac t; clarsimp)
      apply (rule FalseE)
      apply blast
     apply (erule_tac x = to in allE)
     apply (erule impE)
      apply (metis (no_types) add.commute plus_one_helper2 word_not_le word_not_simps(1))
     apply clarsimp
     apply (drule_tac p = "arr + size_of_num_type t * to" and w = w1 in valid_ptr_not_in_frame_same; simp)
      apply (drule_tac x = "arr + size_of_num_type t * to"  and S' = w1 in orthD1; simp)
      apply (rule disjI2)
      apply (rule_tac x = to in exI)
      apply clarsimp
      apply (metis (no_types) add.commute plus_one_helper2 word_not_le word_not_simps(1))
     apply clarsimp
    apply (rule_tac x = v'a in exI)
    apply clarsimp
   apply (rule_tac x = \<sigma> in exI)
   apply (rule_tac x = \<sigma>1 in exI)
   apply (rule_tac x = acc in exI)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (frule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (rule conjI)
    apply (frule_tac t = "(TPrim (Num t))" and len = len and arr = arr 
      in upd_wa_mapAccumnb_bod_preservation'; simp?)
   apply (rule_tac x = w1 in exI)
   apply (rule_tac x = w2 in exI)
   apply (rule_tac x = v in exI)
   apply clarsimp
   apply (rule conjI)
    apply (drule linorder_class.antisym_conv1)
    apply (cut_tac x = frm and n = to in plus_one_helper; simp add: add.commute)
   apply (rule_tac x = v' in exI)
   apply (subgoal_tac "frm = to")
    apply (erule upd_wa_mapAccumnb_bod.elims)
    apply (clarsimp simp: add.commute)
   apply (metis (mono_tags, hide_lams) add.commute not_less_iff_gr_or_eq plus_one_helper word_le_not_less)
  apply (rule FalseE)
  by auto

lemma upd_wa_mapAccumnb_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; upd.proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>'; (wa \<union> wb) \<inter> rc = {}; 
    wa \<inter> wb = {}; wa \<inter> rb = {}; p \<notin> wa \<union> rb \<union> wb \<union> rc; \<sigma> p = option.Some (UAbstract (UWA t len arr));
    upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f acc obsv (rb \<union> rc) (\<sigma>', res); 
    wa_abs_typing_u (UWA t len arr) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
    upd.uval_typing \<Xi>' \<sigma> acc u rb wb; upd.uval_typing \<Xi>' \<sigma> obsv v rc {};
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] 
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
    distinct [a0, a1, a2]; distinct [b0, b1]\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. 
      upd.uval_typing \<Xi>' \<sigma>' res (TRecord [(b0, (TCon ''WordArray'' [t] (Boxed Writable ptrl), Present)),
        (b1, (u, Present))] Unboxed) r' (insert p w') \<and> r' \<subseteq> (ra \<union> rb \<union> rc) \<and> frame \<sigma> (wa \<union> wb) \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule upd.u_t_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule upd.u_t_r_cons1[where r' = rb and w' = wb, simplified]; simp?)
     apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule_tac wa_abs_typing_u_elims(3); simp)
    apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule upd.u_t_r_empty)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (case_tac "len < 1 + to")
   apply (drule upd_wa_mapAccumnb_bod_back_step'; simp?)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = "ra \<union> rb" in exI)
   apply (rule_tac x = "wa \<union> wb" in exI)
   apply (clarsimp simp: upd.frame_id)
   apply (rule upd.u_t_struct; simp?)
   apply (subst Set.Un_insert_left[symmetric])
   apply (rule upd.u_t_r_cons1[where r' = rb and w' = wb, simplified]; simp?)
     apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
     apply (drule_tac wa_abs_typing_u_elims(3); simp)
    apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule upd.u_t_r_empty)
    apply (drule upd.type_repr_uval_repr(1); simp)
   apply (drule_tac wa_abs_typing_u_elims(3); simp)
  apply (subgoal_tac "to < len")
   apply (frule_tac wa_abs_typing_u_elims(1); clarsimp)
   apply (frule upd_wa_mapAccumnb_bod_preservation'; simp?)
   apply clarsimp
   apply (drule upd_wa_mapAccumnb_bod_back_step; simp?)
    apply (drule wa_abs_typing_u_elims(6); simp)
   apply clarsimp
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply (drule_tac x = "URecord [
    (UPtr p (RCon ''WordArray'' [RPrim (Num ta)]), RPtr (RCon ''WordArray'' [RPrim (Num ta)])),
    (r'', upd.uval_repr r'')]" in meta_spec)
   apply clarsimp
   apply (erule upd.u_t_recE; clarsimp)
   apply (erule upd.u_t_r_consE; simp?)
  apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_consE; simp?)
  apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_emptyE; clarsimp)
   apply (drule_tac r = "raa \<union> rc" and 
      w = waa and
      ?\<Gamma> = "[option.Some (TRecord [(a0, TPrim (Num ta), Present), (a1, u, Present), (a2, v, Present)] Unboxed)]" and
      \<tau> = "TRecord [(b0, TPrim (Num ta), Present), (b1, u, Present)] Unboxed" 
      in upd.preservation_mono(1); simp?)
    apply (rule upd.matches_ptrs_some[where ts = "[]" and r' = "{}" and w' = "{}", simplified])
     apply (rule upd.u_t_struct; simp?)
     apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified])
       apply (drule wa_abs_typing_u_elims(5))
       apply (erule_tac x = to in allE)
       apply clarsimp
       apply (rule upd.u_t_prim'; clarsimp)
      apply (rule upd.u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
         apply (rule upd.uval_typing_frame(1); simp?)
         apply blast
        apply (rule upd.u_t_r_empty)
       apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
      apply (rule disjointI)
      apply (frule_tac p = y and u = obsv in upd.uval_typing_valid(1)[rotated 1]; simp)
      apply clarsimp
      apply (drule_tac x = y in orthD2; simp)
      apply clarsimp
      apply (drule_tac p = y and  \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
      apply (subgoal_tac "y \<notin> w \<union> waa")
       apply blast
      apply (drule_tac t = "w \<union> waa" in sym)
      apply simp
      apply blast
     apply (frule wa_abs_typing_u_elims(5))
     apply (erule_tac x = to in allE)
     apply clarsimp
    apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply clarsimp
   apply (thin_tac "frame _ _ _ _")
   apply (cut_tac v = v' and l = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>b in upd.frame_single_update)
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = "{arr + size_of_num_type ta * i |i. i < len} \<union> w'a" in exI)
   apply clarsimp
   apply (erule upd.u_t_recE; clarsimp)
   apply (erule upd.u_t_r_consE; simp?)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym)+
   apply clarsimp
   apply (erule upd.u_t_r_consE; simp?)
   apply (erule conjE)+
   apply clarsimp
   apply (erule upd.u_t_r_emptyE; clarsimp)
   apply (erule u_t_primtE; clarsimp)
   apply (erule upd.u_t_p_absE[where s = "Boxed Writable _", simplified])
   apply (drule_tac s = "RCon _ _" in sym)
   apply (drule_tac t = "lit_type _" in sym; clarsimp)
   apply (frule_tac p = p and \<sigma> = \<sigma> in valid_ptr_not_in_frame_same; simp?)
   apply clarsimp
   apply (rule conjI)
    apply (rule upd.u_t_struct; simp?)
    apply (rule_tac upd.u_t_r_cons1[where r = "{}" and w = "insert _ _", simplified]; simp?)
       apply (rule_tac ptrl = ptrl and
      a = "UWA (TPrim (Num ta)) len arr"
      in upd.u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
         apply (frule_tac \<sigma> = \<sigma>a in wa_abs_typing_u_elims(3); clarsimp)
         apply (drule_tac \<sigma> = \<sigma>a and \<sigma>' = \<sigma>b in upd.abs_typing_frame; simp?)
         apply (rule wa_abs_typing_u_update; simp?)
        apply (rule conjI; clarsimp)
         apply (frule wa_abs_typing_u_elims(5))
         apply (erule_tac x = to in allE)
         apply clarsimp
        apply (drule_tac p = p and \<sigma> = \<sigma>a in valid_ptr_not_in_frame_same; simp?)
       apply (drule wa_abs_typing_u_elims(3); clarsimp)
      apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (drule_tac u = xb and r = rca and w = wc and \<sigma> = \<sigma>b in upd.uval_typing_frame(1); simp?)
        apply (frule_tac p = "arr + size_of_num_type ta * to" in upd.abs_typing_valid; simp?)
         apply (drule wa_abs_typing_u_elims(3); clarsimp)
         apply (rule_tac x = to in exI; simp)
        apply clarsimp
        apply (frule_tac w = wba in wa_abs_typing_u_elims(5))
        apply (erule_tac x = to in allE; clarsimp)
        apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>a in readonly_not_in_frame; simp?)
        apply (drule_tac x = "arr + size_of_num_type ta * to" and S = wba in orthD1; simp?)
        apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; simp)
       apply (drule_tac x = "arr + size_of_num_type ta * to" and S = wba and S' = raa in orthD1; simp?)
        apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; simp)
       apply (drule_tac x = "arr + size_of_num_type ta * to" and S' = rc in orthD1; simp?)
        apply (rule disjI1)
        apply (drule wa_abs_typing_u_elims(3); clarsimp)
        apply (rule_tac x = to in exI; clarsimp)
       apply clarsimp
       apply (drule_tac A = rca and B = "raa \<union> rc" and x = "arr + size_of_num_type ta * to" in in_mono)
       apply blast
      apply (rule upd.u_t_r_empty)
     apply (frule_tac p = p  and \<sigma> = \<sigma>a in readonly_not_in_frame; simp?)
     apply (rule disjointI)
     apply (frule_tac p = "xa" in upd.abs_typing_valid; simp?)
      apply clarsimp
      apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply clarsimp
     apply (frule_tac \<sigma> = \<sigma>a in wa_abs_typing_u_elims(5))
     apply (erule_tac x = i in allE; clarsimp)
     apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>a in readonly_not_in_frame; simp?)
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S = wba in orthD1; simp?)
     apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
     apply (rule_tac x = i in exI; simp)
    apply (rule conjI)
     apply (drule_tac A = rca and B = "raa \<union> rc" and x = p in in_mono; clarsimp)
    apply (rule disjointI)
    apply (drule_tac A = rca and B = "raa \<union> rc" and x = xa in in_mono; clarsimp)
    apply (erule disjE)
     apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = raa in orthD1; simp?)
     apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
     apply (rule_tac x = i in exI; simp)
    apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = rc in orthD1; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = i in exI; simp)
   apply (rule conjI)
    apply (drule_tac A = rca and B = "raa \<union> rc" and C = "ra \<union> rb \<union> rc" in subset_trans; simp?)
   apply (frule_tac p = p  and \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
   apply (frule_tac A = "w'" and x = p and B = "wba \<union> waa" in insert_ident; simp?)
   apply (drule_tac \<sigma> = \<sigma>a and s = wba in frame_expand(2))
    apply (frule_tac w = wba in wa_abs_typing_u_elims(5); clarsimp)
    apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
    apply (thin_tac "\<forall>i. p = arr + size_of_num_type ta * i \<longrightarrow> \<not> i < len")
    apply (erule_tac x = i in allE; clarsimp)
   apply (drule_tac \<sigma> = \<sigma> and \<sigma>' = \<sigma>a and \<sigma>'' = \<sigma>b in upd.frame_trans; simp?)
   apply (drule_tac \<sigma> = \<sigma> in upd.frame_app; simp?)
   apply clarsimp
   apply (subst (asm) insert_absorb[where A = "_ \<union> wb"])
    apply clarsimp
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; simp)
   apply (subst (asm) insert_absorb[where A = "_ \<union> _"])
    apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
    apply (rule_tac x = to in exI; simp)
   apply (drule_tac w = wba in wa_abs_typing_u_elims(3); clarsimp)
   apply (clarsimp simp: frame_def)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  done

definition upd_wa_mapAccumnb
  where
  "upd_wa_mapAccumnb \<Xi>' \<xi>\<^sub>u \<tau>i \<tau>o y z = 
    (let (y1, y2) = y
      in (\<exists>p frm to func acc obsv t u v a0 a1 a2 b0 b1 ra wa rb.
        y2 = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
                      (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
                      (func, RFun), (acc, upd.uval_repr acc), (obsv, upd.uval_repr obsv)] \<and> 
        (\<exists>len arr. y1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> 
          (\<forall>i<len. \<exists>x. y1 (arr + size_of_num_type t * i) = option.Some (UPrim x) \<and> lit_type x = Num t)) \<and> 
        is_uval_fun func \<and> upd.uval_typing \<Xi>' y1 acc u ra wa \<and> upd.uval_typing \<Xi>' y1 obsv v rb {} \<and>
        \<tau>i = TRecord [(a0, TPrim (Num t), Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
        \<tau>o = TRecord [(b0, TPrim (Num t), Present), (b1, u, Present)] Unboxed \<and>
        distinct [a0, a1, a2] \<and> distinct [b0, b1] \<and>
        (\<Xi>', [], [option.Some \<tau>i] \<turnstile> (App (uvalfun_to_exprfun func) (Var 0)) : \<tau>o) \<and> 
        upd_wa_mapAccumnb_bod \<xi>\<^sub>u y1 p frm to (uvalfun_to_exprfun func) acc obsv (ra \<union> rb) z))"

end (* of context *)

end