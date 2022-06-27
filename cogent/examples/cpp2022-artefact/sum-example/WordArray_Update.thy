theory WordArray_Update
  imports WordArray_Abstractions

begin

type_synonym ('f, 'a, 'l) ufoldmapdef = "('f, 'a, 'l) uabsfuns \<Rightarrow> ('f, 'a, 'l) store \<Rightarrow>
                                          'l \<Rightarrow> 32 word \<Rightarrow> 32 word \<Rightarrow> 'f expr \<Rightarrow> 
                                          type \<Rightarrow> ('f, 'a, 'l) uval \<Rightarrow> type \<Rightarrow> ('f, 'a, 'l) uval \<Rightarrow>
                                          (('f, 'a, 'l) store \<times> ('f, 'a, 'l) uval) \<Rightarrow> bool"

definition upd_wa_length_0
  where
  "upd_wa_length_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p t len arr. x2 = UPtr p (RCon ''WordArray'' [RPrim (Num t)]) \<and>
          x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> y2 = UPrim (LU32 len)))"

definition upd_wa_get_0
  where
  "upd_wa_get_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p idx t len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
          (UPrim (LU32 idx), RPrim (Num U32))] None \<and> x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and>
          (idx < len \<longrightarrow> x1 (arr + size_of_num_type t * idx) = option.Some y2) \<and>
            (\<not> idx < len \<longrightarrow> y2 = UPrim (zero_num_lit t))))"

definition upd_wa_put2_0
  where
  "upd_wa_put2_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in (\<exists>p idx val t len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
          (UPrim (LU32 idx), RPrim (Num U32)), (val, RPrim (Num t))] None \<and>
          x1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and>
          y2 = UPtr p (RCon ''WordArray'' [RPrim (Num t)]) \<and>
          (if idx < len 
              then y1 = x1((arr + size_of_num_type t * idx) \<mapsto> val)
              else y1 = x1)))"

function upd_wa_foldnb_bod :: "(funtyp, abstyp, ptrtyp) ufoldmapdef"
  where
  "upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv res = (\<exists>t len arr. 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and>
    (if frm < min to len then (\<exists>v acc' \<sigma>'. \<sigma> (arr + size_of_num_type t * frm) = option.Some v \<and> 
          (\<xi>\<^sub>u, [(URecord [(v, RPrim (Num t)), (acc, type_repr \<tau>a), 
            (obsv, type_repr \<tau>o)] None)] \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>', acc')) \<and>
          upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma>' p (frm + 1) to f \<tau>a acc' \<tau>o obsv res) 
    else (\<sigma>, acc) = res))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _, _, _, _). unat to - unat frm)"; clarsimp)
  apply (clarsimp simp: word_less_nat_alt)
  apply (cut_tac n = frm in unat_Suc2; clarsimp)
   apply (cut_tac y = to in word_not_simps(3); clarsimp simp: word_less_nat_alt)
  apply linarith
  done
declare upd_wa_foldnb_bod.simps[simp del]

function upd_wa_mapAccumnb_bod :: "(char list, atyp, ptrtyp) ufoldmapdef"
  where
  "upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv res = (\<exists>t len arr. 
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr)) \<and> 
    (if frm < min to len then 
      (\<exists>v v' acc' \<sigma>'. \<sigma> (arr + size_of_num_type t * frm) = option.Some v \<and>
      (\<xi>\<^sub>u, [(URecord [(v, RPrim (Num t)), (acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None)]
        \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>', URecord [ (v', RPrim (Num t)), (acc', type_repr \<tau>a)] None)) \<and>
      upd_wa_mapAccumnb_bod \<xi>\<^sub>u (\<sigma>'((arr + size_of_num_type t * frm) \<mapsto> v')) p (frm + 1) to f 
        \<tau>a acc' \<tau>o obsv res) 
    else res = (\<sigma>, URecord [
      (UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])), 
      (acc, type_repr \<tau>a)] None)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(_, _, _, frm, to, _, _, _,_,_,_). unat to - unat frm)"; clarsimp)
  apply (clarsimp simp: word_less_nat_alt)
  apply (cut_tac n = frm in unat_Suc2; clarsimp)
   apply (cut_tac y = to in word_not_simps(3); clarsimp simp: word_less_nat_alt)
  apply linarith
  done
declare upd_wa_mapAccumnb_bod.simps[simp del]

definition upd_wa_foldnb
  where
  "upd_wa_foldnb \<Xi>' \<xi>\<^sub>u \<tau> y z = 
    (let (y1, y2) = y
      in (\<exists>p frm to func acc obsv t u v a0 a1 a2.
        y2 = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
                      (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
                      (func, RFun), (acc, type_repr u), (obsv, type_repr v)] None \<and>
        (\<exists>len arr. y1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr))) \<and>
        is_uval_fun func \<and> 
        \<tau> = TRecord [(a0, TPrim (Num t), Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
        distinct [a0, a1, a2] \<and> (\<Xi>', 0,[], {}, [option.Some \<tau>] \<turnstile> (App (uvalfun_to_exprfun func) (Var 0)) : u) \<and>
        upd_wa_foldnb_bod \<xi>\<^sub>u y1 p frm to (uvalfun_to_exprfun func) u acc v obsv z))"

definition upd_wa_mapAccumnb
  where
  "upd_wa_mapAccumnb \<Xi>' \<xi>\<^sub>u \<tau>i \<tau>o y z = 
    (let (y1, y2) = y
      in (\<exists>p frm to func acc obsv t u v a0 a1 a2 b0 b1.
        y2 = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num t)]), RPtr (RCon ''WordArray'' [RPrim (Num t)])),
                      (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
                      (func, RFun), (acc, type_repr u), (obsv,type_repr v)] None \<and> 
        (\<exists>len arr. y1 p = option.Some (UAbstract (UWA (TPrim (Num t)) len arr))) \<and> 
        is_uval_fun func \<and>
        \<tau>i = TRecord [(a0, TPrim (Num t), Present), (a1, u, Present), (a2, v, Present)] Unboxed \<and>
        \<tau>o = TRecord [(b0, TPrim (Num t), Present), (b1, u, Present)] Unboxed \<and>
        distinct [a0, a1, a2] \<and> distinct [b0, b1] \<and>
        (\<Xi>', 0, [], {}, [option.Some \<tau>i] \<turnstile> (App (uvalfun_to_exprfun func) (Var 0)) : \<tau>o) \<and> 
        upd_wa_mapAccumnb_bod \<xi>\<^sub>u y1 p frm to (uvalfun_to_exprfun func) u acc v obsv z))"

context update_sem begin
lemma discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; 0, K', {} \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; 0, K', {} \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (force simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+

lemma frame_noalias_abs_typing:
assumes "frame \<sigma> u \<sigma>' u'"
and     "abs_typing \<Xi>' v name \<tau>s s r w \<sigma>"
shows   "u  \<inter> w = {} \<Longrightarrow> u' \<inter> w = {}"
and     "u  \<inter> r = {} \<Longrightarrow> u' \<inter> r = {}"
  using assms 
  by (auto iff:  set_eq_iff
           simp: frame_def
           dest: abs_typing_valid)

lemma frame_noalias_abs_typing':
assumes "frame \<sigma> u \<sigma>' u'"
and     "abs_typing \<Xi>' v name \<tau>s s r w \<sigma>"
shows   "u  \<inter> w = {} \<Longrightarrow> w \<inter> u' = {}"
and     "u  \<inter> r = {} \<Longrightarrow> r \<inter> u' = {}"
  using assms 
  by (auto iff:  set_eq_iff
           simp: frame_def
           dest: abs_typing_valid)


end (* of context *)


context WordArray begin

section wordarray_length

lemma upd_wa_length_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' [t] (Boxed ReadOnly ptrl)) r w;
    upd_wa_length_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_length_0_def)
  apply (erule u_t_ptrE; clarsimp)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: frame_def intro!: u_t_prim')
  done

section wordarray_get

lemma upd_wa_get_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
      (b, TPrim (Num U32), Present)] Unboxed) r w; upd_wa_get_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' t r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
 apply (clarsimp simp: upd_wa_get_0_def)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule u_t_r_emptyE; clarsimp)
  apply (erule u_t_primE; subst (asm) lit_type.simps; clarsimp)+
  apply (rule_tac x = "{}" in exI)+
  apply (frule wa_abs_typing_u_elims(1))
  apply (frule wa_abs_typing_u_elims(5))
  apply (clarsimp simp: frame_id)
  apply (erule_tac x = idx in allE)
  apply (case_tac "idx < len"; clarsimp)
   apply (rule u_t_prim'; clarsimp)+
  apply (case_tac ta; clarsimp intro!: u_t_prim')
  done

section wordarray_put2

lemma upd_wa_put2_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TRecord [(a, TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
      (b, TPrim (Num U32), Present), (c, t, Present)] Unboxed) r w; upd_wa_put2_0 (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl)) r' w' \<and>
      r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_t_r_emptyE)
  apply (erule u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (drule_tac t = "type_repr _" in sym)+
  apply (erule type_repr.elims[where y = "RPrim _", simplified]; clarsimp)
  apply (frule tprim_no_pointers(1); clarsimp)
  apply (frule tprim_no_pointers(2); clarsimp)
  apply (rule_tac x = r in exI)
  apply (rule_tac x = "insert p wa" in exI)
  apply (erule u_t_primtE; clarsimp)
  apply (drule_tac t = "lit_type _" in sym)
  apply (rule conjI)
   apply (rule_tac ptrl = ptrl and a = "UWA (TPrim (Num ta)) len arr" 
      in u_t_p_abs_w[where ts = "[TPrim _]", simplified]; simp?)
    apply (clarsimp split: if_split_asm)
    apply (rule wa_abs_typing_u_update; simp)
   apply (frule wa_abs_typing_u_elims(3); clarsimp split: if_splits)
  apply (clarsimp split: if_splits simp: frame_id)
  apply (frule wa_abs_typing_u_elims(3); clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
   apply (rule conjI, clarsimp)
    apply (erule_tac x = idx in allE; clarsimp)+
   apply (rule conjI; clarsimp)
  apply (rule conjI; clarsimp)
  done

section wordarray_fold_no_break

lemma upd_wa_foldnb_bod_to_geq_len:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [],{}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), 
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
     distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm len f u acc v obsv (\<sigma>', res);
     to \<ge> len
    \<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)"
  apply (induct arbitrary: rb wb
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>' res ta taa)
  apply (subst upd_wa_foldnb_bod.simps; clarsimp)
  apply (rule conjI; clarsimp; simp?)
   apply (rename_tac va acc' \<sigma>a)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply clarsimp
   apply (intro exI conjI, assumption)
   apply (drule_tac r = "rb \<union> rc" and
                    w = wb 
                    in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>="[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (drule abs_typing_frame[rotated 1]; simp?)
   apply (erule meta_impE)
    apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply (drule frame_noalias_abs_typing'(2); simp?)
     apply blast
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (drule wa_abs_typing_u_elims(2); clarsimp)
  apply (erule disjE; clarsimp)
  apply (rule FalseE)
  by auto

lemma upd_wa_foldnb_bod_to_geq_lenD:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [],{}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present),
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
      distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res);
     to \<ge> len
    \<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm len f u acc v obsv (\<sigma>', res)"
  apply (induct arbitrary: rb wb
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv \<sigma>' res ta taa)
  apply (subst upd_wa_foldnb_bod.simps; clarsimp)
  apply (rule conjI; clarsimp; simp?)
  apply (erule impE, simp)
  apply clarsimp
  apply (rename_tac va acc' \<sigma>a)
  apply (drule_tac x = acc' in meta_spec)
  apply (drule_tac x = \<sigma>a in meta_spec)
  apply (intro exI conjI, assumption)
  apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
  apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_t_struct; simp?)
    apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = frm in allE; clarsimp)
     apply (rule u_t_prim'; clarsimp)
    apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
     apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
     apply (rule u_t_r_empty)
    apply (subst Int_commute; assumption)
   apply (drule wa_abs_typing_u_elims(5))
   apply (erule_tac x = frm in allE; clarsimp)
   apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>="[]", simplified])
  apply clarsimp
  apply (rename_tac r' w')
  apply (drule_tac x = r' in meta_spec)
  apply (drule_tac x = w' in meta_spec)
  apply clarsimp
  apply (erule meta_impE)
   apply simp
  apply (erule meta_impE)
   apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
  apply (erule meta_impE)
   apply (drule abs_typing_frame[rotated 1]; simp?)
  apply (erule meta_impE)
   apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
  apply (erule meta_impE)
   apply (drule_tac p = p in readonly_not_in_frame; simp?)
  apply (erule meta_impE)
   apply (drule frame_noalias_abs_typing'(2); simp?)
   apply blast
  apply (erule meta_impE)
   apply (drule wa_abs_typing_u_elims(2); clarsimp)
  apply (erule meta_impE)
  apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
  apply (drule wa_abs_typing_u_elims(2); clarsimp)
  done

lemma upd_wa_foldnb_bod_back_step':
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present),
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
     distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f u acc v obsv (\<sigma>', res);
     len < 1 + to
    \<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)"
  apply (induct arbitrary: rb wb
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>' res ta taa)
  apply (subst upd_wa_foldnb_bod.simps; clarsimp)
  apply (rule conjI; clarsimp; simp?)
   apply (erule impE, simp)
   apply clarsimp
   apply (rename_tac va acc' \<sigma>a)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply (intro exI conjI, assumption)
   apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (drule abs_typing_frame[rotated 1]; simp?)
   apply (erule meta_impE)
    apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply (drule frame_noalias_abs_typing'(2); simp?)
    apply blast
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac v= obsv in frame_noalias_uval_typing'(2); simp?)
   apply (drule wa_abs_typing_u_elims(2); clarsimp)
  apply (erule disjE; clarsimp)
  apply (rule FalseE)
  apply (cut_tac a = 1 and b = to in add.commute; clarsimp)
  apply (drule plus_one_helper)
  apply (drule order_class.order.strict_trans2; simp)
  done

lemma upd_wa_foldnb_bod_back_step:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [TPrim (Num ta)] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present),
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
     distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f u acc v obsv (\<sigma>'', res');
     1 + to \<le> len; frm < 1 + to
    \<rbrakk> \<Longrightarrow> \<exists>\<sigma>' res va. upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)
                    \<and> \<sigma>' (arr + size_of_num_type ta * to) = option.Some va
                    \<and> (\<xi>\<^sub>u, [URecord [(va, RPrim (Num ta)), (res, type_repr u),
                        (obsv, type_repr v)] None] \<turnstile> (\<sigma>', App f (Var 0))\<Down>! (\<sigma>'', res'))"
  apply (induct arbitrary: rb wb
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>'', res')"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (clarsimp split: if_splits)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>'' res')
  apply (erule impE, simp)
  apply clarsimp
  apply (rename_tac va acc' \<sigma>a)
  apply (case_tac "frm < to"; clarsimp)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply clarsimp
   apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (erule impE, simp)
      apply clarsimp
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (erule impE, simp)
    apply clarsimp
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply clarsimp
   apply (erule meta_impE, simp)
   apply (erule meta_impE)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (drule abs_typing_frame[rotated 1]; simp?)
   apply (erule meta_impE)
    apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply (drule frame_noalias_abs_typing'(2); simp?)
    apply blast
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (metis add.commute inc_le plus_one_helper2 word_not_simps(1))
   apply clarsimp
   apply (rename_tac \<sigma>' res vb)
   apply (rule_tac x = \<sigma>' in exI)
   apply (rule_tac x = res in exI)
   apply (intro conjI exI; simp?)
   apply (subst upd_wa_foldnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp; simp?)
   apply (intro exI conjI; assumption)
  apply (subst upd_wa_foldnb_bod.simps; clarsimp)
  apply (cut_tac a = 1 and b = to in add.commute; clarsimp)
  apply (drule plus_one_helper; simp)
  apply (erule upd_wa_foldnb_bod.elims; clarsimp)
  done

lemma upd_wa_foldnb_bod_step:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [TPrim (Num ta)] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present),
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
     distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res);
     \<sigma>' (arr + size_of_num_type ta * to) = option.Some va;
     (\<xi>\<^sub>u, [URecord [(va, RPrim (Num ta)), (res, type_repr u),
      (obsv, type_repr v)] None] \<turnstile> (\<sigma>', App f (Var 0))\<Down>! (\<sigma>'', res'));
     frm \<le> to; to < len
    \<rbrakk> \<Longrightarrow> upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm (to + 1) f u acc v obsv (\<sigma>'', res')"
  apply (induct arbitrary: \<sigma>' res rb wb
                rule: upd_wa_foldnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (drule_tac x = len in meta_spec)
  apply (erule upd_wa_foldnb_bod.elims)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv \<sigma>' res)
  apply (clarsimp split: if_splits)
   apply (rename_tac vb acc' \<sigma>a)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (drule_tac x = res in meta_spec)
   apply clarsimp
   apply (drule_tac r = "rb \<union> rc" and
                    w = wb and
                    \<gamma> = "[URecord [(vb, RPrim (Num ta)), (acc, type_repr \<tau>a),
                          (obsv, type_repr \<tau>o)] None]"
                    in preservation_mono(1); simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply clarsimp
   apply (erule meta_impE)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (drule abs_typing_frame[rotated 1]; simp?)
   apply (erule meta_impE)
    apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply (drule frame_noalias_abs_typing'(2); simp?)
    apply blast
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (erule meta_impE)
    apply (simp add: inc_le)
   apply (subst upd_wa_foldnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp)
    apply (intro exI conjI; assumption)
   apply (rule FalseE)
   apply (simp add: less_is_non_zero_p1 plus_one_helper2)
  apply (erule disjE, clarsimp)
   apply (subst upd_wa_foldnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp)
    apply (subst upd_wa_foldnb_bod.simps; clarsimp)
    apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1); simp?)
     apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_t_struct; simp?)
      apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (drule wa_abs_typing_u_elims(5))
       apply (erule_tac x = to in allE; clarsimp)
       apply (rule u_t_prim'; clarsimp)
      apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_empty)
      apply (subst Int_commute; assumption)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = to in allE; clarsimp)
     apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
    apply clarsimp
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
    apply (intro exI, assumption)
   apply (rule FalseE)
   apply (simp add: less_is_non_zero_p1 plus_one_helper2)
  apply (rule FalseE)
  by auto

lemma upd_wa_foldnb_bod_preservation:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed ReadOnly ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present),
      (a2, v, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : u;
     distinct [a0, a1, a2];
     upd_wa_foldnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)
    \<rbrakk> \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' res u r' w' 
                \<and> r' \<subseteq> rb \<union> rc 
                \<and> frame \<sigma> wb \<sigma>' w'"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (intro exI conjI, assumption, blast, simp add: frame_id)
  apply clarsimp
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and
                      ra = ra and
                      wa = wa and
                      rb = rb and
                      rc = rc in upd_wa_foldnb_bod_back_step'; simp?)
   apply (elim meta_allE meta_impE; assumption)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_foldnb_bod.elims; clarsimp)
   apply (intro exI conjI, assumption, blast, simp add: frame_id)
  apply (frule wa_abs_typing_u_elims(1))
  apply (clarsimp simp: not_le not_less)
  apply (rename_tac ta)
  apply (frule_tac ptrl = ptrl and
                     ta = ta and
                     ra = ra and
                     wa = wa and
                     rb = rb and
                     wb = wb and
                     rc = rc 
                   in upd_wa_foldnb_bod_back_step; simp?)
  apply clarsimp
  apply (rename_tac \<sigma>a resa va)
  apply (elim meta_allE meta_impE, assumption)
  apply clarsimp
  apply (rename_tac rb' wb')
  apply (frule_tac r = "rb' \<union> rc" and w = wb' in preservation_mono(1)[rotated 3]; simp?)
  apply (drule (1) abs_typing_frame[rotated 1]; simp?)
   apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_t_struct; simp?)
    apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = to in allE)
     apply (erule impE)
      apply (metis add.commute plus_one_helper2 word_le_not_less)
     apply clarsimp
     apply (rule u_t_prim'; clarsimp)
    apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
     apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
     apply (rule u_t_r_empty)
    apply (drule_tac v = obsv in frame_noalias_uval_typing(2)[rotated 1]; simp?)
    apply blast
   apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
  apply clarsimp
  apply (intro exI conjI, assumption, blast)
  apply (rule frame_trans; simp)
  done

section wordarray_map_no_break

lemma upd_wa_mapAccumnb_bod_to_geq_len:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm len f u acc v obsv (\<sigma>', res);
     to \<ge> len
    \<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)"
  apply (induct arbitrary: rb wb
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac ta)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>' res)
  apply (clarsimp split: if_splits)
   apply (rename_tac x x' acc' \<sigma>a)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (rule conjI; clarsimp; simp?)
   apply (drule_tac x = x' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply clarsimp
   apply (intro exI conjI, assumption)
   apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply (erule u_t_recE; clarsimp)
   apply (erule u_t_r_consE; simp?)
   apply (erule conjE)+
   apply (drule_tac t= "type_repr _" in sym; clarsimp)
   apply (frule tprim_no_pointers(1); clarsimp)
   apply (frule tprim_no_pointers(2); clarsimp)
   apply (erule u_t_r_consE; clarsimp)
   apply (erule u_t_r_emptyE; clarsimp)
   apply (rename_tac xa xb tb r' w')
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (erule_tac x = frm in allE; clarsimp)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (erule u_t_primtE; clarsimp)
    apply (drule_tac t = "lit_type _" in sym; clarsimp)
    apply (drule_tac u = wb and
                     u' = w' and
                     \<sigma> = \<sigma> and
                     \<sigma>' = \<sigma>a 
                     in abs_typing_frame[rotated 1]; simp?)
    apply (drule wa_abs_typing_u_update; simp?)
   apply (cut_tac \<sigma> = \<sigma>a and
                  l = "arr + size_of_num_type ta * frm" and
                  v = xa
                  in frame_single_update)
   apply (frule wa_abs_typing_u_elims(3); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac u = xb and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
     apply (drule_tac p = "arr + size_of_num_type ta * frm" and
                      \<sigma> = \<sigma>
                      in readonly_not_in_frame; simp?; blast)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac u = obsv and \<sigma> = \<sigma> in uval_typing_frame(1); simp?)
    apply (drule_tac u = obsv and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (erule meta_impE; simp?)
   apply (drule frame_noalias_abs_typing'(1)[rotated 1]; simp?)
   apply blast
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  done

lemma upd_wa_mapAccumnb_bod_to_geq_lenD:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res);
     to \<ge> len
    \<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm len f u acc v obsv (\<sigma>', res)"
  apply (induct arbitrary: rb wb
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac ta)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv \<sigma>' res)
  apply (clarsimp split: if_splits)
   apply (rename_tac x x' acc' \<sigma>a)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (drule_tac x = x' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply clarsimp
   apply (intro exI conjI, assumption)
   apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply (erule u_t_recE; clarsimp)
   apply (erule u_t_r_consE; simp)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym; clarsimp)
   apply (frule tprim_no_pointers(1); clarsimp)
   apply (frule tprim_no_pointers(2); clarsimp)
   apply (erule u_t_r_consE; clarsimp)
   apply (erule u_t_r_emptyE; clarsimp)
   apply (rename_tac xa xb tb r' w')
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (erule_tac x = frm in allE; clarsimp)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule meta_impE)
    apply (erule u_t_primtE; clarsimp)
    apply (drule_tac t = "lit_type _" in sym; clarsimp)
    apply (drule_tac u = wb and
                     u' = w' and
                     \<sigma> = \<sigma> and
                     \<sigma>' = \<sigma>a 
                     in abs_typing_frame[rotated 1]; simp?)
    apply (drule wa_abs_typing_u_update; simp?)
   apply (cut_tac \<sigma> = \<sigma>a and
                  l = "arr + size_of_num_type ta * frm" and
                  v = xa 
                  in frame_single_update)
   apply (frule wa_abs_typing_u_elims(3); clarsimp)
   apply (erule meta_impE)
    apply (drule_tac u = xb and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
     apply (drule_tac p = "arr + size_of_num_type ta * frm" and
                      \<sigma> = \<sigma> 
                      in readonly_not_in_frame; simp?; blast)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac u = obsv and \<sigma> = \<sigma> in uval_typing_frame(1); simp?)
    apply (drule_tac u = obsv and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac p = p in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply blast
   apply (erule meta_impE)
    apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (erule meta_impE; simp?)
   apply (drule frame_noalias_abs_typing'(1); simp?)
   apply blast
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (rule FalseE)
  by auto

lemma upd_wa_mapAccumnb_bod_back_step':
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [t] (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f u acc v obsv (\<sigma>', res);
     len < 1 + to
    \<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)"
 apply (induct arbitrary: rb wb
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>', res)"])
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac ta)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>' res)
  apply (clarsimp split: if_splits)
   apply (rename_tac x x' acc' \<sigma>a)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (drule_tac x = x' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply clarsimp
   apply (rule conjI; clarsimp)
    apply (intro exI conjI, assumption)
    apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
     apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
      apply (rule u_t_struct; simp?)
      apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
       apply (drule wa_abs_typing_u_elims(5))
       apply (erule_tac x = frm in allE; clarsimp)
       apply (rule u_t_prim'; clarsimp)
      apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_empty)
      apply (subst Int_commute; assumption)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = frm in allE; clarsimp)
     apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
    apply clarsimp
    apply (rename_tac r' w')
    apply (drule_tac x = r' in meta_spec)
    apply (drule_tac x = w' in meta_spec)
    apply (erule u_t_recE; clarsimp)
    apply (erule u_t_r_consE; simp)
    apply (erule conjE)+
    apply (drule_tac t = "type_repr _" in sym; clarsimp)
    apply (frule tprim_no_pointers(1); clarsimp)
    apply (frule tprim_no_pointers(2); clarsimp)
    apply (erule u_t_r_consE; clarsimp)
    apply (erule u_t_r_emptyE; clarsimp)
    apply (rename_tac xa xb tb r' w')
    apply (erule meta_impE)
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply (erule_tac x = frm in allE; clarsimp)
     apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
    apply (erule meta_impE)
     apply (erule u_t_primtE; clarsimp)
     apply (drule_tac t = "lit_type _" in sym; clarsimp)
     apply (drule_tac u = wb and
                      u' = w' and
                      \<sigma> = \<sigma> and
                      \<sigma>' = \<sigma>a
                      in abs_typing_frame[rotated 1]; simp?)
     apply (drule wa_abs_typing_u_update; simp?)
    apply (cut_tac \<sigma> = \<sigma>a and
                   l = "arr + size_of_num_type ta * frm" and
                   v = xa 
                   in frame_single_update)
    apply (frule wa_abs_typing_u_elims(3); clarsimp)
    apply (erule meta_impE)
     apply (drule_tac u = xb and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
      apply (drule_tac p = "arr + size_of_num_type ta * frm" and
                       \<sigma> = \<sigma> 
                       in readonly_not_in_frame; simp?; blast)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac u = obsv and \<sigma> = \<sigma> in uval_typing_frame(1); simp?)
     apply (drule_tac u = obsv and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac p = p in readonly_not_in_frame; simp?)
    apply (erule meta_impE)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
    apply (erule meta_impE; simp?)
    apply (drule frame_noalias_abs_typing'(1); simp?)
    apply blast
   apply (rule FalseE)
   apply (metis add.commute le_step not_less_iff_gr_or_eq)
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (rule FalseE)
  by auto

lemma upd_wa_mapAccumnb_bod_back_step:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [TPrim (Num ta)] (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (1 + to) f u acc v obsv (\<sigma>''', res');
     1 + to \<le> len; frm < 1 + to
    \<rbrakk> \<Longrightarrow> \<exists>\<sigma>' \<sigma>'' res racc racc' x x' rp. upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)
      \<and> res = URecord [(rp, uval_repr rp), (racc, type_repr u)] None
      \<and> \<sigma>' (arr + size_of_num_type ta * to) = option.Some x
      \<and> (\<xi>\<^sub>u, [URecord [(x, RPrim (Num ta)), (racc, type_repr u),
          (obsv, type_repr v)] None]  \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! 
          (\<sigma>'', URecord [(x', RPrim (Num ta)), (racc', type_repr u)] None))
      \<and> res' = URecord [(rp, uval_repr rp), (racc', type_repr u)] None
      \<and> \<sigma>''' = \<sigma>''(arr + size_of_num_type ta * to \<mapsto> x')
      \<and> rp = UPtr p (RCon ''WordArray'' [type_repr t])"
  apply (induct arbitrary: \<sigma>''' res' rb wb
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>''', res')"])
  apply clarsimp
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm f \<tau>a acc \<tau>o obsv \<sigma>''' res')
  apply (clarsimp split: if_splits)
   apply (rename_tac x x' acc' \<sigma>a)
   apply (drule_tac x = x' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>a in meta_spec)
   apply (drule_tac x = \<sigma>''' in meta_spec)
   apply (drule_tac x = res' in meta_spec)
   apply clarsimp
   apply (drule_tac r = "rb \<union> rc" and w = wb in preservation_mono(1)[rotated 2]; simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply (erule u_t_recE; clarsimp)
   apply (erule u_t_r_consE; simp)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym; clarsimp)
   apply (frule tprim_no_pointers(1); clarsimp)
   apply (frule tprim_no_pointers(2); clarsimp)
   apply (erule u_t_r_consE; clarsimp)
   apply (erule u_t_r_emptyE; clarsimp)
   apply (rename_tac x' acc' tb r' w')
   apply (case_tac "frm < to"; clarsimp)
    apply (erule meta_impE)
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply (erule_tac x = frm in allE; clarsimp)
     apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
    apply (erule meta_impE)
     apply (erule u_t_primtE; clarsimp)
     apply (drule_tac t = "lit_type _" in sym; clarsimp)
     apply (drule_tac u = wb and
                      u' = w' and
                      \<sigma> = \<sigma> and
                      \<sigma>' = \<sigma>a 
                      in abs_typing_frame[rotated 1]; simp?)
     apply (drule wa_abs_typing_u_update; simp?)
    apply (cut_tac \<sigma> = \<sigma>a and
      l = "arr + size_of_num_type ta * frm" and
      v = x' in frame_single_update)
    apply (frule wa_abs_typing_u_elims(3); clarsimp)
    apply (erule meta_impE)
     apply (drule_tac u = acc' and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
      apply (drule_tac p = "arr + size_of_num_type ta * frm" and
                       \<sigma> = \<sigma> 
                       in readonly_not_in_frame; simp?; blast)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac u = obsv and \<sigma> = \<sigma> in uval_typing_frame(1); simp?)
     apply (drule_tac u = obsv and \<sigma> = \<sigma>a in uval_typing_frame(1); simp?)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac p = p in readonly_not_in_frame; simp?)
    apply (erule meta_impE)
     apply blast
    apply (erule meta_impE)
     apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
    apply (erule meta_impE)
     apply (drule frame_noalias_abs_typing'(1); simp?)
     apply blast
    apply (erule meta_impE)
     apply (metis (no_types, hide_lams) add.commute inc_le plus_le_left_cancel_wrap word_le_less_eq word_le_not_less word_plus_strict_mono_right)
    apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
    apply (intro exI conjI; simp?)
   apply (clarsimp simp: not_less_iff_gr_or_eq)
   apply (erule disjE; clarsimp?)
    apply (rule FalseE)
    apply (metis add.commute inc_le not_less)
   apply (cut_tac a = 1 and b = to in add.commute)
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (erule_tac x = to in allE; clarsimp)
   apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (intro exI conjI; simp?)
  apply (rule FalseE)
  by auto

lemma word_set_compr_helper: 
  "(c :: ('a :: len8) word) < 1 + e \<Longrightarrow>
    {a + b * i | i. i < c \<and> d \<le> i \<and> i < e} = {a + b * i | i. i < c \<and> d \<le> i \<and> i < 1 + e}"
  apply (rule equalityI)
   apply (rule subsetI; clarsimp)
   apply (rule_tac x = i in exI; simp)
  apply (rule subsetI; clarsimp)
  apply (rule_tac x = i in exI; simp)
  by (metis add.commute inc_le word_le_less_eq word_le_not_less)

lemma word_set_compr_helper2: 
  "(e :: ('a :: len8) word) \<le> d \<Longrightarrow>
    {a + b * i | i. i < c \<and> d \<le> i \<and> i < e} = {}"
  by auto

lemma word_set_compr_helper3: 
  "\<lbrakk>1 + (e::('a::len8) word) \<noteq> 0; 1 + e \<le> c; d < 1 + e; \<forall>i < c. \<forall>j < c. i = j \<longleftrightarrow> b * i = b * j\<rbrakk> \<Longrightarrow>
    insert (a + b * e) {a + b * i | i. i < c \<and> d \<le> i \<and> i < e} = {a + b * i | i. i < c \<and> d \<le> i \<and> i < 1 + e}"
  apply (rule equalityI)
   apply (drule unatSuc)
   apply (rule subsetI; clarsimp simp: word_le_nat_alt word_less_nat_alt)
   apply (erule disjE)
    apply (rule_tac x = e in exI; clarsimp)
   apply clarsimp
   apply (rename_tac i)
   apply (rule_tac x = i in exI; clarsimp)
  apply (rule subsetI; clarsimp)
  apply (rename_tac i)
  apply (erule_tac x = i in allE; clarsimp)
  apply (erule_tac x = i in allE; clarsimp)
  apply (erule_tac x = e in allE)
  apply (erule impE)
   apply (drule unatSuc; clarsimp simp: word_le_nat_alt word_less_nat_alt)
  apply clarsimp
  apply (clarsimp simp: not_less)
  apply (subgoal_tac "i = e", clarsimp)
  apply (thin_tac "i \<noteq> e")
  apply (thin_tac "b * i \<noteq> b * e")
  apply (drule unatSuc; clarsimp simp: word_le_nat_alt word_less_nat_alt)
  apply (subst unat_arith_simps(3))
  apply unat_arith
  done

lemma upd_wa_mapAccumnb_bod_preservation:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' \<tau>s (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb; p \<notin> rb; p \<notin> rc;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv (\<sigma>', res)
  \<rbrakk> \<Longrightarrow> \<exists>rp ta racc r' w'. 
      res = URecord [(rp, uval_repr rp), (racc, type_repr u)] None
    \<and> rp = UPtr p (RCon ''WordArray'' [type_repr t])
    \<and> t = TPrim (Num ta)
    \<and> wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' \<tau>s (Boxed Writable ptrl) ra wa \<sigma>'
    \<and> uval_typing \<Xi>' \<sigma>' racc u r' w'
    \<and> r' \<subseteq> rb \<union> rc
    \<and> (insert p wa) \<inter> r' = {}
    \<and> (insert p wa) \<inter> w' = {}
    \<and> ra \<inter> w' = {}
    \<and> frame \<sigma> ({arr + size_of_num_type ta * i | i. i < len \<and> frm \<le> i \<and> i < to } \<union> wb) \<sigma>' 
        ({arr + size_of_num_type ta * i | i. i < len \<and> frm \<le> i \<and> i < to } \<union> w')"
  apply (induct to arbitrary: \<sigma>' res)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: frame_id)
   apply blast
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac ta)
  apply (case_tac "len < 1 + to")
   apply (drule_tac ptrl = ptrl and
                      ra = ra and
                      wa = wa and
                      rb = rb and
                      wb = wb and
                      rc = rc 
                    in upd_wa_mapAccumnb_bod_back_step'[rotated -2]; simp?)
   apply (elim meta_allE meta_impE; simp?)
   apply clarsimp
   apply (rename_tac racc r' w')
   apply (rule_tac x = r' in exI)
   apply (rule_tac x = w' in exI)
   apply (clarsimp simp: word_set_compr_helper)
  apply (case_tac "1 + to \<le> frm")
   apply (frule_tac y = "1 + to" and x = frm in leD)
   apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
   apply (rule_tac x = rb in exI)
   apply (rule_tac x = wb in exI)
   apply (clarsimp simp: frame_id word_set_compr_helper2)
   apply blast
  apply (drule_tac ptrl = ptrl and
                     ra = ra and
                     wa = wa and
                     rb = rb and
                     wb = wb and
                     rc = rc 
                   in upd_wa_mapAccumnb_bod_back_step[rotated -3]; simp?)
  apply clarsimp
  apply (elim meta_allE meta_impE, assumption)
  apply clarsimp
  apply (rename_tac \<sigma>'' \<sigma>''' racc racc' x x' r' w')
  apply (drule wa_abs_typing_u_elims(5))
  apply (drule_tac r = "r' \<union> rc" and w = w' in preservation_mono(1)[rotated 3]; simp?)
   apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
    apply (rule u_t_struct; simp?)
    apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = to in allE; clarsimp)
     apply (erule impE)
      apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply clarsimp
     apply (rule u_t_prim'; clarsimp)
    apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
     apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
      apply (drule wa_abs_typing_u_elims(3); clarsimp)
      apply blast
     apply (rule u_t_r_empty)
    apply (frule_tac v = obsv in frame_noalias_uval_typing'(2); (simp add: Int_Un_distrib)?; clarsimp?)
     apply (drule wa_abs_typing_u_elims(3); clarsimp)
     apply blast
    apply (subst Int_commute; blast)
   apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
  apply clarsimp
  apply (rename_tac r'' w'')
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; simp)+
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym; clarsimp)
  apply (erule u_t_r_emptyE; clarsimp)
  apply (erule u_t_primtE; clarsimp)
  apply (drule_tac t = "lit_type _" in sym)
  apply clarsimp
  apply (rename_tac racc' r'' w'' l)
  apply (rule conjI)
   apply (rule wa_abs_typing_u_update; simp?)
    apply (frule_tac u = w' and u' = w'' in abs_typing_frame; simp?)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (cut_tac \<sigma> = \<sigma>''' and
                 l = "arr + size_of_num_type ta * to" and
                 v = "UPrim l" 
                 in frame_single_update)
  apply (rule_tac x = r'' in exI)
  apply (rule_tac x = w'' in exI)
  apply (rule conjI)
   apply (drule_tac u = racc' in uval_typing_frame(1)[rotated 3]; simp?)
    apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
    apply (rule_tac S = wa in orthD1; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (intro exI conjI, simp)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply simp
   apply (rule contra_subsetD; simp?)
   apply simp
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (rule conjI)
    apply (rule_tac S = wa in orthD1; simp?)
    apply (intro exI conjI, simp)
    apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
   apply (rule_tac S' = wa in orthD2; simp?)
   apply (intro exI conjI, simp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (intro conjI)
        apply clarsimp
        apply (rename_tac x)
        apply (drule_tac A = r'' and B = "r' \<union> rc" and c = x in subsetD; simp)
        apply (drule_tac A = r' and B = "rb \<union> rc" and c = x in subsetD; simp)
       apply clarsimp
       apply (drule_tac A = r'' and B = "r' \<union> rc" and c = p in subsetD; simp)
      apply (rule disjointI)
      apply (rename_tac x y)
      apply (drule_tac A = r'' and B = "r' \<union> rc" and c = y in subsetD; simp)
      apply (rule disjE; blast)
     apply (frule wa_abs_typing_u_elims(3); clarsimp)
     apply (drule_tac p = p and \<sigma> = \<sigma> in valid_ptr_not_in_frame_same; simp?)
      apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
     apply (drule_tac p = p and w = w' in readonly_not_in_frame; simp?)
    apply (rule disjointI)
    apply (rename_tac x y)
    apply (frule wa_abs_typing_u_elims(5))
    apply (frule wa_abs_typing_u_elims(3); clarsimp)
    apply (rename_tac i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (drule_tac p = "arr + size_of_num_type ta * i" and \<sigma> = \<sigma>'' in readonly_not_in_frame; simp?)
    apply (drule_tac x = "arr + size_of_num_type ta * i" and S' = w' in orthD1; simp?)
    apply (intro exI conjI; simp)
   apply (drule wa_abs_typing_u_elims(3); clarsimp)
  apply (drule_tac s = "{arr + size_of_num_type ta * i |i. i < len \<and> frm \<le> i \<and> i < 1 + to}" and
      \<sigma> = \<sigma>''' in frame_expand(2); simp?)
   apply (drule_tac u = w' and u' = w'' in abs_typing_frame[rotated 1]; simp?)
   apply (drule wa_abs_typing_u_elims(5); clarsimp)
   apply (rename_tac i)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule_tac s = "{arr + size_of_num_type ta * i |i. i < len \<and> frm \<le> i \<and> i < 1 + to}" and 
      \<sigma> = \<sigma>'' in frame_expand(2); simp?)
   apply (frule wa_abs_typing_u_elims(5); clarsimp)
   apply (rename_tac i)
   apply (erule_tac x = i in allE; clarsimp)+
  apply (drule_tac p = "arr + size_of_num_type ta * to" and \<sigma> = \<sigma> in frame_expand(1))
   apply (erule_tac x = to in allE; clarsimp)
   apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)  
  apply (subst (asm) Un_insert_left[symmetric])
  apply (subst (asm) word_set_compr_helper3; simp?)
   apply (drule distinct_indices; simp?)
  apply (subst (asm) Un_insert_left[symmetric])
  apply (subst (asm) word_set_compr_helper3; simp?)
   apply (drule distinct_indices; simp?)
  apply (drule unatSuc; clarsimp simp: word_less_nat_alt word_le_nat_alt)
  apply (subst (asm) insert_absorb, clarsimp)
   apply (intro exI conjI; simp?; unat_arith?; simp?)
  apply (subst (asm) insert_absorb, clarsimp)
   apply (intro exI conjI; simp?; unat_arith?; simp?)
  apply (drule_tac \<sigma> = \<sigma> and \<sigma>' = \<sigma>'' and \<sigma>'' = \<sigma>''' in frame_trans; simp?)
  apply (drule_tac s = w'' in frame_expand(2))
   apply clarsimp
   apply (rename_tac pa)
   apply (drule_tac p = pa and u = racc' in uval_typing_valid(1)[rotated 1]; simp?)
  apply (erule frame_trans; simp?)
  apply (clarsimp simp: Un_commute)
  done

lemma upd_wa_mapAccumnb_bod_step:
  "\<lbrakk> proc_ctx_wellformed \<Xi>';
     proc_env_matches_ptrs \<xi>\<^sub>u \<Xi>';
     \<sigma> p = option.Some (UAbstract (UWA t len arr));
     wa_abs_typing_u \<Xi>' (UWA t len arr) ''WordArray'' [TPrim (Num ta)] (Boxed Writable ptrl) ra wa \<sigma>;
     uval_typing \<Xi>' \<sigma> acc u rb wb;
     uval_typing \<Xi>' \<sigma> obsv v rc {};
     p \<notin> wa; p \<notin> wb; p \<notin> rb; p \<notin> rc;
     ra \<inter> wb = {}; 
     rb \<inter> wa = {}; 
     rc \<inter> wa = {}; rc \<inter> wb = {};
     wa \<inter> wb = {};
     \<Xi>', 0, [], {}, [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)]
      \<turnstile> (App f (Var 0)) : TRecord [(b0, t, Present), (b1, u, Present)] Unboxed;
     distinct [a0, a1, a2]; distinct [b0, b1];
     upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv
      (\<sigma>', URecord [(rp, uval_repr rp), (racc, type_repr u)] None); 
     rp = UPtr p (RCon ''WordArray'' [type_repr t]) ;
     \<sigma>' (arr + size_of_num_type ta * to) = option.Some va;
     (\<xi>\<^sub>u, [URecord [(va, RPrim (Num ta)), (racc, type_repr u),
      (obsv, type_repr v)] None] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>!
      (\<sigma>'', URecord [(va', RPrim (Num ta)), (racc', type_repr u)] None));
     frm \<le> to; to < len
    \<rbrakk> \<Longrightarrow> upd_wa_mapAccumnb_bod \<xi>\<^sub>u \<sigma> p frm (to + 1) f u acc v obsv
        (\<sigma>''(arr + size_of_num_type ta * to \<mapsto> va'),
        URecord [(rp, uval_repr rp), (racc', type_repr u)] None)"
    apply (induct arbitrary: \<sigma>' racc rb wb
                rule: upd_wa_mapAccumnb_bod.induct[of _ \<xi>\<^sub>u \<sigma> p frm to f u acc v obsv "(\<sigma>',  URecord [(rp, uval_repr rp), (racc, type_repr u)] None)"])
  apply clarsimp
  apply (drule_tac x = ta in meta_spec)
  apply (drule_tac x = len in meta_spec)
  apply (drule_tac x = arr in meta_spec)
  apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp split: if_splits)
  apply (rename_tac \<xi>\<^sub>u \<sigma> p frm to f \<tau>a acc \<tau>o obsv \<sigma>' tb)
  apply (erule impE)
   apply (clarsimp simp: word_le_nat_alt word_less_nat_alt)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (case_tac "frm < to"; clarsimp)
   apply (frule_tac a = frm and b = to in order.strict_implies_not_eq; clarsimp)
   apply (frule_tac a = frm and b = to and c = len in order.strict_trans; clarsimp)
   apply (rename_tac vb v' acc' \<sigma>''')
   apply (drule_tac x = v' in meta_spec)
   apply (drule_tac x = acc' in meta_spec)
   apply (drule_tac x = \<sigma>''' in meta_spec)
   apply (drule_tac x = \<sigma>' in meta_spec)
   apply (drule_tac x = racc in meta_spec)
   apply clarsimp
   apply (drule_tac r = "rb \<union> rc" and
                    w = wb and
                    \<gamma> = "[URecord [(vb, RPrim (Num ta)), (acc, type_repr \<tau>a),
                          (obsv, type_repr \<tau>o)] None]"
                    in preservation_mono(1); simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = frm in allE; clarsimp)
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = frm in allE; clarsimp)
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (rename_tac r' w')
   apply (drule_tac x = r' in meta_spec)
   apply (drule_tac x = w' in meta_spec)
   apply (erule meta_impE)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (rule conjI; clarsimp)
    apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (erule u_t_recE; clarsimp)
   apply (erule u_t_r_consE; simp)
   apply (erule conjE)+
   apply (drule_tac t = "type_repr _" in sym; clarsimp)
   apply (erule u_t_primtE; clarsimp)
   apply (drule_tac t = "lit_type _"  in sym; clarsimp)
   apply (erule meta_impE)
    apply (drule (1) abs_typing_frame; simp?)
    apply (rule wa_abs_typing_u_update; simp?)
   apply (rename_tac l)
   apply (frule_tac u = obsv and ?w1.0 = wb in uval_typing_frame(1)[rotated -1]; simp?)
   apply (drule_tac u = obsv and
      \<sigma> = \<sigma>''' and
      l1 = "arr + size_of_num_type ta * frm" and 
      v1 = "UPrim l" in uval_typing_frame(1)[OF frame_single_update, rotated -1]; simp?)
    apply (drule wa_abs_typing_u_elims(3))
    apply (rule_tac S' = wa in orthD2; clarsimp)
    apply (intro exI conjI, simp, clarsimp simp: word_le_nat_alt word_less_nat_alt)
   apply (erule u_t_r_consE; clarsimp)
   apply (erule u_t_r_emptyE; clarsimp)
   apply (rename_tac acc' tb r' w')
   apply (frule wa_abs_typing_u_elims(3))
   apply (drule_tac u = acc' and 
      l1 = "arr + size_of_num_type ta * frm" and 
      v1 = "UPrim l" in uval_typing_frame(1)[OF frame_single_update, rotated -1]; simp?)
     apply (rule_tac \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
     apply (rule_tac S' = wa in orthD2; clarsimp simp: Int_commute)
     apply (intro exI conjI, simp, clarsimp simp: word_le_nat_alt word_less_nat_alt)
    apply (erule contra_subsetD; simp?)
    apply (rule conjI)
     apply (rule_tac S' = wa in orthD2; clarsimp)
     apply (intro exI conjI, simp, clarsimp simp: word_le_nat_alt word_less_nat_alt)
    apply (rule_tac S' = wa in orthD2; clarsimp)
    apply (intro exI conjI, simp, clarsimp simp: word_le_nat_alt word_less_nat_alt)
   apply (erule meta_impE)
    apply (rule_tac \<sigma> = \<sigma> in readonly_not_in_frame; simp?)
   apply (erule meta_impE)
    apply (erule contra_subsetD; simp?)
   apply (erule meta_impE)
    apply clarsimp
    apply (erule disjoint_subset; simp?)
    apply (clarsimp simp: Int_Un_distrib2)
   apply (erule meta_impE)
    apply (frule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
   apply (erule meta_impE)
    apply (rule disjointI)
    apply (rename_tac x y)
    apply clarsimp
    apply (rename_tac i)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = i in allE; clarsimp)+
    apply (drule_tac p = "arr + size_of_num_type ta * i" in readonly_not_in_frame; simp?)
    apply (rule_tac S = wa and S' = wb in orthD1; simp?)
    apply (intro exI conjI; simp)
   apply (erule meta_impE)
    apply (meson inc_le word_le_less_eq)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)  
   apply (rule conjI; clarsimp)
    apply (rule_tac x = "UPrim l" in exI)
    apply (rule_tac x = acc' in exI)
    apply (rule_tac x = \<sigma>''' in exI)
    apply (rule conjI; simp)
   apply (rule FalseE)
   apply (simp add: less_is_non_zero_p1 plus_one_helper2)
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
  apply (rule conjI; clarsimp)
   apply (intro exI conjI, simp)
   apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)
   apply (frule wa_abs_typing_u_elims(3))
   apply (rule conjI; clarsimp)
   apply (drule_tac r = "rb \<union> rc" and
                    w = wb and
                    \<gamma> = "[URecord [(va, RPrim (Num ta)), (acc, type_repr \<tau>a),
                          (obsv, type_repr \<tau>o)] None]"
                    in preservation_mono(1); simp?)
    apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
     apply (rule u_t_struct; simp?)
     apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
      apply (drule wa_abs_typing_u_elims(5))
      apply (erule_tac x = to in allE; clarsimp)+
      apply (rule u_t_prim'; clarsimp)
     apply (rule u_t_r_cons1[where r' = rc and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
      apply (rule u_t_r_empty)
     apply (subst Int_commute; assumption)
    apply (drule wa_abs_typing_u_elims(5))
    apply (erule_tac x = to in allE; clarsimp)+
    apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>= "[]", simplified])
   apply clarsimp
   apply (drule_tac p = p in valid_ptr_not_in_frame_same; simp?)
   apply (intro exI, assumption)
  apply (rule FalseE)
  apply (meson less_is_non_zero_p1 word_overflow)
  done

end (* of context *)

end