(*
  This file contains the update semantics to C correspondence lemmas for word array functions
*)
theory WordArray_UpdCCorres
  imports WordArray_UAbsFun
begin

context update_sem_init begin

definition
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> (\<xi>' matches-u \<Xi>') \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
      (\<forall>r' w'. val_rel x x'
        \<and> (\<Xi>', \<sigma> \<turnstile> x :u prod.fst (prod.snd (prod.snd (prod.snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>)
        \<longrightarrow> \<not> prod.snd (afun_mon x' st)
            \<and> (\<forall>st' y'. (y', st') \<in> prod.fst (afun_mon x' st)
                \<longrightarrow> (\<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y)
                    \<and> val_rel y y' \<and> (\<sigma>', st') \<in> srel))))"

lemma absfun_corres:
  "abs_fun_rel \<Xi>' srel s \<xi>' afun' \<sigma> st (\<gamma> ! i) v'
  \<Longrightarrow> i < length \<gamma> \<Longrightarrow> val_rel (\<gamma> ! i) v'
  \<Longrightarrow> \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi>' s)))))
  \<Longrightarrow> corres srel
     (App (AFun s [] ls) (Var i))                                            
     (do x \<leftarrow> afun' v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (clarsimp simp: corres_def abs_fun_rel_def)
  apply (frule matches_ptrs_length, simp)
  apply (frule(2) matches_ptrs_proj_single')
  apply clarsimp
  apply (erule impE, blast)
  apply clarsimp
  apply (elim allE, drule mp, blast)
  apply clarsimp
  apply (intro exI conjI[rotated], assumption+)
  apply (rule u_sem_abs_app)
    apply (rule u_sem_afun)
   apply (rule u_sem_var)
  apply simp
  done

lemma abs_fun_rel_def':
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
        (\<forall>r' w'. val_rel x x' \<and> 
            \<Xi>', \<sigma> \<turnstile> x :u prod.fst (prod.snd (prod.snd (prod.snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>
        \<longrightarrow> \<lbrace>\<lambda>s0. s0 = st\<rbrace> 
              afun_mon x' 
            \<lbrace>\<lambda>y' s'. \<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y) \<and> (\<sigma>',s') \<in> srel \<and> val_rel y y'\<rbrace>!))" 
  by (fastforce  simp: abs_fun_rel_def validNF_def valid_def no_fail_def)

end (* of context *)

sublocale WordArray \<subseteq> Generated _ wa_abs_typing_u wa_abs_repr
  by (unfold_locales)

context WordArray begin
              
section "Correspondence Lemmas Between Update Semantics and C"

lemma upd_C_wordarray_put2_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; 
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_put2_0'')))));
     \<xi>0' ''wordarray_put2_0'' = upd_wa_put2_0\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr 
        (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_put2_0'' [] ls) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_put2_0_type_def abbreviated_type_defs)
  apply (erule u_t_recE)
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_t_r_emptyE)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = "t2_C.arr_C v'" in allE)
   apply (erule_tac x = "values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (t2_C.idx_C v')" in allE)
   apply (clarsimp simp: heap_rel_ptr_def heap_rel_meta_def wa_abs_repr_def is_valid_simp type_rel_simp)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t2_C.idx_C v'" in allE)+
   apply (clarsimp simp: val_rel_simp heap_simp type_rel_simp)
  apply clarsimp
  apply (monad_eq simp: upd_wa_put2_0_def)
  apply (case_tac "idx_C v' < len"; clarsimp)
  apply (rule conjI)
    apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (frule_tac p = "t2_C.arr_C v'" in all_heap_rel_ptrD; simp?)
    apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
   apply (clarsimp simp: val_rel_simp heap_simp is_valid_simp)
   apply (drule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t2_C.idx_C v'" in allE; clarsimp)
   apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x. x(values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (idx_C v') := val_C v')) st)" and
      x = "(values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v')" and
      uv' = "UPrim (LU32 (val_C v'))" and uv = "UPrim x"
      in all_heap_rel_updE; simp?; clarsimp?)
    apply (clarsimp simp: type_rel_simp)
   apply (drule_tac upd_h = "(heap_w32_update
      (\<lambda>x. x(values_C (heap_WordArray_u32_C st (t2_C.arr_C v')) +\<^sub>p uint (idx_C v') := val_C v')) st)" and
      x = "(values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v')" and
      uv' = "UPrim (LU32 (val_C v'))" and uv = "UPrim x"
      in all_heap_rel_updE; simp?; clarsimp?)
   apply (rule conjI, clarsimp simp: val_rel_simp)
   apply clarsimp
   apply (rule FalseE)
   apply (cut_tac p = p and q = "((values_C (heap_WordArray_u32_C st (t2_C.arr_C v'))) +\<^sub>p uint (idx_C v'))" in ptr_val_inj)
   apply (clarsimp simp: ptr_add_def)
  apply (monad_eq simp: wordarray_put2_0'_def)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t2_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: val_rel_simp heap_simp is_valid_simp)
  done

lemmas upd_C_wordarray_put2_corres = upd_C_wordarray_put2_corres_gen[rotated -1, of \<xi>0, simplified fun_eq_iff]

lemma upd_C_wordarray_length_corres_gen:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; 
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_length_0'')))));
     \<xi>0' ''wordarray_length_0''= upd_wa_length_0\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr 
         (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_length_0'' [] ls) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_length_0_type_def)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = v' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp wa_abs_repr_def is_valid_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_length_0_def)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = v' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp wa_abs_repr_def heap_simp val_rel_simp)
  apply (monad_eq simp: wordarray_length_0'_def)
  done

lemmas upd_C_wordarray_length_corres = upd_C_wordarray_length_corres_gen[rotated -1, of \<xi>0, simplified fun_eq_iff]

lemma upd_C_wordarray_get_corres_gen:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_get_0'')))));
     \<xi>0' ''wordarray_get_0'' = upd_wa_get_0\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr 
         (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_get_0'' [] ls) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) \<Xi>_def)
  apply (clarsimp simp: val_rel_simp wordarray_get_0_type_def abbreviated_type_defs)
  apply (erule u_t_recE)
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_r_emptyE)
  apply (erule u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_get_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
   apply (drule_tac p = "t1_C.p1_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) len arr)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp wa_abs_repr_def val_rel_simp is_valid_simp heap_simp)
   apply (drule not_le_imp_less)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t1_C.p2_C v'" in allE; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C v')) +\<^sub>p uint (t1_C.p2_C v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD; simp add: type_rel_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_get_0_def)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "t1_C.p2_C v'" in allE)
   apply (monad_eq simp: wordarray_get_0'_def word_less_nat_alt word_le_nat_alt)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
   apply (drule_tac p = "t1_C.p1_C v'" and uv = "UAbstract (UWA (TPrim (Num U32)) len arr)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp wa_abs_repr_def val_rel_simp is_valid_simp heap_simp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C v')) +\<^sub>p uint (t1_C.p2_C v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD;
          clarsimp simp: type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_get_0'_def)
  apply blast
  done

lemmas upd_C_wordarray_get_corres = upd_C_wordarray_get_corres_gen[rotated -1, of \<xi>0, simplified fun_eq_iff]


abbreviation "mk_urecord xs \<equiv> URecord (map (\<lambda>x. (x, uval_repr x)) xs) None"
definition "foldmap_measure i end \<equiv> unat end - unat i"
definition "foldmap_bounds frm to len i e 
  \<equiv> frm \<le> i \<and> e = min to len \<and> (frm < e \<longrightarrow> i \<le> e) \<and> ((\<not>(frm < e)) \<longrightarrow> frm = i)"
definition "foldmap_inv foldmap n \<xi>' \<sigma> p frm i f acc obsv \<sigma>' res s' res'
  \<equiv> foldmap \<xi>' \<sigma> p frm i f (foldmap_acc_type n) acc (foldmap_obsv_type n) obsv (\<sigma>', res) \<and>
      val_rel res res' \<and> (\<sigma>', s') \<in> state_rel"
definition "foldmap_inv_stat obsv obsv' \<equiv> val_rel obsv obsv'"

lemma whileLoop_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoop_inv c b init I (measure M) \<lbrace> Q \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoop c b init \<lbrace> Q \<rbrace>!"
  by (metis assms whileLoop_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done

lemma \<Xi>_wordarray_fold_no_break_0:
  "\<Xi> ''wordarray_fold_no_break_0'' = wordarray_fold_no_break_0_type"
  by (clarsimp simp: \<Xi>_def)

abbreviation "elem_type x \<equiv> (present_type \<circ> (\<lambda>xs. xs ! 0) \<circ> rec_type_list) x"

lemma fold_dispatch_wp:
  "\<lbrakk>proc_ctx_wellformed \<Xi>; proc_env_matches_ptrs \<xi>0' \<Xi>;
    wa_abs_typing_u \<Xi> (UWA (TPrim (Num num)) len arr) ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl) r w \<sigma>;
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num num)) len arr));
    uval_typing \<Xi> \<sigma> acc (foldmap_acc_type ''wordarray_fold_no_break_0'') ra wa;
    uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_fold_no_break_0'') ro {};
    wa \<inter> r = {}; wa \<inter> ro = {}; p \<notin> wa;
    (\<Xi>, 0, [], {}, [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<turnstile> 
    (App f (Var 0)) : (foldmap_funret_type ''wordarray_fold_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
        (App f (Var 0)) (do ret <- dispatch f_num x'; gets (\<lambda>s. ret) od) 
        \<xi>0' [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<sigma> s;
    elem_type (foldmap_funarg_type ''wordarray_fold_no_break_0'') = TPrim (Num num)\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (a', n') = (a, n) \<and> n < e \<and>
      (\<exists>\<sigma>' res x v. args = t3_C.elem_C_update (\<lambda>_. v) a \<and>
        \<sigma>' (arr + size_of_num_type num * n) = option.Some x \<and> val_rel x v \<and>
      foldmap_inv upd_wa_foldnb_bod ''wordarray_fold_no_break_0'' \<xi>0' \<sigma> p frm n f acc obsv \<sigma>' res sa (t3_C.acc_C args)) \<and>
      foldmap_bounds frm to len n e \<and> foldmap_inv_stat obsv (t3_C.obsv_C args)\<rbrace>
      dispatch f_num args 
    \<lbrace>\<lambda>ret sb. (\<exists>\<sigma>' res.
        foldmap_inv upd_wa_foldnb_bod ''wordarray_fold_no_break_0'' \<xi>0' \<sigma> p frm (n + 1) f acc obsv \<sigma>' res sb ret) \<and>
      foldmap_inv_stat obsv (t3_C.obsv_C args) \<and> foldmap_bounds frm to len (n + 1) e \<and> 
      foldmap_measure (n + 1) to < foldmap_measure n' to\<rbrace>!"
  apply (subst validNF_def)
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (subst valid_def)
  apply (subst no_fail_def)
  apply clarsimp
  apply (subst all_imp_conj_distrib[symmetric])
  apply (clarsimp simp: foldmap_inv_def)
  apply (rename_tac sa \<sigma>' res x v)
  apply (erule_tac x = "mk_urecord [x, res, obsv]" in allE)
  apply (erule_tac x = args in allE)
  apply (erule impE)
   apply (subst val_rel_simp; simp add: foldmap_inv_stat_def)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = sa in allE)
  apply (clarsimp simp: corres_def)
  apply (frule_tac t = "TPrim (Num num)" and
      ptrl = ptrl and
      ra = r and
      wa = w and
      rb = ra and
      wb = wa and
      rc = ro in upd_wa_foldnb_bod_preservation[rotated -1];
      (simp add: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)?;
      (clarsimp simp: Int_commute)?)
      apply (frule wa_abs_typing_u_elims(2); clarsimp)
     apply (frule wa_abs_typing_u_elims(2); clarsimp)
    apply (frule wa_abs_typing_u_elims(2); clarsimp)
   apply (frule wa_abs_typing_u_elims(2); clarsimp)
  apply (rename_tac r' w')
  apply (subgoal_tac "matches_ptrs \<Xi> \<sigma>' [(mk_urecord [x, res, obsv])]
      [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] (r' \<union> ro) w'")
   apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
   apply (erule impE, blast)
   apply clarsimp
   apply (rename_tac ret sb)
   apply (erule_tac x = ret in allE)
   apply (erule_tac x = sb in allE)
   apply clarsimp 
   apply (frule update_sem.preservation
                  [OF update_sem_axioms, where \<tau>s = "[]" and \<epsilon>="[]"and K = "[]" and L=0 and C="{}",
                   simplified subst_wellformed_nothing, simplified]; simp?)
    apply clarsimp
   apply (rename_tac \<sigma>'' res' rb wb)
   apply (clarsimp simp: foldmap_bounds_def)
   apply (case_tac "frm < to \<and> frm < len"; clarsimp)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = n in allE; clarsimp)
   apply (frule_tac p = "arr + (size_of_num_type num) * n" in valid_ptr_not_in_frame_same; simp?)
    apply (drule_tac x = "arr + 4 * n" and S = r in orthD1; simp?)
    apply (drule_tac wa_abs_typing_u_elims(2)[where \<tau>s = "[_]", simplified]; simp)
    apply blast
   apply clarsimp
   apply (drule_tac ta = num and 
      arr = arr and 
      len = len and 
      res' = res' and 
      \<sigma>' = \<sigma>' and 
      \<sigma>'' = \<sigma>'' and
      ptrl = ptrl and
      ra = r and 
      wa = w and
      rc = ro in upd_wa_foldnb_bod_step[rotated -5]; simp?; clarsimp?)
        apply (drule_tac v = obsv in type_repr_uval_repr(1); simp)
        apply (drule_tac v = res in type_repr_uval_repr(1); simp)
       apply (drule wa_abs_typing_u_elims(2); clarsimp)
      apply (drule wa_abs_typing_u_elims(2); clarsimp)
     apply (drule wa_abs_typing_u_elims(2); clarsimp)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (rule conjI)
    apply (intro exI conjI; simp)
   apply (frule_tac a = n and k = to in less_is_non_zero_p1)
   apply (drule unatSuc2; clarsimp simp: word_less_nat_alt word_le_nat_alt foldmap_measure_def)
   apply linarith
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule u_t_struct; simp?)
   apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (subst (asm) val_rel_word; clarsimp)
     apply (rule u_t_prim'; clarsimp)
    apply (rule u_t_r_cons1[where r' = ro and w' = "{}", simplified]; simp?)
      apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_empty)
      apply (drule_tac v = obsv in type_repr_uval_repr(1); simp)
     apply (drule_tac v = obsv in frame_noalias_uval_typing(2)[rotated 1]; simp?)
     apply blast
    apply (drule_tac v = res in type_repr_uval_repr(1); simp)
  apply (subst (asm) val_rel_word; clarsimp)
  apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon> = "[]", simplified])
  done

lemma upd_C_wordarray_fold_no_break_corres_gen:
  "\<lbrakk>proc_env_matches_ptrs \<xi>0' \<Xi>; i < length \<gamma>; val_rel (\<gamma> ! i) v'; 
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd(prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))));
    D \<in> k \<or> S \<in> k; 0, K',{} \<turnstile> (foldmap_obsv_type ''wordarray_fold_no_break_0'') :\<kappa> k;
    \<gamma> ! i = URecord fs None; f = prod.fst (fs ! 3);  
    (\<Xi>, 0, [], {}, [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<turnstile> 
    (App (uvalfun_to_exprfun f) (Var 0)) : (foldmap_funret_type ''wordarray_fold_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (uvalfun_to_exprfun f) (Var 0)) (do ret <- dispatch_t4' (t5_C.f_C v') x'; gets (\<lambda>s. ret) od) 
      \<xi>0' [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_fold_no_break_0'')] \<sigma> s;
    \<xi>1' ''wordarray_fold_no_break_0'' = upd_wa_foldnb \<Xi> \<xi>0' (foldmap_funarg_type ''wordarray_fold_no_break_0'');
    elem_type (foldmap_funarg_type ''wordarray_fold_no_break_0'') = TPrim (Num num)\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_fold_no_break_0'' [] []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1' \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule absfun_corres; simp)
  apply (clarsimp simp: abs_fun_rel_def'; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (subst (asm) val_rel_ptr_def; clarsimp)
  apply (subst (asm) val_rel_fun_tag)
  apply (subst (asm) val_rel_word)
  apply (subst (asm) val_rel_word)
  apply (clarsimp simp: upd_wa_foldnb_def wordarray_fold_no_break_0'_def)
  apply (rename_tac pwa_rep frm_rep to_rep f_rep acc a_rep obsv o_rep wa_rep)
  apply (erule u_t_recE; clarsimp)
  apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac r len arr)
  apply (erule u_t_r_consE; simp)
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_r_emptyE; clarsimp)
  apply (frule tfun_no_pointers(1))
  apply (frule tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac acc ra wa obsv ro wo)
  apply (drule discardable_or_shareable_not_writable; simp?)
  apply clarsimp
  apply (subst unknown_bind_ignore)+
  apply (clarsimp simp: join_guards)
  apply wp
      apply (clarsimp simp: unknown_bind_ignore split: prod.split)
      apply (rename_tac var e)
      apply (rule_tac M = "\<lambda>((_, i), _). foldmap_measure i (t5_C.to_C v')" and 
      I = "\<lambda>(a, b) s. (\<exists>\<sigma>' res.
          foldmap_inv upd_wa_foldnb_bod ''wordarray_fold_no_break_0'' \<xi>0' \<sigma> (ptr_val (t5_C.arr_C v'))
          (t5_C.frm_C v') b (uvalfun_to_exprfun f) acc obsv \<sigma>' res s (t3_C.acc_C a)) \<and>
          foldmap_inv_stat obsv (t3_C.obsv_C a) \<and>
          foldmap_bounds (t5_C.frm_C v') (t5_C.to_C v') len b e" in whileLoop_add_invI; simp?)
      apply (wp; clarsimp simp: unknown_bind_ignore split: prod.splits)
          apply (rename_tac sa a n args a' n')
          apply (rule_tac a = a and wa = wa and ra = ra and ro = ro and w = "{}" and r = r and
            ptrl = None in fold_dispatch_wp[rotated 2]; simp?) 
             apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)+
         apply wp
        apply wp
       apply clarsimp
       apply (rename_tac args j \<sigma>' res)
       apply (clarsimp simp: foldmap_bounds_def foldmap_inv_def)
       apply (frule wa_abs_typing_u_elims(5))
       apply (erule_tac x = j in allE; clarsimp)
       apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
       apply (drule_tac acc = acc and
      obsv = obsv and
      rb = ra and
      wb = wa and
      rc = ro and
      ptrl = None and
      ra = r and
      wa = "{}" in upd_wa_foldnb_bod_preservation; simp?; (clarsimp simp: Int_commute)?)
       apply (frule_tac p = "ptr_val (t5_C.arr_C v')" in valid_ptr_not_in_frame_same; simp?)
       apply (drule_tac p = "arr + (size_of_num_type num) * j" in valid_ptr_not_in_frame_same; simp?)
        apply (drule_tac x = "arr + (size_of_num_type num) * j" and S' = wa and S = r in orthD1; simp?)
        apply (drule wa_abs_typing_u_elims(2); clarsimp)
        apply blast
       apply (thin_tac "_ \<in> state_rel")
       apply (rule conjI)
        apply (rule_tac x = \<sigma>' in exI)
        apply (rule_tac x = res in exI)
        apply (rule_tac x = "UPrim x" in exI)
        apply clarsimp
        apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
        apply (rotate_tac -1)
        apply (drule_tac p = "Ptr(arr + (size_of_num_type num) * j)" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp)
        apply (rule_tac x = "heap_w32 s (PTR(32 word) (arr + (size_of_num_type num) * j))" in exI)
        apply (drule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
        apply (clarsimp simp: val_rel_WordArray_u32_C_def ptr_add_def heap_simp mult.commute)
       apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
       apply (rotate_tac -1)
       apply (drule_tac p = "Ptr(arr + (size_of_num_type num) * j)" in all_heap_rel_ptrD; simp?)
        apply (clarsimp simp: type_rel_simp)
       apply (drule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
        apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
       apply (clarsimp simp: is_valid_simp heap_simp val_rel_WordArray_u32_C_def ptr_add_def mult.commute)
      apply (rule conjI)
       apply (erule u_t_funafuntE; clarsimp)
      apply (rename_tac x' j \<sigma>' res)
      apply (rule_tac x = \<sigma>' in exI)
      apply (rule_tac x = res in exI)
      apply (clarsimp simp: foldmap_inv_def)
      apply (clarsimp simp: \<Xi>_wordarray_fold_no_break_0 wordarray_fold_no_break_0_type_def abbreviated_type_defs)
      apply (unfold foldmap_bounds_def)
      apply (erule conjE)+
      apply (case_tac "t5_C.frm_C v' < e")
       apply (erule impE, assumption)
       apply (thin_tac "_ \<longrightarrow> _")
       apply clarsimp
       apply (case_tac "j < t5_C.to_C v'"; clarsimp)
       apply (rule_tac ptrl = None and
      ra = r and 
      wa = "{}" and
      rb = ra and
      wb = wa and
      rc = ro in upd_wa_foldnb_bod_to_geq_len; (simp add: Int_commute)?; clarsimp?)
      apply (erule impE, assumption)
      apply (thin_tac "_ \<longrightarrow> _")
      apply clarsimp
      apply (erule upd_wa_foldnb_bod.elims; clarsimp)
      apply (case_tac "t5_C.frm_C v' < t5_C.to_C v'"; subst upd_wa_foldnb_bod.simps; clarsimp)
     apply wp
    apply wp
   apply (rule validNF_select_UNIV)
  apply (clarsimp simp: foldmap_inv_stat_def)
  apply (clarsimp simp: order.strict_implies_order)
  apply (clarsimp simp: foldmap_inv_def state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t5_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: is_valid_simp val_rel_WordArray_u32_C_def heap_simp)
  apply (subst upd_wa_foldnb_bod.simps; clarsimp)+
  apply (rule conjI; clarsimp)
   apply (subst min_def)
   apply (subst (asm) not_le[symmetric])+
   apply (subst if_not_P; simp?)
  apply (subst min_def)
  apply (clarsimp simp: not_le)
  done

lemma \<Xi>_wordarray_map_no_break_0:
  "\<Xi> ''wordarray_map_no_break_0'' = wordarray_map_no_break_0_type"
  by (clarsimp simp: \<Xi>_def)

lemma map_dispatch_wp:
  "\<lbrakk>proc_ctx_wellformed \<Xi>; proc_env_matches_ptrs \<xi>0' \<Xi>;
    wa_abs_typing_u \<Xi> (UWA (TPrim (Num num)) len arr) ''WordArray'' [TPrim (Num num)] (Boxed Writable ptrl) r w \<sigma>;
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num num)) len arr));
    uval_typing \<Xi> \<sigma> acc (foldmap_acc_type ''wordarray_map_no_break_0'') ra wa;
    uval_typing \<Xi> \<sigma> obsv (foldmap_obsv_type ''wordarray_map_no_break_0'') ro {}; wa \<inter> r = {}; p \<notin> w;
    p \<notin> r; w \<inter> wa = {}; w \<inter> (ra \<union> ro) = {}; wa \<inter> ro = {}; p \<notin> wa; p \<notin> ra; p \<notin> ro; p = ptr_val p';
    (\<Xi>, 0, [], {}, [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<turnstile> 
    (App f (Var 0)) : (foldmap_funret_type ''wordarray_map_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
        (App f (Var 0)) (do ret <- dispatch f_num x'; gets (\<lambda>s. ret) od) 
        \<xi>0' [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<sigma> s;
     elem_type (foldmap_funarg_type ''wordarray_map_no_break_0'') = TPrim (Num num)\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (a', n') = (a, n) \<and> n < e \<and>
      (\<exists>\<sigma>' res x v. args = t6_C.elem_C_update (\<lambda>_. v) a \<and>
        \<sigma>' (arr + size_of_num_type U32 * n) = option.Some x \<and> val_rel x v \<and>
      foldmap_inv upd_wa_mapAccumnb_bod ''wordarray_map_no_break_0'' \<xi>0' \<sigma> p frm n f acc obsv \<sigma>'
        res sa (t10_C p' (t6_C.acc_C args))) \<and>
      foldmap_bounds frm to len n e \<and> foldmap_inv_stat obsv (t6_C.obsv_C args)\<rbrace>
      dispatch f_num args 
     \<lbrace>\<lambda>ret sb. (\<exists>\<sigma>' res. 
        foldmap_inv upd_wa_mapAccumnb_bod ''wordarray_map_no_break_0'' \<xi>0' \<sigma> p frm (n + 1) f acc obsv \<sigma>' res 
          (heap_w32_update (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n 
            then t7_C.p1_C ret else x a) sb) (t10_C p' (t7_C.p2_C ret))) \<and>
        foldmap_inv_stat obsv (t6_C.obsv_C args) \<and>
        foldmap_bounds frm to len (n + 1) e \<and>
        foldmap_measure (n + 1) to < foldmap_measure n' to \<and>
        is_valid_WordArray_u32_C sb p' \<and>
        is_valid_w32 sb (values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n)\<rbrace>!"
  apply (subst validNF_def)
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (subst valid_def)
  apply (subst no_fail_def)
  apply clarsimp
  apply (subst all_imp_conj_distrib[symmetric])
  apply (clarsimp simp: foldmap_inv_def)
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (rename_tac sa \<sigma>' res x v)
  apply (subst (asm) Int_Un_distrib; clarsimp)
  apply (frule_tac t = "TPrim (Num num)" and
      ra = r and
      wa = w and
      rb = ra and
      wb = wa and
      rc = ro in upd_wa_mapAccumnb_bod_preservation; simp?; (clarsimp simp: Int_commute)?)
  apply (rename_tac sa \<sigma>' x v racc r' w')
  apply (erule_tac x = "mk_urecord [x, racc, obsv]" in allE)
  apply (erule_tac x = args in allE)
  apply clarsimp
  apply (erule impE)
   apply (clarsimp simp: val_rel_simp foldmap_inv_stat_def)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = sa in allE)
  apply (clarsimp simp: corres_def)
  apply (subgoal_tac "matches_ptrs \<Xi> \<sigma>' [(mk_urecord [x, racc, obsv])]
      [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] (r' \<union> ro) w'")
   apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
   apply (erule impE, blast)
   apply clarsimp
   apply (rename_tac ret sb)
   apply (erule_tac x = ret in allE)
   apply (erule_tac x = sb in allE)
   apply clarsimp
   apply (frule update_sem.preservation[OF update_sem_axioms, 
                   where \<tau>s = "[]" and \<epsilon>="[]"and K = "[]" and L=0 and C="{}",
                   simplified subst_wellformed_nothing, simplified]; simp?)
   apply clarsimp
   apply (rename_tac \<sigma>'' res' r'a w'a)
   apply (erule u_t_rectE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (erule u_t_r_contE; clarsimp)
   apply (rename_tac x' rd wd racc' r'a w'a)
   apply (frule_tac v = x' in tprim_no_pointers(1); clarsimp)
   apply (frule_tac v = x' in tprim_no_pointers(2); clarsimp)
   apply (clarsimp simp: foldmap_bounds_def)
   apply (case_tac "frm < to \<and> frm < len"; clarsimp)
   apply (drule_tac ta = num and
      arr = arr and
      len = len and
      va = x and
      racc' = racc' and
      va' = x' and
      ra = r and
      wa = w and
      ptrl = ptrl and
      \<sigma>' = \<sigma>' and
      \<sigma>'' = \<sigma>'' and
      racc = racc and
      rc = ro in upd_wa_mapAccumnb_bod_step; simp?; clarsimp?)
    apply (drule_tac v = obsv in type_repr_uval_repr(1))
    apply (drule_tac v = racc in type_repr_uval_repr(1))
    apply (clarsimp simp: val_rel_word)
   apply (thin_tac "_ \<in> state_rel")
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
   apply (frule_tac p = p and \<sigma> = \<sigma> in valid_ptr_not_in_frame_same; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (drule_tac p = "ptr_val p'" and \<sigma> = \<sigma>' and \<sigma>' = \<sigma>'' and w = w' in valid_ptr_not_in_frame_same[rotated -1]; simp?)
   apply (drule_tac p = "arr + (size_of_num_type num) * n" and \<sigma> = \<sigma>' in valid_ptr_not_in_frame_same; simp?)
    apply (drule_tac x = "arr + (size_of_num_type num) * n" and S = w' in orthD2; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (intro exI conjI; simp)
   apply (frule_tac p = p' in all_heap_rel_ptrD; simp?)
    apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
   apply (frule_tac p = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n" and uv = x in all_heap_rel_ptrD; simp?)
     apply (clarsimp simp: val_rel_simp heap_simp)
    apply (clarsimp simp: type_rel_simp val_rel_simp)
   apply (clarsimp simp: is_valid_simp heap_simp)
   apply (rule conjI)
    apply (intro exI conjI, assumption, clarsimp simp: val_rel_simp)
     apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n then t7_C.p1_C ret else x a) sb)" and
      uv = x and uv' = x' and x = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n"
      in all_heap_rel_updE; simp?; clarsimp?)
        apply (clarsimp simp: val_rel_simp)
       apply (drule_tac v = x' in type_repr_uval_repr(1); simp add: val_rel_simp)
      apply (clarsimp simp: val_rel_simp type_rel_simp)
     apply (clarsimp simp: val_rel_simp)
     apply (drule_tac upd_h = "(heap_w32_update 
      (\<lambda>x a. if a = values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n then t7_C.p1_C ret else x a) sb)" and
      uv = x and uv' = x' and x = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n" and
      is_v = is_valid_w32 in all_heap_rel_updE; simp?; clarsimp?)
        apply (clarsimp simp: val_rel_simp)
       apply (drule_tac v = x' in type_repr_uval_repr(1); simp add: val_rel_simp)
      apply (rule conjI)
      apply (clarsimp simp: val_rel_simp)
     apply (rename_tac pa)
      apply (cut_tac p = pa and q = "values_C (heap_WordArray_u32_C sb p') +\<^sub>p uint n" in ptr_val_inj)
      apply clarsimp
     apply (clarsimp simp: ptr_add_def mult.commute val_rel_simp)
   apply (frule_tac a = n and k = to in less_is_non_zero_p1)
   apply (drule unatSuc2; clarsimp simp: word_less_nat_alt word_le_nat_alt foldmap_measure_def)
   apply linarith
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (rule matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule u_t_struct; simp?)
  apply (rule u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (subst (asm) val_rel_word; clarsimp)
     apply (rule u_t_prim'; clarsimp)
    apply (rule u_t_r_cons1[where r' = ro and w' = "{}", simplified]; simp?)
      apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
       apply (drule wa_abs_typing_u_elims(3); clarsimp)
       apply blast
      apply (rule u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
       apply (rule u_t_r_empty)
      apply (drule_tac v = obsv in type_repr_uval_repr(1); simp)
     apply (frule_tac v = obsv in frame_noalias_uval_typing'(2); (simp add: Int_Un_distrib)?; clarsimp?)
      apply (drule wa_abs_typing_u_elims(3); clarsimp)
      apply blast
     apply (subst Int_commute; blast)
    apply (drule_tac v = racc in type_repr_uval_repr(1); simp)
   apply (subst (asm) val_rel_word; clarsimp)
  apply (rule matches_ptrs_empty[where \<tau>s = "[]" and \<epsilon>="[]", simplified])
  done

lemma upd_C_wordarray_map_no_break_corres_gen:
  "\<lbrakk>proc_env_matches_ptrs \<xi>0' \<Xi>; i < length \<gamma>; val_rel (\<gamma> ! i) v';
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd (prod.snd (prod.snd (\<Xi> ''wordarray_map_no_break_0'')))));
     D \<in> k \<or> S \<in> k; 0, K' , {} \<turnstile> (foldmap_obsv_type ''wordarray_map_no_break_0'') :\<kappa> k;
    \<gamma> ! i = URecord fs None; f = prod.fst (fs ! 3);
    (\<Xi>, 0, [], {}, [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<turnstile> 
    (App (uvalfun_to_exprfun f) (Var 0)) : (foldmap_funret_type ''wordarray_map_no_break_0''));
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (uvalfun_to_exprfun f) (Var 0)) (do ret <- dispatch_t8' (t9_C.f_C v') x'; gets (\<lambda>s. ret) od) 
      \<xi>0' [x] \<Xi> [option.Some (foldmap_funarg_type ''wordarray_map_no_break_0'')] \<sigma> s;
    \<xi>1' ''wordarray_map_no_break_0'' = upd_wa_mapAccumnb \<Xi> \<xi>0' 
      (foldmap_funarg_type ''wordarray_map_no_break_0'') (foldmap_funret_type ''wordarray_map_no_break_0'');
    elem_type (foldmap_funarg_type ''wordarray_map_no_break_0'') = TPrim (Num num)\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_map_no_break_0'' [] []) (Var i)) (do x <- main_pp_inferred.wordarray_map_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1' \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule absfun_corres; simp)
  apply (clarsimp simp: abs_fun_rel_def'; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (subst (asm) val_rel_ptr_def; clarsimp)
  apply (subst (asm) val_rel_fun_tag)
  apply (subst (asm) val_rel_word)
  apply (subst (asm) val_rel_word)
  apply (clarsimp simp: upd_wa_mapAccumnb_def wordarray_map_no_break_0'_def)
  apply (rename_tac pwa_rep frm_rep to_rep f_rep acc a_rep o_rep wa_rep)
  apply (erule u_t_recE; clarsimp)
  apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
  apply (erule u_t_r_consE; clarsimp)
  apply (rename_tac r w r' w')
  apply (erule u_t_ptrE; clarsimp)
  apply (rename_tac w)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac len arr)
  apply (erule u_t_r_consE; simp)
  apply (erule u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_r_emptyE; clarsimp)
  apply (frule tfun_no_pointers(1))
  apply (frule tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac acc ra wa obsv ro wo)
  apply (drule_tac v = obsv in discardable_or_shareable_not_writable(1); simp?)
  apply (subst unknown_bind_ignore)+
  apply (clarsimp simp: join_guards) 
  apply wp
      apply (clarsimp simp: unknown_bind_ignore split: prod.split)
       apply (rename_tac var e)
       apply (rule_tac M = "\<lambda>((_, i), _). foldmap_measure i (t9_C.to_C v')" and 
      I = "\<lambda>(a, b) s. (\<exists>\<sigma>' res.
          foldmap_inv upd_wa_mapAccumnb_bod ''wordarray_map_no_break_0'' \<xi>0' \<sigma> (ptr_val (t9_C.arr_C v'))
          (t9_C.frm_C v') b (uvalfun_to_exprfun f) acc obsv  \<sigma>' res s (t10_C (t9_C.arr_C v') (t6_C.acc_C a))) \<and>
          foldmap_inv_stat obsv (t6_C.obsv_C a) \<and>
          foldmap_bounds (t9_C.frm_C v') (t9_C.to_C v') len b e" in whileLoop_add_invI; simp?)
       apply (wp; clarsimp simp: unknown_bind_ignore split: prod.splits)
           apply (rename_tac sa a n args a' n')
           apply (clarsimp simp: conj_left_commute[of "is_valid_w32 _ _", simplified])
           apply (clarsimp simp: conj_commute[of "is_valid_w32 _ _", simplified])
           apply (rule_tac a = a and wa = wa and ra = ra and ro = ro and w = w and r = r and
              ptrl = None in map_dispatch_wp; simp?)
              apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)+
          apply wp
         apply wp
        apply clarsimp
        apply (rename_tac args j \<sigma>' res)
        apply (clarsimp simp: foldmap_inv_def foldmap_bounds_def)
        apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
        apply (subst (asm) Int_Un_distrib; clarsimp)
        apply (drule_tac ptrl = None and
      ra = r and
      wa = w and
      rb = ra and
      wb = wa and
      rc = ro in upd_wa_mapAccumnb_bod_preservation; simp?; (clarsimp simp: Int_commute)?)  
        apply (subst conj_commute[of "is_valid_w32 _ _"]; clarsimp)
        apply (subst conj_commute[of "is_valid_w32 _ _"]; clarsimp)
        apply (frule_tac \<sigma> = \<sigma>' in wa_abs_typing_u_elims(5), erule_tac x = j in allE, clarsimp)
        apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
        apply (frule_tac p = "ptr_val (t9_C.arr_C v')" in valid_ptr_not_in_frame_same; simp?)
         apply (drule wa_abs_typing_u_elims(3); clarsimp)
        apply (frule_tac p = "t9_C.arr_C v'" and \<sigma> = \<sigma>' in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
        apply (clarsimp simp: is_valid_simp heap_simp)
        apply (frule_tac p = "Ptr(arr + (size_of_num_type num) * j)" and
      \<sigma> = \<sigma>' and 
      is_v = is_valid_w32 in all_heap_rel_ptrD; simp?)
         apply (clarsimp simp: type_rel_simp)
        apply clarsimp
        apply (intro conjI exI; simp?)
         apply (clarsimp simp: val_rel_simp ptr_add_def mult.commute)
        apply (clarsimp simp: val_rel_simp ptr_add_def mult.commute)
       apply (rule conjI)
        apply (erule u_t_funafuntE; clarsimp)
       apply (rename_tac args j \<sigma>' res)
       apply (rule_tac x = \<sigma>' in exI)
       apply (rule_tac x = res in exI)
       apply (clarsimp simp: foldmap_inv_def)
       apply (clarsimp simp: \<Xi>_wordarray_map_no_break_0 wordarray_map_no_break_0_type_def abbreviated_type_defs)
       apply (unfold foldmap_bounds_def)
       apply (erule conjE)+
       apply (rule conjI)
        apply (case_tac "t9_C.frm_C v' < e")
         apply (erule impE, assumption)
         apply (thin_tac "_ \<longrightarrow> _")
         apply clarsimp
         apply (case_tac "j < t9_C.to_C v'"; clarsimp)
         apply (subst (asm) Int_Un_distrib; clarsimp)
         apply (rule_tac ptrl = None and
      ra = r and
      wa = w and
      rb = ra and
      wb = wa and
      rc = ro in upd_wa_mapAccumnb_bod_to_geq_len; (simp add: Int_commute)?; clarsimp?)
        apply (erule impE, assumption)
        apply (thin_tac "_ \<longrightarrow> _")
        apply clarsimp
        apply (erule upd_wa_mapAccumnb_bod.elims; clarsimp)
        apply (case_tac "t9_C.frm_C v' < t9_C.to_C v'"; subst upd_wa_mapAccumnb_bod.simps; clarsimp)
       apply (clarsimp simp: val_rel_simp)
      apply wp
     apply wp
    apply (rule validNF_select_UNIV)
   apply (rule validNF_select_UNIV)
  apply (clarsimp simp: foldmap_inv_stat_def)
  apply (clarsimp simp: order.strict_implies_order)
  apply (clarsimp simp: foldmap_inv_def state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (frule_tac p = "t9_C.arr_C v'" in all_heap_rel_ptrD; simp?)
   apply (clarsimp simp: type_rel_simp wa_abs_repr_def)
  apply (clarsimp simp: is_valid_simp val_rel_WordArray_u32_C_def heap_simp)
  apply (subst upd_wa_mapAccumnb_bod.simps; clarsimp)+
  apply (clarsimp simp: val_rel_simp)
  apply (rule conjI; clarsimp)
   apply (subst min_def)
   apply (subst (asm) not_le[symmetric])+
   apply (subst if_not_P; simp?)
  apply (subst min_def)
  apply (clarsimp simp: not_le)
  done

section "Specialised Lemmas for Cogent Functions"

lemma typing_mono_app_cogent_fun:
  "\<Xi>', 0, [], {}, [option.Some a] \<turnstile> f : b \<Longrightarrow> \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (Fun f [] []) (Var 0) : b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth)
    apply (rule right; simp)
   apply (rule typing_fun[where \<delta> = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
     apply (rule weakening_comp.none)
    apply simp
   apply (rule subst_wellformed_nothing)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma typing_mono_fun_cogent_fun:
  "\<Xi>', 0, [], {}, [option.Some a] \<turnstile> f : b \<Longrightarrow> \<Xi>', 0, [], {}, [option.None] \<turnstile> Fun f [] [] : TFun a b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_fun[where \<delta>= "[]"]; 
          (simp add: Cogent.empty_def weakening_conv_all_nth )?)
    apply(rule  weakening_comp.none)
   apply simp
  apply (rule subst_wellformed_nothing)
  done

lemma typing_mono_fun_imp_appfun:
  "\<Xi>', 0, [], {}, [option.None] \<turnstile> Fun f [] []: TFun a b \<Longrightarrow> \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (Fun f [] []) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma upd_C_wordarray_fold_no_break_corres_cog:
  "\<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; 
    \<Gamma>' ! i = option.Some (prod.fst (prod.snd(prod.snd(prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))));
    proc_env_matches_ptrs \<xi>0' \<Xi>;
    \<Xi> ''wordarray_fold_no_break_0'' = (0, [],{}, \<tau>, \<tau>acc);
    \<tau> = TRecord [(''arr'', TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly None), Present),
      (''frm'', TPrim (Num U32), Present), (''to'', TPrim (Num U32), Present),
      (''f'', TFun \<tau>f  \<tau>acc, Present), (''acc'', \<tau>acc, Present), (''obsv'', \<tau>obsv, Present)] Unboxed;
    \<tau>f = TRecord [(''elem'', TPrim (Num num), Present), (''acc'', \<tau>acc, Present), 
      (''obsv'', \<tau>obsv, Present)] Unboxed;
    D \<in> k \<or> S \<in> k; 0, K', {} \<turnstile> \<tau>obsv :\<kappa> k;
    \<gamma> ! i = URecord fs None; UFunction f [] [] = prod.fst (fs ! 3);  
    \<Xi>, 0, [], {}, [option.Some \<tau>f] \<turnstile> f : \<tau>acc;
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr) 
      (App (Fun f [] []) (Var 0)) (do ret <- dispatch_t4' (t5_C.f_C v') x'; gets (\<lambda>s. ret) od) 
      \<xi>0' [x] \<Xi> [option.Some \<tau>f] \<sigma> s;
    \<xi>1' ''wordarray_fold_no_break_0'' = upd_wa_foldnb \<Xi> \<xi>0' \<tau>f\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (Generated.state_rel wa_abs_repr)
         (App (AFun ''wordarray_fold_no_break_0'' [] []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>1' \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (drule typing_mono_app_cogent_fun)
  apply (rule upd_C_wordarray_fold_no_break_corres_gen; simp?)
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: val_rel_simp)
  done

section "Specialised Lemmas for Abstract Functions"
lemma typing_mono_app_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = (0,[],{}, a, b)\<rbrakk> \<Longrightarrow> \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (AFun f [] []) (Var 0) : b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth)
    apply (rule right; simp)
   apply (rule typing_afun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
     apply (rule weakening_comp.none)
    apply simp
   apply (rule subst_wellformed_nothing)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma typing_mono_afun_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = (0, [], {}, a, b)\<rbrakk> \<Longrightarrow> \<Xi>', 0, [], {}, [option.None] \<turnstile> AFun f [] [] : TFun a b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_afun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
    apply (rule weakening_comp.none)
   apply simp
  apply (rule subst_wellformed_nothing)
  done

lemma typing_mono_afun_imp_appafun:
  "\<Xi>', 0, [], {}, [option.None] \<turnstile> AFun f [] []: TFun a b \<Longrightarrow> \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (AFun f [] []) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

end (* of context *)

end