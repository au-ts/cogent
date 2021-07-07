(*
  This file contains the update semantics to C correspondence lemmas for word array functions
*)
theory WordArray_UpdCCorresGen
  imports WordArray_UAbsFun
begin



context WordArray begin

section "Helper Lemmas"

lemma ptr_val_add: 
  "ptr_val (p :: ('a :: c_type) ptr) + of_nat (size_of TYPE('a)) * x = ptr_val (p +\<^sub>p uint x)"
  apply (simp add: ptr_add_def mult.commute)
  done

lemma whileLoop_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoop_inv c b init I (measure M) \<lbrace> Q \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoop c b init \<lbrace> Q \<rbrace>!"
  by (metis assms whileLoop_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done

section "Correspondence Lemmas Between Update Semantics and C"

subsection "wordarray_length"

definition wordarray_length_c
  where
  "wordarray_length_c is_v h l p \<equiv>
    do _ <- guard (\<lambda>s. is_v s p);
       ret <- do _ <- guard (\<lambda>s. is_v s p);
             gets (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l (h s p)))
              od;
       global_exn_var <- gets (\<lambda>_. Return);
       _ <- gets (\<lambda>_. ());
       gets (\<lambda>_. ret)
    od"

lemma upd_C_wordarray_length_c_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>\<Xi>' fn = ([], TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), TPrim (Num U32));
     \<xi>0' fn = upd_wa_length_0;
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p);
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn)))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr (srel) (App (AFun fn []) (Var i))
         (do x <- wordarray_length_c is_v h l_c (v' :: 'a ptr);
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: val_rel_simp)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_length_c_def)
   apply (erule_tac x = \<sigma> in allE)
   apply (erule_tac x = st in allE)
   apply clarsimp
   apply (erule_tac x = v' in allE)
   apply (clarsimp simp: heap_rel_meta_def type_rel_simp wa_abs_repr_def)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (monad_eq simp: wordarray_length_c_def)
  apply (clarsimp simp: upd_wa_length_0_def)
  apply (erule_tac x = "UAbstract (UWA (TPrim (Num num)) len arr)" in allE)
  apply (erule_tac x = "h st v'" in allE)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = st in allE)
  apply clarsimp
  apply (erule_tac x = v' in allE)
  apply (clarsimp simp: heap_rel_meta_def type_rel_simp wa_abs_repr_def)
  done

subsection "wordarray_get"

definition wordarray_get_c
  where
  "wordarray_get_c is_v h is_vw hw l_c v_c p1_c p2_c a \<equiv>
    do _ <- guard (\<lambda>s. is_v s (p1_c a));
       _ <- guard (\<lambda>s. is_v s (p1_c a));
       condition (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s (p1_c a))) \<le> p2_c a)
        (do ret <- gets (\<lambda>_. 0);
            global_exn_var <- gets (\<lambda>_. Return);
            _ <- gets (\<lambda>_. ());
            gets (\<lambda>_. ret)
         od)
        (do _ <- gets (\<lambda>_. ());
            _ <-
            guard (\<lambda>s. is_v s (p1_c a) \<and> is_vw s (v_c (h s (p1_c a)) +\<^sub>p uint (p2_c a)));
            _ <- guard (\<lambda>s. is_v s (p1_c a));
            ret <-
              do _ <- guard (\<lambda>s. is_v s (p1_c a) \<and> is_vw s (v_c (h s (p1_c a)) +\<^sub>p uint (p2_c a)));
                 gets (\<lambda>s. hw s (v_c (h s (p1_c a)) +\<^sub>p uint (p2_c a)))
              od;
            global_exn_var <- gets (\<lambda>_. Return);
            _ <- gets (\<lambda>_. ());
            gets (\<lambda>_. ret)
         od)
    od"

lemma upd_C_wordarray_get_c_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>\<Xi>' fn = ([], TRecord [
        (n0, TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), Present),
        (n1, TPrim (Num U32), Present)] Unboxed, TPrim (Num num));
     \<xi>0' fn = upd_wa_get_0;
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
        (\<forall>(p :: ('b :: {knows_sign,len8}) word ptr) uv. heap_rel_meta is_vw hw x y p);
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     type_rel (RPrim (Num num)) TYPE('b word);
     size_of_num_type num = of_nat (size_of TYPE('b word));
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     val_rel (UPrim (zero_num_lit num)) (0 :: 'b word);
     \<forall>uv (cv :: 'c :: cogent_C_val). val_rel uv cv = (\<exists>p1 p2. uv = URecord [p1, p2] \<and>
        val_rel (prod.fst p1) (p1_c cv) \<and> val_rel (prod.fst p2) (p2_c cv));
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn)))
     \<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr srel (App (AFun fn []) (Var i))
         (do x <- wordarray_get_c is_v h is_vw hw l_c v_c p1_c p2_c (v' :: 'c);
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (rotate_tac -1)
  apply (clarsimp simp: val_rel_simp)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_get_c_def)
   apply (erule_tac x = \<sigma> in allE)
   apply (erule_tac x = st in allE)
   apply clarsimp
   apply (erule_tac x = "p1_c v'" in allE)
   apply (clarsimp simp: heap_rel_meta_def wa_abs_repr_def)
   apply (drule not_le_imp_less)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "p2_c v'" in allE; clarsimp)
   apply (drule_tac p = "v_c (h st (p1_c v')) +\<^sub>p uint (p2_c v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD; simp?)
   apply (simp add: ptr_val_add)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (clarsimp simp: upd_wa_get_0_def)
  apply (monad_eq simp: wordarray_get_c_def)
  apply (erule_tac x = "UAbstract (UWA (TPrim (Num num)) len arr)" in allE)
  apply (erule_tac x = "h st (p1_c v')" in allE)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = st in allE)
  apply clarsimp
  apply (drule_tac p = "p1_c v'" and
                   uv = "UAbstract (UWA (TPrim (Num num)) len arr)" in all_heap_rel_ptrD;
                   (simp add: wa_abs_repr_def)?)
  apply clarsimp
  apply (case_tac "p2_c v' < SCAST(32 signed \<rightarrow> 32) (l_c (h st (p1_c v')))"; clarsimp)
  apply (frule wa_abs_typing_u_elims(5))
  apply (erule_tac x = " p2_c v'" in allE; clarsimp)
  apply (drule_tac p = "v_c (h st (p1_c v')) +\<^sub>p uint (p2_c v')" and
                   uv = "UPrim x" in all_heap_rel_ptrD; simp?)
   apply (simp add: ptr_val_add)
  done

subsection "wordarray_put"

definition wordarray_put_c
  where
  "wordarray_put_c is_v h is_vw hw upd_hw l_c v_c p_c i_c x_c a \<equiv>
    do _ <- guard (\<lambda>s. is_v s (p_c a));
       _ <-
        do _ <- guard (\<lambda>s. is_v s (p_c a));
          condition (\<lambda>s. i_c a < SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))))
            (do _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (v_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
                _ <- guard (\<lambda>s. is_v s (p_c a));
                _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (v_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
                modify (\<lambda>s. upd_hw (\<lambda>x. x(v_c (h s (p_c a)) +\<^sub>p uint (i_c a) := x_c a)) s)
             od)
            (gets (\<lambda>_. ()))
        od;
       ret <- gets (\<lambda>_. p_c a);
       global_exn_var <- gets (\<lambda>_. Return);
       _ <- gets (\<lambda>_. ());
       gets (\<lambda>_. ret)
    od"

lemma upd_C_wordarray_put_c_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>\<Xi>' fn = ([], TRecord [
          (n0, TCon ''WordArray'' [TPrim (Num num)] (Boxed Writable ptrl), Present),
          (n1, TPrim (Num U32), Present), (n2, TPrim (Num num), Present)] Unboxed,
        TCon ''WordArray'' [TPrim (Num num)] (Boxed Writable ptrl));
     \<xi>0' fn = upd_wa_put2_0;
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
        (\<forall>(p :: ('b :: {knows_sign,len8}) word ptr) uv. heap_rel_meta is_vw hw x y p);
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     type_rel (RPrim (Num num)) TYPE('b word);
     size_of_num_type num = of_nat (size_of TYPE('b word));
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     \<forall>uv (cv :: 'c :: cogent_C_val). val_rel uv cv = (\<exists>arr i x. uv = URecord [arr, i, x] \<and>
        val_rel (prod.fst arr) (p_c cv) \<and> val_rel (prod.fst i) (i_c cv) \<and>
        val_rel (prod.fst x) ((x_c cv) :: 'b word));
     \<forall>\<sigma> st (p :: 'b word ptr) l l' v'.
        (\<sigma>, st) \<in> srel \<and> \<sigma> (ptr_val p) = option.Some (UPrim l) \<and> lit_type l = lit_type l' \<and>
        val_rel (UPrim l') v' \<longrightarrow> (\<sigma>(ptr_val p \<mapsto> UPrim l'), upd_hw (\<lambda>x. x(p := v')) st) \<in> srel;
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn)))
     \<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr srel (App (AFun fn []) (Var i))
         (do x <- wordarray_put_c is_v h is_vw hw upd_hw l_c v_c p_c i_c x_c (v' :: 'c);
             gets (\<lambda>s. x)
          od)
         \<xi>0' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp?)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: abs_fun_rel_def; rename_tac r w)
  apply (rotate_tac -1)
  apply (clarsimp simp: val_rel_simp)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_p_absE; simp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp; rename_tac len arr)
  apply (frule upd.tprim_no_pointers)
  apply (frule upd.tprim_no_pointers(2))
  apply clarsimp
  apply (rename_tac r x w len arr)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put_c_def)
   apply (erule_tac x = \<sigma> in allE)
   apply (erule_tac x = st in allE)
   apply clarsimp
   apply (erule_tac x = "p_c v'" in allE)
   apply (clarsimp simp: heap_rel_meta_def wa_abs_repr_def)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = "i_c v'" in allE; clarsimp)
   apply (rename_tac xa)
   apply (drule_tac p = "v_c (h st (p_c v')) +\<^sub>p uint (i_c v')" and
                   uv = "UPrim xa" in all_heap_rel_ptrD; simp?)
   apply (simp add: ptr_val_add)
  apply clarsimp
  apply (erule u_t_primtE)
  apply (drule_tac t = "lit_type _" in sym)
  apply (monad_eq simp: wordarray_put_c_def upd_wa_put2_0_def)
  apply (rename_tac st' l)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = st in allE)
  apply clarsimp
  apply (erule_tac x = "p_c v'" in allE)
  apply (clarsimp simp: heap_rel_meta_def wa_abs_repr_def)
  apply (frule wa_abs_typing_u_elims(5))
  apply (case_tac "i_c v' < SCAST(32 signed \<rightarrow> 32) (l_c (h st (p_c v')))"; clarsimp)
  apply (simp add: ptr_val_add)
  apply (erule_tac x = "i_c v'" in allE; clarsimp)
  done

subsection "Helper Abbreviations"

abbreviation "mk_urecord xs \<equiv> URecord (map (\<lambda>x. (x, upd.uval_repr x)) xs)"

subsection "Loop Invariants and Bounds"

definition "foldmap_measure i end \<equiv> unat end - unat i"
definition "foldmap_bounds frm to len i e 
  \<equiv> frm \<le> i \<and> e = min to len \<and> (frm < e \<longrightarrow> i \<le> e) \<and> ((\<not>(frm < e)) \<longrightarrow> frm = i)"
definition "foldmap_inv foldmap srel \<tau>a \<tau>o \<xi>' \<sigma> p frm i f acc obsv \<sigma>' res s' res'
  \<equiv> foldmap \<xi>' \<sigma> p frm i f \<tau>a acc \<tau>o obsv (\<sigma>', res) \<and>
      val_rel res res' \<and> (\<sigma>', s') \<in> srel"
definition "foldmap_inv_stat obsv obsv' \<equiv> val_rel obsv obsv'"

subsection "wordarray_fold_no_break"

subsection "wordarray_map_no_break"

section "Specialised Correspondence Theorems"

subsection "Helper Lemmas"

\<comment>\<open>AUTOMATE THIS\<close>
lemma upd_uprim_w32:
  "\<forall>\<sigma> st p l l' v'. (\<sigma>, st) \<in> state_rel \<and> \<sigma> (ptr_val p) = option.Some (UPrim l) \<and>
        lit_type l = lit_type l' \<and> val_rel (UPrim l') v'
        \<longrightarrow> (\<sigma>(ptr_val p \<mapsto> UPrim l'), heap_w32_update (\<lambda>x. x(p := v')) st) \<in> state_rel"
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_w32_meta heap_rel_ptr_meta)
  apply (rule conjI)
   apply (rule all_heap_rel_updE; simp?; (clarsimp simp: heap_simp is_valid_simp type_rel_simp)?)
  apply (rule all_heap_rel_updE; simp?; (clarsimp simp: heap_simp is_valid_simp type_rel_simp val_rel_simp)?)
  done

subsection "wordarray_length for 32-bit word arrays"

lemma wordarray_length_wordarray_length_0':
  "wordarray_length_c is_valid_WordArray_u32_C heap_WordArray_u32_C len_C = main_pp_inferred.wordarray_length_0'"
  apply (unfold wordarray_length_c_def main_pp_inferred.wordarray_length_0'_def)
  apply (subst unknown_bind_ignore)
  apply simp
  done

lemma upd_C_wordarray_length_u32_corres:
  " \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_length_0'' []) (Var i)) (wordarray_length_0' v') \<xi>1 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (cut_tac upd_C_wordarray_length_c_corres_gen[where h = heap_WordArray_u32_C and
      is_v = is_valid_WordArray_u32_C and l_c = len_C and v_c = values_C and \<Xi>' = \<Xi> and
      fn = "''wordarray_length_0''" and srel = state_rel and \<xi>0' = \<xi>1 and num = U32 and i = i and
      \<gamma> = \<gamma> and v' = v' and \<Gamma>' = \<Gamma>' and \<sigma> = \<sigma> and st = st and ptrl = undefined,
      simplified wordarray_length_wordarray_length_0']; simp?)
       apply (clarsimp simp: \<Xi>_def wordarray_length_0_type_def)
      apply (clarsimp simp: fun_eq_iff)
     apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta is_valid_simp heap_simp)
    apply (clarsimp simp: type_rel_simp)
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: \<Xi>_def wordarray_length_0_type_def)
  done

subsection "wordarray_get for 32-bit word arrays"

lemma wordarray_get_wordarray_get_0':
  "wordarray_get_c is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32 len_C values_C t1_C.p1_C t1_C.p2_C = main_pp_inferred.wordarray_get_0'"
  apply (unfold wordarray_get_c_def main_pp_inferred.wordarray_get_0'_def)
  apply (subst unknown_bind_ignore)
  apply simp
  done

lemma upd_C_wordarray_get_u32_corres:
  " \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_get_0'' []) (Var i)) (wordarray_get_0' v') \<xi>1 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (cut_tac upd_C_wordarray_get_c_corres_gen[where h = heap_WordArray_u32_C and
      is_v = is_valid_WordArray_u32_C and l_c = len_C and v_c = values_C and \<Xi>' = \<Xi> and
      fn = "''wordarray_get_0''" and srel = state_rel and \<xi>0' = \<xi>1 and num = U32 and i = i and
      \<gamma> = \<gamma> and v' = v' and \<Gamma>' = \<Gamma>' and \<sigma> = \<sigma> and st = st and ptrl = undefined and
      is_vw = is_valid_w32 and hw = heap_w32 and p1_c = t1_C.p1_C and p2_c = t1_C.p2_C and
      ?n0.0 = "''p1''" and ?n1.0 = "''p2''",
      simplified wordarray_get_wordarray_get_0']; simp?)
           apply (clarsimp simp: \<Xi>_def wordarray_get_0_type_def abbreviated_type_defs)
          apply (clarsimp simp: fun_eq_iff)
         apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta is_valid_simp heap_simp
                               heap_rel_ptr_w32_meta)
        apply (clarsimp simp: type_rel_simp)
       apply (clarsimp simp: type_rel_simp)
      apply (clarsimp simp: val_rel_simp)
     apply (clarsimp simp: val_rel_simp)
    apply (clarsimp simp: val_rel_simp)
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: \<Xi>_def wordarray_get_0_type_def abbreviated_type_defs)
  done

subsection "wordarray_put2 for 32-bit word arrays"

lemma wordarray_put_wordarray_put2_0':
  "wordarray_put_c is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32 heap_w32_update len_C values_C t2_C.arr_C t2_C.idx_C t2_C.val_C  = main_pp_inferred.wordarray_put2_0'"
  apply (unfold wordarray_put_c_def main_pp_inferred.wordarray_put2_0'_def)
  apply (subst unknown_bind_ignore)
  apply simp
  done 

lemma upd_C_wordarray_put2_u32_corres:
  " \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_put2_0'' []) (Var i)) (wordarray_put2_0' v') \<xi>1 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (cut_tac upd_C_wordarray_put_c_corres_gen[where h = heap_WordArray_u32_C and
      is_v = is_valid_WordArray_u32_C and l_c = len_C and v_c = values_C and \<Xi>' = \<Xi> and
      fn = "''wordarray_put2_0''" and srel = state_rel and \<xi>0' = \<xi>1 and num = U32 and i = i and
      \<gamma> = \<gamma> and v' = v' and \<Gamma>' = \<Gamma>' and \<sigma> = \<sigma> and st = st and ptrl = undefined and
      is_vw = is_valid_w32 and hw = heap_w32 and p_c = t2_C.arr_C and i_c = t2_C.idx_C and
      x_c = t2_C.val_C and upd_hw = heap_w32_update and
      ?n0.0 = "''arr''" and ?n1.0 = "''idx''" and ?n2.0 = "''val''",
      simplified wordarray_put_wordarray_put2_0']; simp?)
           apply (clarsimp simp: \<Xi>_def wordarray_put2_0_type_def abbreviated_type_defs)
          apply (clarsimp simp: fun_eq_iff)
         apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta is_valid_simp heap_simp
                               heap_rel_ptr_w32_meta)
        apply (clarsimp simp: type_rel_simp)
       apply (clarsimp simp: type_rel_simp)
      apply (clarsimp simp: val_rel_simp)
     apply (clarsimp simp: val_rel_simp)
    apply (rule upd_uprim_w32)
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: \<Xi>_def wordarray_put2_0_type_def abbreviated_type_defs)
  done

subsection "wordarray_fold_no_break for 32-bit word arrays"
end (* of context *)

end