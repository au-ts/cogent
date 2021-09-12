theory WordArrayCorres
  imports
    WordArrayUpdate
    CorresHelper
    CogentTypingHelper
    "build/Generated_CorresSetup"
begin

sublocale WordArrayUpdate \<subseteq> update_sem_init wa_abs_typing_u wa_abs_repr
  by (unfold_locales)

context WordArrayUpdate begin

definition cwa_length
  where
"cwa_length is_v h l_c a \<equiv>
    do _ <- guard (\<lambda>s. is_v s a);
       _ <- guard (\<lambda>s. is_v s a);
       gets (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s a)))
    od"

lemma cwa_length_corres_base:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val) ptr)"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (\<Xi>' name)))"
  and     \<Xi>name: "\<Xi>' name = ([], TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), TPrim (Num U32))"
  and     \<xi>name: "\<xi>' name = uwa_length"
  and     srel: "\<And>x y. (x, y) \<in> state_rel \<Longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p)"
  and     trel: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     vrel: "\<And>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv))"
  and     cfundef: "cfun = cwa_length is_v h l_c"
shows
  "corres state_rel (App (AFun name []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
proof (rule absfun_corres[OF _ \<gamma>len valrel])
  show "abs_fun_rel \<Xi>' state_rel name \<xi>' cfun \<sigma> s (\<gamma> ! i) v'"
    apply (subst abs_fun_rel_def)
    apply (clarsimp simp: cfundef \<Xi>name \<xi>name uwa_length_def)
    apply (erule u_t_tconE; clarsimp simp: val_rel_ptr_def)
    apply (frule wa_abs_typing_u_elims(1); clarsimp)
    apply (cut_tac srel; simp?)
    apply (erule_tac x = v' in allE; clarsimp simp: heap_rel_meta_def wa_abs_repr_def trel)
    apply (rule conjI; monad_eq simp: cwa_length_def)
    apply (clarsimp simp: val_rel_word_def vrel is_signed_bit0_def word_bits_size word_bits_def)
    done
next
  show "\<Gamma> ! i = Some (fst (snd (\<Xi>' name)))"
    by (simp add: \<Gamma>i)
qed

definition cwa_get
  where
"cwa_get is_v h is_vw hw p_c i_c v_c l_c vs_c a \<equiv>
    do _ <- guard (\<lambda>s. is_v s (p_c a));
       _ <- guard (\<lambda>s. is_v s (p_c a));
       condition (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))) \<le> i_c a)
         (return (v_c a))
         (do _ <-
             guard
              (\<lambda>s. is_v s (p_c a) \<and>
                   is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
             _ <- guard (\<lambda>s. is_v s (p_c a));
             _ <-
             guard
              (\<lambda>s. is_v s (p_c a) \<and>
                   is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
             gets (\<lambda>s. hw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)))
          od)
    od"

lemma ptr_val_add: 
  "ptr_val (p :: ('a :: c_type) ptr) + of_nat (size_of TYPE('a)) * x = ptr_val (p +\<^sub>p uint x)"
  apply (simp add: ptr_add_def mult.commute)
  done


lemma cwa_get_corres_base:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (\<Xi>' name)))"
  and     \<Xi>name: "\<Xi>' name = ([], TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                    (''idx'', TPrim (Num U32), Present),
                    (''val'', t, Present)] Unboxed, t)"
  and     \<xi>name: "\<xi>' name = uwa_get"
  and     srel: "\<And>x y. (x, y) \<in> state_rel \<Longrightarrow> 
                  (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
                  (\<forall>(p :: ('c :: cogent_C_val) ptr) uv. heap_rel_meta is_vw hw x y p)"
  and     trela: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     trelc: "type_rel (type_repr t) TYPE('c)"
  and     vrela: "\<And>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (vs_c cv))"
  and     vrelb: "\<And>uv (cv :: 'b). 
                  val_rel uv cv = 
                    (\<exists>p i v. uv = URecord [p, i, v] \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv) \<and> val_rel (prod.fst v) (v_c cv))"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     cfundef: "cfun = cwa_get is_v h is_vw hw p_c i_c v_c l_c vs_c"
shows
  "corres state_rel (App (AFun name []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
proof (rule absfun_corres[OF _ \<gamma>len valrel])
  show "abs_fun_rel \<Xi>' state_rel name \<xi>' cfun \<sigma> s (\<gamma> ! i) v'"
    apply (subst abs_fun_rel_def)
    apply (clarsimp simp: cfundef \<Xi>name \<xi>name vrelb val_rel_ptr_def val_rel_word_def 
                          is_signed_bit0_def word_bits_size word_bits_def ucast_id)
    apply (erule u_t_recE; clarsimp)
    apply (erule u_t_r_consE; clarsimp)+
    apply (erule u_t_r_emptyE; clarsimp)
    apply (erule u_t_tconE; clarsimp)
    apply (erule u_t_primE)
    apply (drule_tac t = "lit_type _" in sym; clarsimp)
    apply (cut_tac srel; simp?)
    apply clarsimp
    apply (frule wa_abs_typing_u_elims(1); clarsimp)
    apply (drule (1) all_heap_rel_ptrD; clarsimp simp: trela wa_abs_repr_def vrela split: atyp.splits)
    apply (rule conjI)
     apply (monad_eq simp: cwa_get_def)
     apply (frule wa_abs_typing_u_elims(5))
     apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
     apply (simp add: ptr_val_add)
     apply (drule (1) all_heap_rel_ptrD)
      apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
     apply clarsimp
    apply clarsimp
    apply (monad_eq simp: cwa_get_def)
    apply (rule_tac x = \<sigma> in exI)
    apply (case_tac "SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c v'))) \<le> i_c v'"; clarsimp)
     apply (rename_tac x rb wb rc)
     apply (rule_tac x = x in exI)
     apply clarsimp
     apply (fastforce simp: uwa_get_def)
    apply (frule wa_abs_typing_u_elims(5))
    apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
    apply (simp add: ptr_val_add)
    apply (drule (1) all_heap_rel_ptrD)
     apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
    apply clarsimp
    apply (rename_tac xa)
    apply (rule_tac x = xa in exI)
    apply (clarsimp simp: uwa_get_def sizet ptr_val_add)
    done
next
  show "\<Gamma> ! i = Some (fst (snd (\<Xi>' name)))"
    by (simp add: \<Gamma>i)
qed

end (* of context *)

sublocale WordArrayUpdate \<subseteq> Generated _ wa_abs_typing_u wa_abs_repr
  by (unfold_locales)

context WordArrayUpdate begin

lemma
  "wordarray_length_0' = cwa_length is_valid heap len_C"
  unfolding wordarray_length_0'_def cwa_length_def
  by (clarsimp simp: is_valid_simp heap_simp unknown_bind_ignore) 


lemma
  "wordarray_get_0' = cwa_get is_valid heap is_valid_w32 heap_w32 arr_C idx_C val_C len_C values_C"
  unfolding wordarray_get_0'_def cwa_get_def
  by (clarsimp simp: is_valid_simp heap_simp unknown_bind_ignore) 

end
end