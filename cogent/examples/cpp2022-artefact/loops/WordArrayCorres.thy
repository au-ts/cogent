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

section "wordarray_length"

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
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), TPrim (Num U32))"
  and     \<xi>name: "\<xi>' name = uwa_length"
  and     srel: "\<And>x y. (x, y) \<in> state_rel \<Longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p)"
  and     trel: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     vrel: "\<And>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv))"
  and     cfundef: "cfun = cwa_length is_v h l_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
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
  show "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
    by (simp add: \<Gamma>i)
qed

lemma cwa_length_corres_base_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val) ptr)"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), TPrim (Num U32))"
  and     \<xi>name: "\<xi>' name = uwa_length"
  and     srel: "\<forall>x y. (x, y) \<in> state_rel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p)"
  and     trel: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     vrel: "\<forall>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv))"
  and     cfundef: "cfun = cwa_length is_v h l_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  by (rule cwa_length_corres_base[OF \<gamma>len valrel _ _ _ _ trel _ cfundef]; (simp add: \<Gamma>i \<Xi>name \<xi>name srel vrel)?)

section "wordarray_get"

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
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
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
                    (\<exists>p i v. uv = URecord [p, i, v] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv) \<and> val_rel (prod.fst v) (v_c cv))"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     cfundef: "cfun = cwa_get is_v h is_vw hw p_c i_c v_c l_c vs_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
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
  show "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
    by (simp add: \<Gamma>i)
qed

lemma cwa_get_corres_base_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                    (''idx'', TPrim (Num U32), Present),
                    (''val'', t, Present)] Unboxed, t)"
  and     \<xi>name: "\<xi>' name = uwa_get"
  and     srel: "\<forall>x y. (x, y) \<in> state_rel \<longrightarrow> 
                  (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
                  (\<forall>(p :: ('c :: cogent_C_val) ptr) uv. heap_rel_meta is_vw hw x y p)"
  and     trela: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     trelc: "type_rel (type_repr t) TYPE('c)"
  and     vrela: "\<forall>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (vs_c cv))"
  and     vrelb: "\<forall>uv (cv :: 'b). 
                  val_rel uv cv = 
                    (\<exists>p i v. uv = URecord [p, i, v] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv) \<and> val_rel (prod.fst v) (v_c cv))"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     cfundef: "cfun = cwa_get is_v h is_vw hw p_c i_c v_c l_c vs_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  by (rule cwa_get_corres_base[OF \<gamma>len valrel _ _ _ _ trela trelc _ _ sizet cfundef]; (simp add: \<Gamma>i \<Xi>name \<xi>name vrela vrelb srel)?)


section "wordarray_put"

definition cwa_put
  where
"cwa_put is_v h is_vw hw_upd p_c i_c v_c l_c vs_c a =
    do _ <- guard (\<lambda>s. is_v s (p_c a));
       _ <-
       do _ <- guard (\<lambda>s. is_v s (p_c a));
          condition (\<lambda>s. i_c a < SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))))
            (do _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
                _ <- guard (\<lambda>s. is_v s (p_c a));
                _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
                modify (\<lambda>s. hw_upd (\<lambda>x. x(vs_c (h s (p_c a)) +\<^sub>p uint (i_c a) := v_c a)) s)
             od)
            (return ())
       od;
       return (p_c a)
    od"
find_theorems  heap_w32_update

lemma cwa_put_corres_base:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
                    (''idx'', TPrim (Num U32), Present),
                    (''val'', t, Present)] Unboxed,
                    TCon ''WordArray'' [t] (Boxed Writable ptrl))"
  and     \<xi>name: "\<xi>' name = uwa_put"
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
                    (\<exists>p i v. uv = URecord [p, i, v] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv) \<and> val_rel (prod.fst v) (v_c cv))"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     upd: "\<And>\<sigma> s (p :: ('c :: cogent_C_val) ptr) v (v' :: ('c :: cogent_C_val)).
                  \<lbrakk>(\<sigma>, s) \<in> state_rel;
                   \<exists>v. \<sigma> (ptr_val p) = option.Some v \<and> uval_typing \<Xi>' \<sigma> v t {} {};
                   uval_typing \<Xi>' \<sigma> v t {} {};
                   val_rel v v'\<rbrakk> \<Longrightarrow>
                   (\<sigma>(ptr_val p \<mapsto> v), hw_upd (\<lambda>x. x(p := v')) s) \<in> state_rel"
  and     cfundef: "cfun = cwa_put is_v h is_vw hw_upd p_c i_c v_c l_c vs_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
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
     apply (monad_eq simp: cwa_put_def)
     apply (frule wa_abs_typing_u_elims(5))
     apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
     apply (simp add: ptr_val_add)
     apply (drule (1) all_heap_rel_ptrD)
      apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
     apply clarsimp
    apply clarsimp
    apply (monad_eq simp: cwa_put_def)
    apply (case_tac "SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c v'))) \<le> i_c v'"; clarsimp)
    apply (rule_tac x = \<sigma> in exI)
     apply (rename_tac x rb wb rc)
     apply (rule_tac x = "UPtr (ptr_val (p_c v')) (RCon ''WordArray'' [type_repr t])" in exI)
     apply clarsimp
     apply (fastforce simp: uwa_put_def)
    apply (frule wa_abs_typing_u_elims(5))
    apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
    apply (simp add: ptr_val_add)
    apply (drule (1) all_heap_rel_ptrD)
     apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
    apply clarsimp
    apply (rename_tac x rb wb rc xa)
    apply (rule_tac x = "\<sigma>(ptr_val (vs_c (h s (p_c v')) +\<^sub>p uint (i_c v')) \<mapsto> x)" in exI)
    apply (rule_tac x = "UPtr (ptr_val (p_c v')) (RCon ''WordArray'' [type_repr t])" in exI)
    apply (clarsimp simp: uwa_put_def sizet ptr_val_add)
    apply (drule l0_imp_uval_typing)
    apply (drule wa_abs_typing_u_elims(8); clarsimp)
    apply (drule (2) no_heap_no_pointers)
    apply (rule upd; simp?)
    done
next
  show "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
    by (simp add: \<Gamma>i)
qed

lemma cwa_put_corres_base_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
                    (''idx'', TPrim (Num U32), Present),
                    (''val'', t, Present)] Unboxed,
                    TCon ''WordArray'' [t] (Boxed Writable ptrl))"
  and     \<xi>name: "\<xi>' name = uwa_put"
  and     srel: "\<forall>x y. (x, y) \<in> state_rel \<longrightarrow> 
                  (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
                  (\<forall>(p :: ('c :: cogent_C_val) ptr) uv. heap_rel_meta is_vw hw x y p)"
  and     trela: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     trelc: "type_rel (type_repr t) TYPE('c)"
  and     vrela: "\<forall>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (vs_c cv))"
  and     vrelb: "\<forall>uv (cv :: 'b). 
                  val_rel uv cv = 
                    (\<exists>p i v. uv = URecord [p, i, v] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv) \<and> val_rel (prod.fst v) (v_c cv))"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     upd: "\<forall>\<sigma> s (p :: ('c :: cogent_C_val) ptr) v (v' :: ('c :: cogent_C_val)).
                  (\<sigma>, s) \<in> state_rel \<and>
                   (\<exists>v. \<sigma> (ptr_val p) = option.Some v \<and> uval_typing \<Xi>' \<sigma> v t {} {}) \<and>
                   uval_typing \<Xi>' \<sigma> v t {} {} \<and>
                   val_rel v v' \<longrightarrow>
                   (\<sigma>(ptr_val p \<mapsto> v), hw_upd (\<lambda>x. x(p := v')) s) \<in> state_rel"
  and     cfundef: "cfun = cwa_put is_v h is_vw hw_upd p_c i_c v_c l_c vs_c"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  by (rule_tac hw = hw in cwa_put_corres_base[OF \<gamma>len valrel _ _ _ _ trela trelc _ _ sizet _ cfundef]; (simp add: \<Gamma>i \<Xi>name \<xi>name vrela vrelb srel upd)?)

section "wordarray_get_opt"

definition cwa_get_opt
  where
"cwa_get_opt is_v h is_vw hw p_c i_c l_c vs_c tag_upd tag_n tag_s s_upd a \<equiv>
    do b <- select UNIV;
       _ <- guard (\<lambda>s. is_v s (p_c a));
       _ <- guard (\<lambda>s. is_v s (p_c a));
       condition (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))) \<le> i_c a)
         (return (tag_upd (\<lambda>_. tag_n) b))
         (do _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
             _ <- guard (\<lambda>s. is_v s (p_c a));
             _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a)));
             gets (\<lambda>s. s_upd (\<lambda>r. hw s (vs_c (h s (p_c a)) +\<^sub>p uint (i_c a))) (tag_upd (\<lambda>_. tag_s) b))
          od)
    od"

lemma cwa_get_opt_corres_base:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                    (''idx'', TPrim (Num U32), Present)] Unboxed,
                    TSum [(''Nothing'', TUnit, Unchecked), (''Something'', t, Unchecked)])"
  and     \<xi>name: "\<xi>' name = uwa_get_opt"
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
                    (\<exists>p i. uv = URecord [p, i] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv))"
  and     vrelr: "\<And>uv (cv :: 'd).
                    val_rel uv cv = (\<exists>repr tag uval.
                      uv = USum tag uval repr \<and>
                      (tag = ''Nothing'' \<and> tag_c cv = tag_n \<and> val_rel uval ((n_c cv) :: unit_t_C) \<or>
                       tag = ''Something'' \<and> tag_c cv = tag_s \<and> val_rel uval (s_c cv)))"
  and     tagC_tagU: "\<And>x y. tag_c (tag_upd (\<lambda>_. y) x) = y"
  and     sC_sU: "\<And>x y. s_c (s_upd (\<lambda>_. y) x) = y"
  and     tagC_sU: "\<And>x y. tag_c (s_upd (\<lambda>_. y) x) = tag_c x"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     cfundef: "cfun = cwa_get_opt is_v h is_vw hw p_c i_c l_c vs_c tag_upd tag_n tag_s s_upd"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do (x :: ('d :: cogent_C_val)) <- cfun v'; gets (\<lambda>s. x) od)
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
     apply (monad_eq simp: cwa_get_opt_def)
     apply (frule wa_abs_typing_u_elims(5))
     apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
     apply (simp add: ptr_val_add)
     apply (drule (1) all_heap_rel_ptrD)
      apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
     apply clarsimp
    apply clarsimp
    apply (monad_eq simp: cwa_get_opt_def)
    apply (rule_tac x = \<sigma> in exI)
    apply (case_tac "SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c v'))) \<le> i_c v'"; clarsimp)
     apply (rename_tac rb a)
     apply (clarsimp simp: uwa_get_opt_def)
     apply (intro exI conjI impI; simp?)
     apply (clarsimp simp: vrelr val_rel_unit_t_C_def tagC_tagU)
    apply (frule wa_abs_typing_u_elims(5))
    apply (erule_tac x = "i_c v'" in allE; clarsimp simp: not_le sizet)
    apply (simp add: ptr_val_add)
    apply (drule (1) all_heap_rel_ptrD)
     apply (drule l0.type_repr_uval_repr; simp add: l0_eq_uval_repr trelc)
    apply clarsimp
    apply (rename_tac rb a x)
    apply (clarsimp simp: uwa_get_opt_def sizet ptr_val_add vrelr tagC_tagU sC_sU tagC_sU)
    done
next
  show "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
    by (simp add: \<Gamma>i)
qed

lemma cwa_get_opt_corres_base_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('b :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, TRecord [
                    (''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                    (''idx'', TPrim (Num U32), Present)] Unboxed,
                    TSum [(''Nothing'', TUnit, Unchecked), (''Something'', t, Unchecked)])"
  and     \<xi>name: "\<xi>' name = uwa_get_opt"
  and     srel: "\<forall>x y. (x, y) \<in> state_rel \<longrightarrow> 
                  (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
                  (\<forall>(p :: ('c :: cogent_C_val) ptr) uv. heap_rel_meta is_vw hw x y p)"
  and     trela: "type_rel (RCon ''WordArray'' [type_repr t]) TYPE('a)"
  and     trelc: "type_rel (type_repr t) TYPE('c)"
  and     vrela: "\<forall>uv (cv :: 'a). 
                  val_rel uv cv = 
                    (\<exists>len arr. uv = UAbstract (UWA t len arr) \<and>
                      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (vs_c cv))"
  and     vrelb: "\<forall>uv (cv :: 'b). 
                  val_rel uv cv = 
                    (\<exists>p i. uv = URecord [p, i] None \<and> val_rel (prod.fst p) (p_c cv) \<and>
                      val_rel (prod.fst i) (i_c cv))"
  and     vrelr: "\<forall>uv (cv :: 'd).
                    val_rel uv cv = (\<exists>repr tag uval.
                      uv = USum tag uval repr \<and>
                      (tag = ''Nothing'' \<and> tag_c cv = tag_n \<and> val_rel uval ((n_c cv) :: unit_t_C) \<or>
                       tag = ''Something'' \<and> tag_c cv = tag_s \<and> val_rel uval (s_c cv)))"
  and     tagC_tagU: "\<forall>x y. tag_c (tag_upd (\<lambda>_. y) x) = y"
  and     sC_sU: "\<forall>x y. s_c (s_upd (\<lambda>_. y) x) = y"
  and     tagC_sU: "\<forall>x y. tag_c (s_upd (\<lambda>_. y) x) = tag_c x"
  and     sizet: "size_of_type t = of_nat (size_of TYPE('c))"
  and     cfundef: "cfun = cwa_get_opt is_v h is_vw hw p_c i_c l_c vs_c tag_upd tag_n tag_s s_upd"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do (x :: ('d :: cogent_C_val)) <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule cwa_get_opt_corres_base[where tag_c = tag_c,
                                      OF \<gamma>len valrel _ _ _ _ trela trelc _ _ _ _ _ _ sizet cfundef];
         (simp add: \<Gamma>i \<Xi>name \<xi>name vrela vrelb srel vrelr tagC_tagU tagC_sU sC_sU)?)
  apply (simp add: sC_sU)
  done


end (* of context *)

end