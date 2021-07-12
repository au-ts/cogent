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
        ret <- do _ <- guard (\<lambda>s. is_v s p); gets (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l (h s p))) od;
        global_exn_var <- gets (\<lambda>_. Return);
        _ <- gets (\<lambda>_. ());
        gets (\<lambda>_. ret)
     od"

lemma upd_C_wordarray_length_c_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>\<comment>\<open>The type of wordarray_length, where @{term fn} is name of the wordarray_length function in C,
        @{term num} is the numeric type of the word array and @{term ptrl} is the pointer layout\<close>
     \<Xi>' fn = ([], TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), TPrim (Num U32));
     \<comment>\<open>The embedding of wordarray_length in the update semantics\<close>
     \<xi>0' fn = upd_wa_length_0;
     \<comment>\<open>For all related Cogent and C states, the Cogent and C heaps for word arrays are related\<close>
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p);
     \<comment>\<open>The type relation for word arrays\<close>
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     \<comment>\<open>The value relation for word arrays, where @{term l_c} extracts the length value and
        @{term v_c} extracts the pointer to the array of words\<close>
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     \<comment>\<open>The rest of the assumptions are the standard value relation of arguments and what their
        types are\<close>
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
(*
lemma upd_C_wordarray_length_c_corres_gen':
  assumes
    \<comment>\<open>The type of wordarray_length, where @{term fn} is name of the wordarray_length function in C,
        @{term num} is the numeric type of the word array and @{term ptrl} is the pointer layout\<close>
    fntyp: "\<Xi>' fn = ([], TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), TPrim (Num U32))"
  and
    \<comment>\<open>The embedding of wordarray_length in the update semantics\<close>
    embed: "\<xi>0' fn = upd_wa_length_0"
  and
    \<comment>\<open>For all related Cogent and C states, the Cogent and C heaps for word arrays are related\<close>
     srel: "\<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p)"
  and
    \<comment>\<open>The type relation for word arrays\<close>
    typrel: "type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a)"
  and
    \<comment>\<open>The value relation for word arrays, where @{term l_c} extracts the length value and
       @{term v_c} extracts the pointer to the array of words\<close>
    valrelwa: "\<forall>uv (cv :: 'a). val_rel uv cv =
      (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
      len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv))"
  and
    argn: "i < length \<gamma>"
  and
    valrelarg: "val_rel (\<gamma> ! i) v'"
  and
    argtyp: "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn)))"
shows
  "update_sem_init.corres wa_abs_typing_u wa_abs_repr (srel) (App (AFun fn []) (Var i))
        (do x <- wordarray_length_c is_v h l_c (v' :: 'a ptr); gets (\<lambda>s. x) od) \<xi>0' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
proof (rule absfun_corres[OF _ argn valrelarg])
next 
  show "abs_fun_rel \<Xi>' srel fn \<xi>0' (wordarray_length_c is_v h l_c) \<sigma> st (\<gamma> ! i) v'"
    apply -
    apply (monad_eq simp: abs_fun_rel_def wordarray_length_c_def)
    thm imp_conjL
    sorry    
next
  show "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn)))" using argtyp by assumption
qed
*)

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
              _ <- guard (\<lambda>s. is_v s (p1_c a) \<and> is_vw s (v_c (h s (p1_c a)) +\<^sub>p uint (p2_c a)));
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
    \<lbrakk>\<comment>\<open>The type of wordarray_get, where @{term fn} is name of the wordarray_get function in C,
        @{term num} is the numeric type of the word array, @{term ptrl} is the pointer layout,
        @{term n0}, @{term n1} are field names and these should be distinct}\<close>
     \<Xi>' fn = ([], TRecord [
        (n0, TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), Present),
        (n1, TPrim (Num U32), Present)] Unboxed, TPrim (Num num));
     \<comment>\<open>The embedding of wordarray_get in the update semantics\<close>
     \<xi>0' fn = upd_wa_get_0;
     \<comment>\<open>For all related Cogent and C states, the Cogent and C heaps for word arrays are related
        and the Cogent and C heaps for the word type of the word array are related\<close>
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
        (\<forall>(p :: ('b :: {knows_sign,len8}) word ptr) uv. heap_rel_meta is_vw hw x y p);
     \<comment>\<open>The type relation for word arrays\<close>
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     \<comment>\<open>The type relation for the word type of the word arrays\<close>
     type_rel (RPrim (Num num)) TYPE('b word);
     \<comment>\<open>The size (in bytes) of the word type of the word arrays\<close>
     size_of_num_type num = of_nat (size_of TYPE('b word));
     \<comment>\<open>The value relation for word arrays, where @{term l_c} extracts the length value and
        @{term v_c} extracts the pointer to the array of words\<close>
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     \<comment>\<open>The 0 values are related\<close>
     val_rel (UPrim (zero_num_lit num)) (0 :: 'b word);
     \<comment>\<open>The value relation for the argument of wordarray_get, where @{term p1_c} extracts the first
        field, which is a pointer to a word array, and the @{term p2_c} extracts the second field,
        which is a 32-bit word\<close>
     \<forall>uv (cv :: 'c :: cogent_C_val). val_rel uv cv = (\<exists>p1 p2. uv = URecord [p1, p2] \<and>
        val_rel (prod.fst p1) (p1_c cv) \<and> val_rel (prod.fst p2) (p2_c cv));
     \<comment>\<open>The rest of the assumptions are the standard value relation of arguments and what their
        types are\<close>
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn))) \<rbrakk>
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
    \<lbrakk>\<comment>\<open>The type of wordarray_put, where @{term fn} is name of the wordarray_put function in C,
        @{term num} is the numeric type of the word array, @{term ptrl} is the pointer layout,
        @{term n0}, @{term n1} and @{term n2} are field names and these should be distinct}\<close>
     \<Xi>' fn = ([], TRecord [
          (n0, TCon ''WordArray'' [TPrim (Num num)] (Boxed Writable ptrl), Present),
          (n1, TPrim (Num U32), Present), (n2, TPrim (Num num), Present)] Unboxed,
        TCon ''WordArray'' [TPrim (Num num)] (Boxed Writable ptrl));
     \<comment>\<open>The embedding of wordarray_put in the update semantics\<close>
     \<xi>0' fn = upd_wa_put2_0;
     \<comment>\<open>For all related Cogent and C states, the Cogent and C heaps for word arrays are related
        and the Cogent and C heaps for the word type of the word array are related\<close>
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
        (\<forall>(p :: ('b :: {knows_sign,len8}) word ptr) uv. heap_rel_meta is_vw hw x y p);
     \<comment>\<open>The type relation for word arrays\<close>
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     \<comment>\<open>The type relation for the word type of the word arrays\<close>
     type_rel (RPrim (Num num)) TYPE('b word);
     \<comment>\<open>The size (in bytes) of the word type of the word arrays\<close>
     size_of_num_type num = of_nat (size_of TYPE('b word));
     \<comment>\<open>The value relation for word arrays, where @{term l_c} extracts the length value and
        @{term v_c} extracts the pointer to the array of words\<close>
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     \<comment>\<open>The value relation for the argument of wordarray_put, where @{term p_c} extracts the first
        field, which is the pointer to a word array, @{term i_c} extracts the second field, which
        is a 32-bit word index, and @{term x_c} extracts the third field, which is a numeric value
        of the same type as the word array elements\<close> 
     \<forall>uv (cv :: 'c :: cogent_C_val). val_rel uv cv = (\<exists>arr i x. uv = URecord [arr, i, x] \<and>
        val_rel (prod.fst arr) (p_c cv) \<and> val_rel (prod.fst i) (i_c cv) \<and>
        val_rel (prod.fst x) ((x_c cv) :: 'b word));
     \<comment>\<open>Assumes that updating a primitive value in the Cogent heap and the C heap should maintain
        the state relation, where @{term upd_hw} updates the C heap mapping given a new mapping and
        the C state. A theorem/lemma should be automatically generated to prove this assumption\<close>
     \<forall>\<sigma> st (p :: 'b word ptr) l l' v'.
        (\<sigma>, st) \<in> srel \<and> \<sigma> (ptr_val p) = option.Some (UPrim l) \<and> lit_type l = lit_type l' \<and>
        val_rel (UPrim l') v' \<longrightarrow> (\<sigma>(ptr_val p \<mapsto> UPrim l'), upd_hw (\<lambda>x. x(p := v')) st) \<in> srel;
     \<comment>\<open>The rest of the assumptions are the standard value relation of arguments and what their
        types are\<close>
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn))) \<rbrakk>
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

definition wordarray_fold_c
  where
  "wordarray_fold_c is_v h is_vw hw l_c v_c p_c s_c e_c f_c a_c o_c a_f e_upd a_upd o_upd disp a \<equiv>
     do arg <- select UNIV;
        _ <- guard (\<lambda>s. is_v s (p_c a));
        ret <-
          do _ <- guard (\<lambda>s. is_v s (p_c a));
             condition (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))) < e_c a)
               (do _ <- guard (\<lambda>s. is_v s (p_c a));
                   _ <- guard (\<lambda>s. is_v s (p_c a));
                   gets (\<lambda>s. SCAST(32 signed \<rightarrow> 32) (l_c (h s (p_c a))))
                od)
               (gets (\<lambda>_. e_c a))
          od;
        e <- gets (\<lambda>_. ret);
        arg <- gets (\<lambda>_. o_upd (\<lambda>_. o_c a) arg);
        arg <- gets (\<lambda>_. a_upd (\<lambda>_. a_c a) arg);
        i <- gets (\<lambda>_. s_c a);
        (arg, i) <-
          do _ <- guard (\<lambda>s. True);
             whileLoop (\<lambda>(arg, i) s. i < e)
               (\<lambda>(arg, i).
                 do (arg, i) <-
                    do _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (v_c (h s (p_c a)) +\<^sub>p uint i));
                       _ <- guard (\<lambda>s. is_v s (p_c a));
                       arg <-
                         do _ <- guard (\<lambda>s. is_v s (p_c a) \<and> is_vw s (v_c (h s (p_c a)) +\<^sub>p uint i));
                            gets (\<lambda>s. e_upd (\<lambda>r. hw s (v_c (h s (p_c a)) +\<^sub>p uint i)) arg)
                         od;
                       retval <- do ret' <- disp (f_c a) arg; gets (\<lambda>_. ret') od;
                       arg <- gets (\<lambda>_. a_upd (\<lambda>_. retval) arg);
                       i <- gets (\<lambda>_. i + 1);
                       gets (\<lambda>_. (arg, i))
                    od;
                    _ <- guard (\<lambda>_. True);
                    gets (\<lambda>_. (arg, i))
                 od)
               (arg, i)
          od;
        ret <- gets (\<lambda>_. a_f arg);
        global_exn_var <- gets (\<lambda>_. Return);
        _ <- gets (\<lambda>_. ());
       gets (\<lambda>_. ret)
     od"


lemma fold_inv_step_wp:
  "\<lbrakk>\<comment>\<open>The types of all abstract functions are well-formed\<close>
    proc_ctx_wellformed \<Xi>';
    \<comment>\<open>All abstract functions defined in @{term \<xi>0'} preserve typing and satisfy the frame constraints\<close>
    upd.proc_env_matches_ptrs \<xi>0' \<Xi>';
    \<comment>\<open>The word array value is type correct\<close>
    wa_abs_typing_u (UWA (TPrim (Num num)) len arr) ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl) r w \<sigma>;
    \<comment>\<open>The pointer @{term p} points to the word array\<close>
    \<sigma> p = option.Some (UAbstract (UWA (TPrim (Num num)) len arr));
    \<comment>\<open>The accumulator value is type correct\<close>
    upd.uval_typing \<Xi>' \<sigma> acc \<tau>a ra wa;
    \<comment>\<open>The observer value is types correct\<close>
    upd.uval_typing \<Xi>' \<sigma> obsv \<tau>o ro {};
    \<comment>\<open>The accumulator writable heap footprint does not overlap with the read-only word array
       heap footprint nor with the read-only heap footprint of the observer\<close>
    wa \<inter> r = {}; wa \<inter> ro = {};
    \<comment>\<open>The pointer to the word array is not in the writable heap footprint of the accumulator\<close>
    p \<notin> wa;
    \<comment>\<open>The type of the argument of the function , which wordarray_fold takes\<close>
    \<tau>f = TRecord [(n0, TPrim (Num num), Present), (n1, \<tau>a, Present), (n2, \<tau>o, Present)] Unboxed;
    \<comment>\<open>The field names are distinct\<close>
    n0 \<noteq> n1; n0 \<noteq> n2; n1 \<noteq> n2;
    \<comment>\<open>The function is type correct\<close>
    (\<Xi>', [], [option.Some \<tau>f] \<turnstile> (App f (Var 0)) : \<tau>a);
    \<comment>\<open>The function's embedding in the update semantics corresponds to its C implementation\<close>
    \<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr srel
        (App f (Var 0)) (do ret <- dispatch f_num x'; gets (\<lambda>s. ret) od)
        \<xi>0' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s;
    \<comment>\<open>The value relation for argument to the function, where @{term elem_f} extracts the first
       field, which contains an element from the word array, @{term acc_f} extracts the second
       field, which is the accumulator, and @{term obsv_f} extracts the third field, which is the
       observer\<close>
    \<forall>uv cv. val_rel uv (cv :: 'a :: cogent_C_val) = (\<exists>elem acc obsv. uv = URecord [elem, acc, obsv] \<and>
      val_rel (prod.fst elem) (elem_f cv) \<and> val_rel (prod.fst acc) (acc_f cv) \<and>
      val_rel (prod.fst obsv) (obsv_f cv));
    \<comment>\<open>Extracting the updated field returns the updated value\<close>
    \<forall>v cv. elem_f (elem_f_upd (\<lambda>_. v) cv) = v\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (a', n') = (a, n) \<and> n < e \<and>
      (\<exists>\<sigma>' res x v. args = elem_f_upd (\<lambda>_. v) a \<and>
        \<sigma>' (arr + size_of_num_type num * n) = option.Some x \<and> val_rel x v \<and>
      foldmap_inv upd_wa_foldnb_bod srel \<tau>a \<tau>o \<xi>0' \<sigma> p frm n f acc obsv \<sigma>' res sa (acc_f args)) \<and>
      foldmap_bounds frm to len n e \<and> foldmap_inv_stat obsv (obsv_f args)\<rbrace>
      dispatch f_num args 
    \<lbrace>\<lambda>ret sb. (\<exists>\<sigma>' res.
        foldmap_inv upd_wa_foldnb_bod srel \<tau>a \<tau>o \<xi>0' \<sigma> p frm (n + 1) f acc obsv \<sigma>' res sb ret) \<and>
      foldmap_inv_stat obsv (obsv_f args) \<and> foldmap_bounds frm to len (n + 1) e \<and> 
      foldmap_measure (n + 1) to < foldmap_measure n' to\<rbrace>!"
  apply (subst validNF_def)
  apply clarsimp
  apply (subst valid_def)
  apply (subst no_fail_def)
  apply clarsimp
  apply (subst all_imp_conj_distrib[symmetric])
  apply (clarsimp simp: foldmap_inv_def)
  apply (rename_tac sa \<sigma>' res x v)
  apply (erule_tac x = "mk_urecord [x, res, obsv]" in allE)
  apply (erule_tac x = args in allE)
  apply (erule impE)
   apply (clarsimp simp: foldmap_inv_stat_def)
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
      simp?;
      (clarsimp simp: Int_commute)?)
      apply (frule wa_abs_typing_u_elims(2); clarsimp)
     apply (frule wa_abs_typing_u_elims(2); clarsimp)
    apply (frule wa_abs_typing_u_elims(2); clarsimp)
   apply (frule wa_abs_typing_u_elims(2); clarsimp)
  apply (rename_tac r' w')
  apply (subgoal_tac "upd.matches_ptrs \<Xi>' \<sigma>' [(mk_urecord [x, res, obsv])]
    [option.Some \<tau>f] (r' \<union> ro) w'")
   apply clarsimp
   apply (erule impE, blast)
   apply clarsimp
   apply (rename_tac ret sb)
   apply (rotate_tac -1)
   apply (erule_tac x = ret in allE)
   apply (erule_tac x = sb in allE)
   apply clarsimp
   apply (frule upd.preservation[where \<tau>s = "[]" and K = "[]", simplified]; simp?)
   apply clarsimp
   apply (rename_tac \<sigma>'' res' rb wb)
   apply (clarsimp simp: foldmap_bounds_def)
   apply (case_tac "frm < to \<and> frm < len"; clarsimp)
   apply (frule wa_abs_typing_u_elims(5))
   apply (erule_tac x = n in allE; clarsimp)
   apply (frule_tac p = "arr + (size_of_num_type num) * n" in valid_ptr_not_in_frame_same; simp?)
    apply (drule_tac x = "arr + (size_of_num_type num) * n" and S = r in orthD1; simp?)
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
        apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
        apply (drule_tac v = res in upd.type_repr_uval_repr(1); simp)
       apply (drule wa_abs_typing_u_elims(2); clarsimp)
      apply (drule wa_abs_typing_u_elims(2); clarsimp)
     apply (drule wa_abs_typing_u_elims(2); clarsimp)
    apply (drule wa_abs_typing_u_elims(2); clarsimp)
   apply (rule conjI)
    apply (intro exI conjI; simp)
   apply (frule_tac a = n and k = to in less_is_non_zero_p1)
   apply (drule unatSuc2; clarsimp simp: word_less_nat_alt word_le_nat_alt foldmap_measure_def)
   apply linarith
  apply clarsimp
  apply (rule upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified])
   apply (rule upd.u_t_struct; simp?)
   apply (rule upd.u_t_r_cons1[where r = "{}" and w = "{}", simplified]; simp?)
     apply (frule_tac wa_abs_typing_u_elims(2))
     apply (drule_tac ?w1.0 = wa and \<sigma>' = \<sigma>' and  ?w2.0 = w' in upd.abs_typing_frame; simp?)
     apply (drule wa_abs_typing_u_elims(5))
     apply (erule_tac x = n in allE; clarsimp simp: foldmap_bounds_def)
     apply (rule upd.u_t_prim'; clarsimp)
    apply (rule upd.u_t_r_cons1[where r' = ro and w' = "{}", simplified]; simp?)
      apply (rule upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]; simp?)
        apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
       apply (rule upd.u_t_r_empty)
      apply (drule_tac v = obsv in upd.type_repr_uval_repr(1); simp)
     apply (rule disjointI)
     apply (rename_tac y)
     apply (frule_tac p = y and r = ro in upd.uval_typing_valid(1)[where w = "{}", simplified]; simp?)
     apply clarsimp
     apply (drule_tac p = y in readonly_not_in_frame; simp?)
     apply (drule_tac x = y and S = ro in orthD1; simp?)
    apply (drule_tac v = res in upd.type_repr_uval_repr(1); simp)
   apply (frule_tac wa_abs_typing_u_elims(2))
   apply (drule_tac ?w1.0 = wa and \<sigma>' = \<sigma>' and  ?w2.0 = w' in upd.abs_typing_frame; simp?)
   apply (drule wa_abs_typing_u_elims(5))
   apply (erule_tac x = n in allE; clarsimp simp: foldmap_bounds_def)
  apply (rule upd.matches_ptrs_empty[where \<tau>s = "[]", simplified])
  done

fun urecord_nth
  where
"urecord_nth (URecord fs) n = prod.fst (fs ! n)" |
"urecord_nth _ _ = undefined"

lemma upd_C_wordarray_fold_c_corres_gen:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>\<comment>\<open>The type of wordarray_fold, where @{term fn} is name of the wordarray_fold
       function in C, @{term num} is the numeric type of the word array, @{term ptrl} is the pointer
       layout, @{term n0}, @{term n1}, @{term n2}, @{term n3}, @{term n4} and @{term n5} are field
       names and these should be distinct, @{term \<tau>a} is the type of the accumulator, @{term \<tau>o} is
       the type of the observer and @{term \<tau>f} is the type of the argument to the function that
       word_array_fold applies and the field names @{term m0}, @{term m1} and @{term m2} are distinct\<close>
     \<Xi>' fn = ([], TRecord [
        (n0, TCon ''WordArray'' [TPrim (Num num)] (Boxed ReadOnly ptrl), Present),
        (n1, TPrim (Num U32), Present), (n2, TPrim (Num U32), Present), (n3, TFun \<tau>f \<tau>a, Present),
        (n4, \<tau>a, Present), (n5, \<tau>o, Present)] Unboxed, \<tau>a);
     \<tau>f = TRecord [(m0, TPrim (Num num), Present), (m1, \<tau>a, Present), (m2, \<tau>o, Present)] Unboxed;
     m0 \<noteq> m1; m0 \<noteq> m2; m1 \<noteq> m2;
     \<comment>\<open>@{term \<tau>o} is read-only i.e. has kind D or S\<close>
     D \<in> k \<or> S \<in> k; K' \<turnstile> \<tau>o :\<kappa> k;
     \<comment>\<open>All abstract functions defined @{term \<xi>0'} preserve typing and satisfy the frame constraints\<close>
     upd.proc_env_matches_ptrs \<xi>0' \<Xi>';
     \<comment>\<open>The embedding of wordarray_fold in the update semantics\<close>
     \<xi>1' fn = upd_wa_foldnb \<Xi>' \<xi>0' \<tau>f;
     \<comment>\<open>For all related Cogent and C states, the Cogent and C heaps for word arrays are related
        and the Cogent and C heaps for the word type of the word array are related\<close>
     \<forall>x y. (x, y) \<in> srel \<longrightarrow> (\<forall>(p :: ('a :: cogent_C_val) ptr) uv. heap_rel_meta is_v h x y p) \<and>
        (\<forall>(p :: ('b :: {knows_sign,len8}) word ptr) uv. heap_rel_meta is_vw hw x y p);
     \<comment>\<open>The type relation for word arrays\<close>
     type_rel (RCon ''WordArray'' [RPrim (Num num)]) TYPE('a);
     \<comment>\<open>The type relation for the word type of the word arrays\<close>
     type_rel (RPrim (Num num)) TYPE('b word);
     \<comment>\<open>The size (in bytes) of the word type of the word arrays\<close>
     size_of_num_type num = of_nat (size_of TYPE('b word));
     \<comment>\<open>The function's embedding in the update semantics corresponds to its C implementation\<close>
     \<forall>x x' \<sigma> s. val_rel x (x' :: 'd) \<longrightarrow>
      update_sem_init.corres wa_abs_typing_u wa_abs_repr srel
        (App (uvalfun_to_exprfun (urecord_nth (\<gamma> ! i) 3)) (Var 0))
        (do ret <- disp (f_c v') x'; gets (\<lambda>s. ret) od) \<xi>0' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s;
     \<comment>\<open>The function is type correct\<close>
     \<Xi>', [], [option.Some \<tau>f] \<turnstile> App (uvalfun_to_exprfun (urecord_nth (\<gamma> ! i) 3)) (Var 0) : \<tau>a;
     \<comment>\<open>The value relation for word arrays, where @{term l_c} extracts the length value and
        @{term v_c} extracts the pointer to the array of words\<close>
     \<forall>uv (cv :: 'a). val_rel uv cv = (\<exists>len arr. uv = UAbstract (UWA (TPrim (Num num)) len arr) \<and>
        len = (SCAST(32 signed \<rightarrow> 32)(l_c cv)) \<and> arr = ptr_val (v_c cv));
     \<comment>\<open>The value relation for the argument of wordarray_fold, where @{term p_c} extracts the pointer
        to the word array, @{term s_c} the start index, @{term e_c} the ending index, @{term f_c}
        the function argument, @{term a_c} the accumulator, and @{term o_c} observer\<close>
     \<forall>uv (cv :: 'c :: cogent_C_val). val_rel uv cv = (\<exists>p s e f acc obsv.
        uv = URecord [p, s, e, f, acc, obsv] \<and> val_rel (prod.fst p) (p_c cv) \<and>
        val_rel (prod.fst s) (s_c cv) \<and> val_rel (prod.fst e) (e_c cv) \<and>
        val_rel (prod.fst f) (f_c cv) \<and> val_rel (prod.fst acc) (a_c cv) \<and>
        val_rel (prod.fst obsv) (o_c cv));
     \<comment>\<open>The value relation for argument to the function, where @{term e_f} extracts the first
        field, which contains an element from the word array, @{term a_f} extracts the second
        field, which is the accumulator, and @{term o_f} extracts the third field, which is the
        observer\<close>
     \<forall>uv cv. val_rel uv (cv :: 'd :: cogent_C_val) = (\<exists>elem acc obsv. uv = URecord [elem, acc, obsv] \<and>
       val_rel (prod.fst elem) (e_f cv) \<and> val_rel (prod.fst acc) (a_f cv) \<and>
       val_rel (prod.fst obsv) (o_f cv));
     \<comment>\<open>Extracting the updated field returns the updated value\<close>
     \<forall>v cv. e_f (e_upd (\<lambda>_. v) cv) = v;
     \<forall>v cv. a_f (a_upd (\<lambda>_. v) cv) = v;
     \<forall>v cv. o_f (o_upd (\<lambda>_. v) cv) = v;
     \<comment>\<open>Extracting field is not affected by updates to other fields\<close>
     \<forall>v cv. e_f (a_upd (\<lambda>_. v) cv) = e_f cv;
     \<forall>v cv. e_f (o_upd (\<lambda>_. v) cv) = e_f cv;
     \<forall>v cv. a_f (e_upd (\<lambda>_. v) cv) = a_f cv;
     \<forall>v cv. a_f (o_upd (\<lambda>_. v) cv) = a_f cv;
     \<forall>v cv. o_f (e_upd (\<lambda>_. v) cv) = o_f cv;
     \<forall>v cv. o_f (a_upd (\<lambda>_. v) cv) = o_f cv;
     \<comment>\<open>The rest of the assumptions are the standard value relation of arguments and what their 
        types are\<close>
     i < length \<gamma>;
     val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi>' fn))) \<rbrakk>
    \<Longrightarrow> update_sem_init.corres wa_abs_typing_u wa_abs_repr srel (App (AFun fn []) (Var i))
         (do x <- wordarray_fold_c is_v h is_vw hw l_c v_c p_c s_c e_c f_c a_c o_c a_f e_upd a_upd o_upd disp (v' :: 'c);
             gets (\<lambda>s. x)
          od)
         \<xi>1' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (rule absfun_corres; simp)
  apply (clarsimp simp: abs_fun_rel_def'; rename_tac r w)
  apply (thin_tac "\<Gamma>' ! i = _")
  apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: upd_wa_foldnb_def wordarray_fold_c_def)
  apply (rename_tac prep frmrep torep f frep acc arep obsv orep r w warep)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1); clarsimp)
  apply (rename_tac r len arr)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_primE)+
  apply (drule_tac t = "lit_type _" in sym)+
  apply clarsimp
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (frule upd.tfun_no_pointers(1))
  apply (frule upd.tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac f acc ra wa obsv ro wo)
  apply (drule upd.discardable_or_shareable_not_writeable; simp?)
  apply clarsimp
  apply (clarsimp simp: join_guards)
  apply wp
      apply (rename_tac var uu e)
      apply (rule_tac M = "\<lambda>((_, i), _). foldmap_measure i (e_c v')" and 
      I = "\<lambda>(a, b) s. (\<exists>\<sigma>' res.
          foldmap_inv upd_wa_foldnb_bod srel \<tau>a \<tau>o \<xi>0' \<sigma> (ptr_val (p_c v'))
          (s_c v') b (uvalfun_to_exprfun f) acc obsv \<sigma>' res s (a_f a)) \<and>
          foldmap_inv_stat obsv (o_f a) \<and>
          foldmap_bounds (s_c v') (e_c v') len b e" in whileLoop_add_invI; simp?)
      apply (wp; clarsimp simp: unknown_bind_ignore split: prod.splits)
          apply (rename_tac sa a n args a' n')
          apply (rule_tac a = a and wa = wa and ra = ra and ro = ro and w = "{}" and r = r and
            ptrl = ptrl and \<Xi>' = \<Xi>' and num = num  and len = len and arr = arr and ?n0.0 = m0 and
            ?n1.0 = m1 and ?n2.0 = m2 and elem_f = e_f and acc_f = a_f and obsv_f = o_f
            in fold_inv_step_wp; simp?) (* takes while *)
         apply wp
        apply wp
       apply clarsimp
       apply (rename_tac args j \<sigma>' res)
       apply (clarsimp simp: foldmap_bounds_def foldmap_inv_def)
       apply (frule wa_abs_typing_u_elims(5))
       apply (erule_tac x = j in allE; clarsimp)
       apply (drule_tac acc = acc and
      obsv = obsv and
      rb = ra and
      wb = wa and
      rc = ro and
      ptrl = ptrl and
      ra = r and
      wa = "{}" in upd_wa_foldnb_bod_preservation; simp?; (clarsimp simp: Int_commute)?)
  

                     

  
  oops

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
  "wordarray_length_c is_valid_WordArray_u32_C heap_WordArray_u32_C len_C
    = main_pp_inferred.wordarray_length_0'"
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
  "wordarray_get_c is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32 len_C
      values_C t1_C.p1_C t1_C.p2_C = main_pp_inferred.wordarray_get_0'"
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
  "wordarray_put_c is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32
      heap_w32_update len_C values_C t2_C.arr_C t2_C.idx_C t2_C.val_C
    = main_pp_inferred.wordarray_put2_0'"
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

lemma wordarray_fold_wordarray_fold_no_break_0':
  "wordarray_fold_c is_valid_WordArray_u32_C heap_WordArray_u32_C is_valid_w32 heap_w32 len_C
      values_C t5_C.arr_C t5_C.frm_C t5_C.to_C t5_C.f_C t5_C.acc_C t5_C.obsv_C t3_C.acc_C
      t3_C.elem_C_update t3_C.acc_C_update t3_C.obsv_C_update dispatch_t4'
    = main_pp_inferred.wordarray_fold_no_break_0'"
  apply (unfold wordarray_fold_c_def main_pp_inferred.wordarray_fold_no_break_0'_def)
  apply (subst unknown_bind_ignore)+
  apply simp
  done
end (* of context *)

end