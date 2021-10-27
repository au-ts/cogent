theory Sum_AllRefine
imports WordArray_SVCorres WordArray_UpdCCorres WordArray_CorresProof_Asm

begin

text
  "This is an example of proving that @{term main_pp_inferred.sum_arr'} refines
  @{term Generated_Shallow_Desugar.sum_arr}. We can show this if we can prove that
  @{thm Generated_cogent_shallow.corres_shallow_C_sum_arr} is true without
  assuming that the abstract functions refine their corresponding shallow embeddings.

  @{term Generated_Shallow_Desugar.sum_arr} depends on the abstract functions defined for word
  arrays. So if we want to prove that our compilation is correct for 
  @{term Generated_Shallow_Desugar.sum_arr}, we need to prove that the "

text
  "First we overload the abstract function environments for the Update semantics with our own
   definitions."

overloading
  user_\<xi>_0' \<equiv> \<xi>_0
begin
definition user_\<xi>_0':
 "user_\<xi>_0' \<equiv> WordArray.\<xi>0" 
end

overloading
  user_\<xi>_1' \<equiv> \<xi>_1
begin
definition user_\<xi>_1':
 "user_\<xi>_1' \<equiv> WordArray.\<xi>1" 
end

sublocale WordArray \<subseteq> Generated_cogent_shallow _ wa_abs_repr wa_abs_typing_v wa_abs_typing_u wa_abs_upd_val
  by (unfold_locales)

context WordArray begin
text 
  "The two word array functions that we need to manually verify are @{term wordarray_length} and
   @{term wordarray_fold_no_break}. The theorems @{thm corres_add corres_sum_arr} are automatically
   generated by Cogent, and we simplify them to use our abstract function environment."

lemmas add_corres = corres_add[simplified \<Xi>_def[symmetric] user_\<xi>_0']
lemmas sum_arr_corres = corres_sum_arr[simplified \<Xi>_def[symmetric] user_\<xi>_1']

text
  "Currently the Cogent compiler does not correctly generate the correct @{term scorres}
   theorems for Cogent functions that call abstract functions. The theorem that should be
   generated would look like the following:"
(*
lemma sum_arr_scorres:
  "\<lbrakk>\<And>i \<gamma> v ts. \<lbrakk>i < length \<gamma>; valRel \<xi>' (v::(32 word) WordArray) (\<gamma> ! i)\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>';
    \<And>i \<gamma> v ts. \<lbrakk>i < length \<gamma>; valRel \<xi>' (v::((32 word) WordArray, 32 word, 32 word,
      (32 word, 32 word, unit) ElemAO \<Rightarrow> 32 word, 32 word, unit) WordArrayMapNoBreakP) (\<gamma> ! i);
      WordArrayMapNoBreakP.f\<^sub>f v = Generated_Shallow_Normal.add;
      \<exists>fs. \<gamma> ! i = VRecord fs \<and> fs ! 3 = (VFunction Generated_Deep_Normal.add [])\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_fold_no_break v) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>';
    valRel \<xi>' v v'\<rbrakk>
  \<Longrightarrow> val.scorres (Generated_Shallow_Normal.sum_arr v) (specialise ts Generated_Deep_Normal.sum_arr) [v'] \<xi>'"
  apply (unfold Generated_Shallow_Normal.sum_arr_def Generated_Deep_Normal.sum_arr_def)
  apply (simp only: specialise.simps)
  apply (clarsimp simp: val.scorres_def)
  apply (erule v_sem_varE)+
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (rename_tac r len)
  apply (drule_tac x = "[v', v']" in meta_spec)
  apply (drule_tac x = v in meta_spec)
  apply (drule_tac x = "[TPrim (Num U32)]" in meta_spec)
  apply clarsimp
  apply (erule_tac x = len in allE)
  apply clarsimp
  apply (drule_tac x = 0  in meta_spec)
  apply (drule_tac x = "[VRecord [v', VPrim (LU32 0), VPrim (LU32 (wordarray_length v)), 
      VFunction Generated_Deep_Normal.add [], VPrim (LU32 0), VUnit],
    VUnit, VPrim (LU32 0), VFunction Generated_Deep_Normal.add [], VPrim (LU32 0),
    VPrim (LU32 (wordarray_length v)), v', v']" in meta_spec)
  apply (drule_tac x = "\<lparr>WordArrayMapNoBreakP.arr\<^sub>f = v, frm\<^sub>f = 0, to\<^sub>f = (wordarray_length v),
    f\<^sub>f = Generated_Shallow_Normal.add, acc\<^sub>f = 0, obsv\<^sub>f = ()\<rparr>" in meta_spec)
  apply (drule_tac x = "[TPrim (Num U32), TPrim (Num U32), TUnit]" in meta_spec)
  apply clarsimp
  apply (erule meta_impE)
   apply (simp add: valRel_records)
   apply clarsimp thm scorres_add
   apply (cut_tac  \<xi> = \<xi>' and
      v' = "VRecord [VPrim (LU32 (ElemAO.elem\<^sub>f x)), VPrim (LU32 (ElemAO.acc\<^sub>f x)), VUnit]"
      in scorres_add[where ts = "[]", simplified val.scorres_def specialise.simps],
      (simp add: valRel_records)?)
   apply (rename_tac s)
   apply (erule_tac x = s in allE)
   apply clarsimp
  apply (erule_tac x = r in allE)
  apply (clarsimp simp: valRel_records)
  done
*)

section "The Shallow to C Correspondence With Assumptions"

text 
  "There are a few assumptions about the locales, we simplify the all refine theorem."
lemmas sum_arr_corres_shallow_C = 
  Generated_cogent_shallow.corres_shallow_C_sum_arr[
    of wa_abs_repr wa_abs_typing_v wa_abs_typing_u wa_abs_upd_val,
    simplified \<Xi>_def[symmetric] user_\<xi>_1',
    OF local.Generated_cogent_shallow_axioms _ _ local.correspondence_init_axioms]

section "Getting Our Theorems to Line Up"

text 
  "Since we made our theorems about word arrays as general as possible, we need to do a little
   bit of massaging to get them to match up with our assumptions."

lemmas wordarray_length_u32_corres = 
  upd_C_wordarray_length_corres_gen[rotated -1, of \<xi>1, simplified fun_eq_iff \<xi>1.simps, simplified]

lemma wordarray_fold_no_break_u32_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_add; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- wordarray_fold_no_break_0' v';
                  gets (\<lambda>s. x)
               od)
         \<xi>1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (subgoal_tac "\<exists>fs. (\<gamma> ! i) = URecord fs")
   apply (erule exE)
   apply (rule_tac k = "kinding_fn [] (foldmap_obsv_type ''wordarray_fold_no_break_0'')" and
      \<xi>0' = \<xi>0 and K' = "[]" and num = U32
      in upd_C_wordarray_fold_no_break_corres_gen; simp?)
          apply (rule upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
         apply (rule disjI1)
         apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def)
        apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def)
       apply (rule kindingI; simp)
      apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def val_rel_simp
      abbreviated_type_defs cogent_function_val_rel untyped_func_enum_defs)
    apply (rule typing_app[of _ 
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      "[option.Some (TRecord [(''elem'', TPrim (Num U32), Present),
        (''acc'', TPrim (Num U32), Present), (''obsv'', TUnit, Present)] Unboxed)]"
      _ _
      "TRecord [(''elem'', TPrim (Num U32), Present), (''acc'', TPrim (Num U32), Present),
        (''obsv'', TUnit, Present)] Unboxed"] ; simp?)
      apply (clarsimp simp: split_def)
      apply (rule_tac k = "{D, S}" in share, rule kindingI; simp?)
     apply (rule typing_fun; simp?)
       apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
       apply (subst wordarray_fold_no_break_0_type_def[symmetric])
       apply (subst \<Xi>_def[symmetric])
       apply (rule add_typecorrect'[simplified add_type_def snd_conv fst_conv])
      apply (clarsimp simp: empty_def weakening_def)
      apply (rule_tac k = "{D, S}" in drop, rule kindingI; simp?)
     apply clarsimp
    apply (subst Generated_TypeProof.abbreviated_type_defs[symmetric])+
    apply (subst wordarray_fold_no_break_0_type_def[symmetric])
    apply (subst \<Xi>_def[symmetric])
    apply (rule typing_var)
     apply (clarsimp simp: weakening_def empty_def)
     apply (rule keep)
     apply (clarsimp simp: abbreviated_type_defs)
      apply clarsimp
     apply (clarsimp simp: val_rel_simp cogent_function_val_rel untyped_func_enum_defs)
     apply (subst dispatch_t4'_def; simp)
     apply (subst unknown_bind_ignore)
     apply (simp add: untyped_func_enum_defs)
     apply (rule corres_app_concrete[simplified]; (simp del: \<xi>0.simps)?)
     apply (simp add: \<Xi>_def wordarray_fold_no_break_0_type_def del: \<xi>0.simps)
     apply (subst wordarray_fold_no_break_0_type_def[symmetric])
     apply (subst \<Xi>_def[symmetric])
     apply (rule add_corres[simplified add_type_def snd_conv fst_conv])
     apply (clarsimp simp: val_rel_simp)
    apply (clarsimp simp: fun_eq_iff)
   apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def abbreviated_type_defs)
  apply (clarsimp simp: val_rel_simp)
  done

text
  "If the assumptions for the @{term scorres} level was working properly, we would need these
   theorems."
(*
lemma wordarray_length_u32_scorres:
  "\<And>i \<gamma> v ts.
   \<lbrakk>i < length \<gamma>; valRel \<xi>p1 (v::32 word WordArray) (\<gamma> ! i)\<rbrakk> 
    \<Longrightarrow> val.scorres (wordarray_length v) (App (AFun ''wordarray_length'' ts) (Var i)) \<gamma> \<xi>p1"
  apply (rule scorres_wordarray_length; clarsimp simp: fun_eq_iff)
  done

lemma wordarray_fold_no_break_u32_scorres:
  "\<And>i \<gamma> v ts.
   \<lbrakk>i < length \<gamma>; valRel \<xi>p1 (v::((32 word) WordArray, 32 word, 32 word,
      (32 word, 32 word, unit) ElemAO \<Rightarrow> 32 word, 32 word, unit) WordArrayMapNoBreakP) (\<gamma> ! i);
    WordArrayMapNoBreakP.f\<^sub>f v = Generated_Shallow_Normal.add;
    \<exists>fs. \<gamma> ! i = VRecord fs \<and> fs ! 3 = VFunction Generated_Deep_Normal.add []\<rbrakk>
    \<Longrightarrow> val.scorres (wordarray_fold_no_break v) (App (AFun ''wordarray_fold_no_break'' ts) (Var i)) \<gamma> \<xi>p1"
  apply (subgoal_tac "\<exists>arr frm to f acc obsv. v = \<lparr>WordArrayMapNoBreakP.arr\<^sub>f = arr, frm\<^sub>f = frm, to\<^sub>f = to,
    f\<^sub>f = f, acc\<^sub>f = acc, obsv\<^sub>f = obsv\<rparr>")
   apply clarsimp
   apply (rule_tac \<xi>p' = \<xi>p in scorres_wordarray_fold_no_break_u32; simp?)
  apply (clarsimp simp: fun_eq_iff )
   apply (clarsimp simp: valRel_records valRel_WordArray_simps)
   apply (rename_tac x v')
   apply (cut_tac v = x and ts = "[]" and \<xi> = \<xi>p and 
      v' = "VRecord [VPrim (LU32 (ElemAO.elem\<^sub>f x)), VPrim (LU32 (ElemAO.acc\<^sub>f x)), VUnit]" in scorres_add)
    apply (clarsimp simp: valRel_records)
   apply (clarsimp simp: val.scorres_def)
  apply (clarsimp simp: valRel_records valRel_WordArray_simps)
  apply (rule_tac x = "WordArrayMapNoBreakP.arr\<^sub>f v" in exI)
  apply (rule_tac x = "WordArrayMapNoBreakP.frm\<^sub>f v" in exI)
  apply (rule_tac x = "WordArrayMapNoBreakP.to\<^sub>f v" in exI)
  apply (rule_tac x = "Generated_Shallow_Normal.add" in exI)
  apply (rule_tac x = "WordArrayMapNoBreakP.acc\<^sub>f v" in exI)
  apply clarsimp
  done
*)
section "Putting It All Together"

text
  "Now with @{thm wordarray_length_u32_corres wordarray_fold_no_break_u32_corres} we can remove the
   assumptions about about @{term corres} and @{term scorres} for @{term wordarray_length} and
   @{term wordarray_fold_no_break}."

declare \<xi>0.simps[simp del]
declare \<xi>1.simps[simp del]

lemmas sum_arr_corres_shallow_C_concrete =  sum_arr_corres_shallow_C[
  of \<xi>m1 \<xi>p1, simplified,
  OF wordarray_length_u32_corres, simplified,
  OF wordarray_fold_no_break_u32_corres[simplified], simplified TrueI, simplified]

section "Further Improvements"

text
  "We can go one step further by removing the assumptions:
    * @{term \<open>value_sem.rename_mono_prog wa_abs_typing_v rename \<Xi> \<xi>m1 \<xi>p1\<close>},
    * @{term \<open>proc_ctx_wellformed \<Xi>\<close>},
    * @{term \<open>value_sem.proc_env_matches wa_abs_typing_v \<xi>m1 \<Xi>\<close>}.

   The @{term \<open>value_sem.rename_mono_prog\<close>} assumption ensures that  monomorphisation of the whole
   Cogent program preserves the semantics of abstract functions. With this assumption, we can prove
   that the monomorphic deep embedding of Cogent expressions refine their polymorphic deep embeddings.
   We prove this is the case in  @{thm value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1}. Note that the
   renaming that occurs due to monomorphisation only really affects abstract functions due to their
   deep embedding being of the form @{term \<open>VAFunction f ts\<close>}, where @{term \<open>(f:: string)\<close>} is the
   name of the monomorphised abstract function. @{term \<open>value_sem.rename_mono_prog\<close>} is proved
   by unfolding the definitions of the deep embeddings of the abstract function and case analysis on
   the arguments and return values. For functions such as @{term wordarray_length}, whose deep
   embedding is very simple, this proof is very simple. For more complex functions such as
   @{term wordarray_fold_no_break}, is more tricky due to the fact that
   @{term wordarray_fold_no_break} is a higher order function, so we need to know that the function
   it takes as an argument preserves it semantics when monomorphisation. We solve this by first
   proving @{term \<open>value_sem.rename_mono_prog\<close>} for first order abstract function and then use that
   result in conjunction with @{thm rename_monoexpr_correct} to prove
   @{term \<open>value_sem.rename_mono_prog\<close>} for second order functions. Note that
   @{thm rename_monoexpr_correct} assumes @{term \<open>proc_ctx_wellformed\<close>} and
   @{term \<open>value_sem.proc_env_matches\<close>}, which we can prove as described below.
   We proved @{term \<open>value_sem.rename_mono_prog\<close>} in @{thm value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p
   value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1} for first order and second order abstract functions
   defined in @{term \<xi>m}, @{term \<xi>m1}, @{term \<xi>p} and @{term \<xi>p1}.

   The @{term \<open>proc_ctx_wellformed\<close>} assumption states that the types of our abstract functions
   are type well-formed. This was fairly easy to prove as it follows from the definition of the
   types of abstract functions (@{thm proc_ctx_wellformed_\<Xi>}.

   The @{term \<open>value_sem.proc_env_matches\<close>} assumption guarantees the preservation of types for
   abstract functions. The key theorems @{thm mono_correct rename_monoexpr_correct}, which
   are used to prove that the monomorphised Cogent expressions refine their polymorphic counterparts.
   For abstract functions which are not higher order and do not do any recursion/iteration, it is
   fairly easy to prove type preservation as this follows from the definition and by using the
   the @{term vval_typing} and @{term vval_typing_record} rules. For recursive/iterative
   functions, this becomes more complex as one would typically need to rely on some sort of
   invariant. For higher order functions, we need to know that all functions that they could possibly
   call also preserve typing, however, in our definition of higher order abstract functions, abstract
   functions can only call first order functions, and we only support up to (and including) second
   order functions. So we can first prove type preservation for all first order functions, and use
   this to prove type preservation for higher order functions. We proved
   @{term \<open>value_sem.proc_env_matches\<close>} in @{thm val_proc_env_matches_\<xi>m_\<Xi>
   val_proc_env_matches_\<xi>m1_\<Xi>} for first order and second order abstract functions defined in
   @{term \<xi>m} and @{term \<xi>m1}."

lemmas sum_arr_corres_shallow_C_concrete_strong = 
  sum_arr_corres_shallow_C_concrete[OF value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m1_\<xi>p1 _ _ 
                                       proc_ctx_wellformed_\<Xi> val_proc_env_matches_\<xi>m1_\<Xi>]

section "Even More Improvement"

text 
  "If we look at the definition of @{term corres_shallow_C}, you will notice that we are implicitly
   assuming that type preservation holds for the deep embedding of abstract functions in the update
   semantics, abstract functions satisfy the @{term frame} constraints. the the deep embeddings of
   abstract functions in the update and value semantics correspond, and that the if the deep embedding
   of an abstract function executes in the update semantics, the corresponding deep embedding in the
   value semantics will also execute (upward propagation of evaluation). These assumptions are
   contained in @{term proc_env_matches_ptrs} and @{term proc_env_u_v_matches}.

   Type preservation for abstract functions in the update semantics and @{term frame} constraint
   satisfiability is contained in @{term proc_env_matches_ptrs}, and can be proved in a similar
   fashion to proving @{term \<open>value_sem.proc_env_matches\<close>} with the addition of using some lemmas
   @{term frame} constraints. We proved @{term proc_env_matches_ptrs} in
   @{thm upd_proc_env_matches_ptrs_\<xi>0_\<Xi> upd_proc_env_matches_ptrs_\<xi>1_\<Xi>} for first order and second
   order abstract functions defined in @{term \<xi>0} and @{term \<xi>1}.
  
   Proving correspondence and upward propagation is contained in @{term proc_env_u_v_matches}.
   For non higher order functions, we can prove this by unfolding the definitions of the two deep
   embeddings and use the rules on @{term upd_val_rel} and @{term upd_val_rel_record}. For higher
   order functions, it is easier to first prove correspondence separately, and use this result to
   prove upward propagation using the  @{thm val_executes_from_upd_executes}. Note that proving
   correspondence requires the knowledge that all the deep embeddings of the functions that could be
   called correspond and upward propagation is true. So we need to first prove 
   @{term proc_env_u_v_matches} for all the orders below the current and then we can apply the
   @{thm mono_correspondence} to prove correspondence for the function argument. We proved
   @{term proc_env_u_v_matches} in @{thm proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi> proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>}
   for first order and second order abstract functions defined in @{term \<xi>0}, @{term \<xi>1}, @{term \<xi>m}
   and @{term \<xi>m1}."

lemma sum_arr_corres_shallow_C_concrete_stronger:
  "\<lbrakk>vv\<^sub>m = rename_val rename (monoval vv\<^sub>p); val_rel_shallow_C rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p1 \<sigma> \<Xi>;
    matches \<Xi> [rename_val rename (monoval vv\<^sub>p)] 
      [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
    \<Longrightarrow> 
    (\<sigma>, s) \<in> state_rel \<longrightarrow>
    (\<exists>r w. u_v_matches \<Xi> \<sigma> [uv\<^sub>m] [rename_val rename (monoval vv\<^sub>p)]
            [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] r w) \<longrightarrow>
    \<not> prod.snd (sum_arr' uv\<^sub>C s) \<and>
    (\<forall>r' s'.
        (r', s') \<in> prod.fst (sum_arr' uv\<^sub>C s) \<longrightarrow>
        (\<exists>\<sigma>' v\<^sub>u\<^sub>m v\<^sub>p.
            \<xi>1, [uv\<^sub>m] \<turnstile> (\<sigma>, Generated_TypeProof.sum_arr) \<Down>! (\<sigma>', v\<^sub>u\<^sub>m) \<and>
            \<xi>m1 , [rename_val rename
                    (monoval vv\<^sub>p)] \<turnstile> Generated_TypeProof.sum_arr \<Down> rename_val rename (monoval v\<^sub>p) \<and>
            (\<sigma>', s') \<in> state_rel \<and> val_rel_shallow_C rename (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) r' v\<^sub>p v\<^sub>u\<^sub>m \<xi>p1 \<sigma>' \<Xi>))"
  apply (frule sum_arr_corres_shallow_C_concrete_strong[simplified corres_shallow_C_def
        proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>1_\<Xi> proc_env_u_v_matches_\<xi>1_\<xi>m1_\<Xi>]; simp?)
  done

section "Proving Functional Correctness"

text
  "We can now easily prove the functional correctness of our @{term sum_arr'} C function. In this
   case, our @{term sum_arr'} C function should sum all the elements of the list which is of type
   @{typ \<open>32 word list\<close>} in our shallow embeeding. Our functional correctness specification would
   look like following:"

definition sum_list :: "32 word list \<Rightarrow> 32 word"
  where
"sum_list xs = fold (+) xs 0"

text
  "Our functional correctness specification @{term sum_list} calls the @{term fold} function to
   iterate of the list and add up all of its elements.

   Before we prove functional correctness, we need to observe that @{term wordarray_length} returns
   a value of type @{typ \<open>32 word\<close>}. This means that any list that refines to a word array in our
   C code should in fact be of length at most @{term \<open>max_word :: 32 word\<close>}. In fact, it should
   actually be less depending on the maximum heap size. You may notice that in our abstract typing
   in the update semantics @{thm wa_abs_typing_u_def}, we enforced that the length of an array times
   the size of an element in the array, should in fact be less than the maximum word, since an array
   larger than that would not fit in memory. So a using thing to prove is the following:"

lemma len_eq_walen_if_le_max32:
  "length xs \<le> unat (max_word :: 32 word)
    \<Longrightarrow> unat (wordarray_length xs) = length xs"
  apply (clarsimp simp: wordarray_length')
  apply (rule le_unat_uoi; simp)
  done

text
  "With this we can now prove functional correctness."

lemma sum_arr_correct:
  "length xs \<le> unat (max_word :: 32 word)
    \<Longrightarrow> sum_list xs = Generated_Shallow_Desugar.sum_arr xs"
  apply (clarsimp simp: sum_list_def Generated_Shallow_Desugar.sum_arr_def
      valRel_records wordarray_fold_no_break' Generated_Shallow_Desugar.add_def
      len_eq_walen_if_le_max32 take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)
  done

section "sum_arr C functional correctness theorem"


definition
  array :: "(lifted_globals \<times> WordArray_u32_C ptr) \<Rightarrow>
              (WordArray_u32_C \<times>
              abstyp \<times>
              vabstyp \<times>
              vabstyp \<times>
              32 word WordArray)"
where
  "array sp = 
    (let (s, p) = sp;
         w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         arr = values_C w;
         xs = (map (\<lambda>i. heap_w32 s (arr +\<^sub>p int i)) [0..<(unat l)]);
         vxs = (map (\<lambda>i. VPrim (LU32 i)) xs);
         rp = RCon ''WordArray'' [RPrim (Num U32)]
    in (w,
        UWA (TPrim (Num U32)) l (ptr_val arr),
        VWA (TPrim (Num U32)) vxs,
        VWA (TPrim (Num U32)) vxs,
        xs))"

abbreviation  "arr\<^sub>c \<equiv> prod.fst \<circ> array"
abbreviation  "arr\<^sub>u \<equiv> prod.fst \<circ> prod.snd \<circ> array"
abbreviation  "arrptr p \<equiv> UPtr (ptr_val p) (RCon ''WordArray'' [RPrim (Num U32)])"
abbreviation  "arr\<^sub>v \<equiv> prod.fst \<circ> prod.snd \<circ> prod.snd \<circ> array"
abbreviation  "arr\<^sub>m sp \<equiv> VAbstract (arr\<^sub>v sp)"
abbreviation  "arr\<^sub>p sp \<equiv> VAbstract ((prod.fst \<circ> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> array) sp)"
abbreviation  "arr\<^sub>s \<equiv> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> prod.snd \<circ> array"
abbreviation  "arrptrs s p \<equiv> map (\<lambda>i. ptr_val (values_C (arr\<^sub>c (s, p)) +\<^sub>p int i))[0..<unat((SCAST(32 signed \<rightarrow> 32))(len_C (arr\<^sub>c (s, p))))]"

definition
  valid_array :: "lifted_globals \<Rightarrow>  WordArray_u32_C ptr \<Rightarrow> bool"
where
  "valid_array s p = 
    (let w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         arr = values_C w
     in is_valid s p \<and> 
        size_of (TYPE(32 word)) * unat l \<le> unat (max_word :: 32 word) \<and>
        (\<forall>i < l. is_valid_w32 s (arr +\<^sub>p uint i)) \<and>
         (\<forall>i < l. ptr_val p \<noteq> ptr_val (arr +\<^sub>p uint i)))"

definition
  same_array :: "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> WordArray_u32_C ptr \<Rightarrow> bool"
where
  "same_array s s' p = 
    (let w = heap s p;
         l = (SCAST(32 signed \<rightarrow> 32))(len_C w);
         w' = heap s' p;
         arr = values_C w
     in valid_array s p \<and>
        valid_array s' p \<and>
        w = w' \<and>
        (\<forall>i < l. heap_w32 s (arr +\<^sub>p uint i) = heap_w32 s' (arr +\<^sub>p uint i)))"

lemma inputs_uv_matches:
  "\<lbrakk>valid_array s p; \<sigma> (ptr_val p) = option.Some (UAbstract (arr\<^sub>u (s, p)));
    \<forall>p \<in> set (arrptrs s p). \<sigma> p = option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)p))))\<rbrakk> \<Longrightarrow>
   u_v_matches \<Xi> \<sigma> [arrptr p] [arr\<^sub>m (s, p)]
      [Some (fst (snd Generated_TypeProof.sum_arr_type))]
      (insert (ptr_val p) (set (arrptrs s p))) {}"
  apply (clarsimp simp: array_def
                        Let_def
                        Generated_TypeProof.sum_arr_type_def
                        Generated_TypeProof.abbreviated_type_defs)
  apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
               u_v_matches_empty[where \<tau>s = "[]", simplified]
               u_v_struct
               u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
               u_v_p_abs_ro[where a = "arr\<^sub>u (s, p)" and ts = "[TPrim (Num U32)]", simplified]
               u_v_prim'
               u_v_r_empty; (simp add: array_def Let_def)?)
  apply (clarsimp simp: wa_abs_upd_val_def)
  apply (rule conjI)
   apply (clarsimp simp: wa_abs_typing_u_def valid_array_def Let_def)
   apply (rule conjI)
    apply (rule equalityI; clarsimp simp: word_less_nat_alt array_def Let_def)
     apply (intro exI conjI; simp?)
     apply (subst le_unat_uoi[OF order.strict_implies_order]; simp?)
    apply (rule image_eqI; simp?)
   apply clarsimp
   apply (erule_tac x = "unat i" in ballE; simp?)
   apply (clarsimp simp: word_less_nat_alt)
  apply (rule conjI)
   apply (clarsimp simp: wa_abs_typing_v_def valid_array_def Let_def)
  apply clarsimp
  apply (erule_tac x = "unat i" in ballE; simp?)
   apply (subst nth_map)
    apply (simp add: word_less_nat_alt)
   apply simp
   apply (simp add: word_less_nat_alt)
   apply (rename_tac i)
   apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p int (unat i))")
    apply simp
   apply (subst ptr_val_inj[symmetric])
   apply simp
  apply (simp add: word_less_nat_alt)
  done

lemma inputs_staterel_valrel:
  "\<lbrakk>valid_array s p\<rbrakk> \<Longrightarrow>
   \<exists>\<sigma>. (\<sigma>, s) \<in> state_rel \<and>
      \<sigma> (ptr_val p) = option.Some (UAbstract (arr\<^sub>u (s, p))) \<and>
      (\<forall>p \<in> set (arrptrs s p). \<sigma> p = option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)p))))) \<and>
      val_rel_shallow_C rename (arr\<^sub>s (s, p)) p (arr\<^sub>p (s, p)) (arrptr p) \<xi>p1 \<sigma> \<Xi>"
  apply (clarsimp simp: val_rel_shallow_C_def
                        valRel_records
                        Let_def
                        val_rel_simp
                        valRel_WordArrayUX
                        ucast_id)
  apply (rule_tac x = "(\<lambda>l. if l = ptr_val p then option.Some (UAbstract (arr\<^sub>u (s, p))) 
                            else if l \<in> set (arrptrs s p)
                              then option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)l))))
                            else None)" in exI)
  apply (rule conjI)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (rule conjI;
          clarsimp simp: heap_rel_ptr_meta
                         heap_rel_meta_def
                         array_def
                         Let_def
                         type_rel_simp
                         wa_abs_repr_def
                         valid_array_def
                         val_rel_simp)
   apply (rename_tac i)
   apply (erule_tac x = "of_nat i" in allE)
   apply (clarsimp simp: word_less_nat_alt)
   apply (cut_tac y = i and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
   apply (subgoal_tac "x = values_C (heap s p) +\<^sub>p uint (of_nat i)")
    apply clarsimp
    apply assumption
   apply (simp add: ptr_add_def)
   apply (subst ptr_val_inj[symmetric])
   apply simp
  apply (rule conjI; clarsimp simp: array_def Let_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_array_def Let_def)
   apply (rename_tac i)
   apply (erule_tac x = "of_nat i" in allE)+
   apply (cut_tac y = i and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
   apply (clarsimp simp: word_less_nat_alt)

  apply (frule_tac \<sigma> = "(\<lambda>l. if l = ptr_val p then option.Some (UAbstract (arr\<^sub>u (s, p))) 
                            else if l \<in> set (arrptrs s p)
                              then option.Some (UPrim (LU32 (heap_w32 s (PTR(32 word)l))))
                            else None)" in inputs_uv_matches; simp?)
   apply (clarsimp simp: valid_array_def Let_def)
   apply (rename_tac j)
   apply (erule_tac x = "of_nat j" in allE)+
   apply (clarsimp simp: word_less_nat_alt)
   apply (cut_tac y = j and z = "(SCAST(32 signed \<rightarrow> 32) (len_C (heap s p)))" in le_unat_uoi; simp?)
    apply (clarsimp simp: array_def Let_def)+
  apply (rule_tac x = "fst (snd Generated_TypeProof.sum_arr_type)" in exI)
  apply (drule_tac i = 0 in  u_v_matches_proj_single'; simp?)
  apply clarsimp
  apply (intro exI conjI; assumption)
  done

lemma inputs_rename_monoval:
  "arr\<^sub>m sp = rename_val rename (monoval (arr\<^sub>p sp))"
  apply (clarsimp simp: rename_def Let_def array_def split: prod.splits)
  done

lemma inputs_val_matches:
  "matches \<Xi> [arr\<^sub>m (s, p)] [Some (fst (snd Generated_TypeProof.sum_arr_type))]"
  apply (clarsimp simp: matches_def
                        Let_def
                        array_def
                        Generated_TypeProof.sum_arr_type_def
                        Generated_TypeProof.abbreviated_type_defs)
  apply (intro v_t_abstract; simp?)
  apply (clarsimp simp: wa_abs_typing_v_def)
  done

lemma WordArray_u32_C_eq_simps:
  "x = y \<longleftrightarrow> len_C x = len_C y \<and> values_C x = values_C y"
  apply (rule iffI)
   apply clarsimp
  apply clarsimp
  by (metis WordArray_u32_C_idupdates(1))

inductive_cases u_v_uvprimE: "upd_val_rel \<Xi>' \<sigma> (UPrim l) (VPrim l') \<tau> r w"

corollary sum_arr_C_correct:
  "\<lbrakk>sorted (arr\<^sub>s (s, p));
    cc = sum_arr' p;
    valid_array s p\<rbrakk> \<Longrightarrow>
   \<not> prod.snd (cc s) \<and> 
   (\<forall>r s'. (r, s') \<in> prod.fst (cc s) \<longrightarrow>
      same_array s s' p \<and>
      r = sum_list (arr\<^sub>s (s, p)))"
  apply (frule_tac inputs_staterel_valrel; clarsimp)
  apply (frule_tac s = s in 
      sum_arr_corres_shallow_C_concrete_stronger[rotated 1];
      (simp add: inputs_rename_monoval[simplified] inputs_val_matches[simplified])?)
   apply (cut_tac sp = "(s, p)" in inputs_rename_monoval[simplified, symmetric]; simp?)
   apply (clarsimp simp: inputs_val_matches[ simplified ])
  apply (cut_tac sp = "(s, p)" in inputs_rename_monoval[simplified, symmetric]; simp?)
  apply (erule impE)
   apply (frule_tac \<sigma> = \<sigma> in inputs_uv_matches; simp?)
   apply (intro exI; assumption)
  apply clarsimp
  apply (erule_tac x = r in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule conjI)
   apply (thin_tac "_ \<in> state_rel")
   apply (frule_tac inputs_uv_matches; simp?)
   apply (drule u_v_matches_to_matches_ptrs)
   apply (drule (1)  update_sem.preservation(1)[OF update_sem_axioms, where \<tau>s = "[]" and K = "[]", simplified, 
                                        OF proc_ctx_wellformed_\<Xi> _ 
                                        upd_proc_env_matches_ptrs_\<xi>1_\<Xi>  _ 
                                        sum_arr_typecorrect',
                                        rotated 1])
   apply (clarsimp simp: Generated_TypeProof.sum_arr_type_def)
   apply (frule tprim_no_pointers(1))
   apply (drule tprim_no_pointers(2))
   apply clarsimp
   apply (clarsimp simp: frame_def fun_eq_iff[symmetric])
   apply (clarsimp simp: valid_array_def same_array_def)
   apply (clarsimp simp: Let_def state_rel_def heap_rel_def heap_rel_ptr_meta)
   apply (erule_tac x = p in allE)
   apply (clarsimp simp: heap_rel_meta_def array_def Let_def type_rel_simps wa_abs_repr_def val_rel_simps)
   apply (rule conjI)
    apply clarsimp
    apply (rename_tac i)
    apply (erule_tac x = "unat i" in ballE; simp?)
     apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p uint i)")
      apply simp
      apply (erule_tac x = "values_C (heap s' p) +\<^sub>p uint i" in allE)
      apply (clarsimp simp: heap_rel_meta_def array_def Let_def type_rel_simps wa_abs_repr_def val_rel_simps)
     apply (simp add: ptr_add_def)
    apply (clarsimp simp: word_less_nat_alt)
   apply (rule conjI)
    apply (clarsimp simp:  WordArray_u32_C_eq_simps)
   apply clarsimp
   apply (rename_tac i)
    apply (erule_tac x = "unat i" in ballE; simp?)
     apply (subgoal_tac "(PTR(32 word) (ptr_val (values_C (heap s p)) + 4 * i)) = (values_C (heap s p) +\<^sub>p uint i)")
      apply simp
      apply (erule_tac x = "values_C (heap s' p) +\<^sub>p uint i" in allE)
      apply (clarsimp simp: heap_rel_meta_def array_def Let_def type_rel_simps wa_abs_repr_def val_rel_simps)
     apply (simp add: ptr_add_def)
    apply (clarsimp simp: word_less_nat_alt)
  apply (rotate_tac -1; subst (asm) val_rel_shallow_C_def)
  apply (clarsimp simp: val_rel_simps valRel_records)
  apply (erule u_v_uvprimE; clarsimp)
  apply (rule sum_arr_correct[symmetric])
   apply (clarsimp simp: array_def Let_def unat_le_helper)+
  done

end (* of context *)

end