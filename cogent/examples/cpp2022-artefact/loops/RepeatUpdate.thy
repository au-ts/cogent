theory RepeatUpdate
  imports UpdateSemHelper
begin

section "Repeat loop definitions" 

text "Main body:
  Summary:
    Does at most @{term \<open>n::nat\<close>} iterations and apply @{term \<open>g ::'f expr\<close>} to update the input
    accumulator and heap. If @{term \<open>f ::'f expr\<close>} returns @{term True} then terminate early.
  Arguments:
    @{term \<open>\<xi>'::('f, 'a, 'l) uabsfuns\<close>} is a partial mapping from abstract function names to their specifications,
    @{term \<open>n::nat\<close>} is a natural number that is recursed on, i.e. terminate if 0 else subtract 1, apply body and repeat ,
    @{term \<open>f ::'f expr\<close>} is a Cogent expression that is used to check if the loop should terminate early,
    @{term \<open>g ::'f expr\<close>} is a Cogent expression that is used to update the heap and the accumulator,
    @{term \<open>\<sigma>::('f, 'a, 'l) store\<close>} is the input heap that is updated each loop iteration,
    @{term \<open>\<sigma>'::('f, 'a, 'l) store\<close>} is the output heap,
    @{term \<open>\<tau>a::type\<close>} is the Cogent type of the accumulator,
    @{term \<open>acc::('f, 'a, 'l) uval\<close>} is the accumulator that is updated each loop iteration,
    @{term \<open>\<tau>o::type\<close>} is the Cogent type of the observer,
    @{term \<open>obsv::('f, 'a, 'l) uval\<close>} is the observer that does not change throughout the loop,
    @{term \<open>ret::('f, 'a, 'l) uval\<close>} is the is the output accumulator value.
  Output:
    @{term True} if the loop evaluates to the output heap and accumulator,
    @{term False} otherwise."

fun urepeat_bod
  where
"urepeat_bod _ 0 _ _ \<sigma> \<sigma>' _ acc _ _ ret = (\<sigma> = \<sigma>' \<and> acc = ret)" |
"urepeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret =
  (\<exists>b. (\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool b))) \<and>
    (if b then \<sigma> = \<sigma>' \<and> acc = ret
     else (\<exists>\<sigma>'' acc'. (\<xi>' , [URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None] 
        \<turnstile> (\<sigma>, App g (Var 0)) \<Down>! (\<sigma>'', acc')) \<and>
      urepeat_bod \<xi>' n f g \<sigma>'' \<sigma>' \<tau>a acc' \<tau>o obsv ret)))"

text "Wrapper with extra checks:
  Summary:
    Checks the arguments are of the correct form and type and then passes these to
    @{term urepeat_bod} with minor processing.
  Checks:
    * The observer type has been banged, i.e. is read-only or is drop-able.
    * The functions f and g are of the correct type and form."

definition urepeat
  where
"urepeat \<Xi>' \<xi>' \<tau>a \<tau>o x y =
  (\<exists>\<sigma> \<sigma>' n f g acc obsv ret.
    x = (\<sigma>, URecord [(UPrim (LU64 n), RPrim (Num U64)), (f, RFun), (g, RFun),
      (acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None) \<and>
    y = (\<sigma>', ret) \<and>
    is_uvalfun f \<and>
    is_uvalfun g \<and>
    bang \<tau>o = \<tau>o \<and>
    (\<Xi>', 0, [], {}, 
      [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (uvalfun_to_expr f) (Var 0)) : TPrim Bool) \<and>
    (\<Xi>', 0, [], {}, 
      [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (uvalfun_to_expr g) (Var 0)) : \<tau>a) \<and>
    urepeat_bod \<xi>' (unat n) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret)"

section "Repeat loop lemmas"

context update_sem begin

subsection "Preservation and frame constraint satisfaction"

lemma urepeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches-u \<Xi>';
    \<Xi>', \<sigma> \<turnstile> acc :u \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> obsv :u \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret;
    \<Xi>', 0, [], {}, 
    [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>r' w'. \<Xi>', \<sigma>' \<turnstile> ret :u \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> frame \<sigma> wa \<sigma>' w'"
  apply (induct arbitrary: ra wa rule: urepeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply (rename_tac \<xi>' f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
   apply clarsimp
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (rename_tac \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
  apply clarsimp
  apply (rename_tac b)
  apply (case_tac b; clarsimp)
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (drule_tac x = False in meta_spec; clarsimp)
  apply (drule_tac x = \<sigma>'' and y = acc' in meta_spec2)
  apply clarsimp
  apply (drule_tac \<gamma> = "[URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None]" and
      \<sigma>' = \<sigma>'' and v = acc' and r = "ra \<union> ro" and w = wa in preservation_mono(1)[rotated -1]; simp?)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      matches_ptrs_empty[where \<tau>s = "[]", simplified])
    apply (rule u_t_struct; simp?) 
    apply (intro u_t_r_cons1[where  r' = ro and w' = "{}", simplified]
      u_t_r_cons1[where  r' = "{}" and w' = "{}", simplified] u_t_r_empty; simp?)
    apply blast 
   apply (simp add: matches_ptrs.matches_ptrs_empty)
  apply clarsimp
  apply (rename_tac r' w')
  apply (drule_tac x = r' and y = w' in meta_spec2; simp)
  apply (erule meta_impE)
   apply (drule_tac u = obsv in uval_typing_frame(1); simp?)
  apply (drule meta_mp)
   apply (drule_tac v = obsv in frame_noalias_uval_typing'(2); simp?)
  apply clarsimp
  apply (rename_tac r'' w'')
  apply (intro exI conjI, assumption)
   apply blast
  apply (rule frame_trans; simp?)
  done

lemma urepeat_preservation:
  "\<And>\<sigma> \<sigma>' v v' r w.
       \<lbrakk>proc_ctx_wellformed \<Xi>';
        \<xi>' matches-u \<Xi>';
        \<Xi>', \<sigma> \<turnstile> v :u TRecord
                     [(''n'', TPrim (Num U64), Present),
                      (''stop'', TFun (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) (TPrim Bool), Present),
                      (''step'', TFun (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) \<tau>a, Present),
                      (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)]
                     Unboxed \<langle>r, w\<rangle>;
        urepeat \<Xi>' \<xi>' \<tau>a \<tau>o (\<sigma>, v) (\<sigma>', v')\<rbrakk>
       \<Longrightarrow> \<exists>r' w'. \<Xi>', \<sigma>' \<turnstile> v' :u \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  unfolding urepeat_def
  apply clarsimp
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)+
  apply (erule u_t_r_emptyE; clarsimp)
  apply (frule tfun_no_pointers)
  apply (drule tfun_no_pointers(2))
  apply clarsimp
  apply (frule tfun_no_pointers)
  apply (drule tfun_no_pointers(2))
  apply clarsimp
  apply (frule tprim_no_pointers)
  apply (drule tprim_no_pointers(2))
  apply clarsimp
  apply (rename_tac \<sigma> \<sigma>' v' n f g acc ra wa obsv ro wo)
  apply (cut_tac \<Xi>' = \<Xi>' and \<sigma> = \<sigma> and \<tau> = \<tau>o and v = obsv and r = ro and w = wo in bang_not_writable(1); simp?)
  apply (rule urepeat_bod_preservation; simp?)
  apply blast
  done

end (* of context *)

subsection "Early termination and step lemmas"

lemma urepeat_bod_early_termination:
  "\<lbrakk>urepeat_bod \<xi>' i f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret; i < n;
    \<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None]  \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))\<rbrakk>
    \<Longrightarrow> urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret"
  apply (induct arbitrary: i rule: urepeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply clarsimp
  apply clarsimp
  apply (rename_tac i)
  apply (case_tac i; clarsimp)
   apply blast
  apply (rename_tac b)
  apply (case_tac b; clarsimp)
   apply blast
  apply (rename_tac ret nat b \<sigma>'' acc')
  apply (rule_tac x = b in exI)
  apply (rule conjI; clarsimp)
  apply (intro exI conjI; assumption)
  done

declare urepeat_bod.simps[simp del]
lemma urepeat_bod_step:
  "\<lbrakk>\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False));
    \<not>(\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)));
    \<xi>', [URecord [(ret, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None] \<turnstile> (\<sigma>', App g (Var 0)) \<Down>! (\<sigma>'', ret');
    urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret\<rbrakk> 
    \<Longrightarrow> urepeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>'' \<tau>a acc \<tau>o obsv ret'"
  apply (induct arbitrary: \<sigma>'' ret' rule: urepeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply (clarsimp simp: urepeat_bod.simps)
  apply clarsimp
  apply (erule urepeat_bod.elims; clarsimp)
  apply (rename_tac \<sigma>'' ret' \<xi> n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret b)
  apply (case_tac b; clarsimp)
  apply (drule_tac x = b in meta_spec; clarsimp)
  apply (elim meta_allE meta_impE, assumption, assumption)
  apply (subst urepeat_bod.simps; clarsimp)
  apply (rule_tac x = b in exI; clarsimp)
  apply (intro exI conjI; assumption)
  done
declare urepeat_bod.simps[simp]

subsection "Deterministic"

lemma urepeat_bod_deterministic:
  "\<lbrakk>determ \<xi>;
    urepeat_bod \<xi> n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret;
    urepeat_bod \<xi> n f g \<sigma> \<sigma>'' \<tau>a acc \<tau>o obsv ret'\<rbrakk>
    \<Longrightarrow> \<sigma>' = \<sigma>'' \<and> ret = ret'"
  apply (induct n arbitrary: \<sigma> acc)
   apply simp
  apply clarsimp
  apply (drule (2) u_sem_u_sem_all_determ(1)[rotated 1]; simp)
  apply clarsimp
  apply (rename_tac n \<sigma> acc b)
  apply (case_tac b; clarsimp)
  apply (drule (2) u_sem_u_sem_all_determ(1)[rotated 1]; simp)
  done

lemma urepeat_deterministic:
  "\<lbrakk>determ \<xi>;
    urepeat \<Xi> \<xi> \<tau>a \<tau>o x y;
    urepeat \<Xi> \<xi> \<tau>a \<tau>o x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding urepeat_def
  apply clarsimp
  apply (drule (3) urepeat_bod_deterministic)
  done

lemma urepeat_bod_step_determ:
  "\<lbrakk>\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False));
    \<xi>', [URecord [(ret, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None] \<turnstile> (\<sigma>', App g (Var 0)) \<Down>! (\<sigma>'', ret');
    urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret;
    determ \<xi>'\<rbrakk> 
    \<Longrightarrow> urepeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>'' \<tau>a acc \<tau>o obsv ret'"
  apply (rule urepeat_bod_step; simp?)
  apply clarsimp
  apply (drule (2) u_sem_u_sem_all_determ(1)[rotated 1]; simp)
  done

subsection "Ordering"

lemma urepeat_bod_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b;
    urepeat_bod \<xi>a n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret\<rbrakk>
    \<Longrightarrow> urepeat_bod \<xi>b n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret"
  apply (induct n arbitrary: \<sigma> acc)
   apply simp
  apply clarsimp
  apply (rename_tac n \<sigma> acc b)
  apply (case_tac b; clarsimp)
   apply (drule (1) u_sem_u_sem_all_rel_leqD)
   apply (rule_tac x = b in exI; clarsimp)
  apply (drule (1) u_sem_u_sem_all_rel_leqD[rotated 1])
  apply (drule (1) u_sem_u_sem_all_rel_leqD[rotated 1])
  apply (rule_tac x = b in exI; clarsimp)
  apply (elim meta_allE meta_impE, assumption)
  apply (intro exI conjI; assumption)
  done

lemma urepeat_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b;
    urepeat \<Xi> \<xi>a \<tau>a \<tau>o x y\<rbrakk>
    \<Longrightarrow> urepeat \<Xi> \<xi>b \<tau>a \<tau>o x y"
  unfolding urepeat_def
  apply clarsimp
  apply (drule (2) urepeat_bod_rel_leqD)
  done

end