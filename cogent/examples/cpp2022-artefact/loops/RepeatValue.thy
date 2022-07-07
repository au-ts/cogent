theory RepeatValue
  imports ValueSemHelper
begin

section "Repeat loop definitions"

text "Main body:
  Summary:
    Does at most @{term \<open>n::nat\<close>} iterations and apply @{term \<open>g ::'f expr\<close>} to update the input
    accumulator. If @{term \<open>f ::'f expr\<close>} returns @{term True} then terminate early.
  Arguments:
    @{term \<open>\<xi>'::('f, 'a) vabsfuns\<close>} is a partial mapping from abstract function names to their specifications,
    @{term \<open>n::nat\<close>} is a natural number that is recursed on, i.e. terminate if 0 else subtract 1, apply body and repeat ,
    @{term \<open>f ::'f expr\<close>} is a Cogent expression that is used to check if the loop should terminate early,
    @{term \<open>g ::'f expr\<close>} is a Cogent expression that is used to update the accumulator,
    @{term \<open>acc::('f, 'a) vval\<close>} is the accumulator that is updated each loop iteration,
    @{term \<open>obsv::('f, 'a) vval\<close>} is the observer that does not change throughout the loop,
    @{term \<open>ret::('f, 'a) vval\<close>} is the is the output accumulator value.
  Output:
    @{term True} if the loop evaluates to the output accumulator,
    @{term False} otherwise."

fun vrepeat_bod
  where
"vrepeat_bod _ 0 _ _ acc _ ret = (acc = ret)" |
"vrepeat_bod \<xi>' (Suc n) f g acc obsv ret =
  (\<exists>b. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool b)) \<and>
    (if b then acc = ret
     else (\<exists>acc'. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App g (Var 0) \<Down> acc') \<and>
      vrepeat_bod \<xi>' n f g acc' obsv ret)))"

context value_sem begin

text "Wrapper with extra checks:
  Summary:
    Checks the arguments are of the correct form and type and then passes these to
    @{term vrepeat_bod} with minor processing.
  Checks:
    * The functions f and g are of the correct type and form."

definition vrepeat
  where
"vrepeat \<Xi>' \<xi>' \<tau>a \<tau>o x y =
  (\<exists>n f g acc obsv ret.
    x = VRecord [VPrim (LU64 n), f, g, acc, obsv] \<and>
    y = ret \<and>
    is_vvalfun f \<and>
    is_vvalfun g \<and>
    (\<Xi>' \<turnstile> acc :v \<tau>a) \<and>
    (\<Xi>' \<turnstile> obsv :v \<tau>o) \<and>
    (\<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (vvalfun_to_expr f) (Var 0)) : TPrim Bool) \<and>
    (\<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (vvalfun_to_expr g) (Var 0)) : \<tau>a) \<and>
    vrepeat_bod \<xi>' (unat n) (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv ret)"

section "Preservation lemmas"

lemma vrepeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches \<Xi>';
    \<Xi>' \<turnstile> acc :v \<tau>a;
    \<Xi>' \<turnstile> obsv :v \<tau>o;
    vrepeat_bod \<xi>' n f g acc obsv ret;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<Xi>' \<turnstile> ret :v \<tau>a"
  apply (induct arbitrary: rule: vrepeat_bod.induct[of _ \<xi>' n f g acc obsv ret])
   apply clarsimp
  apply (clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
  apply (rename_tac \<xi>' n f g acc obsv ret b acc')
  apply (case_tac b; clarsimp)
  apply (drule_tac x = b in meta_spec; clarsimp)
  apply (drule_tac x = acc' in meta_spec; clarsimp)
  apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and v = acc' in 
      preservation(1)[of "[]" "[]" 0 "[]" "{}", OF subst_wellformed_nothing]; simp?)
   apply (clarsimp simp: matches_def)
   apply (rule v_t_record; simp?)
   apply (rule v_t_r_cons1; simp?)+
   apply (rule v_t_r_empty)
  apply (drule meta_mp; simp)
  done

lemma vrepeat_preservation:
  "\<And>v v'.
       \<lbrakk>proc_ctx_wellformed \<Xi>';
        \<xi>' matches \<Xi>';
        \<Xi>' \<turnstile> v :v TRecord
                  [(''n'', TPrim (Num U64), Present),
                   (''stop'', TFun (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) (TPrim Bool), Present),
                   (''step'', TFun (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) \<tau>a, Present),
                   (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)]
                  Unboxed;
        vrepeat \<Xi>' \<xi>' \<tau>a \<tau>o v v'\<rbrakk>
       \<Longrightarrow> \<Xi>' \<turnstile> v' :v \<tau>a"
  unfolding vrepeat_def
  apply clarsimp
  apply (erule v_t_recordE; clarsimp)
  apply (erule v_t_r_consE; clarsimp)+
  apply (rule vrepeat_bod_preservation; simp)
  done

end (* of context *)

section "Early termination and step lemmas"

lemma vrepeat_bod_early_termination:
  "\<lbrakk>vrepeat_bod \<xi>' i f g acc obsv ret; i < n;
    \<xi>' , [VRecord [ret, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True)\<rbrakk>
    \<Longrightarrow> vrepeat_bod \<xi>' n f g acc obsv ret"
  apply (induct arbitrary: i rule: vrepeat_bod.induct[of _ \<xi>' n f g acc obsv ret])
   apply clarsimp
  apply clarsimp
  apply (rename_tac i)
  apply (case_tac i; clarsimp)
   apply blast
  apply (rename_tac b)
  apply (case_tac b; clarsimp)
   apply blast
  apply (rename_tac ret nat b acc')
  apply (rule_tac x = b in exI)
  apply (rule conjI; clarsimp)
  apply (intro exI conjI; assumption)
  done

declare vrepeat_bod.simps[simp del]
lemma vrepeat_bod_step:
  "\<lbrakk>\<xi>', [VRecord [ret, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False);
    \<not>(\<xi>', [VRecord [ret, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True));
    \<xi>', [VRecord [ret, obsv]] \<turnstile> App g (Var 0) \<Down> ret';
    vrepeat_bod \<xi>' n f g acc obsv ret\<rbrakk> 
    \<Longrightarrow> vrepeat_bod \<xi>' (Suc n) f g acc obsv ret'"
  apply (induct arbitrary: ret' rule: vrepeat_bod.induct[of _ \<xi>' n f g acc obsv ret])
  apply (simp only: vrepeat_bod.simps)
   apply (clarsimp simp: vrepeat_bod.simps)
   apply blast
  apply clarsimp
  apply (erule vrepeat_bod.elims; clarsimp)
  apply (rename_tac ret' \<xi> n f g acc obsv ret b)
  apply (case_tac b; clarsimp)
  apply (drule_tac x = b in meta_spec; clarsimp)
  apply (elim meta_allE meta_impE, assumption, assumption)
  apply (subst vrepeat_bod.simps; clarsimp)
  apply (rule_tac x = b in exI; clarsimp)
  apply (intro exI conjI; assumption)
  done
declare vrepeat_bod.simps[simp]

subsection "Deterministic"

lemma vrepeat_bod_deterministic:
  "\<lbrakk>determ \<xi>;
    vrepeat_bod \<xi> n f g acc obsv ret;
    vrepeat_bod \<xi> n f g acc obsv ret'\<rbrakk>
    \<Longrightarrow> ret = ret'"
  apply (induct n arbitrary: acc)
   apply simp
  apply clarsimp
  apply (drule (2) v_sem_v_sem_all_determ(1)[rotated 1]; simp)
  apply clarsimp
  apply (rename_tac n acc b)
  apply (case_tac b; clarsimp)
  apply (drule (2) v_sem_v_sem_all_determ(1)[rotated 1]; simp)
  done

lemma (in value_sem) vrepeat_deterministic:
  "\<lbrakk>determ \<xi>;
    vrepeat \<Xi> \<xi> \<tau>a \<tau>o x y;
    vrepeat \<Xi> \<xi> \<tau>a \<tau>o x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding vrepeat_def
  apply clarsimp
  apply (drule (3) vrepeat_bod_deterministic)
  done

subsection "Ordering"

lemma vrepeat_bod_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b;
    vrepeat_bod \<xi>a n f g acc obsv ret\<rbrakk>
    \<Longrightarrow> vrepeat_bod \<xi>b n f g acc obsv ret"
  apply (induct n arbitrary: acc)
   apply simp
  apply clarsimp
  apply (rename_tac n acc b)
  apply (case_tac b; clarsimp)
   apply (drule (1) v_sem_v_sem_all_rel_leqD(1)[rotated 1])
   apply (rule_tac x = b in exI; clarsimp)
  apply (drule (1) v_sem_v_sem_all_rel_leqD(1)[rotated 1])
  apply (drule (1) v_sem_v_sem_all_rel_leqD(1)[rotated 1])
  apply (rule_tac x = b in exI; clarsimp)
  apply (elim meta_allE meta_impE, assumption)
  apply (intro exI conjI; assumption)
  done

lemma (in value_sem) vrepeat_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b;
    vrepeat \<Xi> \<xi>a \<tau>a \<tau>o x y\<rbrakk>
    \<Longrightarrow> vrepeat \<Xi> \<xi>b \<tau>a \<tau>o x y"
  unfolding vrepeat_def
  apply clarsimp
  apply (drule (2) vrepeat_bod_rel_leqD)
  done

end