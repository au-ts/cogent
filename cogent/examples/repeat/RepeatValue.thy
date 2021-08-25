theory RepeatValue
  imports RepeatAssm
begin

fun vrepeat_bod
  where
"vrepeat_bod _ 0 _ _ acc _ ret = (acc = ret)" |
"vrepeat_bod \<xi>' (Suc n) f g acc obsv ret =
  (\<exists>b. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool b)) \<and>
    (if b then acc = ret
     else (\<exists>acc'. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App g (Var 0) \<Down> acc') \<and>
      vrepeat_bod \<xi>' n f g acc' obsv ret)))"

fun is_vvalfun
  where
"is_vvalfun (VFunction _ _) = True" |
"is_vvalfun (VAFunction _ _) = True" |
"is_vvalfun _  = False"

fun vvalfun_to_expr
  where
"vvalfun_to_expr (VFunction f ts) = Fun f ts" |
"vvalfun_to_expr (VAFunction f ts) = AFun f ts" |
"vvalfun_to_expr _ = undefined"

context value_sem begin

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
    (\<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (vvalfun_to_expr f) (Var 0)) : TPrim Bool) \<and>
    (\<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (vvalfun_to_expr g) (Var 0)) : \<tau>a) \<and>
    vrepeat_bod \<xi>' (unat n) (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv ret)"

definition \<xi>m0 :: "'b \<Rightarrow> ('b, 'a) vval \<Rightarrow> ('b, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m0 f x y = False"

definition \<xi>m1 :: "funtyp \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> (funtyp, 'a) vval \<Rightarrow> bool "
  where
"\<xi>m1 f x y = (if f = ''repeat_0'' then vrepeat \<Xi> \<xi>m0 abbreviatedType1 (TPrim (Num U64)) x y else \<xi>m0 f x y)"

lemma vrepeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches \<Xi>';
    \<Xi>' \<turnstile> acc :v \<tau>a;
    \<Xi>' \<turnstile> obsv :v \<tau>o;
    vrepeat_bod \<xi>' n f g acc obsv ret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<Xi>' \<turnstile> ret :v \<tau>a"
  apply (induct arbitrary: rule: vrepeat_bod.induct[of _ \<xi>' n f g acc obsv ret])
   apply clarsimp
  apply (clarsimp split: if_splits)
  apply (erule disjE; clarsimp)
  apply (case_tac b; clarsimp)
  apply (drule_tac x = b in meta_spec; clarsimp)
  apply (drule_tac x = acc' in meta_spec; clarsimp)
  apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and v = acc' in preservation(1)[of "[]" "[]", simplified]; simp?)
   apply (clarsimp simp: matches_def)
   apply (rule v_t_record; simp?)
   apply (rule v_t_r_cons1; simp?)+
   apply (rule v_t_r_empty)
  apply (drule meta_mp; simp)
  done

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

lemma \<xi>m0_matches_\<Xi>:
  "\<xi>m0 matches \<Xi>'"
  unfolding proc_env_matches_def \<xi>m0_def
  by clarsimp

lemma \<xi>m1_matches_\<Xi>:
  "\<xi>m1 matches \<Xi>"
  unfolding proc_env_matches_def \<xi>m1_def
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (subst (asm) \<Xi>_def; clarsimp simp: repeat_0_type_def)
   apply (rule vrepeat_preservation[OF proc_ctx_wellformed_\<Xi> \<xi>m0_matches_\<Xi>]; (simp add: abbreviated_type_defs)?)
  apply (clarsimp simp: \<xi>m0_def)
  done

end (* of context *)

(*
fun repeat_bod'
  where
"repeat_bod' _ 0 _ _ acc _ ret = (acc = ret)" |
"repeat_bod' \<xi>' (Suc n) f g acc obsv ret =
  (if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False))
    then acc = ret
  else if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True))
    then (\<exists>acc'. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App g (Var 0) \<Down> acc') \<and>
      repeat_bod' \<xi>' n f g acc' obsv ret)
  else False)"

context shallow begin
lemma repeat_bod'_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches \<Xi>';
    \<Xi>' \<turnstile> acc :v \<tau>a;
    \<Xi>' \<turnstile> obsv :v \<tau>o;
    repeat_bod' \<xi>' n f g acc obsv ret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<Xi>' \<turnstile> ret :v \<tau>a"
  apply (induct arbitrary: rule: repeat_bod'.induct[of _ \<xi>' n f g acc obsv ret])
   apply clarsimp
  apply (clarsimp split: if_splits)
  apply (drule_tac x = acc' in meta_spec; clarsimp)
  apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and v = acc' in preservation(1)[of "[]" "[]", simplified]; simp?)
   apply (clarsimp simp: matches_def)
   apply (rule v_t_record; simp?)
   apply (rule v_t_r_cons1; simp?)+
   apply (rule v_t_r_empty)
  apply (drule meta_mp; simp)
  done
end (* of context *)
*)
end