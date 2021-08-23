theory RepeatValue
  imports "build/Generated_AllRefine"
begin

fun vrepeat_bod
  where
"vrepeat_bod _ 0 _ _ acc _ ret = (acc = ret)" |
"vrepeat_bod \<xi>' (Suc n) f g acc obsv ret =
  (if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False))
    then acc = ret
  else if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True))
    then (\<exists>acc'. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App g (Var 0) \<Down> acc') \<and>
      vrepeat_bod \<xi>' n f g acc' obsv ret)
  else False)"

context shallow begin
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
  apply (drule_tac x = acc' in meta_spec; clarsimp)
  apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and v = acc' in preservation(1)[of "[]" "[]", simplified]; simp?)
   apply (clarsimp simp: matches_def)
   apply (rule v_t_record; simp?)
   apply (rule v_t_r_cons1; simp?)+
   apply (rule v_t_r_empty)
  apply (drule meta_mp; simp)
  done


end (* of context *)

end