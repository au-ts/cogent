theory RepeatUpdate
  imports "build/Generated_AllRefine"
begin

section "helper"

lemma whileLoopE_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoopE_inv c b init I (measure M) \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoopE c b init \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  by (metis assms whileLoopE_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done


lemma typing_mono_app_cogent_fun:
  "\<Xi>', [], [option.Some a] \<turnstile> f : b \<Longrightarrow> \<Xi>', [], [option.Some a] \<turnstile> App (Fun f []) (Var 0) : b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth)
    apply (rule right; simp)
    apply (rule typing_fun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
   apply (rule none)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

section "update" 

overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = False"
end

fun urepeat_bod
  where
"urepeat_bod _ 0 _ _ \<sigma> \<sigma>' _ acc _ _ ret = (\<sigma> = \<sigma>' \<and> acc = ret)" |
"urepeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret =
  (\<exists>b. (\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool b))) \<and>
    (if b then \<sigma> = \<sigma>' \<and> acc = ret
     else (\<exists>\<sigma>'' acc'. (\<xi>' , [URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)]] 
        \<turnstile> (\<sigma>, App g (Var 0)) \<Down>! (\<sigma>'', acc')) \<and>
      urepeat_bod \<xi>' n f g \<sigma>'' \<sigma>' \<tau>a acc' \<tau>o obsv ret)))"


fun is_uvalfun
  where
"is_uvalfun (UFunction _ _) = True" |
"is_uvalfun (UAFunction _ _) = True" |
"is_uvalfun _ = False"

fun uvalfun_to_expr
  where
"uvalfun_to_expr (UFunction f ts) = Fun f ts" |
"uvalfun_to_expr (UAFunction f ts) = AFun f ts" |
"uvalfun_to_expr _ = undefined"


definition repeat
  where
"repeat \<Xi>' \<xi>' \<tau>a \<tau>o x y =
  (\<exists>\<sigma> \<sigma>' n f g acc obsv ret.
    x = (\<sigma>, URecord [(UPrim (LU64 n), RPrim (Num U64)), (f, RFun), (g, RFun),
      (acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)]) \<and>
    y = (\<sigma>', ret) \<and>
    is_uvalfun f \<and>
    is_uvalfun g \<and>
    (\<Xi>, [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (uvalfun_to_expr f) (Var 0)) : TPrim Bool) \<and>
    (\<Xi>, [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]
      \<turnstile> (App (uvalfun_to_expr g) (Var 0)) : \<tau>a) \<and>
    urepeat_bod \<xi>' (unat n) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret)"

overloading \<xi>1 \<equiv> \<xi>_1
begin
definition \<xi>1 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>1 f x y = (if f = ''repeat_0'' then repeat \<Xi> \<xi>_0 abbreviatedType1 (TPrim (Num U64)) x y  else \<xi>_0 f x y)"
end

lemma (in update_sem) frame_empty:
  "frame \<sigma> {} \<sigma>' {} \<Longrightarrow> \<sigma> = \<sigma>'"
  apply (clarsimp simp: frame_def fun_eq_iff)
  done

context Generated begin

lemma urepeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches-u \<Xi>';
    \<Xi>', \<sigma> \<turnstile> acc :u \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> obsv :u \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>r' w'. \<Xi>', \<sigma>' \<turnstile> ret :u \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> frame \<sigma> wa \<sigma>' w'"
  apply (induct arbitrary: ra wa rule: urepeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply (rename_tac \<xi>' f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
   apply clarsimp
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (rename_tac \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
  apply clarsimp
  apply (case_tac b; clarsimp)
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (drule_tac x = False in meta_spec; clarsimp)
  apply (drule_tac x = \<sigma>'' and y = acc' in meta_spec2)
  apply clarsimp
  apply (drule_tac \<gamma> = "[URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)]]" and
      \<sigma>' = \<sigma>'' and v = acc' and r = "ra \<union> ro" and w = wa in preservation_mono(1)[rotated -1]; simp?)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply (rule u_t_struct; simp?) 
   apply (intro u_t_r_cons1[where  r' = ro and w' = "{}", simplified]
      u_t_r_cons1[where  r' = "{}" and w' = "{}", simplified] u_t_r_empty; simp?)
   apply blast
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

lemma urepeat_bod_early_termination:
  "\<lbrakk>urepeat_bod \<xi>' i f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret; i < n;
    \<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]]  \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))\<rbrakk>
    \<Longrightarrow> urepeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret"
  apply (induct arbitrary: i rule: urepeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply clarsimp
  apply clarsimp
  apply (rename_tac i)
  apply (case_tac i; clarsimp)
   apply blast
  apply (case_tac b; clarsimp)
   apply blast
  apply (rename_tac ret nat b \<sigma>'' acc')
  apply (rule_tac x = b in exI)
  apply (rule conjI; clarsimp)
  apply (intro exI conjI; assumption)
  done

declare urepeat_bod.simps[simp del]
lemma urepeat_bod_step:
  "\<lbrakk>\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False));
    \<not>(\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)));
    \<xi>', [URecord [(ret, type_repr \<tau>a), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App g (Var 0)) \<Down>! (\<sigma>'', ret');
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

lemma \<xi>_0_matchesu_\<Xi>:
  "\<xi>_0 matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def \<xi>0_def
  by clarsimp

end (* of context *)

lemma (in update_sem) discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (force simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+

lemma (in update_sem) discardable_or_shareable_not_writable':
shows "\<lbrakk> k = kinding_fn K' \<tau>; D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> k = (\<Inter>(_,t,b)\<in>set \<tau>s. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K' t));
         D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  by (meson discardable_or_shareable_not_writable)+

(*
fun repeat_bod
  where
"repeat_bod _ 0 _ _ \<sigma> \<sigma>' _ acc _ _ ret = (\<sigma> = \<sigma>' \<and> acc = ret)" |
"repeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret =
  (if (\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool True))) \<and>
      \<not>(\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool False)))
    then \<sigma> = \<sigma>' \<and> acc = ret
  else if (\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool False))) \<and>
      \<not>(\<xi>' , [URecord [(acc, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] 
      \<turnstile> (\<sigma>, App f (Var 0)) \<Down>! (\<sigma>, UPrim (LBool True)))
    then (\<exists>\<sigma>'' acc'. (\<xi>' , [URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)]] 
        \<turnstile> (\<sigma>, App g (Var 0)) \<Down>! (\<sigma>'', acc')) \<and>
      repeat_bod \<xi>' n f g \<sigma>'' \<sigma>' \<tau>a acc' \<tau>o obsv ret)
  else False)"

context Generated begin

lemma repeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches-u \<Xi>';
    \<Xi>', \<sigma> \<turnstile> acc :u \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> obsv :u \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    repeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>r' w'. \<Xi>', \<sigma>' \<turnstile> ret :u \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> frame \<sigma> wa \<sigma>' w'"
  apply (induct arbitrary: ra wa rule: repeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply (rename_tac \<xi>' f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
   apply clarsimp
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (rename_tac \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret ra wa)
  apply (clarsimp split: if_splits)
   apply (intro exI conjI, assumption, blast, rule frame_id)
  apply (rename_tac \<sigma>'' acc')
  apply (drule_tac x = \<sigma>'' and y = acc' in meta_spec2)
  apply clarsimp
  apply (drule_tac \<gamma> = "[URecord [(acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)]]" and
      \<sigma>' = \<sigma>'' and v = acc' and r = "ra \<union> ro" and w = wa in preservation_mono(1)[rotated -1]; simp?)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      matches_ptrs_empty[where \<tau>s = "[]", simplified])
   apply (rule u_t_struct; simp?) 
   apply (intro u_t_r_cons1[where  r' = ro and w' = "{}", simplified]
      u_t_r_cons1[where  r' = "{}" and w' = "{}", simplified] u_t_r_empty; simp?)
   apply blast
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


lemma repeat_bod_early_termination:
  "\<lbrakk>repeat_bod \<xi>' i f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret; i < n;
    \<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]]  \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True));
    \<not>(\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]]  \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False)))\<rbrakk>
    \<Longrightarrow> repeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret"
  apply (induct arbitrary: i rule: repeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply clarsimp
  apply clarsimp
  apply (rename_tac i)
  apply (rule conjI; clarsimp)
   apply (case_tac i; clarsimp)
   apply (intro exI conjI; assumption)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac i; clarsimp)
  apply (rule conjI; clarsimp)
   apply (case_tac i; clarsimp split: if_splits)
  apply (case_tac i; clarsimp split: if_splits)
  done

lemma repeat_bod_step:
  "\<lbrakk>\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False));
    \<not>(\<xi>', [URecord [(ret, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App f (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)));
    \<xi>', [URecord [(ret, type_repr \<tau>a), (obsv, type_repr \<tau>o)]] \<turnstile> (\<sigma>', App g (Var 0)) \<Down>! (\<sigma>'', ret');
    repeat_bod \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret\<rbrakk> 
    \<Longrightarrow> repeat_bod \<xi>' (Suc n) f g \<sigma> \<sigma>'' \<tau>a acc \<tau>o obsv ret'"
  apply (induct arbitrary: \<sigma>'' ret' rule: repeat_bod.induct[of _ \<xi>' n f g \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv ret])
   apply clarsimp
  apply (simp del: repeat_bod.simps)
  apply (erule repeat_bod.elims; clarsimp simp del: repeat_bod.simps split: if_splits)
  apply (subst repeat_bod.simps; clarsimp simp del: repeat_bod.simps)
  apply (rename_tac \<sigma>'' ret' \<xi>' n f g \<sigma> \<sigma>m \<tau>a acc \<tau>o obsv ret \<sigma>' acc')
  apply (drule_tac x = \<sigma>' and y = acc' in meta_spec2)
  apply (drule_tac x = \<sigma>'' and y = ret' in meta_spec2)
  apply (clarsimp simp del: repeat_bod.simps)
  apply (intro exI conjI; assumption)
  done
end (* of context *)
*)

end