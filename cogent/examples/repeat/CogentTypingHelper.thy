theory CogentTypingHelper
  imports Cogent.TypeTrackingTyping
begin

section "Typing helpers"

subsection "Cogent functions"

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

lemma typing_mono_fun_cogent_fun:
  "\<Xi>', [], [option.Some a] \<turnstile> f : b \<Longrightarrow> \<Xi>', [], [option.None] \<turnstile> Fun f [] : TFun a b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_fun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
  apply (rule none)
  done

lemma typing_mono_fun_imp_appfun:
  "\<Xi>', [], [option.None] \<turnstile> Fun f [] : TFun a b \<Longrightarrow> \<Xi>', [], [option.Some a] \<turnstile> App (Fun f []) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

subsection "Abstract functions"

lemma typing_mono_app_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = ([], a, b)\<rbrakk> \<Longrightarrow> \<Xi>', [], [option.Some a] \<turnstile> App (AFun f []) (Var 0) : b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth)
    apply (rule right; simp)
   apply (rule typing_afun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
    apply clarsimp
   apply (rule none)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma typing_mono_afun_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = ([], a, b)\<rbrakk> \<Longrightarrow> \<Xi>', [], [option.None] \<turnstile> AFun f [] : TFun a b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_afun[where ts = "[]", OF _ _ _ _]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
   apply clarsimp
  apply (rule none)
  done

lemma typing_mono_afun_imp_appafun:
  "\<Xi>', [], [option.None] \<turnstile> AFun f [] : TFun a b \<Longrightarrow> \<Xi>', [], [option.Some a] \<turnstile> App (AFun f []) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

end