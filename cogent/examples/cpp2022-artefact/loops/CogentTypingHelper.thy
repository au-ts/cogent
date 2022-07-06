theory CogentTypingHelper
  imports Cogent.TypeTrackingTyping
begin

section "Typing helpers"

subsection "Cogent functions"

lemma typing_mono_app_cogent_fun:
  "\<Xi>', 0, [], {}, [option.Some a] \<turnstile> f : b \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (Fun f [] []) (Var 0) : b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_app[where x = a and y = b and 
                ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth )
    apply (rule right; simp)
   apply (rule typing_fun[where \<delta> = "[]", OF  _  _]; 
        (simp add: Cogent.empty_def weakening_conv_all_nth)?)
     apply (rule none, simp, simp add: subst_wellformed_nothing) 
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma typing_mono_fun_cogent_fun:
  "\<Xi>', 0, [], {}, [option.Some a] \<turnstile> f : b \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.None] \<turnstile> Fun f [] [] : TFun a b"
  apply (frule typing_to_kinding_env(1); simp?)
  apply (rule typing_fun[where \<delta> = "[]"]; 
        (simp add: Cogent.empty_def weakening_conv_all_nth)?)
    apply (rule none, simp, simp add: subst_wellformed_nothing)
  done

lemma typing_mono_fun_imp_appfun:
  "\<Xi>', 0, [], {}, [option.None] \<turnstile> Fun f [] []: TFun a b \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (Fun f [][]) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and 
          ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

subsection "Abstract functions"

lemma typing_mono_app_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = (0, [],{}, a, b)\<rbrakk> \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (AFun f [] []) (Var 0) : b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_app[where x = a and y = b and 
          ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
    apply (clarsimp simp: split_conv_all_nth)
    apply (rule right; simp)
   apply (rule typing_afun[where ts = "[]"]; (simp add: Cogent.empty_def weakening_conv_all_nth)?)
   apply (rule none, simp, simp add: subst_wellformed_nothing)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

lemma typing_mono_afun_cogent_absfun:
  "\<lbrakk>proc_ctx_wellformed \<Xi>'; \<Xi>' f = (0, [], {}, a, b)\<rbrakk> \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.None] \<turnstile> AFun f [] []: TFun a b"
  apply (unfold  proc_ctx_wellformed_def)
  apply (erule_tac x = f in allE; clarsimp)
  apply (rule typing_afun[where ts = "[]"]; 
        (simp add: Cogent.empty_def weakening_conv_all_nth)?)
    apply (rule none, simp, simp add: subst_wellformed_nothing)
  done

lemma typing_mono_afun_imp_appafun:
  "\<Xi>', 0, [], {}, [option.None] \<turnstile> AFun f [] []: TFun a b \<Longrightarrow> 
   \<Xi>', 0, [], {}, [option.Some a] \<turnstile> App (AFun f [] []) (Var 0) : b"
  apply (frule typing_to_wellformed(1))
  apply (rule typing_app[where x = a and y = b and ?\<Gamma>1.0 = "[option.None]" and ?\<Gamma>2.0 = "[option.Some a]"]; simp?)
   apply (clarsimp simp: split_conv_all_nth)
   apply (rule right; simp)
  apply (rule typing_var; simp add: Cogent.empty_def weakening_conv_all_nth)
  apply (rule keep; simp)
  done

subsection "Helper definitions"

fun no_tvars
  where
"no_tvars (TPrim _) = True" |
"no_tvars TUnit = True" |
"no_tvars (TVar _) = False" |
"no_tvars (TVarBang _) = False" |
"no_tvars (TCustomNum v) = True" |
"no_tvars (TProduct a b) = (if no_tvars a then no_tvars b else False)" |
"no_tvars (TFun a b) = (if no_tvars a then no_tvars b else False)" |
"no_tvars (TCon n a b) = (find (\<lambda>x. \<not>x) (map no_tvars a) = option.None)" |
"no_tvars (TSum a) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_tvars b) a) = option.None)"|
"no_tvars (TRecord a s) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b, c). no_tvars b) a) = option.None)"

fun no_tfun
  where
"no_tfun (TPrim _) = True" |
"no_tfun TUnit = True" |
"no_tfun (TCustomNum v) = True" |
"no_tfun (TVar _) = undefined" |
"no_tfun (TVarBang _) = undefined" |
"no_tfun (TProduct a b) = (if no_tfun a then no_tfun b else False)" |
"no_tfun (TFun a b) = False" |
"no_tfun (TCon n a b) = (find (\<lambda>x. \<not>x) (map no_tfun a) = option.None)" |
"no_tfun (TSum a) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_tfun b) a) = option.None)"|
"no_tfun (TRecord a s) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b, c). no_tfun b) a) = option.None)"

fun no_tcon
  where
"no_tcon (TPrim _) = True" |
"no_tcon TUnit = True" |
"no_tcon (TVar _) = undefined" |
"no_tcon (TVarBang _) = undefined" |
"no_tcon (TCustomNum v) = True" |
"no_tcon (TProduct a b) = (if no_tcon a then no_tcon b else False)" |
"no_tcon (TFun a b) = (if no_tcon a then no_tcon b else False)" |
"no_tcon (TCon n a b) = False" |
"no_tcon (TSum a) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_tcon b) a) = option.None)"|
"no_tcon (TRecord a s) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b, c). no_tcon b) a) = option.None)"

fun no_theap
  where
"no_theap (TPrim _) = True" |
"no_theap TUnit = True" |
"no_theap (TCustomNum v) = True" |
"no_theap (TVar _) = undefined" |
"no_theap (TVarBang _) = undefined" |
"no_theap (TProduct a b) = (if no_theap a then no_theap b else False)" |
"no_theap (TFun a b) = True" |
"no_theap (TCon n a b) = (if b = Unboxed then find (\<lambda>x. \<not>x) (map no_theap a) = option.None else False)" |
"no_theap (TSum a) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_theap b) a) = option.None)"|
"no_theap (TRecord a s) = (if s = Unboxed then find (\<lambda>x. \<not>x) (map (\<lambda>(a,b, c). no_theap b) a) = option.None else False)"

fun no_taken
  where
"no_taken (TPrim _) = True" |
"no_taken TUnit = True" |
"no_taken (TCustomNum v) = True" |
"no_taken (TVar _) = undefined" |
"no_taken (TVarBang _) = undefined" |
"no_taken (TProduct a b) = (if no_taken a then no_taken b else False)" |
"no_taken (TFun a b) = (if no_taken a then no_taken b else False)" |
"no_taken (TCon n a b) = (find (\<lambda>x. \<not>x) (map no_taken a) = option.None)" |
"no_taken (TSum a) = (find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_taken b) a) = option.None)"|
"no_taken (TRecord a s) = (if find (\<lambda>(_, _,x). x = Taken) a = option.None then find (\<lambda>x. \<not>x) (map (\<lambda>(a,b,c). no_taken b) a) = option.None else False)"


lemma find_None_iff_nth:
  "(find P xs = option.None) = (\<forall>i < length xs. \<not> P (xs ! i))"
  apply (clarsimp simp: find_None_iff)
  apply (rule iffI; clarsimp simp: set_conv_nth)
  apply (rename_tac i)
  apply (erule_tac x = "xs ! i" in allE; clarsimp)
  done


lemma no_heap_all_kinding_fn:
  "\<lbrakk>no_tvars t; no_theap t\<rbrakk> \<Longrightarrow> kinding_fn K t = UNIV"
  apply (induct t; clarsimp simp: find_None_iff split: if_splits)
    apply (cut_tac k = UNIV in kind_top; blast)
   apply (rename_tac x a aa b)
   apply (erule_tac x = "(a, aa, b)" in ballE; simp)+
   apply (elim meta_allE meta_impE; simp?)
   apply (clarsimp split: variant_state.splits)
  apply (rule conjI; clarsimp?)
   apply (rename_tac x a aa b)
   apply (erule_tac x = "(a, aa, b)" in ballE; simp)+
   apply (elim meta_allE meta_impE; simp?)
   apply (clarsimp split: record_state.splits)
  apply (cut_tac k = UNIV in kind_top; blast)
  done

lemma no_heap_all_kind:
  "\<lbrakk>no_tvars t; no_theap t; 0, K, {} \<turnstile> t wellformed\<rbrakk> \<Longrightarrow> 0, K, {}\<turnstile> t :\<kappa> UNIV"
  apply (rule kindingI; simp add: no_heap_all_kinding_fn)
  done

lemma no_heap_imp_bang:
  "\<lbrakk>no_tvars t; no_theap t\<rbrakk> \<Longrightarrow> bang t = t"
  apply (induct t; clarsimp simp: find_None_iff list_eq_iff_nth_eq split: if_splits)
   apply (rename_tac x i)
   apply (erule_tac x = "x ! i" in ballE; simp?)+
   apply (clarsimp simp: set_conv_nth)
   apply (elim meta_allE meta_impE; simp?)
   apply (intro exI conjI; simp?)
  apply (rename_tac x i)
  apply (erule_tac x = "x ! i" in ballE; simp?)+
  apply (clarsimp simp: set_conv_nth)
  apply (elim meta_allE meta_impE; simp?)
  apply (intro exI conjI; simp?)
  done

end