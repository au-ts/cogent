theory RepeatAssm
  imports
    UpdateSemHelper
    ValueSemHelper
    "build/Generated_AllRefine"
begin

section "C helpers"

lemma whileLoopE_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoopE_inv c b init I (measure M) \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoopE c b init \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  by (metis assms whileLoopE_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done

section "typing helpers"

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


lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  unfolding proc_ctx_wellformed_def \<Xi>_def
            abbreviated_type_defs repeat_0_type_def
            log2stop_type_def log2step_type_def mylog2_type_def
  by (clarsimp simp: assoc_lookup.simps)


section "correspondence helpers"

context correspondence begin

inductive_cases u_v_urecE      [elim] : "\<Xi>', \<sigma> \<turnstile> URecord fs \<sim> v : \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_uprimE     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> v : TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_r_uemptyE  [elim] : "\<Xi>', \<sigma> \<turnstile>* [] \<sim> vs :r \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_ufunctionE [elim] : "\<Xi>', \<sigma> \<turnstile> UFunction f ts \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_uafunE     [elim] : "\<Xi>', \<sigma> \<turnstile> UAFunction f ts \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_tfunE      [elim] : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"

lemma u_v_discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  u \<sim> v  : \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (fastforce dest!:  upd_val_rel_to_uval_typing upd.discardable_or_shareable_not_writable[OF assms])+

lemma u_v_discardable_or_shareable_not_writable':
shows "\<lbrakk> k = kinding_fn K' \<tau>; D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>  u  \<sim> v  :  \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> k = (\<Inter>(_,t,b)\<in>set \<tau>s. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K' t));
         D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  by (meson u_v_discardable_or_shareable_not_writable)+

lemma u_v_bang_not_writable:
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  u \<sim> v  :  bang \<tau>  \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r map (\<lambda>(n, t, b). (n, bang t, b)) \<tau>s \<langle> r , w \<rangle>  \<rbrakk> \<Longrightarrow> w = {}"
   apply (frule u_v_discardable_or_shareable_not_writable'(1)[where K' = "[]", simplified, rotated -2]; simp?)
    apply (rule kindingI[OF upd_val_rel_to_uval_typing(1)[THEN upd.uval_typing_to_wellformed(1)]]; simp?)
   apply (cut_tac K = "[]" and t = \<tau> in bang_kinding_fn; clarsimp)
  apply (frule u_v_discardable_or_shareable_not_writable'(2)[where K' = "[]", simplified, rotated -2]; simp?)
  apply (frule upd_val_rel_to_uval_typing(2)[THEN upd.uval_typing_to_wellformed(2)])
   apply (clarsimp simp: kinding_record_def)
  apply (rename_tac a aa b)
   apply (erule_tac x = "(a, aa, b)" in ballE; clarsimp)
  apply (clarsimp split: record_state.splits)
  apply (rename_tac a aa ab ac)
  apply (cut_tac K = "[]" and t = ac in bang_kinding_fn; clarsimp)
  done

lemma \<xi>ule_matchesuv:
  "\<lbrakk>\<xi>ub \<sim> \<xi>v matches-u-v \<Xi>'; \<xi>ule \<xi>ua \<xi>ub\<rbrakk> \<Longrightarrow> \<xi>ua \<sim> \<xi>v matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def \<xi>ule_def
  apply clarsimp
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = \<tau>s in allE; clarsimp)
  apply (erule_tac x = aa in allE)
  apply (erule_tac x = a' in allE)
  apply (erule_tac x = v in allE)
  apply (erule_tac x = v' in allE)
  apply (erule_tac x = r in allE)
  apply (erule_tac x = w in allE; clarsimp)
  apply (drule_tac c = "(f, (\<sigma>, aa), (\<sigma>', v))" in  subsetD; simp)
  done

definition proc_env_u_v_matches_alt :: "(('f, 'au, 'l) uabsfuns)

                                  \<Rightarrow> (('f, 'av)    vabsfuns)
                                  \<Rightarrow> ('f \<Rightarrow> poly_type)
                                  \<Rightarrow> bool"
           ("_ \<sim> _ altmatches-u-v _" [30,20] 60) where
  "\<xi>u \<sim> \<xi>v altmatches-u-v \<Xi>'
          \<equiv> (\<forall> f. let (K, \<tau>i, \<tau>o) = \<Xi>' f
                  in (\<forall> \<sigma> \<sigma>' \<tau>s a a' v r w.
                         list_all2 (kinding []) \<tau>s K
                      \<longrightarrow> (\<Xi>' , \<sigma> \<turnstile> a \<sim> a' : instantiate \<tau>s \<tau>i \<langle>r, w\<rangle>)
                      \<longrightarrow> \<xi>u f (\<sigma>, a) (\<sigma>', v)
                      \<longrightarrow> (\<exists>v'. \<xi>v f a' v' \<and> 
                            (\<exists>r' w'. (\<Xi>' , \<sigma>' \<turnstile> v \<sim> v' : instantiate \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                                    \<and> r' \<subseteq> r \<and> upd.frame \<sigma> w \<sigma>' w'))))"

lemma 
  "\<xi>u \<sim> \<xi>v matches-u-v \<Xi>' \<Longrightarrow> \<xi>u \<sim> \<xi>v altmatches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def proc_env_u_v_matches_alt_def
  apply (clarsimp split: prod.splits)
  apply (elim allE, erule impE, assumption)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (elim allE, erule impE, assumption)
  apply (erule allE, erule_tac x = a' in allE, elim allE, erule impE, assumption)
  apply (subst (asm) all_comm)
  apply (erule_tac x = r in allE)
  apply (subst (asm) all_comm)
  apply (erule_tac x = w in allE)
  apply clarsimp
  apply (elim allE impE, assumption)
  apply clarsimp
  apply (intro exI conjI; assumption)
  done

end (* of context *)

section "monomorphisation helpers"

context value_sem begin
thm rename_mono_prog_def
end

section "corres helpers"

context update_sem_init begin

lemma corres_\<xi>ule:
  "\<lbrakk>corres srel c m \<xi>a \<gamma> \<Xi>' \<Gamma> \<sigma> s; \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> corres srel c m \<xi>b \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  unfolding corres_def
  apply clarsimp
  apply (erule impE, rule \<xi>ule_matches, assumption, assumption)
  apply (erule impE, intro exI, assumption)
  apply clarsimp
  apply (elim allE, erule impE, assumption)
  apply clarsimp
  apply (drule u_sem_u_sem_all_\<xi>ule; simp?)
  apply (intro exI conjI; assumption)
  done
end (* of context *)

end