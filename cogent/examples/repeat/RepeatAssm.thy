theory RepeatAssm
  imports "build/Generated_AllRefine"
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


section "update semantics helpers"

inductive_cases u_sem_appE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,App x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_funE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Fun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_afunE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,AFun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_primE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Prim x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_consE: "\<xi>',\<gamma> \<turnstile>* (\<sigma>,xs)\<Down>! (\<sigma>',v)"

context update_sem begin

lemma frame_empty:
  "frame \<sigma> {} \<sigma>' {} \<Longrightarrow> \<sigma> = \<sigma>'"
  apply (clarsimp simp: frame_def fun_eq_iff)
  done

lemma discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (force simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+

lemma discardable_or_shareable_not_writable':
shows "\<lbrakk> k = kinding_fn K' \<tau>; D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; K' \<turnstile>  \<tau>  :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> k = (\<Inter>(_,t,b)\<in>set \<tau>s. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K' t));
         D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; K' \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  by (meson discardable_or_shareable_not_writable)+

lemma bang_not_writable:
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  v  :u  bang \<tau>  \<langle> r , w \<rangle> \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs :ur map (\<lambda>(n, t, b). (n, bang t, b)) \<tau>s \<langle> r , w \<rangle>  \<rbrakk> \<Longrightarrow> w = {}"
  apply (frule discardable_or_shareable_not_writable'(1)[where K' = "[]", simplified, rotated -2]; simp?)
    apply (rule kindingI[OF uval_typing_to_wellformed(1)]; simp?)
   apply (cut_tac K = "[]" and t = \<tau> in bang_kinding_fn; clarsimp)
  apply (frule discardable_or_shareable_not_writable'(2)[where K' = "[]", simplified, rotated -2]; simp?)
  apply (frule uval_typing_to_wellformed(2))
   apply (clarsimp simp: kinding_record_def)
  apply (rename_tac a aa b)
   apply (erule_tac x = "(a, aa, b)" in ballE; clarsimp)
  apply (clarsimp split: record_state.splits)
  apply (rename_tac a aa ab ac)
  apply (cut_tac K = "[]" and t = ac in bang_kinding_fn; clarsimp)
  done

definition \<xi>ule :: "('f, 'a, 'l) uabsfuns \<Rightarrow> ('f, 'a, 'l) uabsfuns \<Rightarrow> bool"
  where
"\<xi>ule f g = ({(n, a, b) | n a b. f n a b} \<subseteq> {(n, a, b) | n a b. g n a b})"

lemma \<xi>vle_matches:
  "\<lbrakk>\<xi>b matches-u \<Xi>'; \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>a matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def \<xi>ule_def
  apply clarsimp
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = \<tau>s in allE; clarsimp)
  apply (erule_tac x = v in allE)
  apply (erule_tac x = v' in allE)
  apply (erule_tac x = r in allE)
  apply (erule_tac x = w in allE; clarsimp)
  apply (drule_tac c = "(f, (\<sigma>, v), (\<sigma>', v'))" in  subsetD; simp)
  done

end (* of context *)

section "value semantics helpers"

context value_sem begin

definition \<xi>vle :: "('f, 'a) vabsfuns \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> bool"
  where
"\<xi>vle f g = ({(n, a, b) | n a b. f n a b} \<subseteq> {(n, a, b) | n a b. g n a b})"

lemma \<xi>vle_matches:
  "\<lbrakk>\<xi>b matches \<Xi>'; \<xi>vle \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>a matches \<Xi>'"
  unfolding proc_env_matches_def \<xi>vle_def
  apply clarsimp
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = \<tau>s in allE; clarsimp)
  apply (erule_tac x = v in allE; clarsimp)
  apply (erule_tac x = v' in allE; clarsimp)
  apply (drule_tac c = "(f, v, v')" in  subsetD; simp)
  done

end (* of context *)

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
  "\<lbrakk>\<xi>ub \<sim> \<xi>v matches-u-v \<Xi>'; upd.\<xi>ule \<xi>ua \<xi>ub\<rbrakk> \<Longrightarrow> \<xi>ua \<sim> \<xi>v matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def upd.\<xi>ule_def
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

end (* of context *)

section "monomorphisation helpers"

end