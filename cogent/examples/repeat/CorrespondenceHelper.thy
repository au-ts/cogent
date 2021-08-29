theory CorrespondenceHelper
  imports
    UpdateSemHelper
    ValueSemHelper
    Cogent.Correspondence
begin 

section "Value relation elimination rules"

context correspondence begin

inductive_cases u_v_urecE      [elim] : "\<Xi>', \<sigma> \<turnstile> URecord fs \<sim> v : \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_uprimE     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> v : TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_r_uemptyE  [elim] : "\<Xi>', \<sigma> \<turnstile>* [] \<sim> vs :r \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_ufunctionE [elim] : "\<Xi>', \<sigma> \<turnstile> UFunction f ts \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_uafunE     [elim] : "\<Xi>', \<sigma> \<turnstile> UAFunction f ts \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_tfunE      [elim] : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"

section "Heap footprint properties"

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

section "Ordering on abstract function specification properties for abstract function correspondence"

lemma \<xi>ule_matchesuv:
  "\<lbrakk>rel_leq \<xi>ua \<xi>ub; \<xi>ub \<sim> \<xi>v matches-u-v \<Xi>'\<rbrakk> \<Longrightarrow> \<xi>ua \<sim> \<xi>v matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def
  apply clarsimp
  apply (rename_tac f K a b \<sigma> \<sigma>' \<tau>s aa a' v v' r w)
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
  apply (drule (1) rel_leqD; simp)
  done

section "Alternate definition of @{term proc_env_u_v_matches}"

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

lemma proc_env_u_v_matches_imp_alt:
  "\<xi>u \<sim> \<xi>v matches-u-v \<Xi>' \<Longrightarrow> \<xi>u \<sim> \<xi>v altmatches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def proc_env_u_v_matches_alt_def
  apply (clarsimp split: prod.splits)
  apply (elim allE, erule impE, assumption)
  apply (rename_tac f x1 a b \<sigma> \<sigma>' \<tau>s aa a' v r w)
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

end