theory CorrespondenceHelper
  imports
    UpdateSemHelper
    ValueSemHelper
    Cogent.Correspondence
begin 

section "Value relation rules"

context correspondence begin

inductive_cases u_v_urecE      [elim] : "\<Xi>', \<sigma> \<turnstile> URecord fs ls \<sim> v : \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_uprimE     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> v : TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_r_uemptyE  [elim] : "\<Xi>', \<sigma> \<turnstile>* [] \<sim> vs :r \<tau>s \<langle>r, w\<rangle>"
inductive_cases u_v_ufunctionE [elim] : "\<Xi>', \<sigma> \<turnstile> UFunction f ts ls \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_uafunE     [elim] : "\<Xi>', \<sigma> \<turnstile> UAFunction f ts ls \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_uptrE      [elim] : "\<Xi>', \<sigma> \<turnstile> UPtr p rp \<sim> v : \<tau> \<langle>r, w\<rangle>"
inductive_cases u_v_uvprimE     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> VPrim l' : \<tau> \<langle>r, w\<rangle>"

inductive_cases u_v_tfunE      : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TFun \<tau> \<rho> \<langle>r, w\<rangle>"
inductive_cases u_v_tprimE     : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TPrim t \<langle>r, w\<rangle>"
inductive_cases u_v_tconE      : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TCon a b c \<langle>r, w\<rangle>"
inductive_cases u_v_tunitE     : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TUnit \<langle>r, w\<rangle>"
inductive_cases u_v_tcnumE     : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TCustomNum n \<langle>r, w\<rangle>"
inductive_cases u_v_tsumE      : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TSum a \<langle>r, w\<rangle>"
inductive_cases u_v_tproductE  : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TProduct a b \<langle>r, w\<rangle>"
inductive_cases u_v_trecordE   : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TRecord t s \<langle>r, w\<rangle>"
inductive_cases u_v_r_temptyE  : "\<Xi>', \<sigma> \<turnstile>* us \<sim> vs :r [] \<langle>r, w\<rangle>"


lemma upd_val_rel_record_lengths:
  "\<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle>r, w\<rangle> \<Longrightarrow> length fs = length fs' \<and> length fs = length \<tau>s"
  apply (induct fs  arbitrary: fs' \<tau>s r w)
   apply clarsimp
   apply (erule u_v_r_uemptyE; simp)
  apply (erule u_v_r_consE'; clarsimp)
   apply (elim meta_allE meta_impE, assumption)
   apply clarsimp
  apply (elim meta_allE meta_impE, assumption)
  apply clarsimp
  done


lemma upd_val_rel_record_alt1:
  "\<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, w\<rangle> \<Longrightarrow> 
      r \<inter> w = {} \<and> length fs = length ts \<and> length fs = length fs' \<and>
      (\<exists>rs ws. r = \<Union>(set rs) \<and> w = \<Union>(set ws) \<and> length rs = length fs \<and> length ws = length fs \<and>
        distinct_sets ws \<and>
        (\<forall>i<length fs. 
          \<exists>x rp x' n t s. fs ! i = (x, rp) \<and> fs' ! i = x' \<and> ts ! i = (n, t, s) \<and> type_repr t = rp \<and>
            (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed \<and> upd.uval_repr x = rp \<and> upd.uval_repr_deep x = rp \<and> rs ! i = {} \<and> ws ! i = {}) \<and>
            (s = Present \<longrightarrow> \<Xi>', \<sigma> \<turnstile> x \<sim> x' : t \<langle>rs ! i, ws ! i\<rangle>)))"
  apply (induct fs arbitrary: fs' ts r w)
   apply clarsimp
   apply (erule u_v_r_uemptyE; clarsimp)
  apply clarsimp
  apply (case_tac ts; clarsimp)
   apply (erule u_v_r_temptyE; clarsimp)
  apply (rename_tac a b fs fs' r w n t s ts)
  apply (clarsimp simp: upd_val_rel_pointers_noalias)
  apply (frule upd_val_rel_record_lengths)
  apply simp
  apply (case_tac fs'; clarsimp)
  apply (rename_tac a' fs')
  apply (drule_tac x = fs' and  y = ts in meta_spec2)
  apply (case_tac s; clarsimp)
   apply (drule_tac x = r and y = w in meta_spec2)
   apply (erule u_v_r_consE; clarsimp)
   apply (rename_tac fs a' fs' ts t x n rs ws)
   apply (rule_tac x = "{} # rs" in exI; clarsimp)
   apply (rule_tac x = "{} # ws" in exI; clarsimp)
   apply (rename_tac i)
   apply (case_tac i; clarsimp)
  apply (erule u_v_r_consE; clarsimp)
  apply (rename_tac fs a' fs' x t r w ts r' w' n)
  apply (drule_tac x = r' and y = w' in meta_spec2; clarsimp)
  apply (rename_tac rs ws)
  apply (rule_tac x = "r # rs" in exI; clarsimp)
  apply (rule_tac x = "w # ws" in exI; clarsimp)
  apply (rename_tac i)
  apply (case_tac i; clarsimp)
  done

lemma upd_val_rel_record_alt2:
  "r \<inter> w = {} \<and> length fs = length ts \<and> length fs = length fs' \<and>
   (\<exists>rs ws. r = \<Union>(set rs) \<and> w = \<Union>(set ws) \<and> 
   length rs = length fs \<and> length ws = length fs \<and>
   distinct_sets ws \<and>
   (\<forall>i<length fs. 
      \<exists>x rp x' n t s. fs ! i = (x, rp) \<and> fs' ! i = x' \<and> ts ! i = (n, t, s) \<and> type_repr t = rp \<and>
          (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed \<and> upd.uval_repr x = rp \<and> upd.uval_repr_deep x = rp \<and> rs ! i = {} \<and> ws ! i = {}) \<and>
          (s = Present \<longrightarrow> \<Xi>', \<sigma> \<turnstile> x \<sim> x' : t \<langle>rs ! i, ws ! i\<rangle>)))
    \<Longrightarrow> \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r ts \<langle>r, w\<rangle>"
  apply (induct fs arbitrary: fs' ts r w; clarsimp)
   apply (rule u_v_r_empty)
  apply (rename_tac a b fs fs' ts rs ws)
  apply (case_tac ts; clarsimp)
  apply (rename_tac n t s ts)
  apply (case_tac fs'; clarsimp)
  apply (rename_tac a' fs')
  apply (drule_tac x = fs' and y = ts in meta_spec2; clarsimp)
  apply (drule_tac x = " \<Union> (set (tl rs))" and y = " \<Union> (set (tl ws))" in meta_spec2)
  apply (erule meta_impE)
   apply (rule conjI)
    apply (erule_tac x = 0 in allE; clarsimp)
    apply (case_tac rs; clarsimp; case_tac ws; clarsimp)
    apply blast 
   apply (rule exI, rule conjI, simp)
   apply (rule exI, rule conjI, simp)
   apply (rule conjI; clarsimp)
   apply (rule conjI)
    apply (erule_tac x = 0 in allE; clarsimp)
    apply (case_tac ws; clarsimp)
    apply clarsimp
    apply (rename_tac i)
    apply (erule_tac x = "Suc i" in allE; clarsimp)
    apply (rule conjI; clarsimp simp: nth_tl)
   apply (frule_tac x = 0 in allE; simp?; clarsimp)
  apply (case_tac s; clarsimp)
   apply (rule u_v_r_cons2; simp?)
   apply (case_tac rs; clarsimp; case_tac ws; clarsimp)
  apply (case_tac rs; clarsimp; case_tac ws; clarsimp)
  apply (rule u_v_r_cons1; simp?)
   apply blast
  apply blast
  done

section "Heap footprint properties"

lemma u_v_discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  u \<sim> v  : \<tau>  \<langle> r , w \<rangle>; 0, K', {} \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; 0, K', {} \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (fastforce dest!:  upd_val_rel_to_uval_typing upd.discardable_or_shareable_not_writable[OF assms])+

lemma u_v_discardable_or_shareable_not_writable':
  shows "\<lbrakk> k = kinding_fn K' \<tau>; D \<in> k \<or> S \<in> k; 
         \<Xi>', \<sigma> \<turnstile>  u  \<sim> v  :  \<tau>  \<langle> r , w \<rangle>; 0, K', {} \<turnstile>  \<tau>  :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> k = (\<Inter>(_,t,b)\<in>set \<tau>s. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K' t));
         D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>* fs \<sim> fs' :r \<tau>s \<langle> r , w \<rangle>; 0, K', {} \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
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

lemma u_v_no_heap_no_pointers:
  "\<lbrakk>no_tvars t; no_theap t; \<Xi>', \<sigma> \<turnstile> u \<sim> v : t \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow> r = {} \<and> w = {}"
  apply (frule upd_val_rel_to_uval_typing(1)[THEN upd.uval_typing_to_wellformed(1)])
  apply (cut_tac K = "[]" and t= t in  no_heap_all_kind; simp?)
  apply (frule_tac k = UNIV in u_v_escapable_no_readers(1); simp?)
  apply (frule  u_v_discardable_or_shareable_not_writable(1)[rotated 1]; simp?)
  apply blast
  done

section "Ordering on abstract function specification properties for abstract function correspondence"

lemma \<xi>ule_matchesuv:
  "\<lbrakk>rel_leq \<xi>ua \<xi>ub; \<xi>ub \<sim> \<xi>v matches-u-v \<Xi>'\<rbrakk> \<Longrightarrow> \<xi>ua \<sim> \<xi>v matches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def
  apply clarsimp
  apply (rename_tac f L K C a b \<sigma> \<sigma>' ls \<tau>s aa a' v v' r w)
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = ls in allE)
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
          \<equiv> (\<forall> f. let (L, K, C, \<tau>i, \<tau>o) = \<Xi>' f
                  in (\<forall> \<sigma> \<sigma>' ls \<tau>s a a' v r w.
                         0, [], {} \<turnstile> ls, \<tau>s :s L, K, C
                      \<longrightarrow> (\<Xi>' , \<sigma> \<turnstile> a \<sim> a' : instantiate ls \<tau>s \<tau>i \<langle>r, w\<rangle>)
                      \<longrightarrow> \<xi>u f (\<sigma>, a) (\<sigma>', v)
                      \<longrightarrow> (\<exists>v'. \<xi>v f a' v' \<and> 
                            (\<exists>r' w'. (\<Xi>' , \<sigma>' \<turnstile> v \<sim> v' : instantiate ls \<tau>s \<tau>o \<langle>r', w'\<rangle>)
                                    \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'))))"

lemma proc_env_u_v_matches_imp_alt:
  "\<xi>u \<sim> \<xi>v matches-u-v \<Xi>' \<Longrightarrow> \<xi>u \<sim> \<xi>v altmatches-u-v \<Xi>'"
  unfolding proc_env_u_v_matches_def proc_env_u_v_matches_alt_def
  apply (clarsimp split: prod.splits)
  apply (elim allE, erule impE, assumption)
  apply (rename_tac f L K C a b \<sigma> \<sigma>' ls \<tau>s aa a' v r w)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = ls in allE)
  apply (erule_tac x = \<tau>s in allE)
  apply ( erule impE, assumption) 
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