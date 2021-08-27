theory UpdateSemHelper
  imports Cogent.UpdateSemantics
begin

section "Function checking and extraction"

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

section "Evaluation elimination rules"

inductive_cases u_sem_appE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,App x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_funE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Fun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_afunE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,AFun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_primE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Prim x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_consE: "\<xi>',\<gamma> \<turnstile>* (\<sigma>,xs)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_varE: "\<xi>', \<gamma> \<turnstile> (\<sigma>, Var x) \<Down>! (\<sigma>', r)"

inductive_cases u_sem_varE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Var i) \<Down>! v'"
inductive_cases u_sem_litE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Lit l) \<Down>! v'"
inductive_cases u_sem_primE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Prim p as) \<Down>! v'"
inductive_cases u_sem_castE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Cast \<tau> e) \<Down>! v'"
inductive_cases u_sem_funE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Fun f ts) \<Down>! v'"
inductive_cases u_sem_afunE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, AFun f ts) \<Down>! v'"
inductive_cases u_sem_appE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, App x y) \<Down>! v'"
inductive_cases u_sem_conE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Con ts t x) \<Down>! v'"
inductive_cases u_sem_memberE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Member e f) \<Down>! v'"
inductive_cases u_sem_unitE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Unit) \<Down>! v'"
inductive_cases u_sem_tupleE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Tuple x y) \<Down>! v'"
inductive_cases u_sem_esacE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Esac t tag) \<Down>! v'"
inductive_cases u_sem_letE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Let a b) \<Down>! v'"
inductive_cases u_sem_letbangE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, LetBang vs a b) \<Down>! v'"
inductive_cases u_sem_caseE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Case x t m n) \<Down>! v'"
inductive_cases u_sem_ifE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, If x t e) \<Down>! v'"
inductive_cases u_sem_structE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Struct ts xs) \<Down>! v'"
inductive_cases u_sem_takeE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Take x f e) \<Down>! v'"
inductive_cases u_sem_putE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Put x f e) \<Down>! v'"
inductive_cases u_sem_splitE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Split x e) \<Down>! v'"
inductive_cases u_sem_promoteE': "\<xi>' , \<gamma> \<turnstile> (\<sigma>, Promote t' e) \<Down>! v'"
inductive_cases u_sem_all_emptyE': "\<xi>' , \<gamma> \<turnstile>* (\<sigma>, []) \<Down>! v'"
inductive_cases u_sem_all_consE': "\<xi>' , \<gamma> \<turnstile>* (\<sigma>, x # xs) \<Down>! vs'"

lemmas u_sem_u_sem_all_elims = u_sem_varE' u_sem_litE' u_sem_primE' u_sem_castE' u_sem_funE'
  u_sem_afunE' u_sem_conE' u_sem_unitE' u_sem_tupleE' u_sem_esacE' u_sem_splitE' u_sem_promoteE'
  u_sem_letE' u_sem_letbangE' u_sem_ifE' u_sem_structE' u_sem_all_emptyE' u_sem_all_consE'

section "Ordering on abstract function specifications and its properties"

definition \<xi>ule :: "('f, 'a, 'l) uabsfuns \<Rightarrow> ('f, 'a, 'l) uabsfuns \<Rightarrow> bool"
  where
"\<xi>ule f g = ({(n, a, b) | n a b. f n a b} \<subseteq> {(n, a, b) | n a b. g n a b})"

lemma \<xi>uleD:
  "\<lbrakk>\<xi>a f a b; \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b f a b"
  unfolding \<xi>ule_def
  apply (drule_tac c = "(f, a, b)" in subsetD; blast)
  done

lemma u_sem_u_sem_all_\<xi>ule:
  shows "\<lbrakk>\<xi>a, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r); \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)"
  and "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs); \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs)"
proof (induct arbitrary: \<xi>b and \<xi>b rule: u_sem_u_sem_all.inducts)
  case (u_sem_abs_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a \<sigma>''' r)
  then show ?case 
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    apply (rule u_sem_u_sem_all.u_sem_abs_app; simp?)
    unfolding \<xi>ule_def by blast
next
  case (u_sem_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a st)
  then show ?case 
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    by (rule u_sem_u_sem_all.u_sem_app; simp?)
qed (auto intro: u_sem_u_sem_all.intros)

lemma (in update_sem) \<xi>ule_matches:
  "\<lbrakk>\<xi>b matches-u \<Xi>'; \<xi>ule \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>a matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def \<xi>ule_def
  apply clarsimp
  apply (rename_tac f K a b \<sigma> \<sigma>' \<tau>s v v' r w)
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

section "Determinism of evaluation"

definition \<xi>u_determ :: "('f, 'a, 'l) uabsfuns \<Rightarrow> bool"
  where
"\<xi>u_determ \<xi>u = (\<forall>f a b c. \<xi>u f a b \<and>  \<xi>u f a c \<longrightarrow> b = c)"

lemma u_sem_u_sem_all_determ:
  shows "\<lbrakk>\<xi>a, \<gamma> \<turnstile> (\<sigma>, e)  \<Down>! v; \<xi>a, \<gamma> \<turnstile> (\<sigma>, e) \<Down>! v'; \<xi>u_determ \<xi>a\<rbrakk> \<Longrightarrow> v = v'"
  and "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs; \<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs'; \<xi>u_determ \<xi>a\<rbrakk> \<Longrightarrow> vs = vs'"
proof (induct arbitrary: v' and vs' rule: u_sem_u_sem_all.inducts)
  case (u_sem_abs_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a \<sigma>''' r)
  then show ?case
    apply -
    apply (erule u_sem_appE')
     apply (rename_tac s f' ts' s' a' s'' r')
     apply (drule_tac x = "(s, UAFunction f' ts')" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply (subst (asm) prod.inject)
     apply (drule_tac x = "(s', a')" in meta_spec)
     apply clarsimp
    unfolding \<xi>u_determ_def
     apply (erule allE)
     apply (erule allE)
     apply (erule_tac x = "(\<sigma>''', r)" in allE)
     apply (erule_tac x = "(s'', r')" in allE)
     apply (elim impE, intro conjI; simp)
     apply (rename_tac s f' ts' s' a')
    apply (drule_tac x = "(s, UFunction f' ts')" in meta_spec)
    apply (elim meta_impE; assumption?)
    apply (subst (asm) prod.inject; simp)
    done
next
  case (u_sem_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a st)
  then show ?case
    apply -
    apply (erule u_sem_appE')
     apply (rename_tac s f' ts' s' a' s'' r')
     apply (drule_tac x = "(s, UAFunction f' ts')" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply (rule FalseE; clarsimp)
    apply (rename_tac s f' ts' s' a')
    apply (drule_tac x = "(s, UFunction f' ts')" in meta_spec)
    apply (drule_tac x = "(s', a')" in meta_spec)
    apply clarsimp
    done
next
  case (u_sem_member \<xi> \<gamma> \<sigma> e \<sigma>' fs f)
  then show ?case
    apply -
    apply (erule u_sem_memberE'; clarsimp)
     apply (elim meta_allE meta_impE; assumption?)
     apply clarsimp
    apply (elim meta_allE meta_impE; assumption?)
    by clarsimp
next
  case (u_sem_memb_b \<xi> \<gamma> \<sigma> e \<sigma>' p r fs f)
  then show ?case
    apply -
    apply (erule u_sem_memberE'; clarsimp)
     apply (elim meta_allE meta_impE; assumption?)
     apply clarsimp
    apply (elim meta_allE meta_impE; assumption?)
    by clarsimp
next
  case (u_sem_case_m \<xi> \<gamma> \<sigma> x \<sigma>' t v ts m st n)
  then show ?case
    apply -
    apply (erule u_sem_caseE')
     apply (rename_tac \<sigma>''' v tsa)
     apply (drule_tac x = "(\<sigma>''', USum t v tsa)" in meta_spec)
     apply (drule_tac x = v' in meta_spec)
     apply clarsimp
    apply (rename_tac \<sigma>''' t' v rs)
    apply (drule_tac x = "(\<sigma>''', USum t' v rs)" in meta_spec)
    apply (elim meta_impE; assumption?)
    by (rule FalseE; clarsimp)
next
  case (u_sem_case_nm \<xi> \<gamma> \<sigma> x \<sigma>' t' v rs t n st m)
  then show ?case
    apply -
    apply (erule u_sem_caseE')
     apply (rename_tac \<sigma>''' v tsa)
     apply (drule_tac x = "(\<sigma>''', USum t v tsa)" in meta_spec)
     apply (elim meta_impE; assumption?)
    apply (rule FalseE; clarsimp)
    apply (rename_tac \<sigma>''' t'a v rsa)
    apply (drule_tac x = "(\<sigma>''', USum t'a v rsa)" in meta_spec)
    apply (drule_tac x = v' in meta_spec)
    by clarsimp
next
  case (u_sem_take \<xi> \<gamma> \<sigma> x \<sigma>' p r fs f e st)
  then show ?case
    apply -
    apply (erule u_sem_takeE')
     apply (rename_tac \<sigma>''' pa ra fsa)
     apply (drule_tac x = "(\<sigma>''', UPtr pa ra)" in meta_spec)
     apply (drule_tac x = v' in meta_spec)
     apply (elim meta_impE; clarsimp)
    apply (rule FalseE)
    apply (rename_tac \<sigma>''' fsa)
    apply (drule_tac x = "(\<sigma>''', URecord fsa)" in meta_spec)
    by clarsimp
next
  case (u_sem_take_ub \<xi> \<gamma> \<sigma> x \<sigma>' fs f e st)
  then show ?case
    apply -
    apply (erule u_sem_takeE')
     apply (rename_tac \<sigma>''' p r fsa)
     apply (rule FalseE)
     apply (drule_tac x = "(\<sigma>''', UPtr p r)" in meta_spec; clarsimp)
    apply (rename_tac \<sigma>''' fsa)
    apply (drule_tac x = "(\<sigma>''', URecord fsa)" in meta_spec)
    apply (drule_tac x = v' in meta_spec)
    by clarsimp
next
  case (u_sem_put \<xi> \<gamma> \<sigma> x \<sigma>' p r fs e \<sigma>'' e' f)
  then show ?case
    apply -
    apply (erule u_sem_putE')
     apply (rename_tac s pa ra fsa s' e'a)
     apply (drule_tac x = "(s, UPtr pa ra)" in meta_spec)
     apply (drule_tac x = "(s', e'a)" in meta_spec)
     apply clarsimp
    apply (rename_tac s fsa s' e'a)
    by (drule_tac x = "(s, URecord fsa)" in meta_spec; clarsimp)
next
  case (u_sem_put_ub \<xi> \<gamma> \<sigma> x \<sigma>' fs e \<sigma>'' e' f)
  then show ?case
    apply -
    apply (erule u_sem_putE')
     apply (rename_tac s p r fsa s' e'a)
     apply (drule_tac x = "(s, UPtr p r)" in meta_spec; clarsimp)
    apply (rename_tac s fsa s' e'a)
    apply (drule_tac x = "(s, URecord fsa)" in meta_spec)
    by (drule_tac x = "(s', e'a)" in meta_spec; clarsimp)
next
  case (u_sem_prim \<xi> \<gamma> \<sigma> as \<sigma>' as' p)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_var \<xi> \<gamma> \<sigma> i) 
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_lit \<xi> \<gamma> \<sigma> l)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_cast \<xi> \<gamma> \<sigma> e \<sigma>' l \<tau> l')
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_fun \<xi> \<gamma> \<sigma> f ts)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_afun \<xi> \<gamma> \<sigma> f ts)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_con \<xi> \<gamma> \<sigma> x \<sigma>' x' ts t)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_unit \<xi> \<gamma> \<sigma>)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_tuple \<xi> \<gamma> \<sigma> x \<sigma>' x' y \<sigma>'' y')
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_esac \<xi> \<gamma> \<sigma> t \<sigma>' tag v ts')
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_let \<xi> \<gamma> \<sigma> a \<sigma>' a' b st)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_letbang \<xi> \<gamma> \<sigma> a \<sigma>' a' b st vs)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
case (u_sem_if \<xi> \<gamma> \<sigma> x \<sigma>' b t e st)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_struct \<xi> \<gamma> \<sigma> xs \<sigma>' vs ts)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_split \<xi> \<gamma> \<sigma> x \<sigma>' a b e st)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_promote \<xi> \<gamma> \<sigma> e e' t')
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_all_empty \<xi> \<gamma> \<sigma>)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
next
  case (u_sem_all_cons \<xi> \<gamma> \<sigma> x \<sigma>' v xs \<sigma>'' vs)
  then show ?case by (fastforce elim!: u_sem_u_sem_all_elims)
qed

section "Heap footprint properties"

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

end (* of context *)

end