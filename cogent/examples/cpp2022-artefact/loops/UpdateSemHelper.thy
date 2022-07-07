theory UpdateSemHelper
  imports
    DeterministicRelation3
    CogentTypingHelper
    Cogent.UpdateSemantics
    AutoCorres.AutoCorres
begin

section "Value typing elimination rules"

inductive_cases (in update_sem) u_t_tfunE: "\<Xi>, \<sigma> \<turnstile> u :u TFun a b \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tprimE: "\<Xi>, \<sigma> \<turnstile> u :u TPrim t \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tcustomE: "\<Xi>, \<sigma> \<turnstile> u :u TCustomNum n \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tconE: "\<Xi>, \<sigma> \<turnstile> u :u TCon n ts s \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tunitE: "\<Xi>, \<sigma> \<turnstile> u :u TUnit \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tsumE: "\<Xi>, \<sigma> \<turnstile> u :u TSum a \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_trecordE: "\<Xi>, \<sigma> \<turnstile> u :u TRecord ts s \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tproductE: "\<Xi>, \<sigma> \<turnstile> u :u TProduct a b \<langle>r, w\<rangle>"

inductive_cases (in update_sem) u_t_r_temptyE : "\<Xi>', \<sigma> \<turnstile>* fs :ur [] \<langle>r, w\<rangle>"

lemma (in update_sem) uval_typing_record_length:
assumes "\<Xi>, \<sigma>  \<turnstile>* fs :ur \<tau>s \<langle>r, w\<rangle>"
shows   "length fs = length \<tau>s"
using assms proof (induct fs arbitrary: \<tau>s r w)
qed (auto)


lemma (in update_sem) uval_typing_record_alt1:
  "\<Xi>', \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle> \<Longrightarrow> 
      r \<inter> w = {} \<and> length fs = length ts \<and>
      (\<exists>rs ws. r = \<Union>(set rs) \<and> w = \<Union>(set ws) \<and> 
        length rs = length fs \<and> length ws = length fs \<and>
        distinct_sets ws \<and>
        (\<forall>i<length fs. 
          \<exists>x rp n t s. fs ! i = (x, rp) \<and> ts ! i = (n, t, s) \<and> type_repr t = rp \<and>
            (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed \<and> uval_repr x = rp \<and> uval_repr_deep x = rp \<and> rs ! i = {} \<and> ws ! i = {}) \<and>
            (s = Present \<longrightarrow> \<Xi>', \<sigma> \<turnstile> x :u t \<langle>rs ! i, ws ! i\<rangle>)))"
  apply (induct fs arbitrary: ts r w)
   apply clarsimp
   apply (erule u_t_r_emptyE; clarsimp)
  apply clarsimp
  apply (case_tac ts; clarsimp)
   apply (erule u_t_r_temptyE; clarsimp)
  apply (rename_tac a b fs r w n t s ts)
  apply (clarsimp simp: uval_typing_pointers_noalias)
  apply (frule uval_typing_record_length)
  apply simp
  apply (drule_tac x = ts in meta_spec)
  apply (case_tac s; clarsimp)
   apply (drule_tac x = r and y = w in meta_spec2)
   apply (erule u_t_r_consE; clarsimp)
   apply (rename_tac fs ts t x n rs ws)
   apply (rule_tac x = "{} # rs" in exI; clarsimp)
   apply (rule_tac x = "{} # ws" in exI; clarsimp)
   apply (rename_tac i)
   apply (case_tac i; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (rename_tac fs x t r w ts r' w' n)
  apply (drule_tac x = r' and y = w' in meta_spec2; clarsimp)
  apply (rename_tac rs ws)
  apply (rule_tac x = "r # rs" in exI; clarsimp)
  apply (rule_tac x = "w # ws" in exI; clarsimp)
  apply (rename_tac i)
  apply (case_tac i; clarsimp)
  done

lemma (in update_sem) uval_typing_record_alt2:
  "r \<inter> w = {} \<and> length fs = length ts \<and>
   (\<exists>rs ws. r = \<Union>(set rs) \<and> w = \<Union>(set ws) \<and> length rs = length fs \<and> length ws = length fs \<and>
   distinct_sets ws \<and>
   (\<forall>i<length fs. 
      \<exists>x rp n t s. fs ! i = (x, rp) \<and> ts ! i = (n, t, s) \<and> type_repr t = rp \<and>
          (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed \<and> uval_repr x = rp \<and> uval_repr_deep x = rp \<and> rs ! i = {} \<and> ws ! i = {}) \<and>
          (s = Present \<longrightarrow> \<Xi>', \<sigma> \<turnstile> x :u t \<langle>rs ! i, ws ! i\<rangle>)))
    \<Longrightarrow> \<Xi>', \<sigma> \<turnstile>* fs :ur ts \<langle>r, w\<rangle>"
  apply (induct fs arbitrary: ts r w; clarsimp)
   apply (rule u_t_r_empty)
  apply (rename_tac a b fs ts rs ws)
  apply (case_tac ts; clarsimp)
  apply (rename_tac n t s ts)
  apply (drule_tac x = ts in meta_spec; clarsimp)
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
   apply (rule u_t_r_cons2; simp?)
   apply (case_tac rs; clarsimp; case_tac ws; clarsimp)
  apply (case_tac rs; clarsimp; case_tac ws; clarsimp)
  apply (rule u_t_r_cons1; simp?)
   apply blast
  apply blast
  done

section "Function checking and extraction"

fun is_uvalfun
  where
"is_uvalfun (UFunction _ _ _) = True" |
"is_uvalfun (UAFunction _ _ _) = True" |
"is_uvalfun _ = False"

fun uvalfun_to_expr
  where
"uvalfun_to_expr (UFunction f ts ls) = Fun f ts ls" |
"uvalfun_to_expr (UAFunction f ts ls) = AFun f ts ls" |
"uvalfun_to_expr _ = undefined"

lemma (in update_sem) uval_typing_uvalfun:
  "\<Xi>, \<sigma> \<turnstile> u :u TFun a b \<langle>r, w\<rangle> \<Longrightarrow> is_uvalfun u"
  apply (erule u_t_tfunE; clarsimp)
  done

fun no_rfun
  where
"no_rfun (RPrim _) = True" |
"no_rfun RUnit = True" |
"no_rfun RFun = False" |
"no_rfun (RCustomNum n) = True" |
"no_rfun (RCon n rs) = (find (\<lambda>x. \<not>x) (map no_rfun rs) = option.None)" |
"no_rfun (RProduct a b) = (if no_rfun a then no_rfun b else False)" |
"no_rfun (RSum a) = (find (\<lambda>x. \<not>x) (map (no_rfun \<circ> prod.snd) a) = option.None)" |
"no_rfun (RRecord a _) = (find (\<lambda>x. \<not>x) (map no_rfun a) = option.None)" |
"no_rfun (RPtr a) = no_rfun a" 



lemma no_tfun_no_rfun:
  "no_tvars t \<Longrightarrow> no_tfun t \<longleftrightarrow> no_rfun (type_repr t)"
  apply (induct t; clarsimp simp: find_None_iff_nth list_eq_iff_nth_eq split: if_splits; simp?)
    apply (rename_tac n ts s)
    apply (case_tac s; clarsimp simp: find_None_iff_nth)
   apply (rule iffI; clarsimp)
    apply (rename_tac x i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: set_conv_nth)
    apply (elim meta_allE meta_impE; simp?)
     apply (intro exI conjI; simp?)
    apply simp
   apply (rename_tac x i a aa b)
   apply (erule_tac x = i in allE; clarsimp)+
   apply (clarsimp simp: set_conv_nth)
   apply (elim meta_allE meta_impE; simp?)
    apply (intro exI conjI; simp?)
   apply simp
  apply (rename_tac fs s)
  apply (case_tac s; clarsimp simp: find_None_iff_nth)
   apply (rule iffI; clarsimp)
    apply (rename_tac i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: set_conv_nth)
    apply (elim meta_allE meta_impE; simp?)
     apply (intro exI conjI; simp?)
    apply simp
   apply (rename_tac x i a aa b)
   apply (erule_tac x = i in allE; clarsimp)+
   apply (clarsimp simp: set_conv_nth)
   apply (elim meta_allE meta_impE; simp?)
    apply (intro exI conjI; simp?)
   apply simp
  apply (rule iffI; clarsimp)
   apply (rename_tac i)
   apply (erule_tac x = i in allE; clarsimp)+
   apply (clarsimp simp: set_conv_nth)
   apply (elim meta_allE meta_impE; simp?)
    apply (intro exI conjI; simp?)
   apply simp
  apply (rename_tac x i a aa b)
  apply (erule_tac x = i in allE; clarsimp)+
  apply (clarsimp simp: set_conv_nth)
  apply (elim meta_allE meta_impE; simp?)
   apply (intro exI conjI; simp?)
  apply simp
  done

fun no_ufun
  where
"no_ufun (UPrim _) = True" |
"no_ufun UUnit  = True" |
"no_ufun (USum a b r) = no_ufun b" |
"no_ufun (UAbstract _) = True" |
"no_ufun (UCustomInt v va) = True" |
"no_ufun (UFunction _ _ _) = False" |
"no_ufun (UAFunction _ _ _) = False" |
"no_ufun (UProduct a b) = (if no_ufun a then no_ufun b else False)" |
"no_ufun (URecord xs _) = (find (\<lambda>x. \<not>x) (map (no_ufun \<circ> prod.fst) xs) = option.None)" |
"no_ufun (UPtr _ r) = no_rfun r"


lemma (in update_sem) no_tfun_imp_no_vfuns:
  "\<lbrakk>no_tvars t; no_tfun t; no_taken t; no_tcon t;  \<Xi>,  \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow> no_ufun v"
proof (induct t arbitrary: \<sigma> v r w)
  case (TRecord x1a x2a)
  then show ?case 
    apply (clarsimp simp: find_None_iff_nth  split: if_splits)
    apply (erule u_t_trecordE; clarsimp simp: find_None_iff_nth)
      apply (frule uval_typing_record_length)
      apply (rename_tac fs i)
      apply (erule_tac x = i in allE; clarsimp)+
      apply (clarsimp simp: set_conv_nth)
      apply (rename_tac fs i x a b)
      apply (case_tac b; clarsimp)
      apply (drule (2) uval_typing_record_nth'; clarsimp)
      apply (elim meta_allE meta_impE; assumption?; simp?)
      apply (intro exI conjI; simp?)
     apply (rename_tac fs r l ptrl i)
     apply (erule_tac x = i in allE; clarsimp)+
     apply (clarsimp simp: no_tfun_no_rfun)
    apply (rename_tac fs w l ptrl i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: no_tfun_no_rfun)
    done
qed (fastforce simp: find_None_iff 
               elim: u_t_tunitE u_t_tprimE u_t_tcustomE u_t_tconE u_t_tproductE)+

section "Evaluation elimination rules"

inductive_cases u_sem_appE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,App x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_funE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Fun x y ls)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_afunE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,AFun x y ls)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_primE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Prim x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_consE: "\<xi>',\<gamma> \<turnstile>* (\<sigma>,xs)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_varE: "\<xi>', \<gamma> \<turnstile> (\<sigma>, Var x) \<Down>! (\<sigma>', r)"

inductive_cases u_sem_varE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Var i) \<Down>! v'"
inductive_cases u_sem_litE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Lit l) \<Down>! v'"
inductive_cases u_sem_primE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Prim p as) \<Down>! v'"
inductive_cases u_sem_castE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Cast \<tau> e) \<Down>! v'"
inductive_cases u_sem_cucastE': "\<xi> , \<gamma> \<turnstile> (\<sigma>, CustomUCast \<tau> e) \<Down>! p'"
inductive_cases u_sem_cdcastE': "\<xi> , \<gamma> \<turnstile> (\<sigma>, CustomDCast \<tau> e) \<Down>! p'"
inductive_cases u_sem_cintE': "\<xi>, \<gamma> \<turnstile> (\<sigma>, CustomInt n v) \<Down>! v'"
inductive_cases u_sem_funE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, Fun f ts ls) \<Down>! v'"
inductive_cases u_sem_afunE': "\<xi>', \<gamma> \<turnstile> (\<sigma>, AFun f ts ls) \<Down>! v'"
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
  u_sem_cucastE' u_sem_cdcastE' u_sem_cintE'

section "Properties of partially ordered abstract function specifications"

lemma u_sem_u_sem_all_rel_leqD:
  assumes "rel_leq \<xi>a \<xi>b"
  shows   "\<xi>a, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r) \<Longrightarrow> \<xi>b, \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)"
  and     "\<xi>a , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs) \<Longrightarrow> \<xi>b , \<gamma> \<turnstile>* (\<sigma>, xs) \<Down>! (\<sigma>', vs)"
  using assms
proof (induct arbitrary: \<xi>b and \<xi>b rule: u_sem_u_sem_all.inducts)
  case (u_sem_abs_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a \<sigma>''' r)
  then show ?case 
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    apply (rule u_sem_u_sem_all.u_sem_abs_app; simp?)
    by (drule (2) rel_leqD)
next
  case (u_sem_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a st)
  then show ?case 
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    by (rule u_sem_u_sem_all.u_sem_app; simp?)
next
  case (u_sem_custom_ucast \<xi> \<gamma> \<sigma> e \<sigma>' n v l')
  then show ?case
    by (fastforce intro!: u_sem_u_sem_all.intros)
qed (auto intro: u_sem_u_sem_all.intros)

lemma (in update_sem) rel_leq_matchesuD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b; \<xi>b matches-u \<Xi>'\<rbrakk> \<Longrightarrow> \<xi>a matches-u \<Xi>'"
  unfolding proc_env_matches_ptrs_def
  apply clarsimp
  apply (rename_tac f L K C a b \<sigma> \<sigma>' ls \<tau>s v v' r w)
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = \<sigma> in allE)
  apply (erule_tac x = \<sigma>' in allE)
  apply (erule_tac x = ls in allE)
  apply (erule_tac x = \<tau>s in allE; clarsimp)
  apply (erule_tac x = v in allE)
  apply (erule_tac x = v' in allE)
  apply (erule_tac x = r in allE)
  apply (erule_tac x = w in allE; clarsimp)
  apply (drule (1) rel_leqD; simp)
  done

section "Determinism of evaluation"

lemma u_sem_u_sem_all_determ:
  assumes "determ \<xi>a"
  shows   "\<lbrakk>\<xi>a, \<gamma> \<turnstile> (\<sigma>, e)  \<Down>! v; \<xi>a, \<gamma> \<turnstile> (\<sigma>, e) \<Down>! v'\<rbrakk> \<Longrightarrow> v = v'"
  and     "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs; \<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs'\<rbrakk> \<Longrightarrow> vs = vs'"
  using assms
proof (induct arbitrary: v' and vs' rule: u_sem_u_sem_all.inducts)
  case (u_sem_abs_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a \<sigma>''' r)
  then show ?case
    apply -
    apply (erule u_sem_appE')
     apply (rename_tac s f' ts' ls' s' a' s'' r')
     apply (drule_tac x = "(s, UAFunction f' ts' ls')" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply (subst (asm) prod.inject)
     apply (drule_tac x = "(s', a')" in meta_spec)
     apply clarsimp
    apply (drule (2) determD[rotated 1]; simp)
    apply (rename_tac s f' ts' ls' s' a')
    apply (drule_tac x = "(s, UFunction f' ts' ls')" in meta_spec)
    apply (elim meta_impE; assumption?)
    apply (subst (asm) prod.inject; simp)
    done
next
  case (u_sem_app \<xi> \<gamma> \<sigma> x \<sigma>' f ts y \<sigma>'' a st)
  then show ?case
    apply -
    apply (erule u_sem_appE')
     apply (rename_tac s f' ts' ls' s' a' s'' r')
     apply (drule_tac x = "(s, UAFunction f' ts' ls')" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply (rule FalseE; clarsimp)
    apply (rename_tac s f' ts' ls' s' a')
    apply (drule_tac x = "(s, UFunction f' ts' ls')" in meta_spec)
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
     apply (rename_tac \<sigma>''' pa ra fsa ptrl)
     apply (drule_tac x = "(\<sigma>''', UPtr pa ra)" in meta_spec)
     apply (drule_tac x = v' in meta_spec)
     apply (elim meta_impE; clarsimp)
    apply (rule FalseE)
    apply (rename_tac \<sigma>''' fsa)
    apply (drule_tac x = "(\<sigma>''', URecord fsa None)" in meta_spec)
    by clarsimp
next
  case (u_sem_take_ub \<xi> \<gamma> \<sigma> x \<sigma>' fs f e st)
  then show ?case
    apply -
    apply (erule u_sem_takeE')
     apply (rename_tac \<sigma>''' p r fsa ptrl)
     apply (rule FalseE)
     apply (drule_tac x = "(\<sigma>''', UPtr p r)" in meta_spec; clarsimp)
    apply (rename_tac \<sigma>''' fsa)
    apply (drule_tac x = "(\<sigma>''', URecord fsa None)" in meta_spec)
    apply (drule_tac x = v' in meta_spec)
    by clarsimp
next
  case (u_sem_put \<xi> \<gamma> \<sigma> x \<sigma>' p r fs e \<sigma>'' e' f)
  then show ?case
    apply -
    apply (erule u_sem_putE')
     apply (rename_tac s pa ra fsa ptrl s' e'a)
     apply (drule_tac x = "(s, UPtr pa ra)" in meta_spec)
     apply (drule_tac x = "(s', e'a)" in meta_spec)
     apply clarsimp
    apply (rename_tac s fsa ptrl s' e'a)
    apply (drule_tac x = "(s, URecord fsa None)" in meta_spec)  
    by (fastforce dest!: u_sem_put.hyps(2))
next
  case (u_sem_put_ub \<xi> \<gamma> \<sigma> x \<sigma>' fs e \<sigma>'' e' f)
  then show ?case
    apply -
    apply (erule u_sem_putE')
     apply (rename_tac s p r fsa ptrl s' e'a)
     apply (drule_tac x = "(s, UPtr p r)" in meta_spec; clarsimp)
    apply (rename_tac s fsa ptrl s' e'a)
    apply (drule_tac x = "(s, URecord fsa None)" in meta_spec)
    apply (drule_tac x = "(s', e'a)" in meta_spec; clarsimp)
    by (fastforce dest!: u_sem_put_ub.hyps(2))
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

qed (fastforce elim!: u_sem_u_sem_all_elims)+

lemma u_sem_u_sem_all_determ_not:
  assumes "determ \<xi>a"
  shows   "\<lbrakk>\<xi>a, \<gamma> \<turnstile> (\<sigma>, e) \<Down>! v; v \<noteq> v'\<rbrakk> \<Longrightarrow> \<not> (\<xi>a, \<gamma> \<turnstile> (\<sigma>, e) \<Down>! v')"
  and     "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs; vs \<noteq> vs'\<rbrakk> \<Longrightarrow> \<not> (\<xi>a , \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! vs')"
  using assms
   apply clarsimp
   apply (erule notE)
   apply (rule u_sem_u_sem_all_determ(1); assumption)
  using assms
  apply clarsimp
  apply (erule notE)
  apply (rule u_sem_u_sem_all_determ(2); assumption)
  done

section "Heap footprint properties"

context update_sem begin

lemma frame_empty:
  "frame \<sigma> {} \<sigma>' {} \<Longrightarrow> \<sigma> = \<sigma>'"
  apply (clarsimp simp: frame_def fun_eq_iff)
  done

lemma frame_expand:
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (insert p w) \<sigma>' (insert p w')"
  "\<lbrakk>frame \<sigma> w \<sigma>' w'; \<forall>p\<in>s. \<sigma> p \<noteq> option.None\<rbrakk> \<Longrightarrow> frame \<sigma> (s \<union> w) \<sigma>' (s \<union> w')"
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: frame_def)
  apply (rule conjI; clarsimp)
  done

lemma frame_single_update_expand:
  "l \<in> w \<Longrightarrow> frame \<sigma> w (\<sigma>(l \<mapsto> v)) w"
  by (clarsimp simp: frame_def)

lemma discardable_or_shareable_not_writable:
assumes "D \<in> k \<or> S \<in> k"
shows "\<lbrakk> \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; 0, K', {} \<turnstile>  \<tau>  :\<kappa>  k \<rbrakk> \<Longrightarrow> w = {}"
and   "\<lbrakk> \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; 0, K', {} \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
  using assms
  by (induct rule: uval_typing_uval_typing_record.inducts)
    (force simp add: kinding_simps kinding_record_simps kinding_variant_set
      dest: abs_typing_readonly[where s = Unboxed,simplified])+

lemma discardable_or_shareable_not_writable':
  shows "\<lbrakk> k = kinding_fn K' \<tau>; D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>  v  :u  \<tau>  \<langle> r , w \<rangle>; 0, K', {} \<turnstile>  \<tau>  :\<kappa> k \<rbrakk> \<Longrightarrow> w = {}"
  and   "\<lbrakk> k = (\<Inter>(_,t,b)\<in>set \<tau>s. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K' t));
         D \<in> k \<or> S \<in> k; \<Xi>', \<sigma> \<turnstile>* fs :ur \<tau>s \<langle> r , w \<rangle>; 0, K', {} \<turnstile>* \<tau>s :\<kappa>r k \<rbrakk> \<Longrightarrow> w = {}"
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

lemma no_heap_no_pointers:
  "\<lbrakk>no_tvars t; no_theap t; \<Xi>', \<sigma> \<turnstile> v :u t \<langle>r, w\<rangle>\<rbrakk> \<Longrightarrow> r = {} \<and> w = {}"
  apply (frule uval_typing_to_wellformed)
  apply (cut_tac K = "[]" and t= t in  no_heap_all_kind; simp?)
  apply (frule_tac k = UNIV in escapable_no_readers(1); simp?)
  apply (frule  discardable_or_shareable_not_writable(1)[rotated 1]; simp?)
  apply blast
  done

end (* of context *)

end