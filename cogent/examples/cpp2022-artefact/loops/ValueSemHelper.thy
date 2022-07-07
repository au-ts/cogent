theory ValueSemHelper
  imports
    DeterministicRelation3
    CogentTypingHelper
    Cogent.ValueSemantics
begin

section "Value typing rules"

inductive_cases (in value_sem) v_t_abstractE   [elim]: "\<Xi> \<turnstile> VAbstract a :v \<tau>"
inductive_cases (in value_sem) v_t_sumE        : "\<Xi> \<turnstile> (VSum a b) :v \<tau>"
inductive_cases (in value_sem) v_t_primE'     : "\<Xi> \<turnstile> VPrim l :v \<tau>"

inductive_cases (in value_sem) v_t_tprimE     : "\<Xi> \<turnstile> v :v TPrim t"
inductive_cases (in value_sem) v_t_tcustomE   : "\<Xi> \<turnstile> v :v TCustomNum n"
inductive_cases (in value_sem) v_t_tfunE      : "\<Xi> \<turnstile> v :v TFun a b"
inductive_cases (in value_sem) v_t_tunitE     : "\<Xi> \<turnstile> v :v TUnit"
inductive_cases (in value_sem) v_t_tconE      : "\<Xi> \<turnstile> v :v TCon n ts s"
inductive_cases (in value_sem) v_t_tsumE      : "\<Xi> \<turnstile> v :v TSum a"
inductive_cases (in value_sem) v_t_tproductE  : "\<Xi> \<turnstile> v :v TProduct a b"
inductive_cases (in value_sem) v_t_trecordE   : "\<Xi> \<turnstile> v :v TRecord ts s"
inductive_cases (in value_sem) v_t_r_temptyE  : "\<Xi>' \<turnstile>* fs :vr []"

lemma (in value_sem) vval_typing_record_alt1:
  "\<Xi>' \<turnstile>* fs :vr ts \<Longrightarrow> 
      length fs = length ts \<and>
      (\<forall>i<length fs. 
        \<exists>x n t s. fs ! i = x \<and> ts ! i = (n, t, s) \<and>
            (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed) \<and>
            (s = Present \<longrightarrow> \<Xi>' \<turnstile> x :v t))"
  apply (induct fs arbitrary: ts)
   apply clarsimp
   apply (erule v_t_r_emptyE; clarsimp)
  apply clarsimp
  apply (case_tac ts; clarsimp)
   apply (erule v_t_r_temptyE; clarsimp)
  apply (rename_tac a fs n t s ts)
  apply (frule vval_typing_record_length)
  apply simp
  apply (drule_tac x = ts in meta_spec)
  apply (case_tac s; clarsimp)
   apply (erule v_t_r_consE; clarsimp)
   apply (rename_tac i t ts n)
   apply (case_tac i; clarsimp)
  apply (erule v_t_r_consE; clarsimp)
  apply (rename_tac i t ts n)
  apply (case_tac i; clarsimp)
  done

lemma (in value_sem) vval_typing_record_alt2:
  "length fs = length ts \<and>
   (\<forall>i<length fs. 
      \<exists>x n t s. fs ! i = x \<and> ts ! i = (n, t, s) \<and>
          (s = Taken \<longrightarrow> 0, [], {} \<turnstile> t wellformed) \<and>
          (s = Present \<longrightarrow> \<Xi>' \<turnstile> x :v t))
    \<Longrightarrow> \<Xi>' \<turnstile>* fs :vr ts"
  apply (induct fs arbitrary: ts; clarsimp)
   apply (rule v_t_r_empty)
  apply (rename_tac a fs ts)
  apply (case_tac ts; clarsimp)
  apply (rename_tac n t s ts)
  apply (drule_tac x = ts in meta_spec; clarsimp)
  apply (erule meta_impE)
  apply clarsimp
   apply (rename_tac i)
   apply (erule_tac x = "Suc i" in allE; clarsimp)
  apply (erule_tac x = 0 in allE; clarsimp)
  apply (case_tac s; clarsimp)
   apply (rule v_t_r_cons2; simp?)
  apply (rule v_t_r_cons1; simp?)
  done

section "Function checking and extraction"

fun is_vvalfun
  where
"is_vvalfun (VFunction _ _ _) = True" |
"is_vvalfun (VAFunction _ _ _) = True" |
"is_vvalfun _  = False"

fun vvalfun_to_expr
  where
"vvalfun_to_expr (VFunction f ts ls) = Fun f ts ls" |
"vvalfun_to_expr (VAFunction f ts ls) = AFun f ts ls" |
"vvalfun_to_expr _ = undefined"

fun no_vfuns
  where
"no_vfuns (VPrim _) = True" |
"no_vfuns VUnit  = True" |
"no_vfuns (VSum a b) = no_vfuns b" |
"no_vfuns (VAbstract _) = True" |
"no_vfuns (VCustomInt v va) = True" |
"no_vfuns (VFunction _ _ _) = False" |
"no_vfuns (VAFunction _ _ _) = False" |
"no_vfuns (VProduct a b) = (if no_vfuns a then no_vfuns b else False)" |
"no_vfuns (VRecord xs) = (find (\<lambda>x. \<not>x) (map no_vfuns xs) = option.None)"

context value_sem begin

lemma no_tfun_imp_no_vfuns:
  "\<lbrakk>no_tvars t; no_tfun t; no_taken t;  \<Xi> \<turnstile> v :v t\<rbrakk> \<Longrightarrow> no_vfuns v"
proof (induct t arbitrary: v)
  case (TRecord x1a x2a)
  then show ?case 
    apply (clarsimp simp: find_None_iff_nth elim!: v_t_trecordE split: if_splits)
    apply (frule vval_typing_record_length)
    apply (rename_tac fs i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: set_conv_nth)
    apply (elim meta_allE meta_impE; assumption?; simp?)
     apply (intro exI conjI; simp?)
    apply (rename_tac fs i x a b)
    apply (case_tac b; clarsimp)
    apply (drule (2) vval_typing_record_nth; simp?)
    done
qed (fastforce simp: find_None_iff 
               elim: v_t_tunitE v_t_tprimE v_t_tcustomE v_t_tconE v_t_sumE v_t_tproductE)+

lemma no_vfuns_monoval:
  "no_vfuns x \<longleftrightarrow> no_vfuns (monoval x)"
  apply (induct x; clarsimp)
  apply (clarsimp simp: find_None_iff)
  done

end (* of context *)

section "Evaluation elimination rules"

inductive_cases v_sem_letE: "\<xi> , \<gamma> \<turnstile> Let a b \<Down> b'"
inductive_cases v_sem_letBangE: "\<xi> , \<gamma> \<turnstile> LetBang vs a b \<Down> b'"
inductive_cases v_sem_litE: "\<xi> , \<gamma> \<turnstile> Lit l \<Down> v"
inductive_cases v_sem_primE: "\<xi> , \<gamma> \<turnstile> Prim p as \<Down> r"
inductive_cases v_sem_memberE: "\<xi> , \<gamma> \<turnstile> Member x f \<Down> r"
inductive_cases v_sem_tupleE: "\<xi> , \<gamma> \<turnstile> Tuple a b \<Down> r"
inductive_cases v_sem_ifE: " \<xi> , \<gamma> \<turnstile> If x t e \<Down> r"
inductive_cases v_sem_conE: "\<xi> , \<gamma> \<turnstile> Con i t x \<Down> r"
inductive_cases v_sem_esacE: "\<xi>, \<gamma> \<turnstile> Esac v  n \<Down> r"
inductive_cases v_sem_caseE:  "\<xi> , \<gamma> \<turnstile> Case x c m n \<Down> r"
inductive_cases v_sem_splitE: "\<xi> , \<gamma> \<turnstile> Split x e \<Down> e'"
inductive_cases v_sem_takeE: "\<xi> , \<gamma> \<turnstile> Take x f e \<Down> e'"
inductive_cases v_sem_putE: "\<xi> , \<gamma> \<turnstile> Put x f e \<Down> e'"
inductive_cases v_sem_castE: "\<xi> , \<gamma> \<turnstile> Cast \<tau> e \<Down> e'"
inductive_cases v_sem_cucastE: "\<xi> , \<gamma> \<turnstile> CustomUCast \<tau>s e \<Down> e'"
inductive_cases v_sem_cdcastE: "\<xi> , \<gamma> \<turnstile> CustomDCast \<tau>s e \<Down> e'"
inductive_cases v_sem_cintE: "\<xi>, \<gamma> \<turnstile> CustomInt n v \<Down> v'"
inductive_cases v_sem_structE: "\<xi> , \<gamma> \<turnstile> Struct ts xs \<Down> e'"
inductive_cases v_sem_AppE: "\<xi> , \<gamma> \<turnstile> App f v \<Down> e'"
inductive_cases v_sem_allE: "\<xi> , \<gamma> \<turnstile>* es \<Down> es'"
inductive_cases v_sem_all_NilE: "\<xi> , \<gamma> \<turnstile>* [] \<Down> es'"
inductive_cases v_sem_all_ConsE: "\<xi> , \<gamma> \<turnstile>* (e#es) \<Down> es'"
inductive_cases v_sem_unitE: "\<xi> , \<gamma> \<turnstile> Unit \<Down> r"
inductive_cases v_sem_promoteE: "\<xi>, \<gamma> \<turnstile> Promote \<tau> e \<Down> r"

lemmas v_sem_elims = v_sem_letE v_sem_letBangE v_sem_litE v_sem_primE v_sem_memberE v_sem_tupleE
  v_sem_ifE v_sem_conE v_sem_esacE v_sem_caseE v_sem_splitE v_sem_takeE v_sem_putE v_sem_castE
  v_sem_structE v_sem_AppE v_sem_allE v_sem_all_NilE v_sem_all_ConsE v_sem_unitE v_sem_promoteE
  v_sem_cdcastE v_sem_cucastE v_sem_cintE


section "Properties on partially ordered abstract function specifications"

lemma v_sem_v_sem_all_rel_leqD:
  assumes "rel_leq \<xi>a \<xi>b"
  shows   "\<xi>a, \<gamma> \<turnstile> e  \<Down> v \<Longrightarrow> \<xi>b, \<gamma> \<turnstile> e \<Down> v"
  and     "\<xi>a , \<gamma> \<turnstile>* es \<Down> vs \<Longrightarrow> \<xi>b , \<gamma> \<turnstile>* es \<Down> vs"
  using assms
proof (induct arbitrary: \<xi>b and \<xi>b rule: v_sem_v_sem_all.inducts)
  case (v_sem_abs_app \<xi> \<gamma> x f ts y a r)
  then show ?case
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    apply (rule v_sem_v_sem_all.v_sem_abs_app; simp?)
    by (drule (2) rel_leqD)
next
  case (v_sem_app \<xi> \<gamma> x e ts y a r)
  then show ?case
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    by (rule v_sem_v_sem_all.v_sem_app; simp?)
next 
  case (v_sem_custom_ucast  \<xi> \<gamma> e n v l')
  then show ?case
    by (fastforce intro!: v_sem_v_sem_all.intros) 
qed (auto intro: v_sem_v_sem_all.intros)

lemma (in value_sem) \<xi>vle_matches:
  "\<lbrakk>rel_leq \<xi>a \<xi>b; \<xi>b matches \<Xi>'\<rbrakk> \<Longrightarrow> \<xi>a matches \<Xi>'"
  unfolding proc_env_matches_def
  apply clarsimp 
  apply (rename_tac f L K C a b ls \<tau>s v v')
  apply (erule_tac x = f in allE; clarsimp)
  apply (erule_tac x = ls in allE)
  apply (erule_tac x = \<tau>s in allE; clarsimp)
  apply (erule_tac x = v in allE; clarsimp)
  apply (erule_tac x = v' in allE; clarsimp)
  apply (drule (1) rel_leqD; simp)
  done

section "Determinism of evaluation"

lemma v_sem_v_sem_all_determ:
  assumes "determ \<xi>a"
  shows   "\<lbrakk>\<xi>a, \<gamma> \<turnstile> e  \<Down> v; \<xi>a, \<gamma> \<turnstile> e \<Down> v'\<rbrakk> \<Longrightarrow> v = v'"
  and     "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* es \<Down> vs; \<xi>a , \<gamma> \<turnstile>* es \<Down> vs'\<rbrakk> \<Longrightarrow> vs = vs'"
  using assms
proof (induct arbitrary: v' and vs' rule: v_sem_v_sem_all.inducts)
  case (v_sem_abs_app \<xi> \<gamma> x f ts y a r)
  then show ?case 
    apply -
    apply (erule v_sem_appE; simp?)    
     apply (rename_tac f' ts' ls' a')
     apply (drule_tac x = "VAFunction f' ts' ls'" in meta_spec; clarsimp)
     apply (drule_tac x = a' in meta_spec; clarsimp)
    apply (drule (2) determD[rotated 1]; simp)
    apply (rename_tac f' ts' ls' a')
    apply (drule_tac x = "VFunction f' ts' ls'" in meta_spec; clarsimp)
    done
next
  case (v_sem_app \<xi> \<gamma> x e ts ls y a r)
  then show ?case
    apply -
    apply (erule v_sem_appE)
     apply (rename_tac f' ts' ls' a')
     apply (drule_tac x = "VAFunction f' ts' ls'" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply blast
    apply (rename_tac f' ts' ls' a')
    apply (drule_tac x = "VFunction f' ts' ls'" in meta_spec)
    apply (elim meta_impE; assumption?)
    apply (drule_tac x = a' in meta_spec; clarsimp)
    done
next
  case (v_sem_case_m \<xi> \<gamma> x t v m m' n)
  then show ?case 
    apply -
    apply (erule v_sem_caseE)
     apply (rename_tac a)
     apply (drule_tac x = "VSum t a" in meta_spec; clarsimp)
    apply (rename_tac a b)
    apply (drule_tac x = "VSum a b" in meta_spec)
    apply (elim meta_impE; assumption?)
    apply (rule FalseE)
    by simp
next
  case (v_sem_case_nm \<xi> \<gamma> x t' v t n n' m)
  then show ?case
    apply -
    apply (erule v_sem_caseE)
     apply (rename_tac a)
     apply (drule_tac x = "VSum t a" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply (rule FalseE)
     apply simp
    by clarsimp
next
  case (v_sem_if \<xi> \<gamma> x b t e r)
  then show ?case 
    apply -
    apply (erule v_sem_ifE)
    apply (rename_tac b')
    by (drule_tac x = "VPrim (LBool b')" in meta_spec; clarsimp)
next
  case (v_sem_take \<xi> \<gamma> x fs f e e')
  then show ?case 
    apply -
    apply (erule v_sem_takeE)
    apply (rename_tac fs')
    by (drule_tac x = "VRecord fs'" in meta_spec; clarsimp)
next
  case (v_sem_put \<xi> \<gamma> x fs e e' f)
  then show ?case 
    apply -
    apply (erule v_sem_putE)
    apply (rename_tac fs' v)
    by (drule_tac x = "VRecord fs'" in meta_spec; clarsimp)
next
  case (v_sem_split \<xi> \<gamma> x a b e e')
  then show ?case 
    apply -
    apply (erule v_sem_splitE)
    apply (rename_tac a' b')
    by (drule_tac x = "VProduct a' b'" in meta_spec; clarsimp)
next
  case (v_sem_prim \<xi> \<gamma> as as' p)
  then show ?case by (fastforce elim!: v_sem_primE)
next
  case (v_sem_struct \<xi> \<gamma> xs vs ts)
  then show ?case by (metis v_sem_structE)
next
  case (v_sem_promote \<xi> \<gamma> e e' t')
  then show ?case by (metis v_sem_promoteE)
next
  case (v_sem_all_empty \<xi> \<gamma>)
  then show ?case by (metis v_sem_all_NilE)
next
  case (v_sem_all_cons \<xi> \<gamma> x v xs vs)
  then show ?case by (metis v_sem_all_ConsE) 
qed (fastforce elim!: v_sem_elims)+

lemma v_sem_v_sem_all_determ_not:
  assumes "determ \<xi>a"
  shows   "\<lbrakk>\<xi>a, \<gamma> \<turnstile> e  \<Down> v; v \<noteq> v'\<rbrakk> \<Longrightarrow> \<not> (\<xi>a, \<gamma> \<turnstile> e \<Down> v')"
  and     "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* es \<Down> vs; vs \<noteq> vs'\<rbrakk> \<Longrightarrow> \<not> (\<xi>a, \<gamma> \<turnstile>* es \<Down> vs')"
  using assms
   apply clarsimp
   apply (erule notE)
   apply (rule v_sem_v_sem_all_determ(1); assumption)
  using assms
  apply clarsimp
  apply (erule notE)
  apply (rule v_sem_v_sem_all_determ(2); assumption)
  done

end