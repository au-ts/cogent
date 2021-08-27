theory ValueSemHelper
  imports "Cogent.ValueSemantics"
begin
section "value semantics helpers"

definition \<xi>vle :: "('f, 'a) vabsfuns \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> bool"
  where
"\<xi>vle f g = ({(n, a, b) | n a b. f n a b} \<subseteq> {(n, a, b) | n a b. g n a b})"

lemma \<xi>vleD:
  "\<lbrakk>\<xi>a f a b; \<xi>vle \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b f a b"
  unfolding \<xi>vle_def
  apply (drule_tac c = "(f, a, b)" in subsetD; simp)
  done

lemma v_sem_v_sem_all_\<xi>vle:
  shows "\<lbrakk>\<xi>a, \<gamma> \<turnstile> e  \<Down> v; \<xi>vle \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b, \<gamma> \<turnstile> e \<Down> v"
  and "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* es \<Down> vs; \<xi>vle \<xi>a \<xi>b\<rbrakk> \<Longrightarrow> \<xi>b , \<gamma> \<turnstile>* es \<Down> vs"
proof (induct arbitrary: \<xi>b and \<xi>b rule: v_sem_v_sem_all.inducts)
  case (v_sem_abs_app \<xi> \<gamma> x f ts y a r)
  then show ?case
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    apply (rule v_sem_v_sem_all.v_sem_abs_app; simp?)
    unfolding \<xi>vle_def by blast
next
  case (v_sem_app \<xi> \<gamma> x e ts y a r)
  then show ?case
    apply -
    apply (drule_tac x = \<xi>b in meta_spec; simp?)+
    by (rule v_sem_v_sem_all.v_sem_app; simp?)
qed (auto intro: v_sem_v_sem_all.intros)

definition \<xi>v_determ :: "('f, 'a) vabsfuns \<Rightarrow> bool"
  where
"\<xi>v_determ \<xi>v = (\<forall>f a b c. \<xi>v f a b \<and>  \<xi>v f a c \<longrightarrow> b = c)"

lemma
  "\<not> \<xi>v_determ (\<lambda>f a b. (b = VPrim (LBool True)) \<or> (b = VPrim (LBool False)))"
  unfolding \<xi>v_determ_def
  apply clarsimp
  apply (rule_tac x = "VPrim (LBool True)" in exI; clarsimp)
  apply (rule_tac x = "VPrim (LBool False)" in exI; clarsimp)
  done

lemma
  "\<xi>v_determ (\<lambda>f a b. b = VUnit)"
  unfolding \<xi>v_determ_def
  by clarsimp

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
inductive_cases v_sem_structE: "\<xi> , \<gamma> \<turnstile> Struct ts xs \<Down> e'"
inductive_cases v_sem_AppE: "\<xi> , \<gamma> \<turnstile> App f v \<Down> e'"
inductive_cases v_sem_allE: "\<xi> , \<gamma> \<turnstile>* es \<Down> es'"
inductive_cases v_sem_all_NilE: "\<xi> , \<gamma> \<turnstile>* [] \<Down> es'"
inductive_cases v_sem_all_ConsE: "\<xi> , \<gamma> \<turnstile>* (e#es) \<Down> es'"
inductive_cases v_sem_unitE: "\<xi> , \<gamma> \<turnstile> Unit \<Down> r"
inductive_cases v_sem_promoteE: "\<xi>, \<gamma> \<turnstile> Promote \<tau> e \<Down> r"

lemmas v_sem_elims =
  v_sem_letE
  v_sem_letBangE
  v_sem_litE
  v_sem_primE
  v_sem_memberE
  v_sem_tupleE
  v_sem_ifE
  v_sem_conE
  v_sem_esacE
  v_sem_caseE
  v_sem_splitE
  v_sem_takeE
  v_sem_putE
  v_sem_castE
  v_sem_structE
  v_sem_AppE
  v_sem_allE
  v_sem_all_NilE
  v_sem_all_ConsE
  v_sem_unitE
  v_sem_promoteE

lemma v_sem_v_sem_all_determ:
  shows "\<lbrakk>\<xi>a, \<gamma> \<turnstile> e  \<Down> v; \<xi>a, \<gamma> \<turnstile> e \<Down> v'; \<xi>v_determ \<xi>a\<rbrakk> \<Longrightarrow> v = v'"
  and "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* es \<Down> vs; \<xi>a , \<gamma> \<turnstile>* es \<Down> vs'; \<xi>v_determ \<xi>a\<rbrakk> \<Longrightarrow> vs = vs'"
proof (induct arbitrary: v' and vs' rule: v_sem_v_sem_all.inducts)
  case (v_sem_abs_app \<xi> \<gamma> x f ts y a r)
  then show ?case 
    apply -
    apply (erule v_sem_appE; simp?)    
     apply (rename_tac f' ts' a')
     apply (drule_tac x = "VAFunction f' ts'" in meta_spec; clarsimp)
     apply (drule_tac x = a' in meta_spec; clarsimp)
    unfolding \<xi>v_determ_def
     apply (erule_tac x = f in allE)
     apply (erule_tac x = a in allE)
     apply (erule_tac x = r in allE)
     apply (erule_tac x = v' in allE)
     apply (erule impE; simp)
     apply (rename_tac f' ts' a')
     apply (drule_tac x = "VFunction f' ts'" in meta_spec; clarsimp)
    done
next
  case (v_sem_app \<xi> \<gamma> x e ts y a r)
  then show ?case
    apply -
    apply (erule v_sem_appE)
     apply (rename_tac f' ts' a')
     apply (drule_tac x = "VAFunction f' ts'" in meta_spec)
     apply (elim meta_impE; assumption?)
     apply blast
    apply (rename_tac f' ts' a')
    apply (drule_tac x = "VFunction f' ts'" in meta_spec)
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
  "\<lbrakk>\<xi>a, \<gamma> \<turnstile> e  \<Down> v; v \<noteq> v'; \<xi>v_determ \<xi>a\<rbrakk> \<Longrightarrow> \<not> (\<xi>a, \<gamma> \<turnstile> e \<Down> v')" and
  "\<lbrakk>\<xi>a , \<gamma> \<turnstile>* es \<Down> vs; vs \<noteq> vs'; \<xi>v_determ \<xi>a\<rbrakk> \<Longrightarrow> \<not> (\<xi>a, \<gamma> \<turnstile>* es \<Down> vs')"
   apply clarsimp
   apply (erule notE)
   apply (rule v_sem_v_sem_all_determ(1); assumption)
  apply clarsimp
  apply (erule notE)
  apply (rule v_sem_v_sem_all_determ(2); assumption)
  done


context value_sem begin


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
end