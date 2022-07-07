theory CorresHelper
  imports 
    UpdateSemHelper
    CogentCRefinement.Cogent_Corres
begin

section "C wp helpers"

lemma whileLoopE_add_invI:
  assumes "\<lbrace> P \<rbrace> whileLoopE_inv c b init I (measure M) \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  shows "\<lbrace> P \<rbrace> whileLoopE c b init \<lbrace> Q \<rbrace>, \<lbrace> R \<rbrace>!"
  by (metis assms whileLoopE_inv_def)

lemma validNF_select_UNIV:
  "\<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace> select UNIV \<lbrace>Q\<rbrace>!"
  apply (subst select_UNIV_unknown)
  apply (rule validNF_unknown)
  done

section "Simplification of corres definition for abstract functions"

context update_sem_init begin

definition
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
      (\<forall>r' w'. val_rel x x'
        \<and> \<Xi>', \<sigma> \<turnstile> x :u fst (snd (snd (snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>
        \<longrightarrow> \<not> snd (afun_mon x' st)
            \<and> (\<forall>st' y'. (y', st') \<in> fst (afun_mon x' st)
                \<longrightarrow> (\<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y)
                    \<and> val_rel y y' \<and> (\<sigma>', st') \<in> srel))))"

lemma absfun_corres:
  "abs_fun_rel \<Xi>' srel s \<xi>' afun' \<sigma> st (\<gamma> ! i) v'
  \<Longrightarrow> i < length \<gamma> \<Longrightarrow> val_rel (\<gamma> ! i) v'
  \<Longrightarrow> \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi>' s)))))
  \<Longrightarrow> corres srel
     (App (AFun s [] []) (Var i))
     (do x \<leftarrow> afun' v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (clarsimp simp: corres_def abs_fun_rel_def)
  apply (frule matches_ptrs_length, simp)
  apply (frule(2) matches_ptrs_proj_single')
  apply clarsimp
  apply (erule impE, blast)
  apply clarsimp
  apply (elim allE, drule mp, blast)
  apply clarsimp
  apply (intro exI conjI[rotated], assumption+)
  apply (rule u_sem_abs_app)
    apply (rule u_sem_afun)
   apply (rule u_sem_var)
  apply simp
  done

lemma abs_fun_rel_def':
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
        (\<forall>r' w'. val_rel x x' \<and> 
              \<Xi>', \<sigma> \<turnstile> x :u fst (snd (snd (snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>
        \<longrightarrow> \<lbrace>\<lambda>s0. s0 = st\<rbrace> 
              afun_mon x' 
            \<lbrace>\<lambda>y' s'. \<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y) \<and> (\<sigma>',s') \<in> srel \<and> val_rel y y'\<rbrace>!))" 
  by (fastforce  simp: abs_fun_rel_def validNF_def valid_def no_fail_def)

end (* of context *)

section "Ordering on abstract function specification properties for corres"

lemma (in update_sem_init) corres_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b; corres srel c m \<xi>a \<gamma> \<Xi>' \<Gamma> \<sigma> s\<rbrakk> \<Longrightarrow> corres srel c m \<xi>b \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  unfolding corres_def
  apply clarsimp
  apply (erule impE, rule rel_leq_matchesuD, assumption, assumption)
  apply (erule impE, intro exI, assumption)
  apply clarsimp
  apply (elim allE, erule impE, assumption)
  apply clarsimp
  apply (drule u_sem_u_sem_all_rel_leqD; simp?)
  apply (intro exI conjI; assumption)
  done

end