theory RepeatCorrespondence
  imports RepeatUpdate RepeatValue
begin

context correspondence_init begin

inductive_cases u_v_primE'     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> x : TPrim \<tau> \<langle>r, w\<rangle>"

lemma uvrepeat_bod_monocorrespondence:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    vrepeat_bod \<xi>v n f g vacc vobsv vret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow>\<exists>r' w'.  \<Xi>', \<sigma>' \<turnstile> uret \<sim> vret : \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> upd.frame \<sigma> wa \<sigma>' w'"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (intro exI conjI; simp?)
    apply blast
   apply (rule upd.frame_id)
  apply clarsimp
  apply (case_tac b; clarsimp)
   apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (erule u_v_primE; clarsimp)
   apply (intro exI conjI; simp?)
    apply blast
   apply (rule upd.frame_id)
  apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
  apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (erule u_v_primE; clarsimp)
  apply (drule_tac r = "ra \<union> ro"  and w = wa and 
      \<gamma> = "[URecord [(uacc, type_repr \<tau>a), (uobsv, type_repr \<tau>o)]]" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                u_v_matches_empty[where \<tau>s = "[]", simplified]
                u_v_struct
                u_v_r_cons1[where w' = "{}", simplified]
                u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (rename_tac r' w')
  apply (thin_tac "upd.frame _ {} _ {}")
  apply (frule_tac u = uobsv and v = vobsv in upd_val_rel_frame(1)[rotated 3]; simp?; clarsimp?)
  apply (frule_tac v = uobsv and v' = vobsv in frame_noalias_upd_val_rel'(2); simp?)
  apply (elim meta_allE meta_impE, assumption, assumption, assumption, assumption, assumption)
  apply clarsimp
  apply (intro exI conjI, assumption, blast)
  apply (erule upd.frame_trans; assumption)
  done

lemma uvrepeat_bod_val_executes_from_upd_executes:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>vret. vrepeat_bod \<xi>v n f g vacc vobsv vret"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (intro exI; simp)
  apply clarsimp
  apply (case_tac b; clarsimp)
   apply (rule_tac x = vacc in exI)
   apply clarsimp
   apply (rule_tac x = b in exI)
   apply clarsimp
   apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and
      \<gamma>' = "[VRecord [vacc, vobsv]]" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (erule u_v_primE'; clarsimp)
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and
      \<gamma>' = "[VRecord [vacc, vobsv]]" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (erule u_v_primE'; clarsimp)
  apply (thin_tac "upd.frame _ {} _ {}")
  apply (frule_tac r = "ra \<union> ro"  and w = wa and
      \<gamma>' = "[VRecord [vacc, vobsv]]" and
      e = "App g (Var 0)" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (frule_tac r = "ra \<union> ro"  and w = wa and
      \<gamma>' = "[VRecord [vacc, vobsv]]" and
      e = "App g (Var 0)" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (frule_tac u = uobsv and v = vobsv in upd_val_rel_frame(1)[rotated 3]; simp?; clarsimp?)
  apply (drule_tac v = uobsv and v' = vobsv in frame_noalias_upd_val_rel'(2)[rotated 1]; simp?)
  apply (elim meta_allE meta_impE, assumption, assumption, assumption, assumption)
  apply clarsimp
  apply (rename_tac ret)
  apply (rule_tac x = ret in exI)
  apply clarsimp
  apply (rule_tac x = b in exI)
  apply clarsimp
  apply (intro exI conjI; assumption)
  done

(*
lemma repeat_bod_monocorrespondence:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    repeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    repeat_bod' \<xi>v n f g vacc vobsv vret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow>\<exists>r' w'.  \<Xi>', \<sigma>' \<turnstile> uret \<sim> vret : \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> upd.frame \<sigma> wa \<sigma>' w'"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (intro exI conjI; simp?)
    apply blast
   apply (rule upd.frame_id)
  apply (clarsimp split: if_splits)
     apply (intro exI conjI; simp?)
      apply blast
     apply (rule upd.frame_id)
    apply (rule FalseE)
    apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
     apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
    apply clarsimp
    apply (erule u_v_primE; clarsimp)
   apply (rule FalseE)
   apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                 u_v_matches_empty[where \<tau>s = "[]", simplified]
                 u_v_struct
                 u_v_r_cons1[where w' = "{}", simplified]
                 u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                 u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (erule u_v_primE; clarsimp)
  apply (rename_tac \<sigma>'' uacc' vacc')
  apply (drule_tac r = "ra \<union> ro"  and w = wa and 
      \<gamma> = "[URecord [(uacc, type_repr \<tau>a), (uobsv, type_repr \<tau>o)]]" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                u_v_matches_empty[where \<tau>s = "[]", simplified]
                u_v_struct
                u_v_r_cons1[where w' = "{}", simplified]
                u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (rename_tac r' w')
  apply (frule_tac u = uobsv and v = vobsv in upd_val_rel_frame(1)[rotated 3]; simp?; clarsimp?)
   apply (frule_tac v = uobsv and v' = vobsv in frame_noalias_upd_val_rel'(2); simp?; clarsimp?)
  apply (elim meta_allE meta_impE, assumption, assumption, assumption, assumption, assumption)
  apply clarsimp
  apply (intro exI conjI, assumption, blast)
  apply (erule upd.frame_trans; assumption)
  done



lemma repeat_bod_val_executes_from_upd_executes:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    repeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>vret. repeat_bod' \<xi>v n f g vacc vobsv vret"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (rule_tac x = vacc in exI)
   apply clarsimp
  apply (clarsimp split: if_splits)
   apply (rule_tac x = vacc in exI)
   apply clarsimp
   apply (rule conjI; clarsimp)
    apply (rule FalseE)
    apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
     apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
    apply clarsimp
    apply (erule u_v_primE; clarsimp)
   apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and
      \<gamma>' = "[VRecord [vacc, vobsv]]" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
     apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
    apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
     apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
    apply clarsimp
   apply (erule u_v_primE'; clarsimp)
    apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and v' = "VPrim (LBool False)" in mono_correspondence(1)[rotated 3]; simp?)
     apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (erule u_v_primE; clarsimp)
  apply (frule_tac r = "ra \<union> ro"  and w = wa and
      \<gamma>' = "[VRecord [vacc, vobsv]]" and
      e = "App g (Var 0)" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (frule_tac r = "ra \<union> ro"  and w = wa and
      \<gamma>' = "[VRecord [vacc, vobsv]]" and
      e = "App g (Var 0)" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply blast
  apply clarsimp
  apply (rename_tac  \<sigma>'' uacc' vacc' r' w')
  apply (frule_tac u = uobsv and v = vobsv in upd_val_rel_frame(1)[rotated 3]; simp?; clarsimp?)
  apply (frule_tac v = uobsv and v' = vobsv in frame_noalias_upd_val_rel'(2); simp?; clarsimp?)
  apply (elim meta_allE meta_impE, assumption, assumption, assumption, assumption)
  apply clarsimp
  apply (rename_tac vret)
  apply (rule_tac x = vret in exI)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (intro exI conjI; assumption)
  apply (rule conjI)
   apply clarsimp
   apply (rule FalseE)
   apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply clarsimp
   apply (erule u_v_primE'; clarsimp)
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and
      \<gamma>' = "[VRecord [vacc, vobsv]]" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (erule u_v_primE'; clarsimp)
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and v' = "VPrim (LBool True)" in mono_correspondence(1)[rotated 3]; simp?)
  apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
   apply (rule upd_val_rel_bang(1); simp)
  apply clarsimp
  apply (erule u_v_primE; clarsimp)
  done
*)
end (* of context *)
end