theory RepeatCorrespondence
  imports RepeatUpdate RepeatValue CorrespondenceHelper
begin

context correspondence begin

section "Mono-correspondence"

lemma uvrepeat_bod_monocorrespondence:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    vrepeat_bod \<xi>v n f g vacc vobsv vret;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow>\<exists>r' w'.  \<Xi>', \<sigma>' \<turnstile> uret \<sim> vret : \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> (ra \<union> ro) \<and> frame \<sigma> wa \<sigma>' w'"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (intro exI conjI; simp?)
    apply blast
   apply (rule upd.frame_id)
  apply clarsimp
  apply (rename_tac n \<sigma> uacc ra wa vacc b ba)
  apply (case_tac b; clarsimp)
   apply (drule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp) 
    apply (simp add:  u_v_matches.u_v_matches_empty)
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
   apply (simp add:  u_v_matches.u_v_matches_empty)
  apply clarsimp
  apply (erule u_v_primE; clarsimp)
  apply (drule_tac r = "ra \<union> ro"  and w = wa and 
      \<gamma> = "[URecord [(uacc, type_repr \<tau>a), (uobsv, type_repr \<tau>o)] None]" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                u_v_matches_empty[where \<tau>s = "[]", simplified]
                u_v_struct
                u_v_r_cons1[where w' = "{}", simplified]
                u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_v_r_empty; simp?)
    apply blast
   apply (simp add:  u_v_matches.u_v_matches_empty)
  apply clarsimp
  apply (rename_tac r' w')
  apply (thin_tac "frame _ {} _ {}")
  apply (frule_tac u = uobsv and v = vobsv in upd_val_rel_frame(1)[rotated 3]; simp?; clarsimp?)
  apply (frule_tac v = uobsv and v' = vobsv in frame_noalias_upd_val_rel'(2); simp?)
  apply (elim meta_allE meta_impE, assumption, assumption, assumption, assumption, assumption)
  apply clarsimp
  apply (intro exI conjI, assumption, blast)
  apply (erule upd.frame_trans; assumption)
  done

section "Upward propagation"

lemma uvrepeat_bod_upward_propagation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
    \<Xi>', \<sigma> \<turnstile> uacc \<sim> vacc : \<tau>a \<langle>ra, wa\<rangle>;
    \<Xi>', \<sigma> \<turnstile> uobsv \<sim> vobsv : \<tau>o \<langle>ro, {}\<rangle>;
    ro \<inter> wa = {};
    urepeat_bod \<xi>u n f g \<sigma> \<sigma>' \<tau>a uacc \<tau>o uobsv uret;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App f (Var 0)) : TPrim Bool;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<exists>vret. vrepeat_bod \<xi>v n f g vacc vobsv vret"
  apply (induct n arbitrary: \<sigma> uacc ra wa vacc)
   apply clarsimp
   apply (intro exI; simp)
  apply clarsimp
  apply (rename_tac n \<sigma> uacc ra wa vacc b)
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
    apply (simp add:  u_v_matches.u_v_matches_empty)
   apply clarsimp
   apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
     apply (rule upd_val_rel_bang(1); simp)
    apply (simp add:  u_v_matches.u_v_matches_empty)
   apply clarsimp
   apply (erule u_v_uprimE; simp)
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" and
      \<gamma>' = "[VRecord [vacc, vobsv]]" in val_executes_from_upd_executes(1)[rotated 3]; simp?)
    apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply (simp add:  u_v_matches.u_v_matches_empty)
  apply clarsimp
  apply (frule_tac r = "(ra \<union> wa) \<union> ro"  and w = "{}" in mono_correspondence(1)[rotated 3]; simp?)
   apply (intro u_v_matches_some[where r' = "{}" and w' = "{}", simplified]
                  u_v_matches_empty[where \<tau>s = "[]", simplified]
                  u_v_struct
                  u_v_r_cons1[where w' = "{}", simplified]
                  u_v_r_cons1[where r' = "{}" and w' = "{}", simplified]
                  u_v_r_empty; simp?)
    apply (rule upd_val_rel_bang(1); simp)
   apply (simp add:  u_v_matches.u_v_matches_empty)
  apply clarsimp
  apply (erule u_v_uprimE; clarsimp)
  apply (thin_tac "frame _ {} _ {}")
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
    apply (simp add:  u_v_matches.u_v_matches_empty)
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
  apply (simp add:  u_v_matches.u_v_matches_empty)
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

section "Mono-correspondence and upward propagation"

lemma uvrepeat_monocorrespond_upward_propagation:
  "\<And>\<sigma> \<sigma>' au av v v' r w.
       \<lbrakk>proc_ctx_wellformed \<Xi>';
        \<xi>u \<sim> \<xi>v matches-u-v \<Xi>';
        \<Xi>', \<sigma> \<turnstile> au \<sim> av : TRecord
                           [(''n'', TPrim (Num U64), Present),
                            (''stop'', TFun (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) (TPrim Bool), Present),
                            (''step'', TFun (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed) \<tau>a, Present),
                            (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)]
                           Unboxed \<langle>r, w\<rangle>;
        urepeat \<Xi>' \<xi>u \<tau>a \<tau>o (\<sigma>, au) (\<sigma>', v)\<rbrakk>
       \<Longrightarrow> (val.vrepeat \<Xi>' \<xi>v \<tau>a \<tau>o av v' \<longrightarrow>
            (\<exists>r' w'. \<Xi>', \<sigma>' \<turnstile> v \<sim> v' : \<tau>a \<langle>r', w'\<rangle> \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
            (\<exists>v'. val.vrepeat \<Xi>' \<xi>v \<tau>a \<tau>o av v')"
  unfolding urepeat_def val.vrepeat_def
  apply clarsimp
  apply (erule u_v_urecE; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)+
  apply (erule u_v_uprimE)
  apply (erule u_v_r_uemptyE)
  apply clarsimp
  apply (frule u_v_tfun_no_pointers)
  apply (frule u_v_tfun_no_pointers(2))
  apply clarsimp
  apply (rename_tac \<sigma> \<sigma>' v v' n f f' g g' rg wg acc acc' ra wa obsv obsv' ro wo)
  apply (frule_tac u = g in  u_v_tfun_no_pointers(1))
  apply (frule_tac u = g in u_v_tfun_no_pointers(2))
  apply clarsimp
  apply (cut_tac \<Xi>' = \<Xi>' and \<sigma> = \<sigma> and \<tau> = \<tau>o and u  = obsv and r = ro and w = wo in u_v_bang_not_writable(1); simp?)
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (drule uvrepeat_bod_monocorrespondence[rotated 5]; simp?)
    apply (erule u_v_tfunE; clarsimp)+
     apply blast
    apply blast
   apply blast
  apply (drule_tac vacc = acc' and vobsv = obsv' and ra = ra and wa = wa
      in uvrepeat_bod_upward_propagation[rotated 5]; simp?)
   apply blast
  apply (erule u_v_tfunE; clarsimp)+
    apply (intro conjI exI upd_val_rel_to_vval_typing(1); assumption)+
  apply (erule u_v_tfunE; clarsimp)+
   apply (intro conjI exI upd_val_rel_to_vval_typing(1); assumption)+
  done

end (* of context *)

end