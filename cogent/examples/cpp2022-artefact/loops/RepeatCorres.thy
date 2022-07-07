theory RepeatCorres
  imports
    RepeatUpdate
    CorresHelper
    CogentTypingHelper
    "build/Generated_CorresSetup"
begin

context update_sem_init begin

definition crepeat
  where
"crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1 a \<equiv>
    do r <- select UNIV;
       (i :: 64 word) <- gets (\<lambda>_. 0);
       a0 <- select UNIV;
       a0 <- gets (\<lambda>_. a1U (\<lambda>_. a0C a) a0);
       a0 <- gets (\<lambda>_. o1U (\<lambda>_. o0C a) a0);
       i <- gets (\<lambda>_. 0);
       doE a0 <-
           doE x <-
               doE _ <- liftE (guard (\<lambda>s. True));
                   whileLoopE (\<lambda>(ret, a0, i) s. i < ((nC a) :: 64 word))
                     (\<lambda>(ret, a0, i).
                         doE x <-
                             doE retval <- liftE (do ret' <- d0 ((stopC a) :: 32 signed word) a0;
                                                     gets (\<lambda>_. ret')
                                                  od);
                                 _ <- doE _ <- liftE (guard (\<lambda>s. True));
                                          condition (\<lambda>s. boolean_C retval \<noteq> 0)
                                            (doE global_exn_var <- liftE (gets (\<lambda>_. Break));
                                                 throwError (global_exn_var, ret, a0)
                                             odE)
                                            (liftE (gets (\<lambda>_. ())))
                                      odE;
                                 liftE (do retval <- do ret' <- d1 ((stepC a) :: 32 signed word) a0;
                                                        gets (\<lambda>_. ret')
                                                     od;
                                           a0 <- gets (\<lambda>_. a1U (\<lambda>_. retval) a0);
                                           i <- gets (\<lambda>_. i + 1);
                                           gets (\<lambda>_. (retval, a0, i))
                                        od)
                             odE;
                             liftE
                              (case x of
                               (ret, a0, i) \<Rightarrow>
                                 do _ <- guard (\<lambda>_. True);
                                    gets (\<lambda>_. (ret, a0, i))
                                 od)
                         odE)
                    (r, a0, i)
               odE;
               liftE (case x of (ret, a0, i) \<Rightarrow> gets (\<lambda>_. a0))
           odE <handle2>
           (\<lambda>(global_exn_var, ret, a0). doE _ <- doE _ <- liftE (guard (\<lambda>s. True));
    condition (\<lambda>s. global_exn_var = Break)
      (liftE (gets (\<lambda>_. ())))
      (throwError ret)
                                                                 odE;
                                                            liftE (gets (\<lambda>_. a0))
                                                        odE);
           ret <- liftE (gets (\<lambda>_. a1C a0));
           global_exn_var <- liftE (gets (\<lambda>_. Return));
           throwError ret
       odE <catch>
       (\<lambda>ret. do _ <- gets (\<lambda>_. ());
                 gets (\<lambda>_. ret)
              od)
    od"

definition repeat_inv
  where
"repeat_inv srel \<xi>' (i :: 64 word) fstop fstep \<sigma> \<tau>a \<tau>o acc obsv s cn cacc cobsv \<equiv>
    val_rel obsv cobsv \<and> i \<le> cn \<and>
    (\<exists>\<sigma>' y. urepeat_bod \<xi>' (unat i) (uvalfun_to_expr fstop) (uvalfun_to_expr fstep) \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv y \<and>
            (\<sigma>', s) \<in> srel \<and> val_rel y cacc)"

definition repeat_measure
  where
"repeat_measure i n = unat n - unat i"

definition repeat_pre_step
  where
"repeat_pre_step srel \<xi>' i j fstop fstep \<sigma> \<tau>a \<tau>o acc obsv s cn cacc cobsv \<equiv> 
    val_rel obsv cobsv \<and> i < cn \<and> i = j \<and> 
    (\<exists>\<sigma>' y. urepeat_bod \<xi>' (unat i) (uvalfun_to_expr fstop) (uvalfun_to_expr fstep) \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv y \<and>
            (\<sigma>', s) \<in> srel \<and> val_rel y cacc \<and>
            (\<xi>', [URecord [(y, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr fstop) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))))"

lemma step_wp:
  assumes \<Xi>wellformed: "proc_ctx_wellformed \<Xi>'"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: ('c :: cogent_C_val)) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     d1corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     a1C_a1U: "\<And>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<And>x y. o1C (a1U y x) = o1C x"
  and     srel: "(\<sigma>, s) \<in> state_rel"
  and     acctyp: "\<Xi>', \<sigma> \<turnstile> acc :u \<tau>a \<langle>ra, wa\<rangle>"
  and     obsvtyp: "\<Xi>', \<sigma> \<turnstile> obsv :u \<tau>o \<langle>ro, {}\<rangle>"
  and     disjoint: "wa \<inter> ro = {}"
  and     valrelacc: "val_rel acc (a0C v')"
  and     valrelobsv: "val_rel obsv (o0C v')"
  shows "\<And>arg j i.
          \<lbrace>\<lambda>sa. repeat_pre_step state_rel \<xi>' i j fstop fstep \<sigma> \<tau>a \<tau>o acc obsv sa (nC v') (a1C arg) (o1C arg)\<rbrace>
            d1 (stepC v') arg 
          \<lbrace>\<lambda>ret sb.
               repeat_inv state_rel \<xi>' (j + 1) fstop fstep \<sigma> \<tau>a \<tau>o acc obsv sb (nC v') (a1C (a1U (\<lambda>_. ret) arg))
                (o1C (a1U (\<lambda>_. ret) arg)) \<and>
               repeat_measure (j+1) (nC v') < repeat_measure i (nC v')\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (clarsimp simp: repeat_pre_step_def repeat_inv_def repeat_measure_def)
  apply (rename_tac s \<sigma>' y)
  apply (insert d1corres)
  apply (drule_tac x = "URecord [(y, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None" and
                   y = arg in meta_spec2)
  apply (drule_tac x = \<sigma>' and y = s in meta_spec2)
  apply (erule meta_impE)
   apply (simp add: valrelc)
  apply (clarsimp simp: corres_def \<Xi>wellformed \<xi>'matchesu)
  apply (erule impE) 
   apply (drule urepeat_bod_preservation[OF \<Xi>wellformed \<xi>'matchesu acctyp obsvtyp
                                            disjoint[simplified Int_commute] _
                                            fsteptype[simplified \<tau>fdef]])
   apply clarsimp
   apply (rename_tac r' w')
   apply (rule_tac x = "r' \<union> ro" in exI)
   apply (rule_tac x = w' in exI)
   apply (clarsimp simp: \<tau>fdef)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
                matches_ptrs_empty[where \<tau>s = "[]", simplified]
                u_t_struct
                u_t_r_cons1[where w' = "{}", simplified]
                u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_t_r_empty; simp?)
     apply (erule uval_typing_frame(1); simp add: obsvtyp disjoint[simplified Int_commute])
    apply (drule frame_noalias_uval_typing'(2)[OF _ obsvtyp disjoint[simplified Int_commute]]; blast)
   apply (simp add:matches_ptrs.matches_ptrs_empty)
  apply clarsimp
  apply (rename_tac a b)
  apply (elim allE impE, assumption)
  apply (clarsimp simp: inc_le)
  apply (simp only: less_is_non_zero_p1[THEN unatSuc2] word_less_nat_alt)
  apply (frule urepeat_bod_step_determ[OF _ _ _ determ]; (simp del: urepeat_bod.simps)?)
  apply (intro conjI exI; assumption?; (simp del: urepeat_bod.simps add: o1C_a1U a1C_a1U)?)
  done

lemma stop_wp:
  assumes \<Xi>wellformed: "proc_ctx_wellformed \<Xi>'"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: ('c :: cogent_C_val)) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     d0corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     srel: "(\<sigma>, s) \<in> state_rel"
  and     acctyp: "\<Xi>', \<sigma> \<turnstile> acc :u \<tau>a \<langle>ra, wa\<rangle>"
  and     obsvtyp: "\<Xi>', \<sigma> \<turnstile> obsv :u \<tau>o \<langle>ro, {}\<rangle>"
  and     disjoint: "wa \<inter> ro = {}"
  and     valrelacc: "val_rel acc (a0C v')"
  and     valrelobsv: "val_rel obsv (o0C v')"
  shows "\<And>j arg j'.
          \<lbrace>\<lambda>sa. (\<exists>\<sigma>' y n. (\<sigma>', sa) \<in> state_rel \<and> val_rel y (a1C arg) \<and> val_rel obsv (o1C arg) \<and>
            j = j' \<and>  j < nC v' \<and>
            urepeat_bod \<xi>' n (uvalfun_to_expr fstop) (uvalfun_to_expr fstep) \<sigma> \<sigma>'
              \<tau>a acc \<tau>o obsv y \<and>
            ((\<xi>' , [URecord [(y, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr fstop) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)))
              \<longrightarrow> n \<ge> unat j \<and> n < unat (nC v')) \<and>
            ((\<xi>' , [URecord [(y, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr fstop) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False)))
              \<longrightarrow> n = unat j))\<rbrace>
            d0 (stopC v') arg 
           \<lbrace>\<lambda>ret sb.
               (boolean_C ret \<noteq> 0 \<longrightarrow>
                (\<exists>\<sigma>' y.
                    urepeat_bod \<xi>' (unat (nC v')) (uvalfun_to_expr fstop) (uvalfun_to_expr fstep) \<sigma> \<sigma>' \<tau>a acc \<tau>o obsv y \<and>
                    (\<sigma>', sb) \<in> state_rel \<and> val_rel y (a1C arg))) \<and>
               (boolean_C ret = 0 \<longrightarrow>
                repeat_pre_step state_rel \<xi>' j j' fstop fstep \<sigma> \<tau>a \<tau>o acc obsv sb (nC v') (a1C arg) (o1C arg))\<rbrace>!"
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (clarsimp simp: repeat_pre_step_def)
  apply (rename_tac s \<sigma>' y n)
  apply (insert d0corres)
  apply (drule_tac x = "URecord [(y, type_repr (bang \<tau>a)), (obsv, type_repr \<tau>o)] None" and
                   y = arg in meta_spec2)
  apply (drule_tac x = \<sigma>' and y = s in meta_spec2)
  apply (erule meta_impE)
   apply (simp add: valrelc)
  apply (clarsimp simp: corres_def \<Xi>wellformed \<xi>'matchesu)
  apply (frule urepeat_bod_preservation[OF \<Xi>wellformed \<xi>'matchesu acctyp obsvtyp
                                           disjoint[simplified Int_commute] _
                                           fsteptype[simplified \<tau>fdef]])
  apply clarsimp
  apply (rename_tac r' w')
  apply (erule impE, rule_tac x = "(r' \<union> w') \<union> ro" in exI, rule_tac x = "{}" in exI) 
   apply (clarsimp simp: \<tau>fdef)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
                matches_ptrs_empty[where \<tau>s = "[]", simplified]
                u_t_struct
                u_t_r_cons1[where w' = "{}", simplified]
                u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_t_r_empty; simp?)
      apply (rule uval_typing_bang(1); simp)
     apply (rule uval_typing_bang(1)[where w = "{}" ,simplified])
     apply (erule uval_typing_frame(1); simp add: obsvtyp disjoint[simplified Int_commute])
    apply (rule wellformed_imp_bang_type_repr[OF uval_typing_to_wellformed(1)[OF obsvtyp]])
   apply (simp add:matches_ptrs.matches_ptrs_empty)
  apply clarsimp
  apply (rename_tac a b)
  apply (elim allE, erule impE, assumption)
  apply clarsimp 
  apply (frule_tac r = "(r' \<union> w') \<union> ro" and w = "{}" 
      in preservation(1)[where K = "[]" and \<tau>s = "[]", simplified,
                         OF subst_wellformed_nothing \<Xi>wellformed _ 
                            \<xi>'matchesu _ fstoptype, simplified, rotated 1])
   apply (clarsimp simp: \<tau>fdef)
   apply (intro matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
                matches_ptrs_empty[where \<tau>s = "[]", simplified]
                u_t_struct
                u_t_r_cons1[where w' = "{}", simplified]
                u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
                u_t_r_empty; simp?)
      apply (rule uval_typing_bang(1); simp)
     apply (rule uval_typing_bang(1)[where w = "{}" ,simplified])
     apply (erule uval_typing_frame(1); simp add: obsvtyp disjoint[simplified Int_commute])
    apply (rule wellformed_imp_bang_type_repr[OF uval_typing_to_wellformed(1)[OF obsvtyp]])
   apply (simp add:matches_ptrs.matches_ptrs_empty)
  apply (clarsimp simp: val_rel_bool_t_C_def)
  apply (erule u_t_primE; clarsimp)
  apply (drule frame_empty; clarsimp)
  apply (rule conjI; clarsimp)
  apply (intro exI conjI; assumption?)
   apply (erule (2) urepeat_bod_early_termination)
  apply (intro exI conjI; assumption?)
  done

lemma crepeat_corres_base:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [],{}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<gamma>i: "\<gamma> ! i = 
               URecord [(UPrim (LU64 n), RPrim (Num U64)), 
                        (fstop, RFun), (fstep, RFun), 
                        (acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     d0corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<And>x x' \<sigma> s. val_rel x x' \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     valrela:  "\<And>x x'. val_rel x (x' :: 'a) \<equiv>
                              \<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x')"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: 'c) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     a1C_a1U: "\<And>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<And>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<And>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<And>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
proof (rule absfun_corres[OF _ \<gamma>len valrel])
  show "abs_fun_rel \<Xi>' state_rel name \<xi>'' cfun \<sigma> s (\<gamma> ! i) v'"
    apply (subst abs_fun_rel_def')
    apply (clarsimp simp: \<Xi>name \<tau>def \<xi>''name cfundef urepeat_def bang\<tau>o \<gamma>i fsteptype[simplified \<tau>fdef])
    apply (insert fstoptype; simp add: \<tau>fdef bang\<tau>o)
    apply (thin_tac "_, _, _, _, _ \<turnstile> _ : _")
    apply (erule u_t_recE; clarsimp)
    apply (erule u_t_r_consE; simp)+
    apply (erule conjE)+
    apply (drule_tac t = "type_repr _" in sym)+
    apply clarsimp
    apply (frule tprim_no_pointers(1); clarsimp)
    apply (drule tprim_no_pointers(2); clarsimp)
    apply (frule tfun_no_pointers(1); clarsimp)
    apply (frule tfun_no_pointers(2); clarsimp)
    apply (drule uval_typing_uvalfun; simp)
    apply (frule tfun_no_pointers(1); clarsimp)
    apply (frule tfun_no_pointers(2); clarsimp)
    apply (drule uval_typing_uvalfun; simp)
    apply (erule u_t_r_emptyE; clarsimp)
    apply (rename_tac ra wa ro wo)
    apply (cut_tac \<Xi>' = \<Xi>' and \<sigma> = \<sigma> and v = obsv and \<tau> = \<tau>o and r = ro and w = wo
        in bang_not_writable(1); simp add: bang\<tau>o)
    apply (clarsimp simp: crepeat_def valrela val_rel_word val_rel_fun_tag)
    apply (wp; (clarsimp split: prod.splits)?)
     apply (rule_tac 
      I = "\<lambda>(a, b, j) s. repeat_inv state_rel \<xi>' j fstop fstep \<sigma> \<tau>a \<tau>o acc obsv s (nC v') (a1C b) (o1C b)" and
      M = "\<lambda>((_,_, j), _). repeat_measure j (nC v')" in whileLoopE_add_invI)
        apply (wp; clarsimp split: prod.splits)
            using d1corres o1C_a1U a1C_a1U
            apply (wp step_wp[OF _ \<xi>'matchesu determ \<tau>fdef fsteptype valrelc]; simp?)
           apply (wp; clarsimp)
          apply (wp; clarsimp)
          using d0corres
          apply (wp stop_wp[OF _ \<xi>'matchesu determ \<tau>fdef fstoptype fsteptype valrelc]; simp?)
         apply clarsimp
         apply (clarsimp simp: repeat_inv_def)
         apply (intro exI conjI; assumption?)
          apply (clarsimp simp: unat_mono)
         apply clarsimp
        apply (clarsimp simp: repeat_inv_def)
       apply wp
      apply (rule validNF_select_UNIV)+
    apply (clarsimp simp: repeat_inv_def o1C_o1U a1C_o1U a1C_a1U)
    done
next
  show "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
    using \<Gamma>i by simp
qed

section "Corres rules which are easier to use"

lemma crepeat_corres:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     d0corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<And>x x' \<sigma> s. val_rel x x' \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     valrela:  "\<And>x x'. val_rel x (x' :: 'a) \<equiv>
                              \<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x')"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: 'c) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     a1C_a1U: "\<And>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<And>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<And>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<And>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (insert \<gamma>i valrel; clarsimp simp: valrela val_rel_word corres_def)
  apply (frule matches_ptrs_length)
  apply (frule_tac  matches_ptrs_proj_single'[OF _ _ \<Gamma>i[simplified \<Xi>name \<tau>def]]; simp?)
   apply (cut_tac \<gamma>len; linarith)
  apply clarsimp
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; simp)+
  apply (erule u_t_r_emptyE; simp)
  apply (elim conjE)
  apply (drule_tac t = "type_repr _" in sym)
  apply clarsimp
  apply (thin_tac "_ \<inter> _ = {}")+
  apply (thin_tac "_ \<subseteq> _")+
  apply (thin_tac "_, _ \<turnstile> _ :u _ \<langle>_, _\<rangle>")+
  apply (cut_tac state_rel = state_rel and \<sigma> = \<sigma> and s = s and \<xi>'' = \<xi>'' in 
      crepeat_corres_base[OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>o _ \<xi>'matchesu determ _ fstoptype
                            fsteptype _ _ valrela valrelc a1C_a1U _ _ _ cfundef]; simp?)
  using \<Gamma>i apply simp
  using \<Xi>name apply simp
  using \<xi>''name apply simp
  using d0corres apply simp
  using d1corres apply simp
  using a1C_o1U apply simp
  using o1C_o1U apply simp
  using o1C_a1U apply simp
  apply (clarsimp simp: corres_def)
  done

lemma crepeat_corres_rel_leq:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd  (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     leq: "rel_leq \<xi>' \<xi>''"
  and     determ: "determ \<xi>''"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     d0corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<And>x x' \<sigma> s. val_rel x x' \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     valrela:  "\<And>x x'. val_rel x (x' :: 'a) \<equiv>
                              \<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x')"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: 'c) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     a1C_a1U: "\<And>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<And>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<And>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<And>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (clarsimp simp: corres_def)
  apply (cut_tac state_rel = state_rel and \<sigma> = \<sigma> and s = s and \<xi>'' = \<xi>'' in 
      crepeat_corres[OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>o _ rel_leq_matchesuD[OF leq]
                       determ_rel_leqD[OF leq determ] \<gamma>i fstoptype fsteptype _ _ valrela
                       valrelc a1C_a1U _ _ _ cfundef]; simp?)
  using \<Gamma>i apply simp
  using \<Xi>name apply simp
  using \<xi>''name apply simp
  using d0corres apply simp
  using d1corres apply simp
  using a1C_o1U apply simp
  using o1C_o1U apply simp
  using o1C_a1U apply simp
  apply (clarsimp simp: corres_def)
  done

lemma crepeat_corres_bang:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun \<tau>f (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>a: "bang \<tau>a = \<tau>a"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     leq: "rel_leq \<xi>' \<xi>''"
  and     determ: "determ \<xi>''"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     d0corres: "\<And>x x' \<sigma> s. val_rel x (x' :: ('c :: cogent_C_val)) \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<And>x x' \<sigma> s. val_rel x x' \<Longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     valrela:  "\<And>x x'. val_rel x (x' :: 'a) \<equiv>
                              \<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x')"
  and     valrelc:  "\<And>x x'. val_rel x (x' :: 'c) \<equiv>
                              \<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x')"
  and     a1C_a1U: "\<And>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<And>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<And>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<And>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule_tac state_rel = state_rel and \<sigma> = \<sigma> and s = s in 
      crepeat_corres_rel_leq[OF \<gamma>len valrel _ _  _  \<tau>fdef bang\<tau>o _ leq
                       determ \<gamma>i _  fsteptype _ _ valrela
                       valrelc a1C_a1U _ _ _ cfundef]; simp?)
  using \<Gamma>i apply simp
  using \<Xi>name \<tau>def \<tau>fdef bang\<tau>a bang\<tau>o apply simp
  using \<xi>''name apply simp
  using \<tau>fdef bang\<tau>a bang\<tau>o fstoptype apply simp
  using d0corres apply simp
  using d1corres apply simp
  using a1C_o1U apply simp
  using o1C_o1U apply simp
  using o1C_a1U apply simp
  done

lemmas crepeat_corres_bang_fun_fun = crepeat_corres_bang
  [where fstop = "UFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_fun]
lemmas crepeat_corres_bang_fun_afun = crepeat_corres_bang
  [where fstop = "UFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_absfun]
lemmas crepeat_corres_bang_afun_fun = crepeat_corres_bang
  [where fstop = "UAFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_fun]
lemmas crepeat_corres_bang_afun_afun = crepeat_corres_bang
  [where fstop = "UAFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_absfun]

lemmas crepeat_corres_fun_fun = crepeat_corres_rel_leq
  [where fstop = "UFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _  typing_mono_app_cogent_fun typing_mono_app_cogent_fun]
lemmas crepeat_corres_fun_afun = crepeat_corres_rel_leq
  [where fstop = "UFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_absfun]
lemmas crepeat_corres_afun_fun = crepeat_corres_rel_leq
  [where fstop = "UAFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_fun]
lemmas crepeat_corres_afun_afun = crepeat_corres_rel_leq
  [where fstop = "UAFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_absfun]


section "Alternate corres rules"

lemma crepeat_corres_base_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<gamma>i: "\<gamma> ! i = URecord [(UPrim (LU64 n), RPrim (Num U64)), (fstop, RFun), (fstep, RFun), (acc, type_repr \<tau>a), (obsv, type_repr \<tau>o)] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrela:  "\<forall>x (x' :: ('a :: cogent_C_val)). val_rel x x' =
                              (\<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None\<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x'))"
  and     valrelc:  "\<forall>x (x' :: ('c :: cogent_C_val)). val_rel x x' =
                              (\<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x'))"
  and     d0corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     a1C_a1U: "\<forall>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<forall>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<forall>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<forall>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule crepeat_corres_base[where o1C = o1C, 
        OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>o _ \<xi>'matchesu determ \<gamma>i fstoptype fsteptype, rotated -1, OF cfundef];
        (simp add: \<Gamma>i \<Xi>name \<xi>''name valrela valrelc a1C_a1U a1C_o1U o1C_o1U o1C_a1U d0corres[simplified] d1corres[simplified])?)
  done

lemma crepeat_corres_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     \<xi>'matchesu: "\<xi>' matches-u \<Xi>'"
  and     determ: "determ \<xi>'"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrela:  "\<forall>x (x' :: ('a :: cogent_C_val)). val_rel x x' =
                              (\<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x'))"
  and     valrelc:  "\<forall>x (x' :: ('c :: cogent_C_val)). val_rel x x' =
                              (\<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x'))"
  and     d0corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     a1C_a1U: "\<forall>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<forall>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<forall>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<forall>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule crepeat_corres[where o1C = o1C, 
        OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>o _ \<xi>'matchesu determ \<gamma>i fstoptype fsteptype, rotated -1, OF cfundef];
        (simp add: \<Gamma>i \<Xi>name \<xi>''name valrela valrelc a1C_a1U a1C_o1U o1C_o1U o1C_a1U d0corres[simplified] d1corres[simplified])?)
  done

lemma crepeat_corres_rel_leq_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun (bang \<tau>f) (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     leq: "rel_leq \<xi>' \<xi>''"
  and     determ: "determ \<xi>''"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some (bang \<tau>f)] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrela:  "\<forall>x (x' :: ('a :: cogent_C_val)). val_rel x x' =
                              (\<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x'))"
  and     valrelc:  "\<forall>x (x' :: ('c :: cogent_C_val)). val_rel x x' =
                              (\<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x'))"
  and     d0corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     a1C_a1U: "\<forall>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<forall>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<forall>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<forall>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule crepeat_corres_rel_leq[where o1C = o1C, 
        OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>o _ leq determ \<gamma>i fstoptype fsteptype, rotated -1, OF cfundef];
        (simp add: \<Gamma>i \<Xi>name \<xi>''name valrela valrelc a1C_a1U a1C_o1U o1C_o1U o1C_a1U d0corres[simplified] d1corres[simplified])?)
  done

lemma crepeat_corres_bang_all:
  assumes \<gamma>len: "i < length \<gamma>"
  and     valrel: "val_rel (\<gamma> ! i) (v' :: ('a :: cogent_C_val))"
  and     \<Gamma>i: "\<Gamma> ! i = Some (fst (snd (snd (snd (\<Xi>' name)))))"
  and     \<Xi>name: "\<Xi>' name = (0, [], {}, \<tau>, \<tau>a)"
  and     \<tau>def: "\<tau> = TRecord [(''n'', TPrim (Num U64), Present),
                              (''stop'', TFun \<tau>f (TPrim Bool), Present),
                              (''step'', TFun \<tau>f \<tau>a, Present),
                              (''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     \<tau>fdef: "\<tau>f = TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed"
  and     bang\<tau>a: "bang \<tau>a = \<tau>a"
  and     bang\<tau>o: "bang \<tau>o = \<tau>o"
  and     \<xi>''name: "\<xi>'' name = urepeat \<Xi>' \<xi>' \<tau>a \<tau>o"
  and     leq: "rel_leq \<xi>' \<xi>''"
  and     determ: "determ \<xi>''"
  and     \<gamma>i: "\<exists>n acc obsv a b. \<gamma> ! i = URecord [n, (fstop, a), (fstep, b), acc, obsv] None"
  and     fstoptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstop) (Var 0) : TPrim Bool"
  and     fsteptype: "\<Xi>', 0, [], {}, [Some \<tau>f] \<turnstile> App (uvalfun_to_expr fstep) (Var 0) : \<tau>a"
  and     valrela:  "\<forall>x (x' :: ('a :: cogent_C_val)). val_rel x x' =
                              (\<exists>n f g acc obsv. x = URecord [n, f, g, acc, obsv] None \<and>
                                val_rel (fst n) (nC x') \<and> val_rel (fst f) (stopC x') \<and>
                                val_rel (fst g) (stepC x') \<and> val_rel (fst acc) (a0C x') \<and>
                                val_rel (fst obsv) (o0C x'))"
  and     valrelc:  "\<forall>x (x' :: ('c :: cogent_C_val)). val_rel x x' =
                              (\<exists>acc obsv. x = URecord [acc, obsv] None \<and> val_rel (fst acc) (a1C x') \<and>
                                val_rel (fst obsv) (o1C x'))"
  and     d0corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstop) (Var 0))
                                    (do ret <- d0 (stopC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some (bang \<tau>f)] \<sigma> s"
  and     d1corres: "\<forall>x x' \<sigma> s. val_rel x x' \<longrightarrow>
                                  corres state_rel (App (uvalfun_to_expr fstep) (Var 0))
                                    (do ret <- d1 (stepC v') x'; gets (\<lambda>s. ret) od)
                                    \<xi>' [x] \<Xi>' [option.Some \<tau>f] \<sigma> s"
  and     a1C_a1U: "\<forall>x y. a1C (a1U (\<lambda>_. y) x) = y"
  and     a1C_o1U: "\<forall>x y. a1C (o1U y x) = a1C x"
  and     o1C_o1U: "\<forall>x y. o1C (o1U (\<lambda>_. y) x) = y"
  and     o1C_a1U: "\<forall>x y. o1C (a1U y x) = o1C x"
  and     cfundef: "cfun = crepeat nC stopC stepC a0C o0C a1C a1U o1U d0 d1"
shows
  "corres state_rel (App (AFun name [] []) (Var i))
    (do x <- cfun v'; gets (\<lambda>s. x) od)
     \<xi>'' \<gamma> \<Xi>' \<Gamma> \<sigma> s"
  apply (rule crepeat_corres_bang[where o1C = o1C, 
        OF \<gamma>len valrel _ _ \<tau>def \<tau>fdef bang\<tau>a bang\<tau>o _ leq determ \<gamma>i fstoptype fsteptype, rotated -1, OF cfundef];
        (simp add: \<Gamma>i \<Xi>name \<xi>''name valrela valrelc a1C_a1U a1C_o1U o1C_o1U o1C_a1U d0corres[simplified] d1corres[simplified])?)
  done

lemmas crepeat_corres_bang_fun_funall = crepeat_corres_bang_all
  [where fstop = "UFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_fun]
lemmas crepeat_corres_bang_fun_afun_all = crepeat_corres_bang_all
  [where fstop = "UFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_absfun]
lemmas crepeat_corres_bang_afun_fun_all = crepeat_corres_bang_all
  [where fstop = "UAFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_fun]
lemmas crepeat_corres_bang_afun_afun_all = crepeat_corres_bang_all
  [where fstop = "UAFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_absfun]

lemmas crepeat_corres_fun_fun_all = crepeat_corres_rel_leq_all
  [where fstop = "UFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _  typing_mono_app_cogent_fun typing_mono_app_cogent_fun]
lemmas crepeat_corres_fun_afun_all = crepeat_corres_rel_leq_all
  [where fstop = "UFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_fun typing_mono_app_cogent_absfun]
lemmas crepeat_corres_afun_fun_all = crepeat_corres_rel_leq_all
  [where fstop = "UAFunction _ _ _" and fstep = "UFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_fun]
lemmas crepeat_corres_afun_afun_all = crepeat_corres_rel_leq_all
  [where fstop = "UAFunction _ _ _" and fstep = "UAFunction _ _ _", simplified,
   OF _ _ _ _ _ _ _ _ _ _ _ typing_mono_app_cogent_absfun typing_mono_app_cogent_absfun]

end (* of context *)

end
