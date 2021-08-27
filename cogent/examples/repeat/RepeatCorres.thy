theory RepeatCorres
  imports
    RepeatAssm
    CorresHelper
    CogentTypingHelper
begin
section "Corres"


context Generated_cogent_shallow begin

lemma dispatch_step:
  "\<And>v' \<sigma> f g acc ra wa obsv ro b c j0 j.
    \<lbrakk>proc_ctx_wellformed \<Xi>; val_rel g FUN_ENUM_log2step;
     upd.uval_typing \<Xi> \<sigma> acc Generated_TypeProof.abbreviatedType1 ra wa; wa \<inter> ro = {};
     upd.uval_typing \<Xi> \<sigma> obsv (TPrim (Num U64)) ro {}\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. j = j0 \<and>
          b = c \<and> val_rel obsv (t2_C.obsv_C c) \<and> j < n_C v' \<and>
          (\<exists>\<sigma>' y. urepeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
              Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
            (\<sigma>', sa) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and>
            (\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
            \<not>(\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))))\<rbrace>
      dispatch_t4' FUN_ENUM_log2step c 
    \<lbrace>\<lambda>y' sb. t2_C.acc_C_update (\<lambda>_. y') b = t2_C.acc_C_update (\<lambda>_. y') c \<and>
            val_rel obsv (t2_C.obsv_C c) \<and>
            j0 + 1 \<le> n_C v' \<and>
            (\<exists>\<sigma>' y.
              urepeat_bod \<xi>_0 (unat (j0 + 1)) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y y') \<and>
            unat (n_C v') - unat (j0 + 1) < unat (n_C v') - unat j\<rbrace>!"
  unfolding dispatch_t4'_def[simplified unknown_bind_ignore]
  apply simp
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (rename_tac s \<sigma>' y)
  apply (cut_tac \<sigma> = \<sigma>' and s = s and a' = c and
      a = "URecord [(y, type_repr Generated_TypeProof.abbreviatedType1),
            (obsv, type_repr (TPrim (Num U64)))]" in corres_log2step[simplified \<Xi>_def[symmetric]])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE, rule \<xi>_0_matchesu_\<Xi>)
  apply (frule_tac \<xi>' = \<xi>_0  and ro = ro and ra = ra and wa = wa and obsv = obsv and acc = acc
      in upd.urepeat_bod_preservation; simp?)
     apply (rule \<xi>_0_matchesu_\<Xi>)
    apply blast
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply clarsimp
  apply (rename_tac r' w')
  apply (erule impE)
   apply (rule_tac x = "r' \<union> ro" in exI)
   apply (rule_tac x = w' in exI)
   apply (simp add: log2step_type_def abbreviated_type_defs)
   apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply blast
  apply clarsimp
  apply (rename_tac res s')
  apply (erule_tac x = res in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule conjI)
   apply unat_arith
  apply (simp only: less_is_non_zero_p1[THEN  unatSuc2])
  apply (rule conjI)
   apply (intro exI conjI; assumption?)
   apply (rule upd.urepeat_bod_step; simp?)
   apply (simp add: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
   apply (intro u_sem_fun)
  apply unat_arith
  done

lemma log2stop_deterministic:
  "\<lbrakk>\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, Generated_TypeProof.log2stop) \<Down>! (\<sigma>', c); d \<noteq> c\<rbrakk>
    \<Longrightarrow> \<not>(\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, App (Fun Generated_TypeProof.log2stop []) (Var 0)) \<Down>! (\<sigma>'', d))"
  "\<lbrakk>\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, Generated_TypeProof.log2stop) \<Down>! (\<sigma>', c); \<sigma>' \<noteq> \<sigma>''\<rbrakk>
    \<Longrightarrow> \<not>(\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, App (Fun Generated_TypeProof.log2stop []) (Var 0)) \<Down>! (\<sigma>'', d))"
  unfolding log2stop_def abbreviatedType1_def
  apply (fastforce elim: u_sem_takeE u_sem_appE u_sem_funE u_sem_afunE u_sem_primE u_sem_consE)+
  done

lemma dispatch_stop:
  "\<And>v' \<sigma> f g acc ra wa obsv ro j b c j'.
    \<lbrakk>proc_ctx_wellformed \<Xi>; val_rel f FUN_ENUM_log2stop; val_rel g FUN_ENUM_log2step;
     upd.uval_typing \<Xi> \<sigma> acc Generated_TypeProof.abbreviatedType1 ra wa; wa \<inter> ro = {};
     upd.uval_typing \<Xi> \<sigma> obsv (TPrim (Num U64)) ro {}\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (\<exists>\<sigma>' y n. (\<sigma>', sa) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and> val_rel obsv (t2_C.obsv_C c) \<and>
            j = j' \<and> b = c \<and> j < n_C v' \<and>
            urepeat_bod \<xi>_0 n (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
              Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
            ((\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))) \<and>
             \<not>(\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False)))
              \<longrightarrow> n \<ge> unat j \<and> n < unat (n_C v')) \<and>
            ((\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
             \<not>(\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)))
              \<longrightarrow> n = unat j))\<rbrace>
      dispatch_t3' FUN_ENUM_log2stop b 
    \<lbrace>\<lambda>x sb.
        (boolean_C x \<noteq> 0 \<longrightarrow>
            (\<exists>\<sigma>' y.
              urepeat_bod \<xi>_0 (unat (n_C v')) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y (t2_C.acc_C c))) \<and>
        (boolean_C x = 0 \<longrightarrow>
            j = j' \<and>
            b = c \<and>
            val_rel obsv (t2_C.obsv_C c) \<and>
            j < n_C v' \<and>
            (\<exists>\<sigma>' y.
              urepeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and>
               (\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
              \<not>(\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)))))\<rbrace>!"
  unfolding dispatch_t3'_def[simplified unknown_bind_ignore]
  apply simp
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (rename_tac s \<sigma>' y n)
  apply (cut_tac \<sigma> = \<sigma>' and s = s and a' = c and
      a = "URecord [(y, type_repr Generated_TypeProof.abbreviatedType1),
            (obsv, type_repr (TPrim (Num U64)))]" in corres_log2stop[simplified \<Xi>_def[symmetric]])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE, rule \<xi>_0_matchesu_\<Xi>)
 apply (frule_tac \<xi>' = \<xi>_0  and ro = ro and ra = ra and wa = wa and obsv = obsv and acc = acc
      in upd.urepeat_bod_preservation; simp?)
     apply (rule \<xi>_0_matchesu_\<Xi>)
    apply blast
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply clarsimp
  apply (rename_tac r' w')
  apply (erule impE, rule_tac x = "r' \<union> ro" in exI)
   apply (rule_tac x = w' in exI)
  apply (simp add: log2stop_type_def abbreviated_type_defs)
   apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply blast
  apply clarsimp
  apply (rename_tac res s')
  apply (erule_tac x = res in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp 
  apply (drule_tac w = "{}" and r = "(r' \<union> w') \<union> ro" and \<tau> = "TPrim Bool" and
      ?\<Gamma>.0 = "[option.Some Generated_TypeProof.abbreviatedType2]"
      in upd.preservation_mono(1)[OF _ _  \<xi>_0_matchesu_\<Xi>]; simp?)
    apply (drule_tac v = y in upd.uval_typing_bang(1))
    apply (clarsimp simp: abbreviated_type_defs)
    apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply (rule log2stop_typecorrect'[simplified fst_conv snd_conv log2stop_type_def])
  apply clarsimp
  apply (frule_tac v = r in upd.tprim_no_pointers(1))
  apply (drule_tac v = r in upd.tprim_no_pointers(2))
  apply clarsimp
  apply (drule upd.frame_empty; clarsimp)
  apply (rule conjI; clarsimp simp: val_rel_bool_t_C_def)
  apply (erule impE)
    apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
    apply (rule conjI)
     apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
     apply (intro u_sem_fun)
    apply (drule_tac d = "UPrim (LBool False)" and \<sigma>'' = \<sigma>'' in log2stop_deterministic(1);simp)
   apply (intro exI conjI; simp?)
   apply (rule_tac i = n in upd.urepeat_bod_early_termination; simp add: word_less_nat_alt)
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
    apply (intro u_sem_fun)
  apply (thin_tac "_ \<longrightarrow> _")
  apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
  apply (frule_tac d = "UPrim (LBool True)" and \<sigma>'' = \<sigma>'' in log2stop_deterministic(1);simp)
  apply (erule impE)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
   apply (intro u_sem_fun)
  apply (intro exI conjI; simp)
  apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
  apply (intro u_sem_fun)
  done


lemma repeat_corres:
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>stop_C v' = FUN_ENUM_log2stop; step_C v' = FUN_ENUM_log2step; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd repeat_0_type))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_0'' []) (Var i)) (do x <- repeat_0' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (rule absfun_corres; simp?)
   prefer 2
  \<comment>\<open>For automation, make a repeat_type_defs lemma\<close>
   apply (clarsimp simp: repeat_0_type_def abbreviated_type_defs \<Xi>_def)
  apply (subst abs_fun_rel_def'; clarsimp)
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def; clarsimp)
  apply (clarsimp simp: repeat_0_type_def)
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (rename_tac r w n rn f rf g rg acc racc obsv robsv)
  apply (subst (asm) val_rel_word64; clarsimp)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (frule upd.tprim_no_pointers(1); clarsimp)
  apply (frule upd.tprim_no_pointers(2); clarsimp)
  apply (frule upd.tfun_no_pointers(1); clarsimp)
  apply (drule upd.tfun_no_pointers(2); clarsimp)
  apply (frule upd.tfun_no_pointers(1); clarsimp)
  apply (drule upd.tfun_no_pointers(2); clarsimp)
  apply (rename_tac f g acc ra wa obsv ro wo)
  apply (frule_tac v = obsv and K' = "[]" in upd.discardable_or_shareable_not_writable'(1)[rotated 2]; simp?)
    apply (rule kindingI; simp)
   apply blast
  apply clarsimp
  unfolding repeat_0'_def
  apply (clarsimp simp: L2polish unknown_bind_ignore)
  apply (subst \<xi>1_def; clarsimp simp: urepeat_def)
  apply (subgoal_tac "is_uvalfun f \<and>
               is_uvalfun g \<and>
               \<Xi>, [], [Some (TRecord
                               [(''acc'', bang Generated_TypeProof.abbreviatedType1, Present),
                                (''obsv'', TPrim (Num U64), Present)]
                               Unboxed)] \<turnstile> App (uvalfun_to_expr f) (Var 0) : TPrim Bool \<and>
               \<Xi>, [], [Some (TRecord
                               [(''acc'', Generated_TypeProof.abbreviatedType1, Present), (''obsv'', TPrim (Num U64), Present)]
                               Unboxed)] \<turnstile> App (uvalfun_to_expr g) (Var 0) : Generated_TypeProof.abbreviatedType1")
   apply simp
   apply (thin_tac "_ \<and> _ \<and> _ \<and> _")
   defer
   apply (clarsimp simp: val_rel_simp cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
    apply (rule log2stop_typecorrect'[simplified snd_conv fst_conv log2stop_type_def abbreviated_type_defs])
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply (wp; (clarsimp split: prod.splits)?)
     apply (rename_tac breakval)
     apply (rule_tac 
      I = "\<lambda>(a, b, c, j) s. b = c \<and> val_rel obsv (t2_C.obsv_C c) \<and> j \<le> n_C v' \<and>
            (\<exists>\<sigma>' y. urepeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                    Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
                   (\<sigma>', s) \<in> state_rel \<and> val_rel y (t2_C.acc_C c))" and
      M = "\<lambda>((_,_,_, j), _). unat (n_C v') - unat j" in whileLoopE_add_invI)
     apply (wp; clarsimp split: prod.splits)
         apply (rename_tac s' prev0 b1 c2 j2 b c1 j1 c j0 bool prev b0 c0 j)
         apply (wp dispatch_step; clarsimp)
        apply clarsimp
        apply (wp; clarsimp)
       apply clarsimp
       apply (wp; simp?)
       apply (wp dispatch_stop; clarsimp)
     apply clarsimp
     apply (intro exI conjI; simp?; clarsimp simp: word_less_nat_alt)
    apply wp
   apply (rule validNF_select_UNIV)
  apply clarsimp
  done
(* 
lemma dispatch_step:
  "\<And>v' \<sigma> f g acc ra wa obsv ro b c j0 j.
    \<lbrakk>proc_ctx_wellformed \<Xi>; val_rel g FUN_ENUM_log2step;
     upd.uval_typing \<Xi> \<sigma> acc Generated_TypeProof.abbreviatedType1 ra wa; wa \<inter> ro = {};
     upd.uval_typing \<Xi> \<sigma> obsv (TPrim (Num U64)) ro {}\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. j = j0 \<and>
          b = c \<and> val_rel obsv (t2_C.obsv_C c) \<and> j < n_C v' \<and>
          (\<exists>\<sigma>' y. repeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
              Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
            (\<sigma>', sa) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and>
            (\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
            \<not>(\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))))\<rbrace>
      dispatch_t4' FUN_ENUM_log2step c 
    \<lbrace>\<lambda>y' sb. t2_C.acc_C_update (\<lambda>_. y') b = t2_C.acc_C_update (\<lambda>_. y') c \<and>
            val_rel obsv (t2_C.obsv_C c) \<and>
            j0 + 1 \<le> n_C v' \<and>
            (\<exists>\<sigma>' y.
              repeat_bod \<xi>_0 (unat (j0 + 1)) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y y') \<and>
            unat (n_C v') - unat (j0 + 1) < unat (n_C v') - unat j\<rbrace>!"
  unfolding dispatch_t4'_def[simplified unknown_bind_ignore]
  apply simp
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (rename_tac s \<sigma>' y)
  apply (cut_tac \<sigma> = \<sigma>' and s = s and a' = c and
      a = "URecord [(y, type_repr Generated_TypeProof.abbreviatedType1),
            (obsv, type_repr (TPrim (Num U64)))]" in corres_log2step[simplified \<Xi>_def[symmetric]])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE, rule \<xi>_0_matchesu_\<Xi>)
  apply (frule_tac \<xi>' = \<xi>_0  and ro = ro and ra = ra and wa = wa and obsv = obsv and acc = acc
      in repeat_bod_preservation; simp?)
     apply (rule \<xi>_0_matchesu_\<Xi>)
    apply blast
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply clarsimp
  apply (rename_tac r' w')
(*
  apply (cut_tac \<Xi> = \<Xi> and \<sigma> = \<sigma>' and r = "r' \<union> ro" and w = w' and
      vs = "[y, obsv]" and
      ns = "[''acc'', ''obsv'']" and
      ts = "[Generated_TypeProof.abbreviatedType1, TPrim (Num U64)]" in upd.uval_typing_all_record; simp?)
   apply (intro upd.u_t_all_cons[where xs= "[_]" and ts = "[_]" and w' = "{}", simplified]
      upd.u_t_all_cons[where xs= "[]" and ts = "[]" and w' = "{}" and r' = "{}", simplified]
      upd.u_t_all_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply blast
*)
  apply (erule impE)
   apply (rule_tac x = "r' \<union> ro" in exI)
   apply (rule_tac x = w' in exI)
   apply (simp add: log2step_type_def abbreviated_type_defs)
   apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply blast
  apply clarsimp
  apply (rename_tac res s')
  apply (erule_tac x = res in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule conjI)
   apply unat_arith
  apply (simp only: less_is_non_zero_p1[THEN  unatSuc2])
  apply (rule conjI)
   apply (intro exI conjI; assumption?)
   apply (rule repeat_bod_step; simp?)
   apply (simp add: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
   apply (intro u_sem_fun)
  apply unat_arith
  done

inductive_cases u_sem_appE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,App x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_funE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Fun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_afunE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,AFun x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_primE: "\<xi>',\<gamma> \<turnstile> (\<sigma>,Prim x y)\<Down>! (\<sigma>',v)"
inductive_cases u_sem_consE: "\<xi>',\<gamma> \<turnstile>* (\<sigma>,xs)\<Down>! (\<sigma>',v)"

lemma log2stop_deterministic:
  "\<lbrakk>\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, Generated_TypeProof.log2stop) \<Down>! (\<sigma>', c); d \<noteq> c\<rbrakk>
    \<Longrightarrow> \<not>(\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, App (Fun Generated_TypeProof.log2stop []) (Var 0)) \<Down>! (\<sigma>'', d))"
  "\<lbrakk>\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, Generated_TypeProof.log2stop) \<Down>! (\<sigma>', c); \<sigma>' \<noteq> \<sigma>''\<rbrakk>
    \<Longrightarrow> \<not>(\<xi>_0, [URecord [(a, f), (b, g)]] \<turnstile> (\<sigma>, App (Fun Generated_TypeProof.log2stop []) (Var 0)) \<Down>! (\<sigma>'', d))"
  unfolding log2stop_def abbreviatedType1_def
  apply (fastforce elim: u_sem_takeE u_sem_appE u_sem_funE u_sem_afunE u_sem_primE u_sem_consE)+
  done

lemma dispatch_stop:
  "\<And>v' \<sigma> f g acc ra wa obsv ro j b c j'.
    \<lbrakk>proc_ctx_wellformed \<Xi>; val_rel f FUN_ENUM_log2stop; val_rel g FUN_ENUM_log2step;
     upd.uval_typing \<Xi> \<sigma> acc Generated_TypeProof.abbreviatedType1 ra wa; wa \<inter> ro = {};
     upd.uval_typing \<Xi> \<sigma> obsv (TPrim (Num U64)) ro {}\<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>sa. (\<exists>\<sigma>' y n. (\<sigma>', sa) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and> val_rel obsv (t2_C.obsv_C c) \<and>
            j = j' \<and> b = c \<and> j < n_C v' \<and>
            repeat_bod \<xi>_0 n (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
              Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
            ((\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True))) \<and>
             \<not>(\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False)))
              \<longrightarrow> n \<ge> unat j \<and> n < unat (n_C v')) \<and>
            ((\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
             \<not>(\<xi>_0 , [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)),
                (obsv, type_repr (TPrim (Num U64)))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)))
              \<longrightarrow> n = unat j))\<rbrace>
      dispatch_t3' FUN_ENUM_log2stop b 
    \<lbrace>\<lambda>x sb.
        (boolean_C x \<noteq> 0 \<longrightarrow>
            (\<exists>\<sigma>' y.
              repeat_bod \<xi>_0 (unat (n_C v')) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y (t2_C.acc_C c))) \<and>
        (boolean_C x = 0 \<longrightarrow>
            j = j' \<and>
            b = c \<and>
            val_rel obsv (t2_C.obsv_C c) \<and>
            j < n_C v' \<and>
            (\<exists>\<sigma>' y.
              repeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
              (\<sigma>', sb) \<in> state_rel \<and> val_rel y (t2_C.acc_C c) \<and>
               (\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool False))) \<and>
              \<not>(\<xi>_0, [URecord [(y, type_repr (bang Generated_TypeProof.abbreviatedType1)), (obsv, RPrim (Num U64))]]
                \<turnstile> (\<sigma>', App (uvalfun_to_expr f) (Var 0)) \<Down>! (\<sigma>', UPrim (LBool True)))))\<rbrace>!"
  unfolding dispatch_t3'_def[simplified unknown_bind_ignore]
  apply simp
  apply (clarsimp simp: validNF_def valid_def no_fail_def)
  apply (subst all_imp_conj_distrib[symmetric]; clarsimp)
  apply (rename_tac s \<sigma>' y n)
  apply (cut_tac \<sigma> = \<sigma>' and s = s and a' = c and
      a = "URecord [(y, type_repr Generated_TypeProof.abbreviatedType1),
            (obsv, type_repr (TPrim (Num U64)))]" in corres_log2stop[simplified \<Xi>_def[symmetric]])
   apply (clarsimp simp: val_rel_simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE, rule \<xi>_0_matchesu_\<Xi>)
 apply (frule_tac \<xi>' = \<xi>_0  and ro = ro and ra = ra and wa = wa and obsv = obsv and acc = acc
      in repeat_bod_preservation; simp?)
     apply (rule \<xi>_0_matchesu_\<Xi>)
    apply blast
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply clarsimp
  apply (rename_tac r' w')
  apply (erule impE, rule_tac x = "r' \<union> ro" in exI)
   apply (rule_tac x = w' in exI)
  apply (simp add: log2stop_type_def abbreviated_type_defs)
   apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply blast
  apply clarsimp
  apply (rename_tac res s')
  apply (erule_tac x = res in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp 
  apply (drule_tac w = "{}" and r = "(r' \<union> w') \<union> ro" and \<tau> = "TPrim Bool" and
      ?\<Gamma>.0 = "[option.Some Generated_TypeProof.abbreviatedType2]"
      in upd.preservation_mono(1)[OF _ _  \<xi>_0_matchesu_\<Xi>]; simp?)
    apply (drule_tac v = y in upd.uval_typing_bang(1))
    apply (clarsimp simp: abbreviated_type_defs)
    apply (intro upd.matches_ptrs_some[where r' = "{}" and w' = "{}", simplified]
      upd.matches_ptrs_empty[where \<tau>s = "[]", simplified]
      upd.u_t_struct
      upd.u_t_r_cons1[where w' = "{}", simplified]
      upd.u_t_r_cons1[where r' = "{}" and w' = "{}", simplified]
      upd.u_t_r_empty; simp?)
    apply (drule_tac u = obsv in upd.uval_typing_frame(1); simp?)
    apply blast
   apply (drule_tac v = obsv in upd.frame_noalias_uval_typing'(2); simp?)
    apply blast
   apply (rule log2stop_typecorrect'[simplified fst_conv snd_conv log2stop_type_def])
  apply clarsimp
  apply (frule_tac v = r in upd.tprim_no_pointers(1))
  apply (drule_tac v = r in upd.tprim_no_pointers(2))
  apply clarsimp
  apply (drule upd.frame_empty; clarsimp)
  apply (rule conjI; clarsimp simp: val_rel_bool_t_C_def)
  apply (erule impE)
    apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
    apply (rule conjI)
     apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
     apply (intro u_sem_fun)
    apply (drule_tac d = "UPrim (LBool False)" and \<sigma>'' = \<sigma>'' in log2stop_deterministic(1);simp)
   apply (intro exI conjI; simp?)
   apply (rule_tac i = n in repeat_bod_early_termination; simp add: word_less_nat_alt)
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
    apply (intro u_sem_fun)
   apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
   apply (drule_tac d = "UPrim (LBool False)" and \<sigma>'' = \<sigma>'' in log2stop_deterministic(1);simp)
  apply (thin_tac "_ \<longrightarrow> _")
  apply (clarsimp simp: val_rel_fun_tag cogent_function_val_rel untyped_func_enum_defs abbreviated_type_defs)
  apply (frule_tac d = "UPrim (LBool True)" and \<sigma>'' = \<sigma>'' in log2stop_deterministic(1);simp)
  apply (erule impE)
   apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
   apply (intro u_sem_fun)
  apply (intro exI conjI; simp)
  apply (rule u_sem_app[where ts ="[]" and y = "Var 0" and \<gamma> = "[_]",
        simplified,OF _ u_sem_var, simplified]; simp?)
  apply (intro u_sem_fun)
  done

lemma 
  "\<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>stop_C v' = FUN_ENUM_log2stop; step_C v' = FUN_ENUM_log2step; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = Some (fst (snd repeat_0_type))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''repeat_0'' []) (Var i)) (do x <- repeat_0' v';
 gets (\<lambda>s. x)
                                                               od)
         \<xi>_1 \<gamma> \<Xi> \<Gamma> \<sigma> s"
  apply (rule absfun_corres; simp?)
   prefer 2
  \<comment>\<open>For automation, make a repeat_type_defs lemma\<close>
   apply (clarsimp simp: repeat_0_type_def abbreviated_type_defs \<Xi>_def)
  apply (subst abs_fun_rel_def'; clarsimp)
  apply (rotate_tac -1)
  apply (subst (asm) \<Xi>_def; clarsimp)
  apply (clarsimp simp: repeat_0_type_def)
  apply (subst (asm) val_rel_simp; clarsimp)
  apply (rename_tac r w n rn f rf g rg acc racc obsv robsv)
  apply (subst (asm) val_rel_word64; clarsimp)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE; clarsimp)
  apply (frule upd.tprim_no_pointers(1); clarsimp)
  apply (frule upd.tprim_no_pointers(2); clarsimp)
  apply (frule upd.tfun_no_pointers(1); clarsimp)
  apply (drule upd.tfun_no_pointers(2); clarsimp)
  apply (frule upd.tfun_no_pointers(1); clarsimp)
  apply (drule upd.tfun_no_pointers(2); clarsimp)
  apply (rename_tac f g acc ra wa obsv ro wo)
  apply (frule_tac v = obsv and K' = "[]" in upd.discardable_or_shareable_not_writable'(1)[rotated 2]; simp?)
    apply (rule kindingI; simp)
   apply blast
  apply clarsimp
  unfolding repeat_0'_def
  apply (clarsimp simp: L2polish unknown_bind_ignore)
  apply (subst \<xi>1_def; clarsimp simp: repeat_def)
  apply (subgoal_tac "is_uvalfun f \<and>
               is_uvalfun g \<and>
               \<Xi>, [], [Some (TRecord
                               [(''acc'', bang Generated_TypeProof.abbreviatedType1, Present),
                                (''obsv'', TPrim (Num U64), Present)]
                               Unboxed)] \<turnstile> App (uvalfun_to_expr f) (Var 0) : TPrim Bool \<and>
               \<Xi>, [], [Some (TRecord
                               [(''acc'', Generated_TypeProof.abbreviatedType1, Present), (''obsv'', TPrim (Num U64), Present)]
                               Unboxed)] \<turnstile> App (uvalfun_to_expr g) (Var 0) : Generated_TypeProof.abbreviatedType1")
   apply simp
   apply (thin_tac "_ \<and> _ \<and> _ \<and> _")
   defer
   apply (clarsimp simp: val_rel_simp cogent_function_val_rel untyped_func_enum_defs)
   apply (intro conjI typing_mono_app_cogent_fun; clarsimp simp: abbreviated_type_defs)
    apply (rule log2stop_typecorrect'[simplified snd_conv fst_conv log2stop_type_def abbreviated_type_defs])
   apply (rule log2step_typecorrect'[simplified snd_conv fst_conv log2step_type_def abbreviated_type_defs])
  apply (wp; (clarsimp split: prod.splits)?)
     apply (rename_tac breakval)
     apply (rule_tac 
      I = "\<lambda>(a, b, c, j) s. b = c \<and> val_rel obsv (t2_C.obsv_C c) \<and> j \<le> n_C v' \<and>
            (\<exists>\<sigma>' y. repeat_bod \<xi>_0 (unat j) (uvalfun_to_expr f) (uvalfun_to_expr g) \<sigma> \<sigma>'
                    Generated_TypeProof.abbreviatedType1 acc (TPrim (Num U64)) obsv y \<and>
                   (\<sigma>', s) \<in> state_rel \<and> val_rel y (t2_C.acc_C c))" and
      M = "\<lambda>((_,_,_, j), _). unat (n_C v') - unat j" in whileLoopE_add_invI)
     apply (wp; clarsimp split: prod.splits)
         apply (rename_tac s' prev0 b1 c2 j2 b c1 j1 c j0 bool prev b0 c0 j)
         apply (wp dispatch_step; clarsimp)
        apply clarsimp
        apply (wp; clarsimp)
       apply clarsimp
       apply (wp; simp?)
       apply (wp dispatch_stop; clarsimp)
     apply clarsimp
     apply (intro exI conjI; simp?; clarsimp simp: word_less_nat_alt)
    apply wp
   apply (rule validNF_select_UNIV)
  apply clarsimp
  done
*)
end (* of context *)
end
