theory RepeatMono
  imports 
    Cogent.Mono
    RepeatValue
    MonoHelper
begin

section "Repeat loop definition"

text "Wrapper with extra checks:
  Summary:
    Checks the arguments are of the correct form and then passes these to
    @{term vrepeat_bod} with minor processing.
  Checks:
    * The functions f and g are of the form."

definition prepeat
  where
"prepeat \<xi>' x y =
  (\<exists>n f g acc obsv ret.
    x = VRecord [VPrim (LU64 n), f, g, acc, obsv] \<and>
    y = ret \<and>
    is_vvalfun f \<and>
    is_vvalfun g \<and>
    vrepeat_bod \<xi>' (unat n) (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv ret)"

section "Monomorphisation lemmas"

context value_sem begin

lemma vrepeat_bod_monoexpr_correct:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches \<Xi>';
    rename_mono_prog rename' \<Xi>' \<xi>' \<xi>'';
    \<Xi>' \<turnstile> (rename_val rename' (monoval acc)) :v \<tau>a;
    \<Xi>' \<turnstile> (rename_val rename' (monoval obsv)) :v \<tau>o;
    is_vvalfun (rename_val rename' (monoval f));
    is_vvalfun (rename_val rename' (monoval g));
    vrepeat_bod \<xi>' n (vvalfun_to_expr (rename_val rename' (monoval f))) 
      (vvalfun_to_expr (rename_val rename' (monoval g))) (rename_val rename' (monoval acc))
      (rename_val rename' (monoval obsv)) ret;
        \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] 
      \<turnstile> (App (vvalfun_to_expr (rename_val rename' (monoval f))) (Var 0)) : TPrim Bool;
    \<Xi>', 0, [], {}, [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] 
      \<turnstile> (App (vvalfun_to_expr (rename_val rename' (monoval g))) (Var 0)) : \<tau>a\<rbrakk>
  \<Longrightarrow> is_vvalfun f \<and> is_vvalfun g \<and> (\<exists>ret'. ret = rename_val rename' (monoval ret') \<and>
         vrepeat_bod \<xi>'' n (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv ret')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (rule conjI)
   apply (case_tac g; clarsimp)
  apply (induct n arbitrary: acc)
   apply clarsimp
  apply clarsimp
  apply (rename_tac n acc b)
  apply (case_tac b; clarsimp)
   apply (rule exI, rule conjI, simp)
   apply (rule_tac x = b in exI; clarsimp)
   apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and
      v' = "VPrim (LBool True)" and
      e = "App (vvalfun_to_expr f) (Var 0)" and
      \<tau> = "TPrim Bool" and 
      ?\<Gamma>.0 = "[Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]"
      in rename_monoexpr_correct(1); simp add: matches_def)
      apply (intro v_t_record v_t_r_cons1 v_t_r_empty vval_typing_bang(1); simp?)
     apply (case_tac f; clarsimp)
    apply (case_tac f; clarsimp)
   apply clarsimp
   apply (rename_tac v)
   apply (case_tac v; clarsimp)
  apply (rename_tac acc')
  apply (frule_tac \<gamma> = "[VRecord [acc, obsv]]" and
      v' = "VPrim (LBool False)" and
      e = "App (vvalfun_to_expr f) (Var 0)" and
      \<tau> = "TPrim Bool" and 
      ?\<Gamma>.0 = "[Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]"
      in rename_monoexpr_correct(1); simp add: matches_def)
     apply (intro v_t_record v_t_r_cons1 v_t_r_empty vval_typing_bang(1); simp?)
    apply (case_tac f; clarsimp)
   apply (case_tac f; clarsimp)
  apply clarsimp
  apply (frule_tac \<gamma> = "[VRecord [acc, obsv]]" and
      v' = acc' and
      e = "App (vvalfun_to_expr g) (Var 0)" and
      \<tau> = \<tau>a and 
      ?\<Gamma>.0 = "[Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]"
      in rename_monoexpr_correct(1); simp add: matches_def)
     apply (intro v_t_record v_t_r_cons1 v_t_r_empty vval_typing_bang(1); simp?)
    apply (case_tac g; clarsimp)
   apply (case_tac g; clarsimp)
  apply clarsimp
  apply (rename_tac v acc')
  apply (drule_tac
      e = "App (vvalfun_to_expr (rename_val rename' (monoval g))) (Var 0)" and
      ?\<Gamma>.0 = "[Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]"
      in preservation(1)[where \<tau>s = "[]" and  K = "[]" , OF subst_wellformed_nothing,
         simplified, rotated -2]; 
     (simp add: matches_def)?)
   apply (intro v_t_record v_t_r_cons1 v_t_r_empty; simp?)
  apply (elim meta_allE meta_impE; assumption?)
  apply clarsimp
  apply (rename_tac ret')
  apply (rule exI, rule conjI, simp)
  apply (rule_tac x = b in exI; clarsimp)
  apply (case_tac v; clarsimp)
  apply (intro exI conjI; assumption)
  done

lemma prepeat_monoexpr_correct:
  "\<And>v v'.
       \<lbrakk>proc_ctx_wellformed \<Xi>';
        \<xi>' matches \<Xi>';
        rename_mono_prog rename' \<Xi>' \<xi>' \<xi>'';
        vrepeat \<Xi>' \<xi>' \<tau>a \<tau>o (rename_val rename' (monoval v)) v'\<rbrakk>
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> prepeat \<xi>'' v v''"
  unfolding vrepeat_def prepeat_def
  apply clarsimp
  apply (rename_tac v v' n f g acc obsv)
  apply (case_tac v; clarsimp)
  apply (rename_tac z za zb zc zd)
  apply (case_tac z; clarsimp)
  apply (drule_tac \<xi>'' = \<xi>'' in vrepeat_bod_monoexpr_correct[rotated 7]; simp?)
  done

end (* of context *)

subsection "Determinism"

lemma prepeat_deterministic:
  "\<lbrakk>determ \<xi>;
    prepeat \<xi> x y;
    prepeat \<xi> x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding prepeat_def
  apply clarsimp
  apply (drule (3) vrepeat_bod_deterministic)
  done

subsection "Ordering"

lemma prepeat_rel_leqD:
  "\<lbrakk>rel_leq \<xi>a \<xi>b;
    prepeat \<xi>a x y\<rbrakk>
    \<Longrightarrow> prepeat \<xi>b x y"
  unfolding prepeat_def
  apply clarsimp
  apply (drule (2) vrepeat_bod_rel_leqD)
  done

end