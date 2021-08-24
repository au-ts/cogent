theory RepeatValue
  imports "build/Generated_AllRefine"
begin

fun vrepeat_bod
  where
"vrepeat_bod _ 0 _ _ acc _ ret = (acc = ret)" |
"vrepeat_bod \<xi>' (Suc n) f g acc obsv ret =
  (if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False))
    then acc = ret
  else if (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool False)) \<and>
      \<not>(\<xi>' , [VRecord [acc, obsv]] \<turnstile> App f (Var 0) \<Down> VPrim (LBool True))
    then (\<exists>acc'. (\<xi>' , [VRecord [acc, obsv]] \<turnstile> App g (Var 0) \<Down> acc') \<and>
      vrepeat_bod \<xi>' n f g acc' obsv ret)
  else False)"

fun is_vvalfun
  where
"is_vvalfun (VFunction _ _) = True" |
"is_vvalfun (VAFunction _ _) = True" |
"is_vvalfun _  = False"

fun vvalfun_to_expr
  where
"vvalfun_to_expr (VFunction f ts) = Fun f ts" |
"vvalfun_to_expr (VAFunction f ts) = AFun f ts" |
"vvalfun_to_expr _ = undefined"

context value_sem begin
definition
  rename_mono_prog' ::
  "(('f \<times> type list) \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> poly_type) \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> ('f, 'a) vabsfuns \<Rightarrow> bool"
where
  "rename_mono_prog' rename' \<Xi>' \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p \<equiv>
     \<xi>\<^sub>r\<^sub>m matches \<Xi>' \<longrightarrow>
     proc_ctx_wellformed \<Xi>' \<longrightarrow>
     (\<forall>f ts v v' v''. \<xi>\<^sub>r\<^sub>m (rename' (f, ts)) (rename_val rename' (monoval v)) v'' \<longrightarrow>
        (\<xi>\<^sub>p f v v' \<longrightarrow>  v'' = (rename_val rename' (monoval v'))) \<and> (\<exists>v'. \<xi>\<^sub>p f v v'))"

lemma
  "rename_mono_prog' rename' \<Xi>' \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p \<Longrightarrow> rename_mono_prog rename' \<Xi>' \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p"
  unfolding rename_mono_prog_def rename_mono_prog'_def
  apply clarsimp
  apply (erule_tac x = f in allE)
  apply (erule_tac x = ts in allE)
  apply (subgoal_tac "\<exists>v'. \<xi>\<^sub>p f v v'")
   apply (erule exE)
   apply (erule_tac x = v in allE)
   apply (erule_tac x = v'a in allE)
   apply (erule_tac x = v' in allE)
   apply clarsimp
   apply (intro exI conjI; simp)
  apply clarsimp
  done

end (* of context *)
context shallow begin
lemma vrepeat_bod_preservation:
  "\<lbrakk>proc_ctx_wellformed \<Xi>';
    \<xi>' matches \<Xi>';
    \<Xi>' \<turnstile> acc :v \<tau>a;
    \<Xi>' \<turnstile> obsv :v \<tau>o;
    vrepeat_bod \<xi>' n f g acc obsv ret;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] \<turnstile> (App g (Var 0)) : \<tau>a\<rbrakk>
      \<Longrightarrow> \<Xi>' \<turnstile> ret :v \<tau>a"
  apply (induct arbitrary: rule: vrepeat_bod.induct[of _ \<xi>' n f g acc obsv ret])
   apply clarsimp
  apply (clarsimp split: if_splits)
  apply (drule_tac x = acc' in meta_spec; clarsimp)
  apply (drule_tac \<gamma> = "[VRecord [acc, obsv]]" and v = acc' in preservation(1)[of "[]" "[]", simplified]; simp?)
   apply (clarsimp simp: matches_def)
   apply (rule v_t_record; simp?)
   apply (rule v_t_r_cons1; simp?)+
   apply (rule v_t_r_empty)
  apply (drule meta_mp; simp)
  done

lemma vrepeat_monocorrect:
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
        \<Xi>', [], [option.Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] 
      \<turnstile> (App (vvalfun_to_expr (rename_val rename' (monoval f))) (Var 0)) : TPrim Bool;
    \<Xi>', [], [option.Some (TRecord [(''acc'', \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)] 
      \<turnstile> (App (vvalfun_to_expr (rename_val rename' (monoval g))) (Var 0)) : \<tau>a\<rbrakk>
  \<Longrightarrow> is_vvalfun f \<and> is_vvalfun g \<and> (\<exists>ret'. ret = rename_val rename' (monoval ret') \<and>
         vrepeat_bod \<xi>'' n (vvalfun_to_expr f) (vvalfun_to_expr g) acc obsv ret')"
  apply (rule conjI)
   apply (case_tac f; clarsimp)
  apply (rule conjI)
   apply (case_tac g; clarsimp)
  apply (induct n arbitrary: ret)
   apply clarsimp
  apply (clarsimp split: if_splits)
   (*apply (rule_tac x = acc in exI)
   apply clarsimp
   apply (rule conjI; clarsimp)*)
 (*  apply (frule_tac 
      \<gamma> = "[VRecord [acc, obsv]]" and
      ?\<Gamma>.0 = " [Some (TRecord [(''acc'', bang \<tau>a, Present), (''obsv'', \<tau>o, Present)] Unboxed)]" and
      e = "App (vvalfun_to_expr f) (Var 0)" and
      v' = "VPrim (LBool True)" and
      \<tau> = "TPrim Bool"
      in rename_monoexpr_correct(1); simp?)
      apply (clarsimp simp: matches_def)
      apply (intro v_t_record v_t_r_cons1 v_t_r_empty; simp?)
      apply (rule vval_typing_bang(1); assumption)
     apply (case_tac f; clarsimp)
    apply (case_tac f; clarsimp)
   apply clarsimp
   apply (rename_tac v)*)
   apply (rule_tac x = acc in exI)
   apply (rule conjI; clarsimp)
(*
    apply (case_tac v; clarsimp)
*)
  defer
   apply (case_tac " \<xi>'' , [VRecord [acc, obsv]] \<turnstile> App (vvalfun_to_expr f) (Var 0) \<Down> VPrim (LBool False)")
    apply (erule impE, assumption)
    apply clarsimp
  (*  apply (case_tac v; clarsimp) *)
  thm  scorres_def

  oops
(*


    value_sem.rename_mono_prog wa_abs_typing_v rename' \<Xi>' \<xi>\<^sub>m \<xi>\<^sub>p;
    val_wa_foldnb_bod \<xi>\<^sub>m t xs frm to (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) 
      (val.rename_val rename' (val.monoval acc )) (val.rename_val rename' (val.monoval obsv)) r;
    is_vval_fun (val.rename_val rename' (val.monoval f)); wa_abs_typing_v (VWA t xs) ''WordArray'' [t]; 
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval acc )) u;
    val.vval_typing \<Xi>' (val.rename_val rename' (val.monoval obsv)) v;
    \<Xi>', [], [option.Some (TRecord [(a0, t, Present), (a1, u, Present), (a2, v, Present)] Unboxed)] \<turnstile>
      App (vvalfun_to_exprfun (val.rename_val rename' (val.monoval f))) (Var 0) : u; 
    distinct [a0, a1, a2]\<rbrakk>
       \<Longrightarrow> is_vval_fun f \<and> (\<exists>r'. r = val.rename_val rename' (val.monoval r') \<and>
         val_wa_foldnb_bod \<xi>\<^sub>p t xs frm to (vvalfun_to_exprfun f) acc obsv r')*)

lemma rename_monoexpr_correct':
  assumes "proc_ctx_wellformed \<Xi>'"
  and     "\<xi>\<^sub>r\<^sub>m matches \<Xi>'"
  and     "rename_mono_prog' rename' \<Xi>' \<xi>\<^sub>r\<^sub>m \<xi>\<^sub>p"
  and     "\<Xi>' \<turnstile> map (rename_val rename' \<circ> monoval) \<gamma> matches \<Gamma>"
  shows   "\<xi>\<^sub>r\<^sub>m, map (rename_val rename' \<circ> monoval) \<gamma> \<turnstile> rename_expr rename' (monoexpr e) \<Down> v' \<Longrightarrow>
             \<Xi>', [], \<Gamma> \<turnstile> rename_expr rename' (monoexpr e) : \<tau>  \<Longrightarrow>
              \<xi>\<^sub>p, \<gamma> \<turnstile> e \<Down>  v \<Longrightarrow>
              v' = rename_val rename' (monoval v)"
  and     "\<xi>\<^sub>r\<^sub>m, map (rename_val rename' \<circ> monoval) \<gamma> \<turnstile>* map (rename_expr rename' \<circ> monoexpr) es \<Down> vs' \<Longrightarrow>
             \<Xi>', [], \<Gamma> \<turnstile>* map (rename_expr rename' \<circ> monoexpr) es : \<tau>s \<Longrightarrow>
             (\<xi>\<^sub>p , \<gamma> \<turnstile>* es \<Down> vs) \<Longrightarrow>
             vs' = (map (rename_val rename' \<circ> monoval) vs)"
  using assms
  proof (induct \<xi>\<^sub>r\<^sub>m "map (rename_val rename' \<circ> monoval) \<gamma>" "rename_expr rename' (monoexpr e)" v'
            and \<xi>\<^sub>r\<^sub>m "map (rename_val rename' \<circ> monoval) \<gamma>" "map (rename_expr rename' \<circ> monoexpr) es" vs'
         arbitrary: \<tau> \<Gamma> \<gamma> e v
           and \<tau>s \<Gamma> \<gamma> es vs
         rule: v_sem_v_sem_all.inducts)
    case (v_sem_var \<xi> i)
    then show ?case
      by (cases e) (force intro: v_sem_v_sem_all.v_sem_var dest: matches_length)+
  next
    case (v_sem_lit \<xi> l)
    then show ?case 
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_lit)
      apply (erule v_sem_litE; clarsimp)
      done
  next
    case (v_sem_prim \<xi> as as' p)
    then show ?case
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_lit)
      apply (erule v_sem_primE; clarsimp)
      apply (erule typing_primE; clarsimp)
      apply (drule_tac x = \<gamma> in meta_spec)
      apply (rename_tac e' bs ts t)
      apply (drule_tac x = e' and y = \<Gamma> in meta_spec2; clarsimp)
      apply (drule_tac x = "map TPrim ts" and y = bs in meta_spec2; clarsimp)
      apply (frule(4) preservation(2) [where \<tau>s = "[]" and K = "[]", simplified])
      apply (frule v_t_map_TPrimD)
      apply clarsimp
      apply (frule eval_prim_preservation)
       apply simp
      apply (erule vval_typing.cases, simp_all)
      apply (drule map_rename_monoval_prim_prim)
      apply clarsimp
      done
  next
    case (v_sem_fun \<xi> f ts)
    then show ?case 
      by (cases e) (auto intro: v_sem_v_sem_all.v_sem_fun)
  next
    case (v_sem_afun \<xi> f ts)
    then show ?case
      by (cases e) (auto intro: v_sem_v_sem_all.v_sem_afun)
  next
    case (v_sem_abs_app \<xi> x f ts y a r)
    then show ?case
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_con)
      apply (rename_tac b c)
      apply (drule_tac x = \<gamma> in meta_spec)
      apply (drule_tac x = \<gamma> in meta_spec)
      apply (erule typing_appE; clarsimp)
      apply (drule_tac x = b in meta_spec)
      apply (drule_tac x = c in meta_spec)
      apply clarsimp
      apply (rename_tac \<Gamma>1 \<Gamma>2 t)
      apply (drule_tac x = \<Gamma>1 and y = "TFun t \<tau>" in meta_spec2)
      apply (drule_tac x = \<Gamma>2 and y = t in meta_spec2)
      apply clarsimp
      apply (frule matches_split'(1); simp?)
      apply (frule matches_split'(2); simp?)
      apply (erule v_sem_appE)
       apply (rename_tac f' ts' a')
       apply (drule_tac x = "VAFunction f' ts'" in meta_spec)
       apply (drule_tac x = a' in meta_spec)
       apply (clarsimp simp: rename_mono_prog'_def)
      apply (rename_tac f' ts' a')
      apply (drule_tac x = "VFunction f' ts'" in meta_spec)
      apply (drule_tac x = a' in meta_spec)
      apply clarsimp
      done
  next
    case (v_sem_cast \<xi> e l \<tau> l')
    then show ?case
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_con)
      apply (erule v_sem_castE; clarsimp)
      apply (erule typing_castE; clarsimp)
      apply (rename_tac e' l' l'' \<tau>)
      apply (drule_tac x = \<gamma> and y = e' in meta_spec2; clarsimp)
      apply (rename_tac e' y y' \<tau>)
      apply (drule_tac x = \<Gamma> and y = "TPrim (Num \<tau>)" in meta_spec2; clarsimp)
      apply (drule_tac x = "VPrim y" in meta_spec; clarsimp)
      done
  next
    case (v_sem_app \<xi> re f ts e' rv rsv \<gamma> e \<tau> \<Gamma>)
    then show ?case
     apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_con)
      apply (rename_tac b c)
      apply (drule_tac x = \<gamma> in meta_spec)
      apply (drule_tac x = \<gamma> in meta_spec)
      apply (erule typing_appE; clarsimp)
      apply (drule_tac x = b in meta_spec)
      apply (drule_tac x = c in meta_spec)
      apply clarsimp
      apply (rename_tac \<Gamma>1 \<Gamma>2 t)
      apply (drule_tac x = \<Gamma>1 and y = "TFun t \<tau>" in meta_spec2)
      apply (drule_tac x = \<Gamma>2 and y = t in meta_spec2)
      apply clarsimp
      apply (frule matches_split'(1); simp?)
      apply (frule matches_split'(2); simp?)
      apply (erule v_sem_appE)
       apply (rename_tac f' ts' a')
       apply (drule_tac x = "VAFunction f' ts'" in meta_spec)
       apply (drule_tac x = a' in meta_spec)
       apply clarsimp
      apply (rename_tac f' ts' a')
      apply (drule_tac x = "VFunction f' ts'" in meta_spec)
      apply (drule_tac x = a' in meta_spec)
      apply clarsimp
      apply (drule_tac x = "[a']" in meta_spec; simp)
      apply (drule_tac x = "specialise ts' f'" in meta_spec; simp)
      apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
      apply (frule(5) preservation(1) [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(2), simplified])
      apply (erule v_t_funE; clarsimp)
      apply (subst (asm) subtyping_simps; clarsimp)
      apply (drule value_subtyping(1)[rotated 1]; simp?)
      apply (rename_tac  ta u t')
      apply (drule_tac x = "[Some ta]" and y = u in meta_spec2; clarsimp)
      apply (drule_tac x = v in meta_spec; clarsimp)
      apply (drule meta_mp; simp add: matches_def)
      done
  next
    case (v_sem_con \<xi> x x' uu t)
    then show ?case
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_con)
      apply (erule v_sem_conE; clarsimp)
      apply (erule typing_conE; clarsimp)
      done
  next
    case (v_sem_member \<xi> e fs f)
    then show ?case 
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_member)
      apply (erule v_sem_memberE; clarsimp)
      apply (erule typing_memberE; clarsimp)
      apply (elim meta_allE meta_impE; simp?)
      apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
      apply (erule v_t_recordE)
      apply (frule vval_typing_record_length)
      apply clarsimp
      done
  next
    case (v_sem_unit \<xi>)
    then show ?case
      apply (cases e; clarsimp intro!:  v_sem_v_sem_all.v_sem_unit)
      apply (erule v_sem_unitE; clarsimp)
      done
  next
    case (v_sem_tuple \<xi> x x' y y')
    then show ?case
      apply (cases e; clarsimp intro!:  v_sem_v_sem_all.v_sem_tuple matches_split')
      apply (erule v_sem_tupleE; clarsimp)
      apply (erule typing_tupleE)
      apply (frule  matches_split'(1); simp?)
      apply (frule  matches_split'(2); simp?)
      apply clarsimp
      done
  next
    case (v_sem_esac \<xi> t ts v)
    then show ?case
      apply (cases e; clarsimp intro!:  v_sem_v_sem_all.v_sem_esac)
      apply (erule v_sem_esacE)
      apply (erule typing_esacE)
      apply (rename_tac e' ts')
      apply clarsimp
      apply (elim meta_allE meta_impE; simp?)
      apply clarsimp
      done
  next
    case (v_sem_let \<xi> a a' b b')
    then show ?case 
      apply (cases e; clarsimp intro!:  v_sem_v_sem_all.v_sem_let)
      apply (erule v_sem_letE)
      apply (erule typing_letE)
      apply (frule matches_split'(1); simp?)
      apply (frule matches_split'(2); simp?)
      apply (rename_tac e1 e2 aa \<Gamma>1 \<Gamma>2 t)
      apply (drule_tac x = \<gamma> and y = e1 in meta_spec2; clarsimp)
      apply (drule_tac x = \<Gamma>1 and y = t in meta_spec2; clarsimp)
      apply (drule_tac x = aa in meta_spec; clarsimp)
      apply (drule_tac x = "aa # \<gamma>" and y = e2 in meta_spec2; clarsimp)
      apply (drule_tac x = "Some t # \<Gamma>2" and y = \<tau> in meta_spec2; clarsimp)
      apply (drule_tac x = v in meta_spec; clarsimp)
      apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
      apply (drule(2) matches_cons'[OF matches_split'(2)])
      apply clarsimp
      done
  next
    case (v_sem_letbang \<xi> a a' b b' vs)
    then show ?case
      apply (cases e; clarsimp intro!:  v_sem_v_sem_all.v_sem_letbang)
      apply (erule v_sem_letBangE)
      apply (erule typing_letbE)
      apply (frule matches_split_bang'(1); simp?)
      apply (frule matches_split_bang'(2); simp?)
      apply (rename_tac e1 e2 aa \<Gamma>1 \<Gamma>2 t k)
      apply (drule_tac x = \<gamma> and y = e1 in meta_spec2; clarsimp)
      apply (drule_tac x = \<Gamma>1 and y = t in meta_spec2; clarsimp)
      apply (drule_tac x = aa in meta_spec; clarsimp)
      apply (drule_tac x = "aa # \<gamma>" and y = e2 in meta_spec2; clarsimp)
      apply (drule_tac x = "Some t # \<Gamma>2" and y = \<tau> in meta_spec2; clarsimp)
      apply (drule_tac x = v in meta_spec; clarsimp)
      apply (frule(4) preservation [where \<tau>s = "[]" and K = "[]", simplified])
      apply (drule(2) matches_cons'[OF matches_split_bang'(2)])
      apply clarsimp
      done
  next
    case (v_sem_case_m \<xi> x t v m m' n)
    then show ?case sorry
  next
    case (v_sem_case_nm \<xi> x t' v t n n' m)
    then show ?case sorry
  next
    case (v_sem_if \<xi> x b t e r)
    then show ?case sorry
  next
    case (v_sem_struct \<xi> xs vs ts)
    then show ?case
      apply (cases e; clarsimp intro: v_sem_v_sem_all.v_sem_struct)
      apply (erule v_sem_structE; clarsimp)
      apply (erule typing_structE; clarsimp)
      done
  next
    case (v_sem_take \<xi> x fs f e e')
    then show ?case sorry
  next
    case (v_sem_put \<xi> x fs e e' f)
    then show ?case sorry
  next
    case (v_sem_split \<xi> x a b e e')
    then show ?case
      apply(cases e; clarsimp intro!: v_sem_v_sem_all.v_sem_split)
      apply (erule v_sem_splitE)
      apply (erule typing_splitE)
      apply (frule matches_split'(1); simp?)
      apply (frule matches_split'(2); simp?)
      apply (rename_tac e1 e2 aa bb \<Gamma>1 \<Gamma>2 t u)
      apply (drule_tac x = \<gamma> and y = e1 in meta_spec2; clarsimp)
      apply (drule_tac x = \<Gamma>1 and y = "TProduct t u" in meta_spec2; clarsimp)
      apply (drule_tac x = "VProduct aa bb"  in meta_spec; clarsimp)
      apply (drule_tac x = "aa # bb # \<gamma>" and y = e2 in meta_spec2; clarsimp)
      apply (drule_tac x = "Some t # Some u # \<Gamma>2" and y = \<tau> in meta_spec2; clarsimp)
      apply (drule_tac x = v in meta_spec; clarsimp)
      apply (frule(5) preservation [where \<tau>s = "[]" and K = "[]", OF _ _ matches_split'(1), simplified])
      apply (erule v_t_productE; clarsimp)
      apply (rename_tac t u)
      apply (drule_tac x = "rename_val rename' (monoval bb)" and ?\<Gamma> = \<Gamma>2 in matches_cons'; simp?)
      apply (drule_tac x = "rename_val rename' (monoval aa)" and ?\<Gamma> = "Some u # \<Gamma>2" in matches_cons'; simp?)
      apply clarsimp
      done
  next
    case (v_sem_promote \<xi> e e' t')
    then show ?case
      apply(cases e; clarsimp intro!: v_sem_v_sem_all.v_sem_promote)
      apply (erule v_sem_promoteE)
      apply (erule typing_promoteE)
      apply clarsimp
      done
  next
    case (v_sem_all_empty \<xi>)
    then show ?case
      by (cases e) (fastforce intro: v_sem_v_sem_all.v_sem_all_empty elim: v_sem_all_NilE)+
  next
    case (v_sem_all_cons \<xi> x v xs vs)
    then show ?case
      apply (cases e;clarsimp intro!: v_sem_v_sem_all.intros)
      apply (elim v_sem_all_ConsE typing_all_consE; clarsimp; frule matches_split'(1); simp?; frule matches_split'(2); simp?; clarsimp)+
      done
  qed

end (* of context *)

end