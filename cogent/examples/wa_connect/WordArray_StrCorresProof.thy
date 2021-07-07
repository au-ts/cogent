theory WordArray_StrCorresProof
  imports WordArray_CorresProof_Asm  WordArray_UpdCCorres
begin
context WordArray begin


section "Stronger Correspondence defintions"

definition
  corres_strong ::
  "((funtyp, abstyp, ptrtyp) store \<times> 's) set \<Rightarrow>
   funtyp expr \<Rightarrow>
   ('s,('a::cogent_C_val)) nondet_monad \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uabsfuns \<Rightarrow>
   (funtyp, abstyp, ptrtyp) uval env \<Rightarrow>
   (funtyp \<Rightarrow> poly_type) \<Rightarrow>
   ctx \<Rightarrow>
   (funtyp, abstyp, ptrtyp) store \<Rightarrow>
   's \<Rightarrow>
   bool"
where
  "corres_strong srel c m \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> s \<equiv>
   (\<sigma>,s) \<in> srel \<longrightarrow>
   (\<exists>r w. upd.matches_ptrs \<Xi>' \<sigma> \<gamma> \<Gamma>' r w \<longrightarrow>
   (\<not> prod.snd (m s)) \<and>
   (\<forall>r' s'. (r',s') \<in> prod.fst (m s) \<longrightarrow>
     (\<exists>\<sigma>' r.(\<xi>', \<gamma> \<turnstile> (\<sigma>,c)  \<Down>! (\<sigma>',r)) \<and> (\<sigma>',s') \<in> srel \<and> val_rel r r')))"
(*
definition corres_shallow_C_strong where
  "corres_shallow_C_strong
     (rename' :: funtyp \<times> type list \<Rightarrow> funtyp)
     (srel :: ((funtyp, abstyp, ptrtyp) store \<times> 's) set)
     (v\<^sub>s :: 'sv)
     (prog\<^sub>m :: funtyp expr)
     (prog\<^sub>C :: ('s, 'cv :: cogent_C_val) nondet_monad)
     (\<xi>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uabsfuns)
     (\<xi>\<^sub>v\<^sub>m :: (funtyp, vabstyp) vabsfuns)
     (\<xi>\<^sub>v\<^sub>p :: (funtyp, vabstyp) vabsfuns)
     (\<gamma>\<^sub>u\<^sub>m :: (funtyp, abstyp, ptrtyp) uval env)
     (\<gamma>\<^sub>v\<^sub>m :: (funtyp, vabstyp) vval env)
     (\<Xi>\<^sub>m :: funtyp \<Rightarrow> poly_type)
     (\<Gamma>\<^sub>m :: ctx)
     (\<sigma> :: (funtyp, abstyp, ptrtyp) store)
     (s :: 's) \<equiv>
   upd.proc_env_matches_ptrs \<xi>\<^sub>u\<^sub>m \<Xi>\<^sub>m \<longrightarrow>
   (\<sigma>, s) \<in> srel \<longrightarrow>
   (\<exists>r w. u_v_matches \<Xi>\<^sub>m \<sigma> \<gamma>\<^sub>u\<^sub>m \<gamma>\<^sub>v\<^sub>m \<Gamma>\<^sub>m r w) \<longrightarrow>
   (\<not> prod.snd (prog\<^sub>C s) \<and>
   (\<forall>r' s'. (r', s') \<in> prod.fst (prog\<^sub>C s) \<longrightarrow>
     (\<exists>\<sigma>' v\<^sub>u\<^sub>m v\<^sub>p.
      (\<xi>\<^sub>u\<^sub>m, \<gamma>\<^sub>u\<^sub>m \<turnstile> (\<sigma>, prog\<^sub>m) \<Down>! (\<sigma>', v\<^sub>u\<^sub>m)) \<and>
       (\<xi>\<^sub>v\<^sub>m, \<gamma>\<^sub>v\<^sub>m \<turnstile> prog\<^sub>m \<Down> val.rename_val rename' (val.monoval v\<^sub>p)) \<and>
       (\<sigma>', s') \<in> srel \<and>
       val_rel_shallow_C rename v\<^sub>s r' v\<^sub>p v\<^sub>u\<^sub>m \<xi>\<^sub>v\<^sub>p \<sigma>' \<Xi>\<^sub>m)))"
*)

section "Stronger Correspondence Lemmas/Theorems"

subsection "wordarray_put2"

lemma upd_C_wordarray_put2_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (cut_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_put2_corres; clarsimp simp: corres_def)
  done
subsection "wordarray_length"

lemma upd_C_wordarray_length_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (cut_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_length_corres; clarsimp simp: corres_def)
  done

subsection "wordarray_get"

lemma upd_C_wordarray_get_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel wa_abs_repr) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (cut_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_get_corres; clarsimp simp: corres_def)
  done

end (* end of context *)
end