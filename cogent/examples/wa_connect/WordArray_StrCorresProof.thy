theory WordArray_StrCorresProof
  imports WordArray_CorresProof_Asm WordArray_SCCorres WordArray_UpdCCorres
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

section "Stronger Correspondence Lemmas/Theorems"

subsection "wordarray_put2"

lemma upd_C_wordarray_put2_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (drule_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_put2_corres; clarsimp simp: corres_def)
  done

theorem shallow_C_wordarray_put2_corres_strong:
"\<lbrakk>vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; 
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32
     (main_pp_inferred.wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply (insert value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p 
                val_proc_env_matches_\<xi>m_\<Xi> 
                proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
                proc_ctx_wellformed_\<Xi>
                upd_C_wordarray_put2_corres
                upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (rule shallow_C_wordarray_put2_corres; simp)
  done

subsection "wordarray_length"

lemma upd_C_wordarray_length_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (drule_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_length_corres; clarsimp simp: corres_def)
  done

theorem shallow_C_wordarray_length_corres_strong:
"\<lbrakk>vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_length_u32 vv\<^sub>s) Generated_TypeProof.wordarray_length_u32
     (main_pp_inferred.wordarray_length_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))] \<sigma> s"
  apply (insert value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p 
                val_proc_env_matches_\<xi>m_\<Xi> 
                proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
                proc_ctx_wellformed_\<Xi>
                upd_C_wordarray_length_corres
                upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (rule shallow_C_wordarray_length_corres; simp)
  done

subsection "wordarray_get"

lemma upd_C_wordarray_get_corres_strong:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> corres_strong (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> st"
  apply (insert proc_ctx_wellformed_\<Xi> upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (unfold corres_strong_def)
  apply (drule_tac i  = i  and 
                   \<gamma>  = \<gamma>  and 
                   v' = v' and
                   \<Gamma>' = \<Gamma>' and
                   \<sigma>  = \<sigma>  and
                   st = st in upd_C_wordarray_get_corres; clarsimp simp: corres_def)
  done

theorem shallow_C_wordarray_get_strong:
"\<lbrakk>vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_get_u32 vv\<^sub>s) Generated_TypeProof.wordarray_get_u32
     (main_pp_inferred.wordarray_get_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))] \<sigma> s"
  apply (insert value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p 
                val_proc_env_matches_\<xi>m_\<Xi> 
                proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>
                proc_ctx_wellformed_\<Xi>
                upd_C_wordarray_get_corres
                upd_proc_env_matches_ptrs_\<xi>0_\<Xi>)
  apply (rule shallow_C_wordarray_get_corres; simp)
  done

end (* end of context *)
end