theory Abstract_CorresProof
  imports Generated_CorresProof WordArray_C_Abstraction

begin


locale WordArray = main_pp_inferred begin
  definition "abs_repr' a \<equiv> case a of
      WAU32 _ _ \<Rightarrow> (''WordArray'', [RPrim (Num U32), RPrim (Num U32)])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

  definition "abs_typing' a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      WAU32 len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32), TPrim (Num U32)] \<and> sig \<noteq> Unboxed \<and>
                      (sigil_perm sig = Some ReadOnly \<longrightarrow> w = {} \<and> r = {arr + 4 * i | i. i < len}) \<and>
                      (sigil_perm sig = Some Writable \<longrightarrow> r = {} \<and> w = {arr + 4 * i | i. i < len}) \<and>
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = Some (UPrim (LU32 x)))
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"
end

sublocale WordArray \<subseteq>
  update_sem_init abs_typing' abs_repr'
  apply (unfold abs_repr'_def[abs_def] abs_typing'_def[abs_def])
  apply unfold_locales
         apply (clarsimp split: atyp.splits)
         apply (case_tac s; clarsimp)
         apply (case_tac x11a; simp)
        apply (clarsimp split: atyp.splits)
        apply (case_tac s; clarsimp)
        apply (case_tac x11a; clarsimp)
       apply (clarsimp split: atyp.splits)
       apply (case_tac s; clarsimp)
       apply (case_tac x11a; clarsimp)
      apply (clarsimp split: atyp.splits)
      apply (case_tac s; clarsimp)
      apply (case_tac x11a; clarsimp)
      apply (clarsimp split: atyp.splits)
      apply (case_tac s; clarsimp)
     apply (case_tac x11a; clarsimp; erule_tac x = i in allE; clarsimp)
    apply (clarsimp split: atyp.splits)
    apply (case_tac s, (case_tac s', simp_all)+)[]
   apply (clarsimp split: atyp.splits)
  apply (clarsimp split: atyp.splits)

(*
          apply (case_tac s; blast elim: bang_sigil.elims) 
         apply (case_tac s; blast elim: bang_sigil.elims)[]
        apply (case_tac s) blast elim: bang_sigil.elims)[] 
       apply simp+
   apply (clarsimp split: atyp.splits)
     apply (case_tac s, (case_tac s', simp_all)+)[]
    apply (case_tac s, (case_tac s', simp_all)+)[]
   apply (case_tac s, (case_tac s', simp_all)+)[]
  apply (clarsimp split: atyp.splits)
*)
  sorry

sublocale WordArray \<subseteq> Generated t abs_typing' abs_repr'
  apply (unfold abs_repr'_def[abs_def] abs_typing'_def[abs_def])
  apply unfold_locales
        apply (clarsimp split: atyp.splits)
          apply (case_tac s; blast elim: bang_sigil.elims)+
   apply (clarsimp split: atyp.splits)
     apply (case_tac s, case_tac s', simp_all)
    apply (case_tac s, case_tac s', simp_all)
   apply (case_tac s, case_tac s', simp_all)
  apply (clarsimp split: atyp.splits)
  done

context WordArray begin

section "Extract Proof Obligation"

ML \<open>
val y = Symtab.lookup prop_tab "wordarray_put2_0_corres_0"
val SOME (_, _, _, z) = y;
\<close>

section "Dirty hacks to generate the correct definitions for the proof"

subsection "State and Heap Relation"
(*
definition
  heap_rel_ptr_w32 ::
  "(funtyp, abstyp, ptrtyp) store \<Rightarrow> lifted_globals \<Rightarrow>
   (32 word) ptr \<Rightarrow> bool"
where
  "\<And> \<sigma> h p.
    heap_rel_ptr_w32 \<sigma> h p \<equiv>
   (\<forall> uv.
     \<sigma> (ptr_val p) = Some uv \<longrightarrow>
     type_rel (uval_repr uv) TYPE(32 word) \<longrightarrow>
     is_valid_w32 h p \<and> val_rel uv (heap_w32 h p))"

lemma heap_rel_ptr_w32_meta:
  "heap_rel_ptr_w32 = heap_rel_meta is_valid_w32 heap_w32"
  by (simp add: heap_rel_ptr_w32_def[abs_def] heap_rel_meta_def[abs_def])

definition heap_rel'
  where
  "heap_rel' \<sigma> h \<equiv> (\<forall>(p :: WordArray_u32_C ptr). heap_rel_ptr \<sigma> h p) \<and> 
                    (\<forall>(p' :: 32 word ptr). heap_rel_ptr_w32 \<sigma> h p')"

definition state_rel' :: "((funtyp, abstyp, ptrtyp) store \<times> lifted_globals) set"
where
  "state_rel' = {(\<sigma>, h). heap_rel' \<sigma> h}"
*)
thm state_rel_def
thm heap_rel_def 
(*
  Christine: 
    the generated heap_rel definition is just True 
    at the moment. I have updated the definition manually 
    in the settup file to the definition that you had here. 
*)
subsection "Update semantics abstraction"

definition \<xi>_0' :: "(char list, atyp, 32 word) uabsfuns" 
  where
  "\<xi>_0' x y z = 
      (let (y1, y2) = y;
           (z1, z2) = z
      in
           (if x = ''wordarray_put2_0'' then
                (case y2 of 
                      URecord [(UPtr p r, _), 
                            (UPrim (LU32 idx), _ ), (UPrim (LU32 val), _)] 
                        \<Rightarrow> (\<lambda>l. (case y1 p of Some (UAbstract (WAU32 len arr))
                                      \<Rightarrow> (if l = arr + 4 * idx \<and> idx < len 
                                            then Some (UPrim (LU32 val)) else y1 l)
                                  | _ \<Rightarrow> y1 l)) = z1 \<and> 
                            UPtr p r = z2
                    | _ \<Rightarrow> False)
           else False))" 

section "Proof"

definition valid_c_wordarray
  where
  "valid_c_wordarray s w \<equiv> is_valid_WordArray_u32_C s w \<and> 
                            (\<forall>i < w_l s w. is_valid_w32 s ((w_p s w) +\<^sub>p uint i)) "

definition valid_cogent_wordarray
  where
  "valid_cogent_wordarray \<sigma> s w \<equiv> (\<exists>len arr. len = w_l s w \<and> arr = ptr_val (w_p s w) \<and> 
                                    \<sigma> (ptr_val w) = Some (UAbstract (WAU32 len arr)) \<and> 
                                   (\<forall>i < len. \<sigma> (arr + 4 * i) = Some (UPrim (LU32 (heap_w32 s ((w_p s w) +\<^sub>p uint i))))))"

definition corres_wordarray
  where
  "corres_wordarray \<sigma> s w \<equiv> valid_c_wordarray s w \<and> valid_cogent_wordarray \<sigma> s w"

lemma  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
       \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = Some (fst (snd (\<Xi> ''wordarray_put2_0'')));
        corres_wordarray \<sigma> st (arr_C v')\<rbrakk> \<Longrightarrow>
       corres state_rel (App (AFun ''wordarray_put2_0'' []) (Var i)) (do x <- wordarray_put2_0' v';
  gets (\<lambda>s. x)
                                                                      od)
        \<xi>_0' \<gamma> \<Xi> \<Gamma>' \<sigma> st" 
  apply (clarsimp simp: corres_def)
  apply (rule conjI; clarsimp)
   apply (monad_eq simp: wordarray_put2_0'_def corres_wordarray_def valid_c_wordarray_def)  
\<comment>\<open> First prove that the function wordarray_put2 does not fail. This requires the \<alpha> abstraction \<close>
   
\<comment>\<open> \<xi>_0 is currently undefined so we make our own defintion. We also need the fact the pointer actually points to a word array \<close>
  apply (rule_tac x = "\<lambda>l. (case (\<sigma> \<circ> ptr_val \<circ> arr_C) v' of 
                                Some (UAbstract (WAU32 len arr)) \<Rightarrow>
                                      (if l = arr + 4 * idx_C v' \<and> idx_C v' < len 
                                          then Some (UPrim (LU32 (val_C v'))) 
                                      else \<sigma> l)
                              | _  \<Rightarrow> \<sigma> l)" in exI)
  apply (clarsimp simp: val_rel_simp)
  apply (rule_tac x = "UPtr (ptr_val r') repr" in exI)
  apply (rule conjI)
\<comment> \<open> Prove that the application of the abstraction to the arguments produces the expected return
     value \<close>
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (simp add: \<xi>_0'_def)
   apply (monad_eq simp: wordarray_put2_0'_def)

   apply (rule conjI)
   apply (clarsimp simp: state_rel_def heap_rel_def)
\<comment> \<open> Prove the heap relation for WordArray_u32_C objects\<close>
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: corres_wordarray_def valid_cogent_wordarray_def)
    apply (simp add:  heap_rel_ptr_meta)
    apply (clarsimp simp: heap_rel_meta_def)
    apply (monad_eq simp: wordarray_put2_0'_def)
    apply (case_tac "idx_C v' < w_l st (arr_C v')"; clarsimp)
     apply (rule conjI; clarsimp)
      apply (rule FalseE)
      apply (simp add: type_rel_simp)
     apply (drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: is_valid_simp heap_simp)
    apply (drule_tac p = x and uv = uv in  all_heap_rel_ptrD; clarsimp)

\<comment> \<open> Prove the heap relation for 32-bit words \<close>
   apply (clarsimp simp: corres_wordarray_def valid_cogent_wordarray_def)
   apply (simp add: heap_rel_ptr_w32_meta)
   apply (clarsimp simp: heap_rel_meta_def)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (case_tac "idx_C v' < w_l st (arr_C v')"; clarsimp)
    apply (erule_tac x = "idx_C v'" in allE; clarsimp)
    apply (rule conjI; clarsimp)
     apply (simp add: val_rel_simp)
    apply (rule conjI; clarsimp)
     apply (simp add: ptr_add_def)
     apply (rule FalseE)
     apply (metis Ptr_ptr_val mult.commute)
    apply (drule_tac p = x and uv = uv in  all_heap_rel_ptrD; clarsimp)
   apply (rule conjI; clarsimp)
    apply (drule_tac p = "w_p st (arr_C v') +\<^sub>p uint (idx_C v')" and uv = uv in all_heap_rel_ptrD;
           clarsimp simp: ptr_add_def mult.commute)
   apply (drule_tac p = x and uv = uv in  all_heap_rel_ptrD; simp)

\<comment> \<open> Prove the value relation for the return value \<close>
  apply (rule_tac x = "repr" in exI; simp)
  done



(*

lemma "\<xi>_0' matches-u \<Xi>"
  apply (unfold proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (case_tac  "f = ''wordarray_put2_0''")
   prefer 2
   apply (case_tac  "f = ''wordarray_put2_u32''")
    prefer 2
    apply clarsimp
    apply (rule FalseE)
    apply (clarsimp simp: \<xi>_0'_def)
  apply clarsimp
   prefer 2
   apply clarsimp
   apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType1_def)
   apply (clarsimp simp:  \<Xi>_def)
   apply (case_tac v; clarsimp simp: \<xi>_0'_def)
  apply (case_tac x4; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac list; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1; clarsimp)
   apply (case_tac lista; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1; clarsimp)
   apply (case_tac list; clarsimp)
   apply (case_tac "\<sigma> x91"; clarsimp)
  prefer 2
(*
   apply (rule_tac x = "{}" in  exI)
   apply (rule_tac x = "{}" in exI)
   apply (rule conjI)
     apply (erule u_t_recE; clarsimp)
     apply (erule u_t_r_consE; clarsimp)
    apply (erule u_t_r_consE; clarsimp)
    apply (erule u_t_r_consE; clarsimp)
    apply (erule u_t_r_emptyE; clarsimp)
    apply (drule type_repr_uval_repr)
  apply clarsimp
  thm conjE
  *)
*)

end (* of context *)


end