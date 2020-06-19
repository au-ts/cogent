theory Manual_AllRefine
  imports Generated_AllRefine
begin


thm  Generated_cogent_shallow.corres_shallow_C_wordarray_put2_u32[no_vars]
thm  Generated_cogent_shallow.corres_shallow_C_wordarray_length_u32[no_vars]
thm  Generated_cogent_shallow.corres_shallow_C_wordarray_get_u32[no_vars]
thm Generated_cogent_shallow.corres_shallow_C_sum_arr[no_vars]
section "Shallow Word Array Value Relation"

overloading
  valRel_WordArrayU32 \<equiv> valRel
begin
  definition valRel_WordArrayU32: 
    "\<And>\<xi> x v. valRel_WordArrayU32 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (32 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU32 (x ! i)))"
end

section "Shallow Word Array Function Definitions"

overloading
  wordarray_put2' \<equiv> wordarray_put2
begin
definition wordarray_put2':
 "wordarray_put2' (x :: ('a WordArray, 32 word, 'a) WordArrayPutP) \<equiv> (WordArrayPutP.arr\<^sub>f x)[unat (WordArrayPutP.idx\<^sub>f x) := WordArrayPutP.val\<^sub>f x]" 
end

overloading
  wordarray_length' \<equiv> wordarray_length
begin
definition wordarray_length':
 "wordarray_length' (x :: 'a WordArray) \<equiv> (of_nat (length x) :: 32 word)" 
end

overloading
  wordarray_get' \<equiv> wordarray_get
begin
definition wordarray_get':
 "wordarray_get' (x :: (32 word WordArray, 32 word) RR) \<equiv> (if unat (RR.p2\<^sub>f x) < length (RR.p1\<^sub>f x) then (RR.p1\<^sub>f x) ! unat (RR.p2\<^sub>f x) else 0)" 
end

section "\<xi> Abstractions"

definition upd_wa_put2_0
  where
  "upd_wa_put2_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in (\<exists>p idx val. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
          (UPrim (LU32 idx), RPrim (Num U32)), (UPrim (LU32 val), RPrim (Num U32))] \<and>
          y2 = UPtr p (RCon ''WordArray'' [RPrim (Num U32)]) \<and>
          y1 = (\<lambda>l. (if \<exists>len arr. x1 p = option.Some (UAbstract (WAU32 len arr)) \<and> 
                        l = arr + 4 * idx \<and> idx < len then option.Some (UPrim (LU32 val)) else x1 l))))"

definition upd_wa_get_0
  where
  "upd_wa_get_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p idx len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
          (UPrim (LU32 idx), RPrim (Num U32))] \<and> x1 p = option.Some (UAbstract (WAU32 len arr)) \<and> 
            (idx < len \<longrightarrow> x1 (arr + 4 * idx) = option.Some y2) \<and>
            (\<not> idx < len \<longrightarrow> y2 = UPrim (LU32 0))))"

definition upd_wa_length_0
  where
  "upd_wa_length_0 x y =
      (let (x1, x2) = x;
           (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p len arr. x2 = UPtr p (RCon ''WordArray'' [RPrim (Num U32)]) \<and>
          x1 p = option.Some (UAbstract (WAU32 len arr)) \<and> y2 = UPrim (LU32 len)))"

definition val_wa_length_0
  where
  "val_wa_length_0 x y = (\<exists>xs len. x = VAbstract (VWA xs) \<and> y = VPrim (LU32 len) \<and> 
                                length xs = unat len)" 


definition val_wa_get_0
  where
  "val_wa_get_0 x y =
      (\<exists>xs idx v. x = VRecord [VAbstract (VWA xs), VPrim (LU32 idx)] \<and> y = VPrim (LU32 v) \<and>
       (unat idx < length xs \<longrightarrow> xs ! unat idx = y) \<and> (\<not> unat idx < length xs \<longrightarrow> v = 0))" 

definition val_wa_put2_0
  where
  "val_wa_put2_0 x y =
      (\<exists>xs idx val. x = VRecord [VAbstract (VWA xs), VPrim (LU32 idx), VPrim (LU32 val)] \<and>
       y = VAbstract (VWA (xs[unat idx := VPrim (LU32 val)])))" 


fun \<xi>0 :: "(char list, atyp, 32 word) uabsfuns" 
  where
  "\<xi>0 x y z = 
    (if x = ''wordarray_put2_0'' then upd_wa_put2_0 y z
     else (if x = ''wordarray_get_0'' then upd_wa_get_0 y z
           else (if x = ''wordarray_length_0'' then upd_wa_length_0 y z
                 else False)))" 

fun \<xi>m :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>m x y z = 
    (if x = ''wordarray_put2_0'' then val_wa_put2_0 y z
     else (if x = ''wordarray_get_0'' then val_wa_get_0 y z
           else (if x = ''wordarray_length_0'' then val_wa_length_0 y z
                 else False)))" 

fun \<xi>p :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>p x y z = 
    (if x = ''wordarray_put2'' then val_wa_put2_0 y z
     else (if x = ''wordarray_get'' then val_wa_get_0 y z
           else (if x = ''wordarray_length'' then val_wa_length_0 y z
                 else False)))" 

lemma word_mult_cancel_left: 
  fixes a b c :: "('a::len) word"
  assumes "0 \<le> a" "0 \<le> b" "0 \<le> c"
  assumes "uint c * uint a \<le> uint (max_word :: ('a::len) word)"
  assumes "uint c * uint b \<le> uint (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  apply (rule iffI)
   using assms
   apply (unfold word_mult_def word_of_int_def)
    apply (clarsimp simp:Abs_word_inject max_word_def uint_word_of_int m1mod2k uint_0_iff )
   apply fastforce
   done

locale WordArray = main_pp_inferred begin
  definition "abs_repr_u a \<equiv> case a of
      WAU32 _ _ \<Rightarrow> (''WordArray'', [RPrim (Num U32)])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

  definition "abs_typing_u a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      WAU32 len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)] \<and> sig \<noteq> Unboxed \<and>
                      (sigil_perm sig = option.Some ReadOnly \<longrightarrow> w = {} \<and> r = {arr + 4 * i | i. i < len}) \<and>
                      (sigil_perm sig = option.Some Writable \<longrightarrow> r = {} \<and> w = {arr + 4 * i | i. i < len}) \<and>
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x))) \<and> 4 * unat len \<le> unat (max_word :: ptrtyp)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"

  definition "abs_typing_v a name \<tau>s \<equiv>
    (case a of
      VWA xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)] \<and> (\<forall>i < length xs. \<exists>x. xs ! i = VPrim (LU32 x))
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"

  definition  "abs_upd_val' au av name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    abs_typing_u au name \<tau>s sig r w \<sigma> \<and> abs_typing_v av name \<tau>s \<and>
    (case au of
      WAU32 len arr \<Rightarrow>
        (case av of 
          VWA xs \<Rightarrow> unat len = length xs \<and> 
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x)) \<and> 
                                     xs ! (unat i) = VPrim (LU32 x))
          | _ \<Rightarrow> False)
      | _ \<Rightarrow> (case av of
                VTOther _ \<Rightarrow> True
             |  _ \<Rightarrow> False))"

lemma distinct_indices:
  "abs_typing_u (WAU32 len arr) n ts s r w \<sigma> \<Longrightarrow> \<forall>i < len. \<forall>j < len. i = j \<longleftrightarrow> 4 * i = 4 * j"
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp simp: abs_typing_u_def)
  apply (clarsimp simp: abs_typing_u_def)
  apply (subgoal_tac "0 \<le> i")
   apply (frule_tac b = j and c = 4 in word_mult_cancel_left; clarsimp simp: uint_nat)
    apply (subgoal_tac "int (unat i) < int (unat len)")
     apply linarith
    apply (simp add: unat_mono)
   apply (subgoal_tac "int (unat j) < int (unat len)")
    apply linarith
   apply (simp add: unat_mono)
  apply simp
  done      
end

sublocale WordArray \<subseteq> Generated_cogent_shallow _ abs_repr_u abs_typing_v abs_typing_u abs_upd_val'
  apply (unfold abs_repr_u_def[abs_def] abs_typing_v_def[abs_def] abs_typing_u_def[abs_def] abs_upd_val'_def[abs_def])
  apply (unfold_locales; clarsimp split: vatyp.splits atyp.splits)
          apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
         apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
        apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
       apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
      apply (case_tac s; clarsimp; case_tac x11a; clarsimp; erule_tac x = i in allE; clarsimp)
     apply (case_tac s, (case_tac s', simp_all)+)[]
    apply (unfold UpdateSemantics.frame_def)
    apply (erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply (case_tac s; clarsimp; case_tac x11a; clarsimp;
           drule_tac x = "x12 + 4 * i" in orthD1; simp; rule_tac x = i in exI; simp)
   apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
  apply (case_tac s; clarsimp; case_tac x11a; clarsimp)
   apply (rule conjI; clarsimp; erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply auto[1]
   apply (erule_tac x = i in allE; clarsimp)
   apply auto[1]
  apply (rule conjI; clarsimp; erule_tac x = "x12 + 4 * i" in allE; clarsimp)
    apply (erule_tac x = i in allE; clarsimp)
    apply (rule_tac x = x in exI)
    apply auto[1]
   apply (erule_tac x = i in allE; clarsimp)
   apply auto[1]
  done

context WordArray begin


section "Naturally True Shared Assumptions for Isabelle to C Correspondence Lemmas"

lemma value_sem_rename_mono_prog_rename_\<Xi>_\<xi>m_\<xi>p: 
  "value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: val.rename_mono_prog_def)
  apply (rule conjI; clarsimp)
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_length_0_def)
   apply (case_tac v; clarsimp)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x = v' in exI)
   apply (subst (asm) rename_def)
   apply (subst (asm) assoc_lookup.simps)+
   apply (clarsimp split: if_split_asm simp: val_wa_get_0_def)
   apply (case_tac v; clarsimp)
   apply (case_tac z; clarsimp)
   apply (case_tac za; clarsimp)
  apply clarsimp
  apply (rule_tac x = v' in exI)
  apply (subst (asm) rename_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm simp: val_wa_put2_0_def)
  apply (case_tac v; clarsimp)
  apply (case_tac z; clarsimp)
  apply (case_tac za; clarsimp)
  apply (case_tac zb; clarsimp)
  done

lemma val_proc_env_matches_\<xi>m_\<Xi>:
  "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType6_def val_wa_get_0_def)
    apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: wordarray_length_0_type_def val_wa_length_0_def)
   apply (rule val.v_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType5_def val_wa_put2_0_def)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
   apply (erule val.v_t_abstractE)
  apply (rule val.v_t_abstract)
   apply (clarsimp simp: abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (case_tac "i = unat idx")
    apply (rule_tac x = val in exI; simp)
   apply (rule_tac x = x in exI; simp)
  apply simp
  done

lemma proc_env_u_v_matches_\<xi>0_\<xi>m_\<Xi>:
  "proc_env_u_v_matches \<xi>0 \<xi>m \<Xi>"
  apply (clarsimp simp: proc_env_u_v_matches_def)
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: upd_wa_get_0_def wordarray_get_0_type_def abbreviatedType6_def)
    apply (erule u_v_recE'; clarsimp)
    apply (erule u_v_r_consE'; clarsimp)
    apply (erule u_v_p_absE'; clarsimp)
    apply (erule u_v_r_consE'; clarsimp)
    apply (erule u_v_r_emptyE')
    apply (erule u_v_primE')+
    apply (subst (asm) lit_type.simps)+
    apply clarsimp
    apply (rule conjI)
     apply (clarsimp simp: val_wa_get_0_def)
     apply (rule_tac x = "{}" in exI)+
     apply (clarsimp simp: abs_upd_val'_def frame_def word_less_nat_alt)
     apply (erule_tac x = idx in allE)
     apply clarsimp
     apply (case_tac "unat idx < length xs"; clarsimp intro!: u_v_prim[where l = "(LU32 _)", simplified])
    apply (clarsimp simp: word_less_nat_alt abs_upd_val'_def)
    apply (case_tac a'; clarsimp simp: word_less_nat_alt)
    apply (erule_tac x = idx in allE)
    apply (case_tac "unat idx < length x1"; clarsimp)
     apply (rule_tac x = "VPrim (LU32 x)" in exI)
     apply (clarsimp simp: val_wa_get_0_def)
    apply (rule_tac x = "VPrim (LU32 0)" in exI)
    apply (clarsimp simp: val_wa_get_0_def)
   apply (clarsimp simp: upd_wa_length_0_def wordarray_length_0_type_def)
   apply (erule u_v_p_absE'; clarsimp)
   apply (clarsimp simp: abs_upd_val'_def)
   apply (case_tac a'a; clarsimp)
   apply (rule conjI)
    apply (clarsimp simp: val_wa_length_0_def)
    apply (rule_tac x = "{}" in exI)+
    apply (clarsimp simp: frame_def intro!: u_v_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: abs_upd_val'_def)
   apply (rule_tac x = "VPrim (LU32 len)" in exI)
   apply (clarsimp simp: val_wa_length_0_def)
  apply (clarsimp simp: upd_wa_put2_0_def wordarray_put2_0_type_def abbreviatedType5_def)
  apply (erule u_v_recE'; clarsimp)
  apply (erule u_v_r_consE'; clarsimp)
  apply (erule u_v_p_absE'; clarsimp)
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_v_r_consE'; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule u_v_r_emptyE')
  apply (erule u_v_primE')+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: val_wa_put2_0_def)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "insert p w" in exI)
   apply clarsimp
   apply (rule conjI)
    apply (rule_tac a = a and  ptrl = undefined in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
       apply simp
      apply (clarsimp simp: abs_upd_val'_def)
      apply (case_tac a; clarsimp)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_u_def)
      apply (rule conjI)
       apply (clarsimp simp: abs_typing_v_def word_less_nat_alt)
       apply (erule_tac x = i in allE)
       apply (case_tac "i = unat idx"; clarsimp)
      apply (clarsimp simp: word_less_nat_alt)
      apply (rule conjI)
       apply (drule distinct_indices)
       apply (clarsimp simp: word_less_nat_alt)
       apply (erule_tac x = i in allE)+
       apply clarsimp
       apply (erule_tac x = idx in allE)
       apply clarsimp
      apply clarsimp
      apply (erule_tac x = i in allE)
      apply clarsimp
      apply (case_tac "unat i = unat idx"; clarsimp)
     apply (clarsimp simp: abs_upd_val'_def)
     apply (erule_tac x = idx in allE)
     apply clarsimp
    apply simp
   apply (clarsimp simp: frame_def)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
    apply (rule conjI; clarsimp)
    apply (clarsimp simp: abs_upd_val'_def abs_typing_u_def)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a; clarsimp simp: abs_typing_u_def)
  apply (case_tac a'; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (x1[unat idx := VPrim (LU32 val)]))" in exI)
  apply (clarsimp simp: val_wa_put2_0_def)
  done

lemma upd_proc_env_matches_ptrs_\<xi>0_\<Xi>:
  "upd.proc_env_matches_ptrs \<xi>0 \<Xi>"
  apply (unfold upd.proc_env_matches_ptrs_def)
  apply clarsimp
  apply (subst (asm) \<Xi>_def)
  apply (subst (asm) assoc_lookup.simps)+
  apply (clarsimp split: if_split_asm)
    apply (clarsimp simp: wordarray_get_0_type_def abbreviatedType6_def upd_wa_get_0_def)
    apply (erule upd.u_t_recE; clarsimp)
    apply (erule upd.u_t_r_consE; clarsimp)
    apply (erule upd.u_t_p_absE; clarsimp)
    apply (erule upd.u_t_r_consE; clarsimp)
    apply (erule upd.u_t_r_emptyE; clarsimp)
    apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)+
    apply (rule_tac x = "{}" in exI)+
    apply (clarsimp simp: frame_def abs_typing_u_def)
    apply (erule_tac x = idx in allE)
    apply (case_tac "idx < len"; clarsimp intro!: upd.u_t_prim[where l = "(LU32 _)", simplified])
   apply (clarsimp simp: wordarray_length_0_type_def upd_wa_length_0_def)
   apply (erule upd.u_t_p_absE; clarsimp)
   apply (rule_tac x = "{}" in exI)+
   apply (clarsimp simp: frame_def intro!: upd.u_t_prim[where l = "(LU32 _)", simplified])
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType5_def upd_wa_put2_0_def)
  apply (erule upd.u_t_recE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp)
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_consE; simp)
  apply (erule conjE)+
  apply (subst (asm) type_repr.simps[symmetric])+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (case_tac a; clarsimp)
   apply (rule_tac x = ra in exI)
   apply (rule_tac x = "insert p w" in exI)
   apply (rule conjI)
    apply (rename_tac len arr)
    apply (rule_tac ptrl = undefined and a = "WAU32 len arr" in upd.u_t_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
       apply simp
      apply (clarsimp simp: abs_typing_u_def)
     apply (clarsimp simp: abs_typing_u_def)
    apply clarsimp
   apply (clarsimp simp: frame_def abs_typing_u_def)
   apply (rule conjI; clarsimp)
    apply (rule conjI)
     apply (rule disjI2)
     apply (rule disjI2)
     apply (rule_tac x = idx in exI; simp)
    apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
  apply (clarsimp simp: abs_typing_u_def)
  done

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  apply (clarsimp simp: proc_ctx_wellformed_def \<Xi>_def)
  apply (clarsimp split: if_splits
                  simp: assoc_lookup.simps
                        wordarray_get_0_type_def abbreviatedType6_def wordarray_get_u32_type_def
                        wordarray_length_0_type_def wordarray_length_u32_type_def
                        wordarray_put2_0_type_def abbreviatedType5_def wordarray_put2_u32_type_def
                        wordarray_fold_no_break_0_type_def abbreviatedType1_def
                        wordarray_map_no_break_0_type_def abbreviatedType4_def abbreviatedType3_def abbreviatedType2_def
                        dec_type_def dec_arr_type_def
                        inc_type_def inc_arr_type_def
                        sum_type_def sum_arr_type_def
                        mul_type_def mul_arr_type_def)
  done



section "Correspondence From Isabelle Shallow Embedding to C"

theorem shallow_C_wordarray_put2_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32
     (main_pp_inferred.wordarray_put2_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp: corres_shallow_C_def)
  apply (monad_eq simp: wordarray_put2_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_put2_u32_type_def; subst wordarray_put2_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_put2_u32_type_def wordarray_put2_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (xs[unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s) := VPrim (LU32 (WordArrayPutP.val\<^sub>f vv\<^sub>s))]))" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_put2_0_def)
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2')
  apply (subst val_rel_shallow_C_def)
  apply (clarsimp simp: valRel_WordArrayPutP valRel_WordArrayU32)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (case_tac "i = unat (WordArrayPutP.idx\<^sub>f vv\<^sub>s)"; clarsimp)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType5_def)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE; clarsimp)
  apply (erule u_v_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp)
  apply (rule_tac x = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in exI)
  apply (rule_tac x = ra in exI)
  apply (rule_tac x = "insert (ptr_val (t2_C.arr_C uv\<^sub>C)) wa" in exI)
  apply (clarsimp simp: upd_wa_put2_0_def)
  apply (rule_tac ptrl = undefined and a = a in u_v_p_abs_w[where ts = "[TPrim (Num U32)]", simplified])
     apply simp
    apply (clarsimp simp: abs_upd_val'_def)
    apply (case_tac a; clarsimp)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_u_def)
    apply (rule conjI)
     apply (clarsimp simp: abs_typing_v_def)
     apply (erule_tac x = i in allE)
     apply clarsimp
     apply (case_tac "i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp)
    apply clarsimp
    apply (rule conjI; clarsimp)
     apply (drule distinct_indices)
     apply (erule_tac x = i in allE)+
     apply clarsimp
     apply (erule_tac x = "t2_C.idx_C uv\<^sub>C" in allE)
     apply (clarsimp simp: word_less_nat_alt)
    apply (erule_tac x = i in allE)
    apply clarsimp
    apply (case_tac "unat i = unat (t2_C.idx_C uv\<^sub>C)"; clarsimp)
   apply (clarsimp simp: abs_upd_val'_def)
   apply (erule_tac x = " idx_C uv\<^sub>C" in allE)
   apply clarsimp
  apply clarsimp
  done



theorem shallow_C_wordarray_length_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_length_u32 vv\<^sub>s) Generated_TypeProof.wordarray_length_u32
     (main_pp_inferred.wordarray_length_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))] \<sigma> s"
  apply clarsimp
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_length_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_length_u32_type_def; subst wordarray_length_0_type_def; simp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_length_u32_type_def wordarray_length_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (monad_eq simp: wordarray_length_0'_def val_rel_simp)
  apply (rule_tac x = "VPrim (LU32 (SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C s uv\<^sub>C))))" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_length_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply (clarsimp simp: Generated_TypeProof.wordarray_length_u32_type_def)
  apply (frule val_rel_shallow_C_elim(1); clarsimp simp: valRel_WordArrayU32)
  apply (frule val_rel_shallow_C_elim(3); clarsimp simp: val_rel_simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (clarsimp simp: abs_upd_val'_def)
  apply (case_tac a; clarsimp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta)
  apply (drule_tac p =  uv\<^sub>C and 
                  uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
         clarsimp simp: is_valid_simp heap_simp abs_repr_u_def type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_length_0_def)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_length_u32_def wordarray_length')
  apply (rule conjI)
   apply (metis word_unat.Rep_inverse)
  apply (rule conjI)
   apply (rule u_v_prim[where l = "LU32 _", simplified])
  apply (clarsimp simp: val_rel_simp)
  done


theorem shallow_C_wordarray_get_corres:
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_get_u32 vv\<^sub>s) Generated_TypeProof.wordarray_get_u32
     (main_pp_inferred.wordarray_get_u32' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p [uv\<^sub>m] [vv\<^sub>m] \<Xi>
     [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))] \<sigma> s"
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(1))
  apply (clarsimp simp: valRel_RR valRel_WordArrayU32)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[uv\<^sub>m]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_get_u32'_def)
  apply (drule meta_mp)
   apply (drule val_rel_shallow_C_elim(3); simp)
  apply (drule meta_mp)
   apply (subst \<Xi>_def; subst wordarray_get_u32_type_def; subst wordarray_get_0_type_def; clarsimp)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def wordarray_get_u32_type_def wordarray_get_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_get_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VPrim (LU32 r')" in exI)
  apply (frule_tac i = 0 and 
                   \<tau> = "(prod.fst (prod.snd Generated_TypeProof.wordarray_get_u32_type))" 
                       in u_v_matches_proj_single'; simp)
  apply clarsimp
  apply (frule val_rel_shallow_C_elim(3))
  apply (clarsimp simp: val_rel_simp wordarray_get_u32_type_def abbreviatedType6_def)
  apply (erule u_v_recE)
  apply (erule u_v_r_consE; clarsimp)+
  apply (erule u_v_r_emptyE)
  apply (erule u_v_primE)
  apply (subst (asm) lit_type.simps; simp)
  apply (erule u_v_p_absE; clarsimp)
  apply (erule u_sem_appE; erule u_sem_afunE; clarsimp)
  apply (erule u_sem_varE; clarsimp simp: upd_wa_get_0_def)
  apply (simp add: word_less_nat_alt)
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: val_wa_get_0_def abs_upd_val'_def)
  apply (erule_tac x = "t1_C.p2_C uv\<^sub>C" in allE; clarsimp simp: word_less_nat_alt)
  apply (subst val_rel_shallow_C_def)
  apply (rule_tac x = "TPrim (Num U32)" in exI)
  apply (rule_tac x = "{}" in exI)+
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_get_u32_def wordarray_get' abs_upd_val'_def word_less_nat_alt)
  apply (erule_tac x = "unat (t1_C.p2_C uv\<^sub>C)" in allE)
  apply (force simp: val_rel_simp intro!: u_v_prim[where l = "LU32 _", simplified])
  done

section "Correspondence Lemmas Between Update Semantics and C"

lemma upd_C_wordarray_put2_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_put2_0'')))")
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_put2_0_type_def abbreviatedType5_def)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_primE)+
  apply (subst (asm) lit_type.simps)+
  apply clarsimp
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = "t2_C.arr_C x'" in allE)
   apply (erule_tac x = "values_C (heap_WordArray_u32_C st (t2_C.arr_C x')) +\<^sub>p uint (t2_C.idx_C x')" in allE)
   apply (clarsimp simp: heap_rel_ptr_def heap_rel_ptr_w32_def abs_repr_u_def is_valid_simp type_rel_simp)
   apply (erule_tac x = "t2_C.idx_C x'" in allE)+
   apply (clarsimp simp: val_rel_simp heap_simp type_rel_simp)
  apply clarsimp
  apply (rule_tac x = "\<lambda>l. (if \<exists>len arr. (\<sigma> \<circ> ptr_val \<circ> t2_C.arr_C) x' = option.Some (UAbstract (WAU32 len arr)) \<and> 
                                l = arr + 4 * t2_C.idx_C x' \<and> t2_C.idx_C x' < len 
                            then option.Some (UPrim (LU32 (t2_C.val_C x'))) 
                            else \<sigma> l)" in exI)
  apply (rule_tac x = "UPtr (ptr_val y') (RCon ''WordArray'' [RPrim (Num U32)])" in exI)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_put2_0'_def upd_wa_put2_0_def)
  apply (rule conjI)
   apply (rule_tac x = "RCon ''WordArray'' [RPrim (Num U32)]" in exI, simp)
  apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
  apply (rule conjI)
   apply (clarsimp simp: heap_rel_meta_def)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: type_rel_simp)
   apply (monad_eq simp: wordarray_put2_0'_def)
   apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (t2_C.arr_C x')))"; 
          drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: is_valid_simp heap_simp)
  apply (erule_tac x = "t2_C.arr_C x'" in allE)
  apply (clarsimp simp: heap_rel_meta_def abs_repr_u_def type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_put2_0'_def heap_simp is_valid_simp)
  apply (rule conjI; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t2_C.arr_C x')) +\<^sub>p uint (t2_C.idx_C x')" and 
                   uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  apply (rule conjI)
   apply (clarsimp simp: ptr_add_def)
   apply (metis Ptr_ptr_val mult.commute)
  apply clarsimp
  apply (case_tac "idx_C x' < SCAST(32 signed \<rightarrow> 32) (len_C (heap_WordArray_u32_C st (t2_C.arr_C x')))";
         drule_tac p = x and uv = uv in all_heap_rel_ptrD; clarsimp simp: type_rel_simp val_rel_simp)
  done


lemma upd_C_wordarray_length_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))")
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_length_0_type_def)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = x' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp abs_repr_u_def is_valid_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_length_0_def)
   apply (monad_eq simp: wordarray_length_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def)
   apply (erule_tac x = x' in allE)
   apply (clarsimp simp: heap_rel_ptr_def type_rel_simp abs_repr_u_def heap_simp val_rel_simp)
  apply (monad_eq simp: wordarray_length_0'_def)
  done


lemma upd_C_wordarray_get_corres:
"\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_get_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_get_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def; rename_tac r w)
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_get_0'')))")
  apply (clarsimp simp: val_rel_simp \<Xi>_def wordarray_get_0_type_def abbreviatedType6_def)
  apply (erule upd.u_t_recE)
  apply (erule upd.u_t_r_consE; clarsimp)+
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (rule conjI)
   apply (monad_eq simp: wordarray_get_0'_def)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp abs_repr_u_def val_rel_simp is_valid_simp heap_simp)
   apply (drule not_le_imp_less)
   apply (erule_tac x = "t1_C.p2_C x'" in allE; clarsimp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C x')) +\<^sub>p uint (t1_C.p2_C x')" and
                   uv = "UPrim (LU32 x)" in all_heap_rel_ptrD; simp add: type_rel_simp)
  apply clarsimp
  apply (rule_tac x = \<sigma> in exI)
  apply (rule conjI)
   apply (clarsimp simp: upd_wa_get_0_def)
   apply (erule_tac x = "t1_C.p2_C x'" in allE)
   apply (monad_eq simp: wordarray_get_0'_def word_less_nat_alt word_le_nat_alt)
   apply (clarsimp simp: state_rel_def heap_rel_def heap_rel_ptr_meta heap_rel_ptr_w32_meta)
   apply (drule_tac p = "t1_C.p1_C x'" and uv = "UAbstract (WAU32 x11 x12)" in all_heap_rel_ptrD; 
          clarsimp simp: type_rel_simp abs_repr_u_def val_rel_simp is_valid_simp heap_simp)
   apply (drule_tac p = "values_C (heap_WordArray_u32_C st (t1_C.p1_C x')) +\<^sub>p uint (t1_C.p2_C x')" and
                   uv = "UPrim (LU32 x)" in all_heap_rel_ptrD;
          clarsimp simp: type_rel_simp val_rel_simp)
  apply (monad_eq simp: wordarray_get_0'_def)
  apply blast
  done


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

thm val_rel_simp
find_theorems "cogent_function_val_rel"

theorem
"\<lbrakk>\<And>i \<gamma> v' \<Gamma>' \<sigma>' st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_length_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_length_0'' []) (Var i))
         (do x <- main_pp_inferred.wordarray_length_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma>' st;
 \<And>v' i \<gamma> \<Gamma> \<sigma> s.
    \<lbrakk>t5_C.f_C v' = FUN_ENUM_sum; i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma> ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma> \<sigma> s;
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p;
 vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.sum_arr vv\<^sub>s) Generated_TypeProof.sum_arr (main_pp_inferred.sum_arr' uv\<^sub>C) \<xi>0 \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.sum_arr_type))] \<sigma> s"
  apply (monad_eq simp: sum_arr'_def  corres_shallow_C_def)
  apply (frule val_rel_shallow_C_elim(1))
  
  oops

lemma
" \<And>v' i \<gamma> \<Gamma>' \<sigma> s.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u)
         (App (AFun ''wordarray_fold_no_break_0'' []) (Var i)) (do x <- main_pp_inferred.wordarray_fold_no_break_0' v';
gets (\<lambda>s. x)
                                                                od)
         \<xi>0 \<gamma> \<Xi>  \<Gamma>' \<sigma> s"
  apply (rule afun_corres; simp)
  apply (clarsimp simp: abs_rel_def') find_theorems "whileLoop" name:"inv" 
  apply (thin_tac "i < length \<gamma>")
  apply (thin_tac "val_rel (\<gamma> ! i) v'")
  apply (thin_tac "\<Gamma>' ! i = option.Some (prod.fst (prod.snd (\<Xi> ''wordarray_fold_no_break_0'')))")
  apply clarsimp
  apply (clarsimp simp: val_rel_simp)
(*
  apply (clarsimp simp: cogent_function_val_rel
                        FUN_ENUM_sum_def
                        FUN_ENUM_dec_def
                        FUN_ENUM_inc_def
                        FUN_ENUM_mul_def
                        FUN_ENUM_dec_arr_def
                        FUN_ENUM_inc_arr_def
                        FUN_ENUM_mul_arr_def
                        FUN_ENUM_sum_arr_def
                        FUN_ENUM_wordarray_get_0_def
                        FUN_ENUM_wordarray_length_0_def
                        FUN_ENUM_wordarray_put2_0_def
                        FUN_ENUM_wordarray_fold_no_break_0_def
                        FUN_ENUM_wordarray_map_no_break_0_def
                        FUN_ENUM_wordarray_get_u32_def
                        FUN_ENUM_wordarray_length_u32_def
                        FUN_ENUM_wordarray_put2_u32_def)
*)
  apply (erule upd.u_t_recE)
  apply (clarsimp simp: \<Xi>_def wordarray_fold_no_break_0_type_def abbreviatedType1_def)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_p_absE; clarsimp simp: abs_typing_u_def)
  apply (case_tac a; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_primE; subst (asm) lit_type.simps; clarsimp)
  apply (erule upd.u_t_r_consE; clarsimp)
  apply (erule upd.u_t_r_emptyE)
  apply (erule upd.u_t_unitE)thm cogent_function_val_rel
  apply (case_tac "sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_mul")
   apply (case_tac "sint (t5_C.f_C x') \<noteq> sint FUN_ENUM_sum")
    apply (clarsimp simp: cogent_function_val_rel
                          FUN_ENUM_sum_def
                          FUN_ENUM_dec_def
                          FUN_ENUM_inc_def
                          FUN_ENUM_mul_def
                          FUN_ENUM_dec_arr_def
                          FUN_ENUM_inc_arr_def
                          FUN_ENUM_mul_arr_def
                          FUN_ENUM_sum_arr_def
                          FUN_ENUM_wordarray_get_0_def
                          FUN_ENUM_wordarray_length_0_def
                          FUN_ENUM_wordarray_put2_0_def
                          FUN_ENUM_wordarray_fold_no_break_0_def
                          FUN_ENUM_wordarray_map_no_break_0_def
                          FUN_ENUM_wordarray_get_u32_def
                          FUN_ENUM_wordarray_length_u32_def
                          FUN_ENUM_wordarray_put2_u32_def)

    apply (rule FalseE)
    apply (erule disjE)
     apply (clarsimp simp: dec_def)
     apply (erule upd.u_t_functionE)
     apply (erule typing_takeE)+
     apply (erule typing_letE)+
     apply (erule typing_structE)
     apply (erule typing_all_consE)+
     apply (erule typing_varE)+
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: inc_def)
     apply (erule upd.u_t_functionE)
     apply (erule typing_takeE)+
     apply (erule typing_letE)+
     apply (erule typing_structE)
     apply (erule typing_all_consE)+
     apply (erule typing_varE)+
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: dec_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
     apply (erule typing_letE)
     apply (erule typing_letbE)
     apply (erule typing_letE)+
     apply (erule typing_appE)+
     apply (erule typing_afunE)+
     apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: inc_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
     apply (erule typing_letE)
     apply (erule typing_letbE)
     apply (erule typing_letE)+
     apply (erule typing_appE)+
     apply (erule typing_afunE)+
     apply (clarsimp simp: wordarray_map_no_break_0_type_def abbreviatedType2_def)
     apply (clarsimp simp: subtyping_simps(4) subtyping.simps[of _ _ "TPrim (Num U32)", simplified])
    apply (erule disjE)
     apply (clarsimp simp: mul_arr_def)
     apply (erule upd.u_t_functionE; clarsimp)
  
  oops
(*
fun upd_wa_foldnb_0'  :: "(char list, atyp, 32 word) ufundef" 
  where
"upd_wa_foldnb_0' (b1, b2) c = (\<exists>p frm to f ts acc len arr. 
    b2 = URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
      (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
      (UFunction f ts, RFun), (UPrim (LU32 acc), RPrim (Num U32)), (UUnit, RUnit)] \<and> 
    b1 p = option.Some (UAbstract (WAU32 len arr)) \<and>
    (if frm < min to frm 
      then (\<exists>v b1' acc' \<xi>. (b1 (arr + 4 * frm) = option.Some (UPrim (LU32 v))) \<and> 
        (\<xi>, [(URecord [(UPrim (LU32 v), RPrim (Num U32)), (UPrim (LU32 acc), RPrim (Num U32)), 
          (UUnit, RUnit)])] \<turnstile> (b1, App (Fun f ts) (Var 0)) \<Down>! (b1', UPrim (LU32 acc'))) \<and>
        upd_wa_foldnb_0' (b1', URecord [(UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
          (UPrim (LU32 (frm + 1)), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
          (UFunction f ts, RFun), (UPrim (LU32 acc'), RPrim (Num U32)), (UUnit, RUnit)]) c)
    else (b1, b2) = c))"
(*
fun upd_wa_foldnb_body
*)
definition upd_wa_fold_nb_0 :: "(char list, atyp, 32 word) ufundef" 
  where
"upd_wa_fold_nb_0 x y =
     (let (x1, x2) = x;
          (y1, y2) = y
      in x1 = y1 \<and> (\<exists>p frm to f ts acc len arr. x2 = URecord [
          (UPtr p (RCon ''WordArray'' [RPrim (Num U32)]), RPtr (RCon ''WordArray'' [RPrim (Num U32)])),
          (UPrim (LU32 frm), RPrim (Num U32)), (UPrim (LU32 to), RPrim (Num U32)),
          (UFunction f ts, RFun), (UPrim (LU32 acc), RPrim (Num U32)), (UUnit, RUnit)] \<and> 
          x1 p = option.Some (UAbstract (WAU32 len arr))))"


value "[7 ..(min 3 5)]"
term "SOME (x:: nat). x = 0"
term "THE x. x"
term fold
(*
  bad_\<sigma> ptr = None
  \<sigma> p = option.Some (UAbstract (WAU32 len arr))
  xs = [frm .. (min to len)]
  acc_f = (\<sigma>, acc)
  f = (\<lambda>i (\<sigma>, acc).
        (case \<sigma> (arr + i) of
            option.Some (UPrim (LU32 v)) \<Rightarrow>
            | _ \<Rightarrow> (bad_\<sigma>, UUnit)))
*)
*)
end (* of context *)
end