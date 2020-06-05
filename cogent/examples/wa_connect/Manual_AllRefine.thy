theory Manual_AllRefine
  imports Generated_AllRefine
begin


thm  Generated_cogent_shallow.corres_shallow_C_wordarray_put2_u32[no_vars]


overloading
  valRel_WordArrayU32 \<equiv> valRel
begin
  definition valRel_WordArrayU32: 
    "\<And>\<xi> x v. valRel_WordArrayU32 (\<xi> :: (funtyp,vabstyp) vabsfuns) (x :: (32 word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
      \<exists>xs. v = VAbstract (VWA xs) \<and> length x = length xs \<and> (\<forall>i < length xs. xs ! i = VPrim (LU32 (x ! i)))"
end

overloading
  wordarray_put2' \<equiv> wordarray_put2
begin
definition wordarray_put2':
 "wordarray_put2' (x :: ('a WordArray, 32 word, 'a) WordArrayPutP) \<equiv> (WordArrayPutP.arr\<^sub>f x)[unat (WordArrayPutP.idx\<^sub>f x) := WordArrayPutP.val\<^sub>f x]" 
end
thm wordarray_put2'

thm valRel_WordArrayU32

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
                        \<Rightarrow> (\<lambda>l. (case y1 p of option.Some (UAbstract (WAU32 len arr))
                                      \<Rightarrow> (if l = arr + 4 * idx \<and> idx < len 
                                            then option.Some (UPrim (LU32 val)) else y1 l)
                                  | _ \<Rightarrow> y1 l)) = z1 \<and> 
                            UPtr p r = z2
                    | _ \<Rightarrow> False)
           else False))" 

definition \<xi>m :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>m x y z = (if x = ''wordarray_put2_0'' then
                (case y of 
                      VRecord [VAbstract (VWA xs), 
                            VPrim (LU32 idx), VPrim (LU32 val)] 
                        \<Rightarrow> VAbstract (VWA (xs[unat idx := VPrim (LU32 val)])) = z
                    | _ \<Rightarrow> False)
           else False)" 


definition \<xi>p :: "(char list, vatyp) vabsfuns" 
  where
  "\<xi>p x y z = (if x = ''wordarray_put2'' then
                (case y of 
                      VRecord [VAbstract (VWA xs), 
                            VPrim (LU32 idx), VPrim (LU32 val)] 
                        \<Rightarrow> VAbstract (VWA (xs[unat idx := VPrim (LU32 val)])) = z
                    | _ \<Rightarrow> False)
           else False)" 

locale WordArray = main_pp_inferred begin
  definition "abs_repr_u a \<equiv> case a of
      WAU32 _ _ \<Rightarrow> (''WordArray'', [RPrim (Num U32)])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

  definition "abs_typing_u a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      WAU32 len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [TPrim (Num U32)] \<and> sig \<noteq> Unboxed \<and>
                      (sigil_perm sig = option.Some ReadOnly \<longrightarrow> w = {} \<and> r = {arr + 4 * i | i. i < len}) \<and>
                      (sigil_perm sig = option.Some Writable \<longrightarrow> r = {} \<and> w = {arr + 4 * i | i. i < len}) \<and>
                      (\<forall>i < len. \<exists>x. \<sigma>(arr + 4 * i) = option.Some (UPrim (LU32 x)))
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
lemma "\<lbrakk>\<forall>i<length arrv. arrv ! i = VPrim (LU32 (arr ! i)); length (arr :: 32 word WordArray) = length arrv\<rbrakk> \<Longrightarrow>
val.matches \<Xi> [VRecord [VAbstract (VWA arrv), VPrim (LU32 (idx :: 32 word)), VPrim (LU32 (val :: 32 word))]]
         [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]"
  apply (clarsimp simp: val.matches_def Generated_TypeProof.wordarray_put2_u32_type_def Generated_TypeProof.abbreviatedType1_def)
  apply (rule val.v_t_record)
   apply (rule val.v_t_r_cons1)
    apply (rule val.v_t_abstract)
     apply (clarsimp simp: abs_typing_v_def)
    apply (clarsimp simp: type_wellformed_all_pretty_def)
   apply (rule val.v_t_r_cons1)
    apply auto[1]
   apply (rule val.v_t_r_cons1)
    apply auto[1]
   apply (rule val.v_t_r_empty)
  apply auto
  done
lemma "correspondence_init abs_repr_u abs_typing_v abs_typing_u abs_upd_val'"
  by (simp add: correspondence_init_axioms)

lemma "value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p"
  apply (clarsimp simp: rename_def \<Xi>_def \<xi>m_def \<xi>p_def val.rename_mono_prog_def)
  apply (rule conjI)
   apply clarsimp
   apply (case_tac v; clarsimp)
   apply (case_tac x4; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac list; clarsimp)
    apply (case_tac x5; clarsimp)
   apply (case_tac x5; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1a; clarsimp)
   apply (case_tac lista; clarsimp)
   apply (case_tac list; clarsimp)
    apply (case_tac a; clarsimp)
    apply (case_tac x1a; clarsimp)
   apply (case_tac a; clarsimp)
   apply (case_tac x1a; clarsimp)
  apply (case_tac ts; clarsimp)
  apply (case_tac list; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac x1; clarsimp)
  apply (case_tac "f = ''wordarray_put2''"; clarsimp)
  done

lemma "val.proc_env_matches \<xi>m \<Xi>"
  apply (clarsimp simp: val.proc_env_matches_def \<Xi>_def)
  apply (case_tac "f = ''wordarray_put2_0''")
   defer
   apply (case_tac "f = ''wordarray_put2_u32''")
    apply (clarsimp simp: \<xi>m_def)
   apply (rule FalseE)
   apply (clarsimp simp: \<xi>m_def)
  apply (clarsimp simp: wordarray_put2_0_type_def abbreviatedType1_def \<xi>m_def)
  apply (case_tac v; clarsimp)
  apply (case_tac x4; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x5; clarsimp)
  apply (case_tac list; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1a; clarsimp)
  apply (case_tac lista; clarsimp)
  apply (case_tac a; clarsimp)
  apply (case_tac x1a; clarsimp)
  apply (case_tac list; clarsimp)
  apply (erule val.v_t_recordE)
  apply (erule val.v_t_r_consE; clarsimp)
  apply (rule val.v_t_abstract)
   apply (erule val.v_t_abstractE)
   apply (clarsimp simp: abs_typing_v_def)
   apply (erule_tac x = i in allE; clarsimp)
   apply (case_tac "i = unat x4")
    apply (rule_tac x = x4a in exI; simp)
   apply (rule_tac x = x in exI; simp)
  apply simp
  done

(*
theorem manual_generated_theorem:
"\<lbrakk>Generated_cogent_shallow abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 \<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>_0' \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st;
 correspondence_init abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>_0' \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (subgoal_tac "\<exists>arr idx val. vv\<^sub>s = \<lparr>WordArrayPutP.arr\<^sub>f = arr, idx\<^sub>f = idx, val\<^sub>f = val\<rparr>")
   prefer 2
   apply (case_tac vv\<^sub>s; clarsimp)
  apply clarsimp
  apply (subgoal_tac "\<exists>arrv. vv\<^sub>p = VRecord [VAbstract (VWA arrv), VPrim (LU32 idx), VPrim (LU32 val)]")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "(\<forall>i < length arrv. arrv ! i = VPrim (LU32 (arr ! i))) \<and> length arr = length arrv")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "val_rel uv\<^sub>m uv\<^sub>C")
  prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def)
  apply (clarsimp simp: val_rel_simp)
  apply (rule_tac vv\<^sub>s = vv\<^sub>s and 
                  vv\<^sub>p = vv\<^sub>p and
                   \<tau>o = "prod.snd (prod.snd Generated_TypeProof.wordarray_put2_u32_type)" and 
                  prog\<^sub>p = "expr.Let (Var 0) (App (AFun ''wordarray_put2'' [TPrim (Num U32)]) (Var 0))"
                      in corres_shallow_C_intro)
          apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def rename_def)
         apply simp
        apply simp
       apply simp
  
       apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def
                             Generated_TypeProof.abbreviatedType1_def
                             Generated_TypeProof.wordarray_put2_u32_def)
(*
       apply (rule_tac ?\<Gamma>1.0 = "[option.Some (TRecord 
                                    [(''arr'', TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined), Present),
                                     (''idx'', TPrim (Num U32), Present), 
                                     (''val'', TPrim (Num U32), Present)]  Unboxed)]" and 
                       ?\<Gamma>2.0 = "[]" and 
                       t = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in typing_let)
         
*)
       defer
      apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
      apply (monad_eq simp: wordarray_put2_u32'_def)
(*
       apply (rule_tac ?\<Gamma>1.0 = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" and
                       ?\<Gamma>2.0 = "[]" and
                       t = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" in corres_let)
  *)
      defer
      defer
      apply simp
     apply (clarsimp simp: val_rel_shallow_C_def)
    prefer 3
    apply (clarsimp simp: val.scorres_def)
    apply (erule v_sem_varE; clarsimp)
    apply (erule v_sem_appE)
     prefer 2
     apply (rule FalseE)
     apply blast
    apply (erule v_sem_afunE)
    apply (erule v_sem_varE)
    apply (clarsimp simp: \<xi>p_def)
    apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2' valRel_WordArrayU32)
    apply (erule_tac x = i in allE; clarsimp)
    apply (case_tac "i = unat idx"; clarsimp)

      apply (rule_tac ?\<Gamma>1.0 = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" and
                       ?\<Gamma>2.0 = "[]" and
                       t = "(prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))" in typing_let)
     prefer 2
     apply (rule typing_var; clarsimp simp: Cogent.empty_def)
     apply (clarsimp simp: weakening_conv_all_nth)
     apply (rule keep)
     apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType1_def)
    apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def abbreviatedType1_def)
    apply (clarsimp simp: split_conv_all_nth)

(*  apply (clarsimp simp: corres_shallow_C_def)*)
  oops
*)
(*
\<xi>_m == monomorphic value semantics contexts for values
\<xi>_p == polymorphic ...
vv_s == value of the argument of the function, i.e. wordarray_put2, in the shallow Isabelle embedding
vv_p == value of the argument of the function, i.e. wordarray_put2, in the polymorphic value semantics
vv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic value semantics
uv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic update semantics
uv_c == value of the argument of the function, i.e. wordarray_put2, in the autocorres generated C
*)


theorem manual_generated_theorem':
"\<lbrakk>Generated_cogent_shallow abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 \<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v'; \<Gamma>' ! i = option.Some (prod.fst (prod.snd wordarray_put2_0_type))\<rbrakk>
    \<Longrightarrow> update_sem_init.corres abs_typing_u abs_repr_u (Generated.state_rel abs_repr_u) (App (AFun ''wordarray_put2_0'' []) (Var i))
         (do x <- wordarray_put2_0' v';
             gets (\<lambda>s. x)
          od)
         \<xi>_0' \<gamma>
         (assoc_lookup
           [(''wordarray_put2_0'', wordarray_put2_0_type), (''wordarray_put2_u32'', Generated_TypeProof.wordarray_put2_u32_type)]
           ([], TUnit, TUnit))
         \<Gamma>' \<sigma> st;
 correspondence_init abs_repr_u abs_typing_v abs_typing_u abs_upd_val';
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>m \<xi>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>_0' \<xi>m \<xi>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  apply (subgoal_tac "\<exists>arr idx val. vv\<^sub>s = \<lparr>WordArrayPutP.arr\<^sub>f = arr, idx\<^sub>f = idx, val\<^sub>f = val\<rparr>")
   prefer 2
   apply (case_tac vv\<^sub>s; clarsimp)
  apply clarsimp
  apply (subgoal_tac "\<exists>arrv. vv\<^sub>p = VRecord [VAbstract (VWA arrv), VPrim (LU32 idx), VPrim (LU32 val)]")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "(\<forall>i < length arrv. arrv ! i = VPrim (LU32 (arr ! i))) \<and> length arr = length arrv")
   prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def valRel_WordArrayPutP valRel_WordArrayU32)
  apply clarsimp
  apply (subgoal_tac "val_rel uv\<^sub>m uv\<^sub>C")
  prefer 2
   apply (clarsimp simp: val_rel_shallow_C_def)
  apply (clarsimp simp: val_rel_simp)
  apply (drule_tac x = 0 in meta_spec)
  apply (drule_tac x = "[URecord [(UPtr (ptr_val (arr_C uv\<^sub>C)) repr, b), (UPrim (LU32 (idx_C uv\<^sub>C)), ba),
                            (UPrim (LU32 (val_C uv\<^sub>C)), bb)]]" in meta_spec)
  apply (drule_tac x = uv\<^sub>C in meta_spec)
  apply (drule_tac x = "[option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]" in meta_spec)
  apply (drule_tac x = \<sigma> in meta_spec)
  apply (drule_tac x = s in meta_spec)
  apply (clarsimp simp:  corres_shallow_C_def)
  apply (monad_eq simp: wordarray_put2_u32'_def)
  apply (drule  meta_mp)
   apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_type_def 
                         Generated_TypeProof.abbreviatedType1_def 
                         wordarray_put2_0_type_def)
  apply (clarsimp simp: corres_def)
  apply (erule impE)
   apply (clarsimp simp: \<Xi>_def)
  apply (erule impE)
   apply (clarsimp simp: \<Xi>_def)
  apply (erule impE)
   apply (rule_tac x = r in exI)
   apply (rule_tac x = x in exI)
   apply (frule u_v_matches_to_matches_ptrs)
   apply (clarsimp simp: \<Xi>_def
                         Generated_TypeProof.wordarray_put2_u32_type_def 
                         Generated_TypeProof.abbreviatedType1_def 
                         wordarray_put2_0_type_def)
  apply clarsimp
  apply (erule_tac x = r' in allE)
  apply (erule_tac x = s' in allE)
  apply clarsimp
  apply (rule_tac x = \<sigma>' in exI)
  apply (rule_tac x = ra in exI)
  apply (clarsimp simp: Generated_TypeProof.wordarray_put2_u32_def)
  apply (rule conjI)
   apply (rule_tac \<sigma>' = \<sigma> and a' = uv\<^sub>m in u_sem_let)
  apply clarsimp
    apply (rule u_sem_var[where i = 0 and \<gamma> = "[_]", simplified])
   apply clarsimp
   apply (rule u_sem_abs_app)
     apply (rule u_sem_afun)
    apply (rule u_sem_var)
   apply (erule u_sem_appE; clarsimp)
    apply (erule u_sem_afunE; clarsimp)
    apply (erule u_sem_varE; clarsimp)
   apply (erule u_sem_afunE; clarsimp)
  apply (rule_tac x = "VAbstract (VWA (arrv[unat idx := VPrim (LU32 val)]))" in exI)
  apply clarsimp
  apply (rule conjI)
   apply (rule v_sem_let)
    apply (rule v_sem_var)
   apply (rule v_sem_abs_app)
     apply (rule v_sem_afun)
    apply (rule v_sem_var)
   apply (clarsimp simp: \<xi>m_def)
  apply (clarsimp simp: Generated_Shallow_Desugar.wordarray_put2_u32_def wordarray_put2')
  apply (clarsimp simp: val_rel_shallow_C_def)
  apply (clarsimp simp: valRel_WordArrayU32)
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x = i in allE)
   apply clarsimp
   apply (case_tac "i = unat idx"; clarsimp)
  apply (rule_tac x = "TCon ''WordArray'' [TPrim (Num U32)] (Boxed Writable undefined)" in exI)
  apply (rule_tac x = rb in exI)
  apply (rule_tac x = xa in exI)
  apply (clarsimp simp: val_rel_simp)
  thm u_v_p_abs_w
  apply (rule  u_v_p_abs_w)   
  sorry

end (* of context *)
end