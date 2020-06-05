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
 value_sem.rename_mono_prog abs_typing_v rename \<Xi> \<xi>\<^sub>m \<xi>\<^sub>p; vv\<^sub>m = value_sem.rename_val rename (value_sem.monoval vv\<^sub>p);
 correspondence_init.val_rel_shallow_C abs_repr_u abs_upd_val' rename vv\<^sub>s uv\<^sub>C vv\<^sub>p uv\<^sub>m \<xi>\<^sub>p \<sigma> \<Xi>; proc_ctx_wellformed \<Xi>;
 value_sem.proc_env_matches abs_typing_v \<xi>\<^sub>m \<Xi>;
 value_sem.matches abs_typing_v \<Xi> [vv\<^sub>m] [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))]\<rbrakk>
\<Longrightarrow> correspondence_init.corres_shallow_C abs_repr_u abs_typing_u abs_upd_val' rename (Generated.state_rel abs_repr_u)
     (Generated_Shallow_Desugar.wordarray_put2_u32 vv\<^sub>s) Generated_TypeProof.wordarray_put2_u32 (wordarray_put2_u32' uv\<^sub>C) \<xi>_0' \<xi>\<^sub>m \<xi>\<^sub>p
     [uv\<^sub>m] [vv\<^sub>m] \<Xi> [option.Some (prod.fst (prod.snd Generated_TypeProof.wordarray_put2_u32_type))] \<sigma> s"
  apply clarsimp
  oops
(*
\<xi>_m == monomorphic value semantics contexts for values
\<xi>_p == polymorphic ...
vv_s == value of the argument of the function, i.e. wordarray_put2, in the shallow Isabelle embedding
vv_p == value of the argument of the function, i.e. wordarray_put2, in the polymorphic value semantics
vv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic value semantics
uv_m == value of the argument of the function, i.e. wordarray_put2, in the monomorphic update semantics
uv_c == value of the argument of the function, i.e. wordarray_put2, in the autocorres generated C
*)
end (* of context *)
end