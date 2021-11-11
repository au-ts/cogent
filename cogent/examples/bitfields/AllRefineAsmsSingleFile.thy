theory AllRefineAsmsSingleFile
  imports
  NameUn 
Cogent.ValueSemantics
 "build/Generated_AllRefine"
   
begin


section "Function types wellformed"

lemma proc_ctx_wellformed_\<Xi>:
  "proc_ctx_wellformed \<Xi>"
  unfolding proc_ctx_wellformed_def \<Xi>_def
            Generated_Deep_Normal.abbreviated_type_defs 
            Generated_TypeProof.abbreviated_type_defs
            Generated_TypeProof.foo_type_def
Generated_TypeProof.u4_to_u8_type_def
Generated_TypeProof.u8_to_u4_type_def
Generated_TypeProof.u8_to_u2_type_def
Generated_TypeProof.u2_to_u8_type_def
Generated_TypeProof.id2_type_def
Generated_TypeProof.id4_type_def

  by (clarsimp simp: assoc_lookup.simps matches_fields_layout_def upt_def match_repr_layout_simps match_constraint_def)

lemma \<Xi>_simps:
  "\<Xi> ''u4_to_u8'' = u4_to_u8_type"
  "\<Xi> ''u2_to_u8'' = u2_to_u8_type"
  "\<Xi> ''foo'' = foo_type"
  "\<Xi> ''u8_to_u4'' = u8_to_u4_type"
  "\<Xi> ''u8_to_u2'' = u8_to_u2_type"
      apply (clarsimp simp: \<Xi>_def
Generated_TypeProof.u4_to_u8_type_def Generated_Deep_Normal.u4_to_u8_type_def
Generated_TypeProof.u2_to_u8_type_def Generated_Deep_Normal.u2_to_u8_type_def
Generated_TypeProof.foo_type_def Generated_Deep_Normal.foo_type_def
Generated_TypeProof.u8_to_u4_type_def Generated_Deep_Normal.u8_to_u4_type_def
Generated_TypeProof.u8_to_u2_type_def Generated_Deep_Normal.u8_to_u2_type_def
Generated_TypeProof.abbreviated_type_defs Generated_Deep_Normal.abbreviated_type_defs
)+
  done

section "Abstract functions specification for the update semantics"
 

definition uun_from_u8 ::"nat \<Rightarrow> (funtyp, abstyp, ptrtyp) ufundef"
  where 
"uun_from_u8 n x y = (
\<exists> \<sigma> v1 v2. x = (\<sigma>, UPrim (LU8 v1)) \<and> y = (\<sigma>, UAbstract (UUN n v2)) \<and>
   v2 = (unat v1) AND 2^n - 1
  )"


definition uun_to_u8 ::"nat \<Rightarrow> (funtyp, abstyp, ptrtyp) ufundef"
  where 
"uun_to_u8 n x y = (
\<exists> \<sigma> v1 v2. x = (\<sigma>, UAbstract (UUN n v1)) \<and> y = (\<sigma>, UPrim (LU8 v2)) \<and>
   v2 = of_nat v1
  )"

overloading \<xi>0 \<equiv> \<xi>_0
begin
definition \<xi>0 :: "(funtyp, abstyp, ptrtyp) uabsfuns"
  where
"\<xi>0 f x y = 
  (if f = ''u4_to_u8'' then uun_to_u8 4 x y
   else if f = ''u8_to_u4'' then uun_from_u8 4 x y
   else if f = ''u2_to_u8'' then uun_to_u8 2 x y
   else if f = ''u8_to_u2'' then uun_from_u8 2 x y
   else False)"

end

lemma \<xi>_0_simps:
  "\<xi>_0 ''u4_to_u8'' = uun_to_u8 4"
"\<xi>_0 ''u2_to_u8'' = uun_to_u8 2"
"\<xi>_0 ''u8_to_u4'' = uun_from_u8 4"
"\<xi>_0 ''u8_to_u2'' = uun_from_u8 2"
  apply (clarsimp simp: \<xi>0_def fun_eq_iff)+
  done

subsection "Preservation for abstract functions"



section "Cast Locale"

locale CastUpdate 
begin

  definition "un_abs_repr a \<equiv> case a of  
      UUN s _ \<Rightarrow>  (name_un s , [])                      
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"


  
  definition "un_abs_typing_u \<Xi>' a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      UUN s n \<Rightarrow> sig = Unboxed \<and> name = name_un s \<and> \<tau>s = [] \<and> n < 2^s \<and> r = {} \<and> w = {}

    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"

lemma un_abs_typing_u_elims:
  "un_abs_typing_u \<Xi>' (UUN ss nn) n \<tau>s s r w \<sigma> \<Longrightarrow> s = Unboxed \<and> n = name_un ss \<and> \<tau>s = [] \<and> nn < 2^ss \<and>  r = {} \<and> w = {}"
  by (unfold un_abs_typing_u_def[abs_def]; clarsimp split: atyp.splits type.splits)+

lemma un_abs_typing_name_un_elims:
  "un_abs_typing_u \<Xi>' a (name_un n) \<tau>s s r w \<sigma> 
    \<Longrightarrow> \<exists>v . a = UUN n v \<and> \<tau>s = []"
  apply(unfold un_abs_typing_u_def[abs_def]; clarsimp split: atyp.splits type.splits)+
  using string_of_nat_at0_le[of n]
    apply(simp add:string_of_nat_inj)+
  done



end (* of context *)


sublocale CastUpdate \<subseteq> update_sem un_abs_typing_u un_abs_repr

  apply (unfold un_abs_repr_def[abs_def] un_abs_typing_u_def[abs_def])
  apply (unfold_locales; clarsimp split: atyp.splits)
  done


sublocale CastUpdate \<subseteq> update_sem_init un_abs_typing_u un_abs_repr 
  by (unfold_locales)



section "Abstract functions specifications for the monomorphic value semantics"



section "Cast Locale"

type_synonym funtyp = "char list"
datatype vatyp = VUN nat (* size *) nat (* value *) | VTOther "unit"
type_synonym vabstyp = vatyp

locale CastValue 
begin

  definition "un_abs_typing_v \<Xi>' a name \<tau>s \<equiv>
    (case a of    
      VUN s n \<Rightarrow> name = name_un s  \<and> \<tau>s = [] \<and> n < 2^s 
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"

lemma un_abs_typing_v_elims:
  "un_abs_typing_v \<Xi>' (VUN sz vl) n \<tau>s  \<Longrightarrow> n = name_un sz  \<and> \<tau>s = [] \<and> vl < 2^sz"
  by (unfold un_abs_typing_v_def[abs_def]; clarsimp split: vatyp.splits type.splits prim_type.splits)+



end (* of context *)

sublocale CastValue \<subseteq> value_sem un_abs_typing_v
  apply (unfold un_abs_typing_v_def[abs_def])
  apply (unfold_locales)
  apply (clarsimp split: vatyp.splits )
  done


section "Cast Methods"

subsection "vun_to_u8"

definition vun_to_u8 :: "nat \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"vun_to_u8 n x y = 
  (\<exists> v1 v2. x = VAbstract (VUN n v1) \<and> y = VPrim (LU8 v2) \<and> v2 = of_nat v1)"

lemma (in CastValue) vun_to_u8_preservation:
  "\<lbrakk>vval_typing \<Xi>' v (TCon (name_un n) [] Unboxed); vun_to_u8 n v v'\<rbrakk>
    \<Longrightarrow> vval_typing \<Xi>' v' (TPrim (Num U8))"
  by (fastforce simp: vun_to_u8_def)



subsection "vun_from_u8"

definition vun_from_u8 :: "nat \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"vun_from_u8 n x y = 
  (\<exists> v1 v2. x = VPrim (LU8 v1) \<and> y = VAbstract (VUN n v2) \<and> v2 = (unat v1) AND 2^n - 1)"

lemma (in CastValue) vun_from_u8_preservation:
  "\<lbrakk>vval_typing \<Xi>' v (TPrim (Num U8)); vun_from_u8 n v v'\<rbrakk>
    \<Longrightarrow> vval_typing \<Xi>' v' (TCon (name_un n) [] Unboxed)"
  by(fastforce intro:v_t_abstract simp add:un_abs_typing_v_def bitAND_nat_def vun_from_u8_def)


sublocale CastValue \<subseteq> monomorph_sem un_abs_typing_v
  by (unfold_locales)

context CastValue begin

text "If user defines for \<xi>n, we can derive \<xi>i for i < n" 

definition \<xi>m0 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool "
  where
"\<xi>m0 f x y =
    (if f = ''u4_to_u8'' then vun_to_u8 4 x y
   else if f = ''u8_to_u4'' then vun_from_u8 4 x y
   else if f = ''u2_to_u8'' then vun_to_u8 2 x y
   else if f = ''u8_to_u2'' then vun_from_u8 2 x y
   else False)"

subsection "Preservation for abstract functions"

text "If user proves for \<xi>n, we can derive \<xi>i for i < n" 

lemma \<xi>m0_matches_\<Xi>:
  "proc_env_matches \<xi>m0  \<Xi>"
  unfolding proc_env_matches_def \<xi>m0_def
  apply clarsimp
   apply (intro conjI impI;
         simp add: \<Xi>_simps 
Generated_TypeProof.u8_to_u2_type_def
Generated_TypeProof.u8_to_u4_type_def
Generated_TypeProof.u4_to_u8_type_def
Generated_TypeProof.u2_to_u8_type_def
                   Generated_TypeProof.abbreviated_type_defs;
clarsimp simp add:subst_wellformed_def)                        
     apply (rule vun_from_u8_preservation[where n = 2, simplified, simplified char_of_def, simplified];simp)
    apply (rule vun_to_u8_preservation[where n = 2, simplified, simplified char_of_def, simplified];simp)
   apply (rule vun_from_u8_preservation[where n = 4, simplified, simplified char_of_def, simplified];simp)
  apply (rule vun_to_u8_preservation[where n = 4, simplified, simplified char_of_def, simplified];simp)
  done



end (* of context *)

section "Abstract functions specifications for the polymorphic value semantics"

text "If user defines \<xi>n, we can derive \<xi>i for i < n" 

definition \<xi>p0 :: "funtyp \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"\<xi>p0 f x y =
    (if f = ''u4_to_u8'' then vun_to_u8 4 x y
   else if f = ''u8_to_u4'' then vun_from_u8 4 x y
   else if f = ''u2_to_u8'' then vun_to_u8 2 x y
   else if f = ''u8_to_u2'' then vun_from_u8 2 x y
   else False)"



section "Correspondence between abstract functions in the update semantics and C"

context Generated begin


end (* of context *)

sublocale CastUpdate \<subseteq> Generated _ un_abs_typing_u un_abs_repr
  by (unfold_locales)

sublocale CastUpdate \<subseteq> update_sem_init un_abs_typing_u un_abs_repr
  by (unfold_locales)


section "Simplification of corres definition for abstract functions"

context update_sem_init begin

definition
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
      (\<forall>r' w'. val_rel x x'
        \<and> \<Xi>', \<sigma> \<turnstile> x :u fst (snd (snd (snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>
        \<longrightarrow> \<not> snd (afun_mon x' st)
            \<and> (\<forall>st' y'. (y', st') \<in> fst (afun_mon x' st)
                \<longrightarrow> (\<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y)
                    \<and> val_rel y y' \<and> (\<sigma>', st') \<in> srel))))"

lemma absfun_corres:
  "abs_fun_rel \<Xi>' srel s \<xi>' afun' \<sigma> st (\<gamma> ! i) v'
  \<Longrightarrow> i < length \<gamma> \<Longrightarrow> val_rel (\<gamma> ! i) v'
  \<Longrightarrow> \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi>' s)))))
  \<Longrightarrow> corres srel
     (App (AFun s [] []) (Var i))
     (do x \<leftarrow> afun' v'; gets (\<lambda>s. x) od)
     \<xi>' \<gamma> \<Xi>' \<Gamma>' \<sigma> st"
  apply (clarsimp simp: corres_def abs_fun_rel_def)
  apply (frule matches_ptrs_length, simp)
  apply (frule(2) matches_ptrs_proj_single')
  apply clarsimp
  apply (erule impE, blast)
  apply clarsimp
  apply (elim allE, drule mp, blast)
  apply clarsimp
  apply (intro exI conjI[rotated], assumption+)
  apply (rule u_sem_abs_app)
    apply (rule u_sem_afun)
   apply (rule u_sem_var)
  apply simp
  done

lemma abs_fun_rel_def':
  "abs_fun_rel \<Xi>' srel afun_name \<xi>' afun_mon \<sigma> st x x'
    = (proc_ctx_wellformed \<Xi>' \<longrightarrow> \<xi>' matches-u \<Xi>' \<longrightarrow> (\<sigma>,st) \<in> srel \<longrightarrow>
        (\<forall>r' w'. val_rel x x' \<and> \<Xi>', \<sigma> \<turnstile> x :u fst (snd (snd (snd (\<Xi>' afun_name)))) \<langle>r', w'\<rangle>
        \<longrightarrow> \<lbrace>\<lambda>s0. s0 = st\<rbrace> 
              afun_mon x' 
            \<lbrace>\<lambda>y' s'. \<exists>\<sigma>' y. \<xi>' afun_name (\<sigma>, x) (\<sigma>', y) \<and> (\<sigma>',s') \<in> srel \<and> val_rel y y'\<rbrace>!))" 
  by (fastforce  simp: abs_fun_rel_def validNF_def valid_def no_fail_def)

end (* of context *)

inductive_cases (in update_sem) u_t_tconE: "\<Xi>', \<sigma> \<turnstile> u :u TCon n ts s \<langle>r, w\<rangle>"
inductive_cases (in update_sem) u_t_tprimE: "\<Xi>', \<sigma> \<turnstile> u :u TPrim t \<langle>r, w\<rangle>"


context CastUpdate begin

lemma u4_to_u8_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''u4_to_u8'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''u4_to_u8'' [] []) (Var i)) (do x <- u4_to_u8' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply(rule absfun_corres)    
     apply(clarsimp simp add:abs_fun_rel_def u4_to_u8'_def \<Xi>_simps \<xi>_0_simps u4_to_u8_type_def)
     apply (erule u_t_tconE)
       apply clarsimp
       apply monad_eq        
       apply (clarsimp simp: uun_to_u8_def  val_rel_U4_C_def val_rel_word_def  is_signed_bit0_def word_bits_size word_bits_def)       
       apply word_bitwise       
      apply(simp_all)
  done

lemma u2_to_u8_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''u2_to_u8'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''u2_to_u8'' [] []) (Var i)) (do x <- u2_to_u8' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply(rule absfun_corres)    
     apply(clarsimp simp add:abs_fun_rel_def u2_to_u8'_def \<Xi>_simps \<xi>_0_simps u2_to_u8_type_def)
     apply (erule u_t_tconE)
       apply clarsimp
       apply monad_eq        
       apply (clarsimp simp: uun_to_u8_def  val_rel_U2_C_def val_rel_word_def  is_signed_bit0_def word_bits_size word_bits_def)       
       apply word_bitwise       
      apply(simp_all)
  done

lemma u8_to_u4_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''u8_to_u4'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''u8_to_u4'' [] []) (Var i)) (do x <- u8_to_u4' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply(rule absfun_corres)    
     apply(clarsimp simp add:abs_fun_rel_def u8_to_u4'_def \<Xi>_simps \<xi>_0_simps u8_to_u4_type_def)
     apply (erule u_t_tprimE)
     apply clarsimp
     apply monad_eq        
     apply (clarsimp simp: uun_from_u8_def  val_rel_U4_C_def val_rel_word_def  is_signed_bit0_def word_bits_size word_bits_def)       
     apply(thin_tac "Num U8 = _")
     apply(clarsimp simp add:word_size bitAND_nat_def)
     apply(simp flip: ucast_and_mask[where n=4, simplified mask_def, simplified])
     apply(simp add:ucast_id unat_def uint_and)
     apply word_bitwise
  apply(simp_all)
  done

lemma u8_to_u2_corres:
  "\<And>i \<gamma> v' \<Gamma>' \<sigma> st.
    \<lbrakk>i < length \<gamma>; val_rel (\<gamma> ! i) v';
     \<Gamma>' ! i = Some (fst (snd (snd (snd (\<Xi> ''u8_to_u2'')))))\<rbrakk>
    \<Longrightarrow> corres state_rel (App (AFun ''u8_to_u2'' [] []) (Var i)) (do x <- u8_to_u2' v';
        gets (\<lambda>s. x)
     od)
         \<xi>_0 \<gamma> \<Xi> \<Gamma>' \<sigma> st"
  apply(rule absfun_corres)    
     apply(clarsimp simp add:abs_fun_rel_def u8_to_u2'_def \<Xi>_simps \<xi>_0_simps u8_to_u2_type_def)
     apply (erule u_t_tprimE)
     apply clarsimp
     apply monad_eq        
     apply (clarsimp simp: uun_from_u8_def  val_rel_U2_C_def val_rel_word_def  is_signed_bit0_def word_bits_size word_bits_def)       
     apply(thin_tac "Num U8 = _")
     apply(clarsimp simp add:word_size bitAND_nat_def)
     apply(simp flip: ucast_and_mask[where n=2, simplified mask_def, simplified])
     apply(simp add:ucast_id unat_def uint_and)
     apply word_bitwise
  apply(simp_all)
  done

end (* of context *)


section "Correspondence between abstract functions in the update and value semantics"

section "Cast Locale Definition"

locale Cast = 
  upd: CastUpdate +
  val: CastValue
begin

  definition  "un_abs_upd_val \<Xi>' au av name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    upd.un_abs_typing_u \<Xi>' au name \<tau>s sig r w \<sigma> \<and> val.un_abs_typing_v \<Xi>' av name \<tau>s \<and>
    (case au of     
        UUN s n \<Rightarrow> (
            case av of
              VUN s' n' \<Rightarrow> s = s' \<and> n = n'
              | _ \<Rightarrow> False
         )
      | _ \<Rightarrow> (case av of
                VTOther _ \<Rightarrow> True
             |  _ \<Rightarrow> False))"

lemma un_abs_upd_val_elims:
  "un_abs_upd_val \<Xi>' au av n \<tau>s s r w \<sigma> \<Longrightarrow> upd.un_abs_typing_u \<Xi>' au n \<tau>s s r w \<sigma>"
  "un_abs_upd_val \<Xi>' au av n \<tau>s s r w \<sigma> \<Longrightarrow> val.un_abs_typing_v \<Xi>' av n \<tau>s"
  "un_abs_upd_val \<Xi>' (UUN sz vl) (VUN sz' vl') n \<tau>s s r w \<sigma>
    \<Longrightarrow> sz = sz' \<and> vl = vl'"
  by (unfold un_abs_upd_val_def[abs_def]; 
      clarsimp split: atyp.splits vatyp.splits type.splits prim_type.splits)+

lemma un_abs_upd_val_uvun_elims:
  "un_abs_upd_val \<Xi>' (UUN sz vl) (VUN sz' vl') n \<tau>s s r w \<sigma>
    \<Longrightarrow> sz = sz' \<and> vl = vl'"
  using un_abs_upd_val_elims
  by metis
  



end (* of context *)

sublocale Cast \<subseteq> correspondence upd.un_abs_repr val.un_abs_typing_v upd.un_abs_typing_u un_abs_upd_val
  apply (unfold_locales)
     apply (unfold un_abs_upd_val_def[abs_def]; clarsimp split: atyp.splits vatyp.splits)
    apply (unfold un_abs_upd_val_def[abs_def]; clarsimp split: atyp.splits vatyp.splits)
   apply (unfold un_abs_upd_val_def[abs_def]; clarsimp split: atyp.splits vatyp.splits)
  using upd.abs_typing_bang val.abs_typing_bang
     apply blast+
apply (unfold un_abs_upd_val_def[abs_def]; clarsimp split: atyp.splits vatyp.splits)
    apply (drule upd.abs_typing_frame[rotated 1]; simp?)+
  done

inductive_cases (in correspondence) u_v_uprimE     [elim] : "\<Xi>', \<sigma> \<turnstile> UPrim l \<sim> v : TPrim \<tau> \<langle>r, w\<rangle>"
inductive_cases (in correspondence) u_v_tconE      : "\<Xi>', \<sigma> \<turnstile> u \<sim> v : TCon a b c \<langle>r, w\<rangle>"

context Cast begin




section "Cast Methods"

subsection "un_from_u8"

lemma uvun_from_u8_monocorrespond_upward_propagation:
  "\<And>\<sigma> \<sigma>' au av v v' r w.
       \<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TPrim (Num U8)) r w;
        uun_from_u8 n (\<sigma>, au) (\<sigma>', v)\<rbrakk>
       \<Longrightarrow> (vun_from_u8 n av v' \<longrightarrow>
            (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' (TCon (name_un n) [] Unboxed) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
            (\<exists>v'. vun_from_u8 n av v')"
  apply (clarsimp simp: vun_from_u8_def uun_from_u8_def)  
  apply (erule u_v_uprimE; clarsimp)
  apply (intro exI[where x = "{}"])
  apply (simp add:upd.frame_id)
  apply(intro u_v_abstract)  
   apply (simp add:un_abs_upd_val_def)
   apply(simp add:upd.un_abs_typing_u_def val.un_abs_typing_v_def)
   apply(simp add:bitAND_nat_def)
  apply simp
  done

lemma uvun_to_u8_monocorrespond_upward_propagation:
  "\<And>\<sigma> \<sigma>' au av v v' r w.
       \<lbrakk>upd_val_rel \<Xi>' \<sigma> au av (TCon (name_un n) [] Unboxed) r w;
        uun_to_u8 n (\<sigma>, au) (\<sigma>', v)\<rbrakk>
       \<Longrightarrow> (vun_to_u8 n av v' \<longrightarrow>
            (\<exists>r' w'. upd_val_rel \<Xi>' \<sigma>' v v' (TPrim (Num U8)) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w')) \<and>
            (\<exists>v'. vun_to_u8 n av v')"
  apply (clarsimp simp: vun_to_u8_def uun_to_u8_def)  
  apply (erule u_v_tconE; clarsimp)
  apply(intro conjI)
   apply(intro impI)
   apply clarsimp
   apply(frule un_abs_upd_val_uvun_elims, clarsimp)
   apply(intro exI conjI)+
     apply(rule u_v_prim[where l = "LU8 (of_nat _)", simplified])
    apply simp
   apply (simp add:un_abs_upd_val_def upd.un_abs_typing_u_def upd.frame_id)
  apply (simp add:un_abs_upd_val_def)
  apply(case_tac a';simp)
  done






end 
sublocale Cast \<subseteq> correspondence_init upd.un_abs_repr val.un_abs_typing_v upd.un_abs_typing_u un_abs_upd_val
  by (unfold_locales)

context Cast begin

lemma \<xi>_0_\<xi>m0_matchesuv_\<Xi>:
  "proc_env_u_v_matches \<xi>_0 val.\<xi>m0  \<Xi>"
  unfolding proc_env_u_v_matches_def \<xi>0_def val.\<xi>m0_def
  apply clarsimp
  apply (rule conjI; clarsimp simp: \<Xi>_simps 
Generated_TypeProof.u8_to_u2_type_def
Generated_TypeProof.u2_to_u8_type_def
Generated_TypeProof.u8_to_u4_type_def
Generated_TypeProof.u4_to_u8_type_def

                                    Generated_TypeProof.abbreviated_type_defs
uvun_to_u8_monocorrespond_upward_propagation[where n = 2, simplified, simplified char_of_def, simplified]
uvun_from_u8_monocorrespond_upward_propagation[where n = 2,  simplified, simplified char_of_def, simplified]
uvun_to_u8_monocorrespond_upward_propagation[where n = 4, simplified, simplified char_of_def, simplified]
uvun_from_u8_monocorrespond_upward_propagation[where n = 4,  simplified, simplified char_of_def, simplified]

                                    
)+
  done

end (* of context *)

section "Monomorphisation of abstract functions"

context CastValue begin

lemma  vun_from_u8_monoexpr_correct:
  "\<And>v v'.
       vun_from_u8 n (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vun_from_u8 n v v''"
  apply (clarsimp simp: vun_from_u8_def)
  apply (case_tac v; clarsimp)
  done

lemma vun_to_u8_monoexpr_correct:
  "\<And>v v'.
       vun_to_u8 n (rename_val rename' (monoval v)) v'
       \<Longrightarrow> \<exists>v''. v' = rename_val rename' (monoval v'') \<and> vun_to_u8 n v v''"
  apply (clarsimp simp: vun_to_u8_def)
  apply (case_tac v; clarsimp)
  done

lemma rename_mono_prog_\<xi>m0_\<xi>p0:
  "rename_mono_prog rename \<Xi> \<xi>m0 \<xi>p0"   
  unfolding rename_mono_prog_def \<xi>m0_def \<xi>p0_def
  apply clarsimp
  apply (intro conjI impI; clarsimp?)
    apply (subst (asm) rename_def,
           clarsimp simp: assoc_lookup.simps 
                    vun_to_u8_monoexpr_correct vun_from_u8_monoexpr_correct
                    split: if_splits)+
  done

end (* of context *)

section "Correspondence between shallow and polymorphic value semantics"

sublocale CastValue \<subseteq> shallow un_abs_typing_v
  by (unfold_locales)


section 'shallow'

section "Shallow definitions of casts"


overloading su8_to_u4 \<equiv> u8_to_u4
begin
definition su8_to_u4 :: "8 word \<Rightarrow> 4 word" where "su8_to_u4 = ucast"
end

overloading su8_to_u2 \<equiv> u8_to_u2
begin
definition su8_to_u2 :: "8 word \<Rightarrow> 2 word" where "su8_to_u2 = ucast"
end

overloading su2_to_u8 \<equiv> u2_to_u8
begin
definition su2_to_u8 :: "2 word \<Rightarrow> 8 word" where "su2_to_u8 = ucast"
end

overloading su4_to_u8 \<equiv> u4_to_u8
begin
definition su4_to_u8 :: "4 word \<Rightarrow> 8 word" where "su4_to_u8 = ucast"
end



overloading
  valRel_U4 \<equiv> valRel
begin
definition valRel_U4:
"\<And>\<xi>' x v. 
  valRel_U4 (\<xi>' :: (funtyp, vabstyp) vabsfuns) (x :: U4) (v :: (funtyp, vabstyp) vval) \<equiv> 
     (v = VAbstract (VUN 4 (unat x)))
"
end

overloading
  valRel_U2 \<equiv> valRel
begin
definition valRel_U2:
"\<And>\<xi>' x v. 
  valRel_U2 (\<xi>' :: (funtyp, vabstyp) vabsfuns) (x :: U2) (v :: (funtyp, vabstyp) vval) \<equiv> 
     (v = VAbstract (VUN 2 (unat x)))
"
end



sublocale CastValue \<subseteq> shallow un_abs_typing_v
  by (unfold_locales)


(* these are not explicitly needed, since they are sorried by cogent ! ! *)

lemma (in CastValue) scorres_u2_to_u8:
  "scorres (u2_to_u8 :: 2 word \<Rightarrow> 8 word)
     (AFun ''u2_to_u8'' ts ls) \<gamma> \<xi>p0"
 apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp simp add:\<xi>p0_def)
  apply (erule notE)
  unfolding vun_to_u8_def su2_to_u8_def valRel_U2
  apply (clarsimp split: if_splits)  
  using ucast_nat_def by blast

lemma (in CastValue) scorres_u8_to_u2:
  "scorres (u8_to_u2 :: 8 word \<Rightarrow> 2 word)
     (AFun ''u8_to_u2'' ts ls) \<gamma> \<xi>p0"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp simp add:\<xi>p0_def)
  apply (erule notE)
  unfolding vun_from_u8_def su8_to_u2_def valRel_U2
  apply (clarsimp)    
  apply(simp add:unat_def)
  apply(simp add:bitAND_nat_def)
  apply (simp add:Bits_Int.AND_mod[where n = 2, simplified])
  apply(rule HOL.arg_cong[where f = "nat"])
  apply(simp add:ucast_def)
  by (simp add: int_word_uint)


lemma (in CastValue) scorres_u4_to_u8:
  "scorres (u4_to_u8 :: 4 word \<Rightarrow> 8 word)
     (AFun ''u4_to_u8'' ts ls) \<gamma> \<xi>p0"
    apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp simp add:\<xi>p0_def)
  apply (erule notE)
  unfolding vun_to_u8_def su4_to_u8_def valRel_U4
  apply (clarsimp)  
  using ucast_nat_def by blast

lemma (in CastValue) scorres_u8_to_u4:
  "scorres (u8_to_u4 :: 8 word \<Rightarrow> 4 word)
     (AFun ''u8_to_u4'' ts ls) \<gamma> \<xi>p0"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp simp add:\<xi>p0_def)
  apply (erule notE)
  unfolding vun_from_u8_def su8_to_u4_def valRel_U4
  apply (clarsimp)    
  apply(simp add:unat_def)
  apply(simp add:bitAND_nat_def)
  apply (simp add:Bits_Int.AND_mod[where n = 4, simplified])
  apply(rule HOL.arg_cong[where f = "nat"])
  apply(simp add:ucast_def)
  by (simp add: int_word_uint)

section "All refine"

definition foo_spec :: "R\<^sub>T \<Rightarrow> R\<^sub>T"
  where "foo_spec f = 
(if  f1\<^sub>f f then
f \<lparr> f3\<^sub>f := f3\<^sub>f f && 0x0c \<rparr>
else
f \<lparr> f2\<^sub>f := f2\<^sub>f f + 1 \<rparr>)"

lemma foo_shallow_correct: "Generated_Shallow_Desugar.foo x = foo_spec x"
  apply(clarsimp  simp add:foo_spec_def Generated_Shallow_Desugar.foo_def
Let\<^sub>d\<^sub>s_def take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def su4_to_u8_def su2_to_u8_def su8_to_u2_def su8_to_u4_def 
)
  apply(cases "f1\<^sub>f x"; clarsimp)
   apply(simp flip:ucast_down_bitwise(2)[where y = "0x0C"])
   apply (simp add: ucast_id)
  apply(clarsimp  simp add:cast_simps)
  apply(simp add:ucast_id)
  done
  

sublocale Cast \<subseteq> Generated_cogent_shallow _ upd.un_abs_repr val.un_abs_typing_v upd.un_abs_typing_u un_abs_upd_val
  by (unfold_locales)

context Cast begin

lemmas corres_shallow_C_foo_concrete =  corres_shallow_C_foo[folded \<Xi>_def, simplified,
  OF upd.u4_to_u8_corres[simplified], simplified, simplified \<Xi>_simps, simplified,
  OF upd.u8_to_u4_corres[simplified], simplified, simplified \<Xi>_simps, simplified
, OF upd.u2_to_u8_corres[simplified], simplified, simplified \<Xi>_simps, simplified
, OF upd.u8_to_u2_corres[simplified], simplified, simplified \<Xi>_simps, simplified
, OF correspondence_init_axioms val.rename_mono_prog_\<xi>m0_\<xi>p0
 _ _ proc_ctx_wellformed_\<Xi> val.\<xi>m0_matches_\<Xi>,
simplified, simplified foo_shallow_correct
]

(* TODO *)
(*
corollary foo_C_correct:
  "\<lbrakk>
    cc = upd.foo' p

    \<rbrakk> \<Longrightarrow>
   \<not> prod.snd (cc s) \<and> 
   (\<forall>r s'. (r, s') \<in> prod.fst (cc s) \<longrightarrow>
      same_array s s' p \<and>
      r = p
      (r < length (arrlist (s, p)) \<longrightarrow> (arrlist (s, p)) ! unat r = v) \<and> 
      (\<not> unat r < length (arrlist (s, p)) \<longrightarrow> v \<notin> set (arrlist (s, p))))"
(*
p is valid pointer
(let w = heap s p;
unfold a value relation
*) 

*)
end






end