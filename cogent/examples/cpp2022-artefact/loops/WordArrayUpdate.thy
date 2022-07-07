theory WordArrayUpdate
  imports
    UpdateSemHelper
    "build/Generated_CorresSetup"
    
begin

section "Helper Word Lemmas"

lemma word_mult_cancel_left: 
  fixes a b c :: "('a::len) word"
  assumes "uint c * uint a \<le> uint (max_word :: ('a::len) word)"
  assumes "uint c * uint b \<le> uint (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  apply (rule iffI)
   using assms
   apply (unfold word_mult_def word_of_int_def)
    apply (clarsimp simp:Abs_word_inject max_word_def uint_word_of_int m1mod2k uint_0_iff )
   apply fastforce
   done

lemma word_mult_cancel_left_bounded: 
  fixes a b c d :: "('a::len) word"
  assumes "a \<le> d" "b \<le> d"
  assumes "unat c * unat d \<le> unat (max_word :: ('a::len) word)"
  shows "c * a = c * b \<longleftrightarrow> c = 0 \<or> a = b"
  using assms
  apply -
  apply (clarsimp simp: word_le_nat_alt)
  apply (frule_tac i = "unat a" and j = "unat d" and k = "unat c" in mult_le_mono2)
  apply (drule_tac i = "unat b" and j = "unat d" and k = "unat c" in mult_le_mono2)
  by (metis (mono_tags, hide_lams) assms(3) le_unat_uoi mult_left_cancel mult_zero_left not_less_iff_gr_or_eq unat_0 unat_mono word_arith_nat_mult)

section "Helper Functions"

fun is_prim_type :: "type \<Rightarrow> bool"
  where
"is_prim_type (TPrim _) = True" |
"is_prim_type _ = False"

fun is_num_type :: "prim_type \<Rightarrow> bool"
  where
"is_num_type (Num _) = True" |
"is_num_type _ = False"

fun size_of_num_type :: "num_type \<Rightarrow> ptrtyp"
  where
"size_of_num_type U8 = of_nat (size_of (TYPE(8 word)))" |
"size_of_num_type U16 = of_nat (size_of (TYPE(16 word)))" |
"size_of_num_type U32 = of_nat (size_of (TYPE(32 word)))" |
"size_of_num_type U64 = of_nat (size_of (TYPE(64 word)))"

fun size_of_prim_type :: "prim_type \<Rightarrow> ptrtyp"
  where
"size_of_prim_type Bool = of_nat (size_of (TYPE(bool_t_C)))" |
"size_of_prim_type (Num x) = size_of_num_type x" |
"size_of_prim_type _ = undefined"

fun size_of_type :: "type \<Rightarrow> ptrtyp"
  where
"size_of_type (TPrim t) = size_of_prim_type t" |
"size_of_type _ = undefined"

lemma size_of_num_type_not_zero:
  "size_of_num_type t \<noteq> 0"
  by (case_tac t; clarsimp)

section "Base Level Locale"

locale level0_update begin

definition l0u_repr :: "abstyp \<Rightarrow> name \<times> repr list"
  where
"l0u_repr a \<equiv> case a of
      UWA t _ _ \<Rightarrow> (''WordArray'', [type_repr t])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"

definition l0u_typing :: "('f \<Rightarrow> poly_type) \<Rightarrow> 'au \<Rightarrow> name \<Rightarrow> Cogent.type list \<Rightarrow> sigil \<Rightarrow> 'l set \<Rightarrow> 'l set \<Rightarrow> ('f, 'au, 'l) store \<Rightarrow> bool"
  where
"l0u_typing \<Xi>' a v t s r w \<sigma> = False"

end

sublocale level0_update \<subseteq> update_sem l0u_typing l0u_repr
  apply (unfold l0u_typing_def[abs_def] l0u_repr_def[abs_def])
  apply (unfold_locales)
  by simp+


section "Word Array Locale"

locale WordArrayUpdate =
  l0: level0_update
begin

  definition "wa_abs_repr a \<equiv> case a of
      UWA t _ _ \<Rightarrow> (''WordArray'', [type_repr t])
    | _ \<Rightarrow> (''Unknown Abstract Type'', [])"
  
  definition "wa_abs_typing_u \<Xi>' a name \<tau>s sig (r :: ptrtyp set) (w :: ptrtyp set) \<sigma> \<equiv>
    (case a of
      UWA t len arr \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [t] \<and> sig \<noteq> Unboxed \<and>
                       no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t \<and>
                       (sigil_perm sig = option.Some ReadOnly \<longrightarrow> w = {} \<and> 
                        r = {arr + size_of_type t * i | i. i < len}) \<and>
                       (sigil_perm sig = option.Some Writable \<longrightarrow> r = {} \<and> 
                        w = {arr + size_of_type t * i | i. i < len}) \<and>
                       (\<forall>i < len. \<exists>x. \<sigma>(arr + size_of_type t * i) = option.Some x \<and> 
                                     l0.uval_typing \<Xi>' \<sigma> x t {} {} ) \<and>
                       unat (size_of_type t)  * unat len \<le> unat (max_word :: ptrtyp)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [] \<and> r = {} \<and> w = {} \<and> sig = Unboxed)"

lemma wa_abs_typing_u_elims:
  "wa_abs_typing_u \<Xi>' a ''WordArray'' \<tau>s s r w \<sigma> 
    \<Longrightarrow> \<exists>len arr t. a = UWA t len arr \<and> \<tau>s = [t]"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s (Boxed ReadOnly ptrl) r w \<sigma>
    \<Longrightarrow> r = {arr + size_of_type t * i | i. i < len} \<and> w = {}"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s (Boxed Writable ptrl) r w \<sigma>
    \<Longrightarrow> r = {} \<and> w = {arr + size_of_type t * i | i. i < len}"
  "wa_abs_typing_u \<Xi>' a ''WordArray'' \<tau>s s r w \<sigma> \<Longrightarrow> s \<noteq> Unboxed"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s s r w \<sigma>
    \<Longrightarrow> \<forall>i < len. \<exists>x. \<sigma> (arr + size_of_type t * i) = option.Some x \<and> l0.uval_typing \<Xi>' \<sigma> x t {} {}"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s s r w \<sigma>
    \<Longrightarrow> unat (size_of_type t) * unat len \<le> unat (max_word :: ptrtyp)"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s s r w \<sigma> \<Longrightarrow> n = ''WordArray''"
  "wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s s r w \<sigma> \<Longrightarrow> no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t"
  by (unfold wa_abs_typing_u_def[abs_def]; clarsimp split: atyp.splits type.splits)+

lemma distinct_indices:
  "\<lbrakk>wa_abs_typing_u \<Xi>' (UWA t len arr) n ts s r w \<sigma>; size_of_type t > 0\<rbrakk> \<Longrightarrow> 
    \<forall>i < len. \<forall>j < len. i = j \<longleftrightarrow> size_of_type t * i = size_of_type t * j"
  apply clarsimp
  apply (rule iffI)
   apply clarsimp
  apply (clarsimp simp: wa_abs_typing_u_def)
  apply (cut_tac a = i and b = j and c = "size_of_type t" and d = len in word_mult_cancel_left_bounded; simp)
  apply (erule disjE; clarsimp)
  done

lemma wa_abs_typing_u_update:
  "\<lbrakk>wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s (Boxed Writable ptrl) r w \<sigma>;
    i < len; l0.uval_typing \<Xi>' \<sigma> v t {} {}\<rbrakk> 
    \<Longrightarrow> wa_abs_typing_u \<Xi>' (UWA t len arr) n \<tau>s (Boxed Writable ptrl) r w 
      (\<sigma> ((arr + size_of_type t * i) \<mapsto> v))"
  apply (clarsimp simp: wa_abs_typing_u_def)
  apply (rule conjI; clarsimp)
   apply (erule l0.uval_typing_frame(1)[where w = "{}" and r = "{}", simplified, OF l0.frame_single_update])
  apply (rename_tac j)
  apply (erule_tac x = j in allE; clarsimp)
  apply (erule l0.uval_typing_frame(1)[where w = "{}" and r = "{}", simplified, OF l0.frame_single_update])
  done

end (* of context *)

sublocale WordArrayUpdate \<subseteq> update_sem wa_abs_typing_u wa_abs_repr
  apply (unfold wa_abs_repr_def[abs_def] wa_abs_typing_u_def[abs_def])
  apply (unfold_locales; clarsimp split: atyp.splits)
        apply (clarsimp simp: no_heap_imp_bang)
        apply (case_tac s; clarsimp; rename_tac perm ptrl; case_tac perm; clarsimp)
       apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
      apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
     apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
    apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
     apply (elim allE impE, assumption, elim exE conjE, intro exI, assumption)
    apply (elim allE impE, assumption, elim exE conjE, intro exI, assumption)
  (* apply (case_tac s; clarsimp; case_tac s'; clarsimp)*)
  apply (erule allE, erule  impE, assumption)
  apply clarsimp
  apply (frule l0.uval_typing_frame; simp?)
  apply (intro exI conjI; simp?)
  apply (clarsimp simp: frame_def)
  apply (rename_tac t len arr i x)
  apply (erule_tac x = "arr + size_of_type t * i" in allE)
  apply (case_tac s; clarsimp; rename_tac perm; case_tac perm; clarsimp)
   apply (drule_tac x = "arr + size_of_type t * i" in orthD1; clarsimp)
   apply (intro exI conjI; simp?)
  apply (drule_tac x = "arr + size_of_type t * i" in orthD1; clarsimp)
  apply (intro exI conjI; simp?)
  done

lemma (in WordArrayUpdate) l0_eq_uval_repr:
  "l0.uval_repr x = uval_repr x" 
  apply (induct x; clarsimp simp: l0.l0u_repr_def wa_abs_repr_def)
  done

lemma (in WordArrayUpdate) l0_eq_uval_repr_deep:
  "l0.uval_repr_deep x = uval_repr_deep x" 
  apply (induct x; clarsimp simp: l0.l0u_repr_def wa_abs_repr_def)
  done

lemma (in WordArrayUpdate) l0_imp_uval_typing:
  shows "l0.uval_typing \<Xi>' \<sigma> v t r w\<Longrightarrow> uval_typing \<Xi>' \<sigma> v t r w"
  and   "l0.uval_typing_record \<Xi>' \<sigma> vs ts r w \<Longrightarrow> uval_typing_record \<Xi>' \<sigma> vs ts r w"
proof (induct rule: l0.uval_typing_uval_typing_record.inducts)
qed (fastforce intro!: update_sem.uval_typing_uval_typing_record.intros[OF update_sem_axioms]
                 simp: l0_eq_uval_repr l0_eq_uval_repr_deep l0.l0u_typing_def)+

lemma (in WordArrayUpdate) no_tcon_uval_typing_imp_l0:
  "\<lbrakk>no_tvars t; no_tcon t; uval_typing \<Xi>' \<sigma> v t r w\<rbrakk> \<Longrightarrow> l0.uval_typing \<Xi>' \<sigma> v t r w"
proof (induct t arbitrary: \<sigma> v r w)
case (TRecord x1a x2a)
  then show ?case 
    apply (clarsimp simp: find_None_iff_nth)
    apply (erule u_t_trecordE; clarsimp intro!: l0.uval_typing_uval_typing_record.intros)
      apply (drule uval_typing_record_alt1)
      apply (rule l0.uval_typing_record_alt2)
      apply clarsimp
      apply (rule exI, rule conjI, simp)
      apply (rule exI, rule conjI, simp)
      apply clarsimp
      apply (rename_tac i)
      apply (erule_tac x = i in allE; clarsimp)+
      apply (clarsimp simp: l0_eq_uval_repr l0_eq_uval_repr_deep set_conv_nth)
      apply (elim meta_allE meta_impE; simp?)
      apply (intro exI conjI; simp?)
     apply (rule l0.u_t_p_rec_ro; simp?)
     apply (drule uval_typing_record_alt1)
     apply (rule l0.uval_typing_record_alt2)
     apply clarsimp
     apply (rule exI, rule conjI, simp)
     apply (rule exI, rule conjI, simp)
     apply clarsimp
     apply (rename_tac i)
     apply (erule_tac x = i in allE; clarsimp)+
     apply (clarsimp simp: l0_eq_uval_repr l0_eq_uval_repr_deep set_conv_nth)
     apply (elim meta_allE meta_impE; simp?)
     apply (intro exI conjI; simp?)
    apply (rule l0.u_t_p_rec_w; simp?)
    apply (drule uval_typing_record_alt1)
    apply (rule l0.uval_typing_record_alt2)
    apply clarsimp
    apply (rule exI, rule conjI, simp)
    apply (rule exI, rule conjI, simp)
    apply clarsimp
    apply (rename_tac i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: l0_eq_uval_repr l0_eq_uval_repr_deep set_conv_nth)
    apply (elim meta_allE meta_impE; simp?)
    apply (intro exI conjI; simp?)
    done
qed (fastforce elim!: u_t_tfunE u_t_tprimE u_t_tsumE u_t_tproductE u_t_tunitE u_t_tcustomE
              intro!: l0.uval_typing_uval_typing_record.intros
                simp: find_None_iff)+
  
section "Word Array Methods"

subsection "wordarray_length"

definition uwa_length :: "(funtyp, abstyp, ptrtyp) ufundef"
  where
"uwa_length x y = 
  (\<exists>\<sigma> p t len arr. x = (\<sigma>, UPtr p (RCon ''WordArray'' [type_repr t])) \<and> 
    \<sigma> p = option.Some (UAbstract (UWA t len arr)) \<and> y = (\<sigma>, UPrim (LU32 len)))"

lemma (in WordArrayUpdate) uwa_length_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TCon ''WordArray'' \<tau>s (Boxed ReadOnly ptrl)) r w; uwa_length (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' (TPrim (Num U32)) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: uwa_length_def)
  apply (erule u_t_ptrE; clarsimp)
  apply (intro exI conjI, rule u_t_prim', simp, simp, rule frame_id)
  done

lemma uwa_length_determ:
  "\<lbrakk>uwa_length (\<sigma>, x) (\<sigma>', y); uwa_length (\<sigma>, x) (\<sigma>'', z)\<rbrakk>
    \<Longrightarrow> \<sigma>' = \<sigma>'' \<and> y = z"
  unfolding uwa_length_def
  apply (elim exE conjE)
  apply simp
  done


subsection "wordarray_get"

definition uwa_get :: "(funtyp, abstyp, ptrtyp) ufundef"
  where
"uwa_get x y = 
  (\<exists>\<sigma> p t len arr i v. 
    x = (\<sigma>, URecord [(UPtr p (RCon ''WordArray'' [type_repr t]), RPtr (RCon ''WordArray'' [type_repr t])),
                     (UPrim (LU32 i), RPrim (Num U32)), (v, type_repr t)] None) \<and>
    \<sigma> p = option.Some (UAbstract (UWA t len arr)) \<and>
    (if i < len then \<exists>v'. \<sigma> (arr + size_of_type t * i) = option.Some v' \<and> y = (\<sigma>, v') else y = (\<sigma>, v)))"

lemma (in WordArrayUpdate) uwa_get_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TRecord 
                      [(''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                       (''idx'', TPrim (Num U32), Present),
                       (''val'', t, Present)] Unboxed) r w;
    uwa_get (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' t r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: uwa_get_def)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1))
  apply (elim exE conjE)
  apply (drule_tac t = "type_repr  _" in sym)
  apply (drule_tac t = "UWA _ _ _" in sym)
  apply clarsimp
  apply (erule u_t_r_consE; simp)+
  apply (elim conjE)
  apply (erule u_t_r_emptyE; simp)
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_primE)
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
  apply (clarsimp split: if_splits)
   apply (frule  wa_abs_typing_u_elims(5))
   apply (elim allE impE, assumption, clarsimp)
   apply (drule l0_imp_uval_typing)
   apply (intro exI conjI, assumption, blast)
   apply (frule wa_abs_typing_u_elims(8))
   apply (rename_tac p len arr i ra x rb)
   apply clarsimp
   apply (drule (2) no_heap_no_pointers; clarsimp)
   apply (rule frame_id)
  apply (intro exI conjI, assumption, blast, rule frame_id)
  done

lemma uwa_get_determ:
  "\<lbrakk>uwa_get (\<sigma>, x) (\<sigma>', y); uwa_get (\<sigma>, x) (\<sigma>'', z)\<rbrakk>
    \<Longrightarrow> \<sigma>' = \<sigma>'' \<and> y = z"
  unfolding uwa_get_def
  apply (elim exE conjE)
  apply simp
  apply (clarsimp split: if_splits)
  done

subsection "wordarray_put"

definition uwa_put :: "(funtyp, abstyp, ptrtyp) ufundef"
  where
"uwa_put x y = 
  (\<exists>\<sigma> parr p t len arr i v. 
    x = (\<sigma>, URecord [(parr, RPtr (RCon ''WordArray'' [type_repr t])),
                     (UPrim (LU32 i), RPrim (Num U32)), (v, type_repr t)] None) \<and>
    parr = UPtr p (RCon ''WordArray'' [type_repr t]) \<and>
    \<sigma> p = option.Some (UAbstract (UWA t len arr)) \<and> 
    (if i < len then y = (\<sigma>(arr + size_of_type t * i \<mapsto> v), parr) else y = (\<sigma>, parr)))"

lemma (in WordArrayUpdate) uwa_put_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TRecord 
                      [(''arr'', TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
                       (''idx'', TPrim (Num U32), Present),
                       (''val'', t, Present)] Unboxed) r w;
    uwa_put (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl)) r' w' \<and>
                r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: uwa_put_def)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1))
  apply (elim exE conjE)
  apply (drule_tac t = "type_repr  _" in sym)
  apply (drule_tac t = "UWA _ _ _" in sym)
  apply clarsimp
  apply (erule u_t_r_consE; simp)+
  apply (elim conjE)
  apply (erule u_t_r_emptyE; simp)
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_primE)
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
  apply (rename_tac p len arr i ra wa x rb wb)
  apply (rule_tac x = ra in exI)
  apply (rule_tac x = "insert p wa" in exI)
  apply (frule wa_abs_typing_u_elims(8))
  apply clarsimp
  apply (frule (2) no_heap_no_pointers; clarsimp)
  apply (clarsimp split: if_splits)
   apply (rule conjI)
    apply (rule_tac a = "UWA t len arr" in  u_t_p_abs_w[where ts = "[t]", simplified]; simp?)
     apply (rule wa_abs_typing_u_update; simp?)
     apply (erule (2) no_tcon_uval_typing_imp_l0)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
   apply (rule frame_expand(1)[OF frame_single_update_expand]; simp?)
    apply (drule wa_abs_typing_u_elims(3); clarsimp)
    apply (intro exI conjI; simp)
  apply (rule conjI)
   apply (rule_tac a = "UWA t len arr" in  u_t_p_abs_w[where ts = "[t]", simplified]; simp?)
  apply (rule frame_id)
  done

lemma uwa_put_determ:
  "\<lbrakk>uwa_put (\<sigma>, x) (\<sigma>', y); uwa_put (\<sigma>, x) (\<sigma>'', z)\<rbrakk>
    \<Longrightarrow> \<sigma>' = \<sigma>'' \<and> y = z"
  unfolding uwa_put_def
  apply (clarsimp simp only: prod.inject)
  apply (clarsimp split: if_splits)
  done

subsection "wordarray_get_opt"

definition uwa_get_opt :: "(funtyp, abstyp, ptrtyp) ufundef"
  where
"uwa_get_opt x y = 
  (\<exists>\<sigma> p t len arr i. 
    x = (\<sigma>, URecord [(UPtr p (RCon ''WordArray'' [type_repr t]), RPtr (RCon ''WordArray'' [type_repr t])),
                     (UPrim (LU32 i), RPrim (Num U32))] None) \<and>
    \<sigma> p = option.Some (UAbstract (UWA t len arr)) \<and>
    (if i < len 
      then \<exists>v'. \<sigma> (arr + size_of_type t * i) = option.Some v' \<and> 
        y = (\<sigma>, USum ''Something'' v' [(''Nothing'', RUnit), (''Something'', type_repr t)])
    else y = (\<sigma>, USum ''Nothing'' UUnit [(''Nothing'', RUnit), (''Something'', type_repr t)])))"

lemma (in WordArrayUpdate) uwa_get_opt_preservation:
  "\<lbrakk>uval_typing \<Xi>' \<sigma> v (TRecord 
                      [(''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                       (''idx'', TPrim (Num U32), Present)] Unboxed) r w;
    uwa_get_opt (\<sigma>, v) (\<sigma>', v')\<rbrakk>
    \<Longrightarrow> \<exists>r' w'. uval_typing \<Xi>' \<sigma>' v' (TSum [(''Nothing'', TUnit, Unchecked), (''Something'', t, Unchecked)]) r' w' \<and> r' \<subseteq> r \<and> frame \<sigma> w \<sigma>' w'"
  apply (clarsimp simp: uwa_get_opt_def)
  apply (erule u_t_recE; clarsimp)
  apply (erule u_t_r_consE; clarsimp)
  apply (erule u_t_ptrE; clarsimp)
  apply (frule wa_abs_typing_u_elims(1))
  apply (elim exE conjE)
  apply (drule_tac t = "type_repr  _" in sym)
  apply (drule_tac t = "UWA _ _ _" in sym)
  apply clarsimp
  apply (erule u_t_r_consE; simp)+
  apply (elim conjE)
  apply (erule u_t_r_emptyE; simp)
  apply (drule_tac t = "type_repr _" in sym)+
  apply clarsimp
  apply (erule u_t_primE)
  apply (drule_tac t = "lit_type _" in sym; clarsimp)
  apply (clarsimp split: if_splits)
   apply (frule  wa_abs_typing_u_elims(5))
   apply (elim allE impE, assumption, clarsimp)
   apply (drule l0_imp_uval_typing)
   apply (rule_tac x = "{}" in exI)+
   apply simp?
   apply (rule conjI)
    apply (erule u_t_sum; simp?)
   apply (rule frame_id)
  apply (rule_tac x = "{}" in exI)+
  apply simp?
  apply (fastforce intro!: u_t_sum u_t_unit frame_id)
  done

lemma uwa_get_opt_determ:
  "\<lbrakk>uwa_get_opt (\<sigma>, x) (\<sigma>', y); uwa_get_opt (\<sigma>, x) (\<sigma>'', z)\<rbrakk>
    \<Longrightarrow> \<sigma>' = \<sigma>'' \<and> y = z"
  unfolding uwa_get_opt_def
  apply (elim exE conjE)
  apply (clarsimp simp only: prod.inject)
  apply (clarsimp split: if_splits) 
  done

end