theory WordArrayValue
  imports
    ValueSemHelper
begin

section 
"Cogent Value Typing with Arrays"

text 
"Short: 
  For Arrays to be welltyped, they need to carry values of the specified types. As Arrays may carry 
  Cogent values, the definition of typing for Arrays depends on Cogent's typing relation which in turn 
  depend on the typing relation of abstract types. 
  We define two locale interpretations to resolve this circularity: one for pure Cogent types which can 
  be used for defining what it means for Arrays to be welltyped, then another for Cogent including Arrays.

 Detailed:
   In this section we define a typing relation for Arrays on hte value semantics level.
   As Arrays carry Cogent values, they should only be welltyped if the Cogent values are also welltyped.
   Therefore, the typing relation for Arrays relies on the value typing relation of Cogent expressions.
   Recall that the value typing relation also relies on the typing of abstract types. 
   Therefore, first we need to define a value_sem_pure locale that provides a value typing relation for pure Cogent 
   values (with no additional abstract types). Then this is used to define Array typing which is used to 
  define a typing relation for arrays, which in turn is used to define a second value_sem_with_arrays locale 
  instanciating the typing relation of abstract types with that of arrays."

type_synonym funtyp = name
datatype vatyp = VWA type "(name, vatyp) vval list" | VTOther "unit"
type_synonym vabstyp = vatyp

section 
"Pure Cogent Value Semantics Locale"


abbreviation "l0v_typing \<equiv>
       (\<lambda>f a v t. False) :: (name \<Rightarrow> poly_type) \<Rightarrow> vatyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"

interpretation l0 : 
  value_sem  "l0v_typing :: (name \<Rightarrow> poly_type) \<Rightarrow> vatyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
  by unfold_locales

interpretation l0' : 
  value_sem  constrains abs_typing :: "(name \<Rightarrow> poly_type) \<Rightarrow> vatyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
  apply unfold_locales

definition 
  wa_abs_typing_v ::  
    "(name \<Rightarrow> poly_type) \<Rightarrow> vatyp \<Rightarrow> name \<Rightarrow> type list \<Rightarrow> bool"
where
  "wa_abs_typing_v \<Xi>' a name \<tau>s \<equiv>
    (case a of
      VWA t xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [t] \<and> 
      no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t \<and>
      (\<forall>i < length xs. \<exists>x. xs ! i = x \<and>  l0.vval_typing \<Xi>' x t)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"


interpretation value_sem_array :
  value_sem  wa_abs_typing_v 
  by (unfold_locales) (clarsimp split: vatyp.splits simp: no_heap_imp_bang wa_abs_typing_v_def)

locale value_sem_init
context value_sem_init
begin
abbreviation "l0v_typing \<equiv>
       (\<lambda>f a v t. False) :: (funtyp \<Rightarrow> poly_type) \<Rightarrow> vabstyp \<Rightarrow> name \<Rightarrow> Cogent.type list \<Rightarrow> bool"

context value_sem
begin

sublocale level0_value : value_sem l0v_typing
   by (unfold_locales)
  
end



context value_sem 
begin
definition "wa_abs_typing_v \<Xi>' a name \<tau>s \<equiv>
    (case a of
      VWA t xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [t] \<and> 
      no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t \<and>
      (\<forall>i < length xs. \<exists>x. xs ! i = x \<and>  vval_typing \<Xi>' x t)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"

sublocale WordArrayValue: value_sem wa_abs_typing_v  
   by (unfold_locales) (clarsimp split: vatyp.splits simp: no_heap_imp_bang wa_abs_typing_v_def)

sublocale level0_value : value_sem wa_abs_typing_v
  apply (unfold_locales)
  

end

print_theorems


section 
"Cogent with Arrays Value Semantics Locale"

definition "wa_abs_typing_v \<Xi>' a name \<tau>s \<equiv>
    (case a of
      VWA t xs \<Rightarrow> name = ''WordArray'' \<and> \<tau>s = [t] \<and> 
      no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t \<and>
      (\<forall>i < length xs. \<exists>x. xs ! i = x \<and>  level0_value.vval_typing \<Xi>' x t)
    | _ \<Rightarrow> name = ''Unknown Abstract Type'' \<and> \<tau>s = [])"



lemma wa_abs_typing_v_elims:
  "wa_abs_typing_v \<Xi>' a ''WordArray'' \<tau>s \<Longrightarrow> \<exists>t xs. a = VWA t xs \<and> \<tau>s = [t]"
  "wa_abs_typing_v \<Xi>' (VWA t xs) n \<tau>s 
    \<Longrightarrow> \<forall>i < length xs. \<exists>x. xs ! i = x \<and> level0_value.vval_typing \<Xi>' x t"
  "wa_abs_typing_v \<Xi>' (VWA t xs) n \<tau>s  \<Longrightarrow> n = ''WordArray''"
  "wa_abs_typing_v \<Xi>' (VWA t xs) n \<tau>s  \<Longrightarrow> no_tvars t \<and> no_tfun t \<and> no_taken t \<and> no_tcon t \<and> no_theap t"
  by (unfold wa_abs_typing_v_def[abs_def]; clarsimp split: vatyp.splits type.splits prim_type.splits)+

lemma wa_abs_typing_v_update:
  "\<lbrakk>wa_abs_typing_v \<Xi>' (VWA t xs) n \<tau>s; i < length xs; level0_value.vval_typing \<Xi>' v t\<rbrakk> 
    \<Longrightarrow> wa_abs_typing_v \<Xi>' (VWA t (xs[i := v])) n \<tau>s"
  by (clarsimp simp: wa_abs_typing_v_def  nth_list_update)

interpretation WordArrayValue: value_sem wa_abs_typing_v  
   by (unfold_locales) (clarsimp split: vatyp.splits simp: no_heap_imp_bang wa_abs_typing_v_def)

context level0_value 
begin 
sublocale A "int B" end
sublocale level0_value \<subseteq> lattice
lemma  l0_imp_vval_typing:
  shows "level0_value.vval_typing \<Xi>' v t \<Longrightarrow> WordArrayValue.vval_typing \<Xi>' v t"
  and   "level0_value.vval_typing_record \<Xi>' vs ts \<Longrightarrow> WordArrayValue.vval_typing_record \<Xi>' vs ts"
proof (induct rule: level0_value.vval_typing_vval_typing_record.inducts)
qed (fastforce intro!: value_sem.vval_typing_vval_typing_record.intros[OF value_sem_axioms]
                 simp: level0_value.l0v_typing_def)+

lemma (in WordArrayValue) no_tcon_vval_typing_imp_l0:
  "\<lbrakk>no_tvars t; no_tcon t; vval_typing \<Xi>' v t\<rbrakk> \<Longrightarrow> l0.vval_typing \<Xi>' v t"
proof (induct t arbitrary: v)
case (TRecord x1a x2a)
  then show ?case 
    apply (clarsimp simp: find_None_iff_nth)
    apply (erule v_t_trecordE; clarsimp intro!: l0.vval_typing_vval_typing_record.intros)
    apply (drule vval_typing_record_alt1)
    apply (rule l0.vval_typing_record_alt2)
    apply clarsimp
    apply (rename_tac i)
    apply (erule_tac x = i in allE; clarsimp)+
    apply (clarsimp simp: set_conv_nth)
    apply (elim meta_allE meta_impE; simp?)
    apply (intro exI conjI; simp?)
    done
qed (fastforce elim!: v_t_tfunE v_t_tprimE v_t_tsumE v_t_tproductE v_t_tunitE
              intro!: l0.vval_typing_vval_typing_record.intros
                simp: find_None_iff)+

section "Word Array Methods"

subsection "wordarray_length"

definition vwa_length :: "(funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"vwa_length x y = 
  (\<exists>t xs len. x = VAbstract (VWA t xs) \<and> y = VPrim (LU32 len) \<and> length xs = unat len)"

lemma (in WordArrayValue) vwa_length_preservation:
  "\<lbrakk>vval_typing \<Xi>' v (TCon ''WordArray'' \<tau>s (Boxed ReadOnly ptrl)); vwa_length v v'\<rbrakk>
    \<Longrightarrow> vval_typing \<Xi>' v' (TPrim (Num U32))"
  by (fastforce simp: vwa_length_def)

lemma vwa_length_determ:
  "\<lbrakk>vwa_length x y; vwa_length x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding vwa_length_def
  apply (clarsimp simp only: prod.inject)
  apply (clarsimp split: if_splits)
  done

subsection "wordarray_get"

definition vwa_get :: "(funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"vwa_get x y = 
  (\<exists>t xs i v. x = VRecord [VAbstract (VWA t xs), VPrim (LU32 i), v] \<and> no_vfuns y \<and>
    (if unat i < length xs then y = xs ! unat i else y = v))"

lemma (in WordArrayValue) vwa_get_preservation:
  "\<lbrakk>vval_typing \<Xi>' v (TRecord 
                      [(''arr'', TCon ''WordArray'' [t] (Boxed ReadOnly ptrl), Present),
                       (''idx'', TPrim (Num U32), Present),
                       (''val'', t, Present)] Unboxed);
    vwa_get v v'\<rbrakk>
    \<Longrightarrow> vval_typing \<Xi>' v' t"
  apply (clarsimp simp: vwa_get_def)
  apply (elim v_t_recordE v_t_r_consE v_t_primE v_t_abstractE; clarsimp split: if_splits)
  apply (erule notE)
  apply (frule wa_abs_typing_v_elims(1))
  apply (drule wa_abs_typing_v_elims(2))
  apply (elim allE impE, assumption)
  apply clarsimp
  apply (erule l0_imp_vval_typing)
  done

lemma vwa_get_determ:
  "\<lbrakk>vwa_get x y; vwa_get x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding vwa_get_def
  apply (clarsimp simp only: prod.inject)
  apply (clarsimp split: if_splits)
  done

subsection "wordarray_put"

definition vwa_put :: "(funtyp, vabstyp) vval \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"
  where
"vwa_put x y = 
  (\<exists>t xs i v. x = VRecord [VAbstract (VWA t xs), VPrim (LU32 i), v] \<and> no_vfuns v \<and>
    y = VAbstract (VWA t (xs[unat i := v])))"

lemma (in WordArrayValue) vwa_put_preservation:
  "\<lbrakk>vval_typing \<Xi>' v (TRecord 
                      [(''arr'', TCon ''WordArray'' [t] (Boxed Writable ptrl), Present),
                       (''idx'', TPrim (Num U32), Present),
                       (''val'', t, Present)] Unboxed);
    vwa_put v v'\<rbrakk>
    \<Longrightarrow> vval_typing \<Xi>' v' (TCon ''WordArray'' [t] (Boxed Writable ptrl))"
  apply (clarsimp simp: vwa_put_def)
  apply (elim v_t_recordE v_t_r_consE v_t_primE v_t_abstractE v_t_r_emptyE; clarsimp split: if_splits)
  apply (erule notE)
  apply (rule v_t_abstract; simp?)
  apply (frule wa_abs_typing_v_elims(1); clarsimp)
  apply (rename_tac xs i va)
  apply (case_tac "unat i < length xs"; simp?)
  apply (rule wa_abs_typing_v_update; simp?)
  apply (drule wa_abs_typing_v_elims(4); clarsimp)
  apply (erule (2) no_tcon_vval_typing_imp_l0)
  done

lemma vwa_put_determ:
  "\<lbrakk>vwa_put x y; vwa_put x z\<rbrakk>
    \<Longrightarrow> y = z"
  unfolding vwa_put_def
  apply (clarsimp simp only: prod.inject)
  apply (clarsimp split: if_splits)
  done

end