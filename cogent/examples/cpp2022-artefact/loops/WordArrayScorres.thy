theory WordArrayScorres
  imports
    WordArrayMono
    "build/Generated_SCorres_Normal"
    AutoCorres.AutoCorres
begin

section "Shallow word array method definitions"

primrec swa_to_list
  where
"swa_to_list (SWA xs) = xs"

fun list_to_swa
  where
"list_to_swa xs = SWA xs"


overloading swa_length \<equiv> wordarray_length
begin
definition swa_length :: "'a WordArray \<Rightarrow> 32 word"
  where
"swa_length x = (of_nat (length (swa_to_list x)) :: 32 word)"
end (* of overloading *)

overloading swa_get \<equiv> wordarray_get
begin
definition swa_get :: "('a WordArray, 32 word, 'a) WordArrayGetP \<Rightarrow> 'a"
  where
"swa_get x = 
  (let arr = swa_to_list (WordArrayGetP.arr\<^sub>f x);
         i = unat (WordArrayGetP.idx\<^sub>f x);
         v = WordArrayGetP.val\<^sub>f x
   in if i < length arr then arr ! i else v)"
end (* of overloading *)

overloading swa_put \<equiv> wordarray_put
begin
definition swa_put :: "('a WordArray, 32 word, 'a) WordArrayGetP \<Rightarrow> 'a WordArray"
  where
"swa_put x = 
  (let arr = swa_to_list (WordArrayGetP.arr\<^sub>f x);
         i = unat (WordArrayGetP.idx\<^sub>f x);
         v = WordArrayGetP.val\<^sub>f x
   in list_to_swa (arr[i:= v]))"
end (* of overloading *)

overloading swa_get_opt \<equiv> wordarray_get_opt
begin
definition swa_get_opt :: "('a WordArray, 32 word) WordArrayGetOP \<Rightarrow> (unit, 'a) Opt"
  where
"swa_get_opt x = 
  (let arr = swa_to_list (WordArrayGetOP.arr\<^sub>f x);
         i = unat (WordArrayGetOP.idx\<^sub>f x)
   in if i < length arr then Something (arr ! i) else Nothing ())"
end (* of overloading *)

overloading
  valRel_WordArrayWord \<equiv> valRel
begin
definition valRel_WordArrayWord:
"\<And>\<xi>' x v. 
  valRel_WordArrayWord (\<xi>' :: (funtyp, vabstyp) vabsfuns) (x :: (('a::len8) word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
    (if len_of TYPE('a) = 8 then 
        \<exists>xs xs'. v = VAbstract (VWA (TPrim (Num U8)) xs) \<and> xs' = swa_to_list x \<and> length xs' = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU8 (ucast (xs' ! i))))
      else if len_of TYPE('a) = 16 then 
        \<exists>xs xs'. v = VAbstract (VWA (TPrim (Num U16)) xs) \<and> xs' = swa_to_list x \<and> length xs' = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU16 (ucast (xs' ! i))))
      else if len_of TYPE('a) = 32 then 
        \<exists>xs xs'. v = VAbstract (VWA (TPrim (Num U32)) xs) \<and> xs' = swa_to_list x \<and> length xs' = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU32 (ucast (xs' ! i))))
      else if len_of TYPE('a) = 64 then 
        \<exists>xs xs'. v = VAbstract (VWA (TPrim (Num U64)) xs) \<and> xs' = swa_to_list x \<and> length xs' = length xs \<and> (\<forall>i < length xs. (xs ! i) = VPrim (LU64 (ucast (xs' ! i))))
      else False)"
end

sublocale level0_value \<subseteq> shallow l0v_typing
  by (unfold_locales)

sublocale WordArrayValue \<subseteq> shallow wa_abs_typing_v
  by (unfold_locales)

context WordArrayValue begin

lemma wordarray_length_scorres:
  "\<xi> ''wordarray_length'' =  vwa_length 
    \<Longrightarrow> scorres (wordarray_length :: ('a :: len8) word WordArray \<Rightarrow> 32 word) 
        (AFun ''wordarray_length'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_length_def swa_length_def valRel_WordArrayWord
  apply (clarsimp split: if_splits)
  done

lemma wordarray_get_u8_scorres:
  "\<xi> ''wordarray_get'' =  vwa_get 
    \<Longrightarrow> scorres 
       (wordarray_get :: (8 word WordArray, 32 word, 8 word) WordArrayGetP \<Rightarrow> 8 word) 
       (AFun ''wordarray_get'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_def swa_get_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_u16_scorres:
  "\<xi> ''wordarray_get'' =  vwa_get 
    \<Longrightarrow> scorres 
        (wordarray_get :: (16 word WordArray, 32 word, 16 word) WordArrayGetP \<Rightarrow> 16 word) 
        (AFun ''wordarray_get'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_def swa_get_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_u32_scorres:
  "\<xi> ''wordarray_get'' =  vwa_get 
    \<Longrightarrow> scorres 
        (wordarray_get :: (32 word WordArray, 32 word, 32 word) WordArrayGetP \<Rightarrow> 32 word) 
        (AFun ''wordarray_get'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_def swa_get_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_u64_scorres:
  "\<xi> ''wordarray_get'' =  vwa_get 
    \<Longrightarrow> scorres 
        (wordarray_get :: (64 word WordArray, 32 word, 64 word) WordArrayGetP \<Rightarrow> 64 word) 
        (AFun ''wordarray_get'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_def swa_get_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_put_u8_scorres:
  "\<xi> ''wordarray_put'' =  vwa_put 
    \<Longrightarrow> scorres 
        (wordarray_put :: (8 word WordArray, 32 word, 8 word) WordArrayGetP \<Rightarrow> 8 word WordArray) 
        (AFun ''wordarray_put'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_put_def swa_put_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  by (metis (no_types, hide_lams) nth_list_update_eq nth_list_update_neq)

lemma wordarray_put_u16_scorres:
  "\<xi> ''wordarray_put'' =  vwa_put 
    \<Longrightarrow> scorres (wordarray_put :: (16 word WordArray, 32 word, 16 word) WordArrayGetP \<Rightarrow> 16 word WordArray) (AFun ''wordarray_put'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_put_def swa_put_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  by (metis (no_types, hide_lams) nth_list_update_eq nth_list_update_neq)

lemma wordarray_put_u32_scorres:
  "\<xi> ''wordarray_put'' =  vwa_put 
    \<Longrightarrow> scorres (wordarray_put :: (32 word WordArray, 32 word, 32 word) WordArrayGetP \<Rightarrow> 32 word WordArray) (AFun ''wordarray_put'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_put_def swa_put_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  by (metis (no_types, hide_lams) nth_list_update_eq nth_list_update_neq)

lemma wordarray_put_u64_scorres:
  "\<xi> ''wordarray_put'' =  vwa_put 
    \<Longrightarrow> scorres (wordarray_put :: (64 word WordArray, 32 word, 64 word) WordArrayGetP \<Rightarrow> 64 word WordArray) (AFun ''wordarray_put'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_put_def swa_put_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  by (metis (no_types, hide_lams) nth_list_update_eq nth_list_update_neq)


lemma wordarray_get_opt_u8_scorres:
  "\<xi> ''wordarray_get_opt'' =  vwa_get_opt 
    \<Longrightarrow> scorres (wordarray_get_opt :: (8 word WordArray, 32 word) WordArrayGetOP \<Rightarrow> (unit, 8 word) Opt) (AFun ''wordarray_get_opt'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_opt_def swa_get_opt_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_opt_u16_scorres:
  "\<xi> ''wordarray_get_opt'' =  vwa_get_opt 
    \<Longrightarrow> scorres (wordarray_get_opt :: (16 word WordArray, 32 word) WordArrayGetOP \<Rightarrow> (unit, 16 word) Opt) (AFun ''wordarray_get_opt'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_opt_def swa_get_opt_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_opt_u32_scorres:
  "\<xi> ''wordarray_get_opt'' =  vwa_get_opt 
    \<Longrightarrow> scorres (wordarray_get_opt :: (32 word WordArray, 32 word) WordArrayGetOP \<Rightarrow> (unit, 32 word) Opt) (AFun ''wordarray_get_opt'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_opt_def swa_get_opt_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

lemma wordarray_get_opt_u64_scorres:
  "\<xi> ''wordarray_get_opt'' =  vwa_get_opt 
    \<Longrightarrow> scorres (wordarray_get_opt :: (64 word WordArray, 32 word) WordArrayGetOP \<Rightarrow> (unit, 64 word) Opt) (AFun ''wordarray_get_opt'' ts []) \<gamma> \<xi>"
  apply (clarsimp simp: scorres_def)
  apply (erule v_sem_afunE; clarsimp)
  apply (erule notE)
  unfolding vwa_get_opt_def swa_get_opt_def valRel_WordArrayWord valRel_records
  apply (clarsimp split: if_splits simp: Let_def ucast_id valRel_records)
  done

end (* of context *)

end