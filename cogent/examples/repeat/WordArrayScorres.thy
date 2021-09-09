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

class cogent_S_val = 
  fixes valrel :: "(funtyp, vabstyp) vabsfuns \<Rightarrow> 'a \<Rightarrow> (funtyp, vabstyp) vval \<Rightarrow> bool"

instantiation bool :: cogent_S_val
begin
definition valrel_bool_def:
"valrel \<xi> x x' \<equiv> (x' = VPrim (LBool x))"
instance ..
end

instantiation prod :: (cogent_S_val, cogent_S_val) cogent_S_val
begin
definition valrel_prod_def:
"valrel \<xi> x x' \<equiv> (\<exists>a b. x' = VProduct a b \<and> valrel \<xi> (prod.fst x) a \<and> valrel \<xi> (prod.snd x) b)"
instance ..
end

instantiation WordArray :: (cogent_S_val) cogent_S_val
begin
definition valrel_WordArray_def:
"valrel \<xi> x x' \<equiv> (\<exists>t xs xs'. x' = VAbstract (VWA t xs) \<and> xs' = swa_to_list x \<and> length xs = length xs' \<and> (\<forall>i < length xs. valrel \<xi> (xs' ! i) (xs ! i)))"
instance ..
end
(*
overloading
  valRel_WordArrayUX \<equiv> valRel
begin
definition valRel_WordArrayUX:
"\<And>\<xi>' x v. valRel_WordArrayUX (\<xi>' :: (funtyp, vabstyp) vabsfuns) (x :: (('a::len8) word) WordArray) (v :: (funtyp, vabstyp) vval) \<equiv> 
  (\<exists>t xs. v = VAbstract(VWA t xs) \<and> length xs = length x \<and> (\<forall>i < length xs. valRel \<xi>' (x ! i) (xs ! i)))"
end
*)
end