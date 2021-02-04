theory WordArray_Shallow
  imports Generated_AllRefine

begin

section "Helper Functions and Lemmas"

fun myslice :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where
"myslice frm to xs = List.take (to - frm) (List.drop frm xs)"

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
 "wordarray_get' (x :: (('a::len8) word WordArray, 32 word) T0) \<equiv> (if unat (T0.p2\<^sub>f x) < length (T0.p1\<^sub>f x) then (T0.p1\<^sub>f x) ! unat (T0.p2\<^sub>f x) else 0)" 
end


overloading
  wordarray_fold_no_break' \<equiv> wordarray_fold_no_break
begin
definition wordarray_fold_no_break':
 "wordarray_fold_no_break' (x :: ('a WordArray, 32 word, 32 word, ('a, 'acc, 'obsv) ElemAO \<Rightarrow> 'acc, 'acc, 'obsv) WordArrayMapNoBreakP) \<equiv> 
    fold (\<lambda>a b. (WordArrayMapNoBreakP.f\<^sub>f x) (ElemAO.make a b (WordArrayMapNoBreakP.obsv\<^sub>f x))) 
         (myslice (unat (WordArrayMapNoBreakP.frm\<^sub>f x)) (unat (WordArrayMapNoBreakP.to\<^sub>f x)) (WordArrayMapNoBreakP.arr\<^sub>f x)) 
         (WordArrayMapNoBreakP.acc\<^sub>f x)" 
end


fun mapAccum :: "('a \<Rightarrow> 'b  \<Rightarrow> ('c \<times> 'b)) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> ('c list \<times> 'b)"
  where
"mapAccum _ [] acc = ([], acc)" |
"mapAccum f (x#xs) acc = 
  (let (a, b) = f x acc;
       (as, b') = mapAccum f xs b
   in (a#as, b'))"

fun listAccumStep :: "('a \<Rightarrow> 'b  \<Rightarrow> ('c \<times> 'b)) \<Rightarrow> 'a \<Rightarrow> ('c list \<times> 'b) \<Rightarrow> ('c list \<times> 'b)"
  where
"listAccumStep f x (ys, acc) = (let (y, acc') = f x acc in (ys @ [y], acc'))"

lemma mapAccum_step:
  "mapAccum f (xs @ [x]) acc = listAccumStep f x (mapAccum f xs acc)"
  apply (induct arbitrary: x acc rule: list.induct)
   apply clarsimp
  apply (clarsimp split: prod.split)
  done


lemma mapAccum_length:
  "length (prod.fst (mapAccum f xs acc)) = length xs"
  apply (induct arbitrary: acc rule: rev_induct)
   apply simp
  apply (subst mapAccum_step)
  apply clarsimp
  apply (drule_tac x = acc in meta_spec)
  by (metis (no_types, lifting) Product_Type.split_def fst_conv length_append_singleton listAccumStep.simps prod.collapse)


lemma 
  "map f xs = prod.fst (mapAccum (\<lambda>a b. (f a, b)) xs ())"
  by (induct xs; clarsimp split: prod.split)

lemma
  "fold f xs acc = prod.snd (mapAccum (\<lambda>a b. (a, f a b)) xs acc)"
  apply (induct rule: rev_induct; clarsimp split: prod.split)
  apply (subst mapAccum_step)
  by (metis (no_types, lifting) case_prod_beta listAccumStep.simps prod.collapse snd_conv)



fun cogent_isa_pair :: "('a, 'b) T0 \<Rightarrow> ('a \<times> 'b)"
  where
"cogent_isa_pair x = (T0.p1\<^sub>f x, T0.p2\<^sub>f x)"

term "mapAccum 
          (\<lambda>a b. cogent_isa_pair ((WordArrayMapNoBreakP.f\<^sub>f x) (ElemAO.make a b (WordArrayMapNoBreakP.obsv\<^sub>f x)))) 
          (myslice (unat (WordArrayMapNoBreakP.frm\<^sub>f x)) (unat (WordArrayMapNoBreakP.to\<^sub>f x)) (WordArrayMapNoBreakP.arr\<^sub>f x)) 
          (WordArrayMapNoBreakP.acc\<^sub>f x)"
overloading
  wordarray_map_no_break' \<equiv> wordarray_map_no_break
begin
definition wordarray_map_no_break':
 "wordarray_map_no_break' (x :: ('a WordArray, 32 word, 32 word, ('a, 'acc, 'obsv) ElemAO \<Rightarrow> ('a, 'acc) T0, 'acc, 'obsv) WordArrayMapNoBreakP) \<equiv> 
    (let xs = List.take (unat (WordArrayMapNoBreakP.frm\<^sub>f x)) (WordArrayMapNoBreakP.arr\<^sub>f x);
         zs = List.drop (unat (WordArrayMapNoBreakP.to\<^sub>f x)) (WordArrayMapNoBreakP.arr\<^sub>f x);
        (ys, acc) = mapAccum 
          (\<lambda>a b. cogent_isa_pair ((WordArrayMapNoBreakP.f\<^sub>f x) (ElemAO.make a b (WordArrayMapNoBreakP.obsv\<^sub>f x)))) 
          (myslice (unat (WordArrayMapNoBreakP.frm\<^sub>f x)) (unat (WordArrayMapNoBreakP.to\<^sub>f x)) (WordArrayMapNoBreakP.arr\<^sub>f x)) 
          (WordArrayMapNoBreakP.acc\<^sub>f x)
    in (if (WordArrayMapNoBreakP.frm\<^sub>f x) \<le> (WordArrayMapNoBreakP.to\<^sub>f x) 
        then T0.make (xs @ ys @ zs) acc 
        else T0.make (WordArrayMapNoBreakP.arr\<^sub>f x) acc))" 
end

end