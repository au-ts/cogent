theory WordArray_Shallow
  imports "../lib/FunBucket"

begin

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
  "wordarray_get' (x :: ((('a ::len0) word) WordArray \<times> 32 word)) \<equiv> (if unat (prod.snd x) < length (prod.fst x) then (prod.fst x) ! unat (prod.snd x) else 0)"
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

overloading
  wordarray_map_no_break' \<equiv> wordarray_map_no_break
begin
definition wordarray_map_no_break':
 "wordarray_map_no_break' (x :: ('a WordArray, 32 word, 32 word, ('a, 'acc, 'obsv) ElemAO \<Rightarrow> ('a \<times> 'acc), 'acc, 'obsv) ArrayMapP) \<equiv> 
    (let xs = List.take (unat (ArrayMapP.frm\<^sub>f x)) (ArrayMapP.arr\<^sub>f x);
         zs = List.drop (unat (ArrayMapP.to\<^sub>f x)) (ArrayMapP.arr\<^sub>f x);
        (ys, acc) = mapAccum 
          (\<lambda>a b. ((ArrayMapP.f\<^sub>f x) (ElemAO.make a b (ArrayMapP.obsv\<^sub>f x)))) 
          (slice (unat (ArrayMapP.frm\<^sub>f x)) (unat (ArrayMapP.to\<^sub>f x)) (ArrayMapP.arr\<^sub>f x)) 
          (ArrayMapP.acc\<^sub>f x)
    in (if (ArrayMapP.frm\<^sub>f x) \<le> (ArrayMapP.to\<^sub>f x) 
        then ((xs @ ys @ zs), acc)
        else ((ArrayMapP.arr\<^sub>f x), acc)))" 
end
end
