(*
This file is generated by Cogent

*)

theory Generated_Shallow_Desugar
imports "Generated_ShallowShared"
begin

definition
  expstop :: "(32 word, 32 word) StepParam \<Rightarrow> bool"
where
  "expstop ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>x. False)"

definition
  log2stop :: "((64 word, 64 word) T0, 64 word) StepParam \<Rightarrow> bool"
where
  "log2stop ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(a,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(b,ds\<^sub>4). (>=) a obsv))))"

definition
  searchStop :: "((32 word, 32 word) T0, (32 word WordArray, 32 word) T0) StepParam \<Rightarrow> bool"
where
  "searchStop ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t obsv T0.p1\<^sub>f) (\<lambda>(arr,ds\<^sub>5). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>5 T0.p2\<^sub>f) (\<lambda>(v,ds\<^sub>6). HOL.Let ((wordarray_length :: 32 word WordArray \<Rightarrow> 32 word) arr) (\<lambda>len. HOL.Let (WordArrayGetP.make arr l (0 :: 32 word)) (\<lambda>args. HOL.Let ((wordarray_get :: (32 word WordArray, 32 word, 32 word) WordArrayGetP \<Rightarrow> 32 word) args) (\<lambda>x. HOL.If ((>=) l r) True False)))))))))"

definition
  expstep :: "(32 word, 32 word) StepParam \<Rightarrow> 32 word"
where
  "expstep ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). (*) acc obsv))"

definition
  log2step :: "((64 word, 64 word) T0, 64 word) StepParam \<Rightarrow> (64 word, 64 word) T0"
where
  "log2step ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(a,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(b,ds\<^sub>4). T0.make ((*) a (2 :: 64 word)) ((+) b (1 :: 64 word))))))"

definition
  searchNext :: "((32 word, 32 word) T0, (32 word WordArray, 32 word) T0) StepParam \<Rightarrow> (32 word, 32 word) T0"
where
  "searchNext ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t obsv T0.p1\<^sub>f) (\<lambda>(arr,ds\<^sub>5). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>5 T0.p2\<^sub>f) (\<lambda>(v,ds\<^sub>6). HOL.Let ((+) l (checked_div ((-) r l) (2 :: 32 word))) (\<lambda>m. HOL.Let (WordArrayGetP.make arr m (0 :: 32 word)) (\<lambda>args. HOL.Let ((wordarray_get :: (32 word WordArray, 32 word, 32 word) WordArrayGetP \<Rightarrow> 32 word) args) (\<lambda>x. HOL.If ((<) x v) (T0.make ((+) m (1 :: 32 word)) r) (T0.make l m))))))))))"

definition
  binarySearch :: "(32 word WordArray, 32 word) T0 \<Rightarrow> 32 word"
where
  "binarySearch ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T0.p1\<^sub>f) (\<lambda>(arr,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T0.p2\<^sub>f) (\<lambda>(v,ds\<^sub>2). HOL.Let ((wordarray_length :: 32 word WordArray \<Rightarrow> 32 word) arr) (\<lambda>len. HOL.Let (RepParam.make (ucast len :: 64 word) searchStop searchNext (T0.make (0 :: 32 word) len) (T0.make arr v)) (\<lambda>args. HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ((repeat :: (64 word, ((32 word, 32 word) T0, (32 word WordArray, 32 word) T0) StepParam \<Rightarrow> bool, ((32 word, 32 word) T0, (32 word WordArray, 32 word) T0) StepParam \<Rightarrow> (32 word, 32 word) T0, (32 word, 32 word) T0, (32 word WordArray, 32 word) T0) RepParam \<Rightarrow> (32 word, 32 word) T0) args) T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). l))))))"

definition
  myexp :: "(32 word, 32 word) T0 \<Rightarrow> 32 word"
where
  "myexp ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T0.p1\<^sub>f) (\<lambda>(a,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T0.p2\<^sub>f) (\<lambda>(b,ds\<^sub>2). HOL.Let (RepParam.make (ucast b :: 64 word) expstop expstep (1 :: 32 word) a) (\<lambda>args. (repeat :: (64 word, (32 word, 32 word) StepParam \<Rightarrow> bool, (32 word, 32 word) StepParam \<Rightarrow> 32 word, 32 word, 32 word) RepParam \<Rightarrow> 32 word) args)))"

definition
  mylog2 :: "64 word \<Rightarrow> 64 word"
where
  "mylog2 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>n. HOL.Let (RepParam.make n log2stop log2step (T0.make (1 :: 64 word) (0 :: 64 word)) n) (\<lambda>args. HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ((repeat :: (64 word, ((64 word, 64 word) T0, 64 word) StepParam \<Rightarrow> bool, ((64 word, 64 word) T0, 64 word) StepParam \<Rightarrow> (64 word, 64 word) T0, (64 word, 64 word) T0, 64 word) RepParam \<Rightarrow> (64 word, 64 word) T0) args) T0.p1\<^sub>f) (\<lambda>(a,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T0.p2\<^sub>f) (\<lambda>(b,ds\<^sub>2). b))))"

end
