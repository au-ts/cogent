(*
This file is generated by Cogent

*)

theory Generated_Shallow_Normal
imports "Generated_ShallowShared"
begin

definition
  wordarray_put32 :: "32 word WordArrayPutP\<^sub>T \<Rightarrow> 32 word WordArray"
where
  "wordarray_put32 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>args. (wordarray_put :: 32 word WordArrayPutP\<^sub>T \<Rightarrow> 32 word WordArray) args)"

definition
  expstop :: "(32 word, 32 word) StepParam\<^sub>T \<Rightarrow> bool"
where
  "expstop ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>x. False)"

definition
  log2stop :: "((64 word, 64 word) T1, 64 word) StepParam\<^sub>T \<Rightarrow> bool"
where
  "log2stop ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T1.p1\<^sub>f) (\<lambda>(a,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T1.p2\<^sub>f) (\<lambda>(b,ds\<^sub>4). (>=) a obsv))))"

definition
  searchStop :: "((32 word, 32 word, bool) T0, (32 word WordArray, 32 word) T1) StepParam\<^sub>T \<Rightarrow> bool"
where
  "searchStop ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>4 T0.p3\<^sub>f) (\<lambda>(b,ds\<^sub>5). HOL.If b True (HOL.Let ((>=) l r) (\<lambda>an\<^sub>1\<^sub>3. HOL.If an\<^sub>1\<^sub>3 True False)))))))"

definition
  expstep :: "(32 word, 32 word) StepParam\<^sub>T \<Rightarrow> 32 word"
where
  "expstep ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). (*) acc obsv))"

definition
  log2step :: "((64 word, 64 word) T1, 64 word) StepParam\<^sub>T \<Rightarrow> (64 word, 64 word) T1"
where
  "log2step ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T1.p1\<^sub>f) (\<lambda>(a,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T1.p2\<^sub>f) (\<lambda>(b,ds\<^sub>4). HOL.Let (2 :: 64 word) (\<lambda>an\<^sub>2\<^sub>6. HOL.Let ((*) a an\<^sub>2\<^sub>6) (\<lambda>an\<^sub>2\<^sub>4. HOL.Let (1 :: 64 word) (\<lambda>an\<^sub>2\<^sub>9. HOL.Let ((+) b an\<^sub>2\<^sub>9) (\<lambda>an\<^sub>2\<^sub>7. T1.make an\<^sub>2\<^sub>4 an\<^sub>2\<^sub>7))))))))"

definition
  searchNext :: "((32 word, 32 word, bool) T0, (32 word WordArray, 32 word) T1) StepParam\<^sub>T \<Rightarrow> (32 word, 32 word, bool) T0"
where
  "searchNext ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 StepParam.acc\<^sub>f) (\<lambda>(acc,ds\<^sub>2). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>2 StepParam.obsv\<^sub>f) (\<lambda>(obsv,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t acc T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>4 T0.p3\<^sub>f) (\<lambda>(b,ds\<^sub>5). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t obsv T1.p1\<^sub>f) (\<lambda>(arr,ds\<^sub>6). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>6 T1.p2\<^sub>f) (\<lambda>(v,ds\<^sub>7). HOL.Let ((-) r l) (\<lambda>an\<^sub>3\<^sub>9. HOL.Let (2 :: 32 word) (\<lambda>an\<^sub>4\<^sub>2. HOL.Let (checked_div an\<^sub>3\<^sub>9 an\<^sub>4\<^sub>2) (\<lambda>an\<^sub>3\<^sub>8. HOL.Let ((+) l an\<^sub>3\<^sub>8) (\<lambda>m. HOL.Let (0 :: 32 word) (\<lambda>an\<^sub>4\<^sub>5. HOL.Let (WordArrayGetP.make arr m an\<^sub>4\<^sub>5) (\<lambda>args. HOL.Let ((wordarray_get :: 32 word WordArrayGetP\<^sub>T \<Rightarrow> 32 word) args) (\<lambda>x. HOL.Let ((<) x v) (\<lambda>an\<^sub>4\<^sub>7. HOL.If an\<^sub>4\<^sub>7 (HOL.Let (1 :: 32 word) (\<lambda>an\<^sub>5\<^sub>2. HOL.Let ((+) m an\<^sub>5\<^sub>2) (\<lambda>an\<^sub>5\<^sub>0. T0.make an\<^sub>5\<^sub>0 r b))) (HOL.Let ((>) x v) (\<lambda>an\<^sub>5\<^sub>5. HOL.If an\<^sub>5\<^sub>5 (T0.make l m b) (HOL.Let True (\<lambda>an\<^sub>6\<^sub>3. T0.make m r an\<^sub>6\<^sub>3)))))))))))))))))))"

definition
  binarySearch :: "(32 word WordArray, 32 word) T1 \<Rightarrow> 32 word"
where
  "binarySearch ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T1.p1\<^sub>f) (\<lambda>(arr,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T1.p2\<^sub>f) (\<lambda>(v,ds\<^sub>2). HOL.Let ((wordarray_length :: 32 word WordArray \<Rightarrow> 32 word) arr) (\<lambda>len. HOL.Let (ucast len :: 64 word) (\<lambda>an\<^sub>6\<^sub>7. HOL.Let searchStop (\<lambda>an\<^sub>6\<^sub>9. HOL.Let searchNext (\<lambda>an\<^sub>7\<^sub>0. HOL.Let (0 :: 32 word) (\<lambda>an\<^sub>7\<^sub>2. HOL.Let False (\<lambda>an\<^sub>7\<^sub>4. HOL.Let (T0.make an\<^sub>7\<^sub>2 len an\<^sub>7\<^sub>4) (\<lambda>an\<^sub>7\<^sub>1. HOL.Let (T1.make arr v) (\<lambda>an\<^sub>7\<^sub>5. HOL.Let (RepParam.make an\<^sub>6\<^sub>7 an\<^sub>6\<^sub>9 an\<^sub>7\<^sub>0 an\<^sub>7\<^sub>1 an\<^sub>7\<^sub>5) (\<lambda>args. HOL.Let ((repeat :: ((32 word, 32 word, bool) T0, (32 word WordArray, 32 word) T1) RepParam\<^sub>T \<Rightarrow> (32 word, 32 word, bool) T0) args) (\<lambda>an\<^sub>7\<^sub>8. HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t an\<^sub>7\<^sub>8 T0.p1\<^sub>f) (\<lambda>(l,ds\<^sub>3). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>3 T0.p2\<^sub>f) (\<lambda>(r,ds\<^sub>4). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>4 T0.p3\<^sub>f) (\<lambda>(b,ds\<^sub>5). HOL.If b l len)))))))))))))))"

definition
  myexp :: "(32 word, 32 word) T1 \<Rightarrow> 32 word"
where
  "myexp ds\<^sub>0 \<equiv> HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>0 T1.p1\<^sub>f) (\<lambda>(a,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T1.p2\<^sub>f) (\<lambda>(b,ds\<^sub>2). HOL.Let (ucast b :: 64 word) (\<lambda>an\<^sub>8\<^sub>5. HOL.Let expstop (\<lambda>an\<^sub>8\<^sub>7. HOL.Let expstep (\<lambda>an\<^sub>8\<^sub>8. HOL.Let (1 :: 32 word) (\<lambda>an\<^sub>8\<^sub>9. HOL.Let (RepParam.make an\<^sub>8\<^sub>5 an\<^sub>8\<^sub>7 an\<^sub>8\<^sub>8 an\<^sub>8\<^sub>9 a) (\<lambda>args. (repeat :: (32 word, 32 word) RepParam\<^sub>T \<Rightarrow> 32 word) args)))))))"

definition
  mylog2 :: "64 word \<Rightarrow> 64 word"
where
  "mylog2 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>n. HOL.Let log2stop (\<lambda>an\<^sub>9\<^sub>3. HOL.Let log2step (\<lambda>an\<^sub>9\<^sub>4. HOL.Let (1 :: 64 word) (\<lambda>an\<^sub>9\<^sub>6. HOL.Let (0 :: 64 word) (\<lambda>an\<^sub>9\<^sub>7. HOL.Let (T1.make an\<^sub>9\<^sub>6 an\<^sub>9\<^sub>7) (\<lambda>an\<^sub>9\<^sub>5. HOL.Let (RepParam.make n an\<^sub>9\<^sub>3 an\<^sub>9\<^sub>4 an\<^sub>9\<^sub>5 n) (\<lambda>args. HOL.Let ((repeat :: ((64 word, 64 word) T1, 64 word) RepParam\<^sub>T \<Rightarrow> (64 word, 64 word) T1) args) (\<lambda>an\<^sub>9\<^sub>9. HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t an\<^sub>9\<^sub>9 T1.p1\<^sub>f) (\<lambda>(a,ds\<^sub>1). HOL.Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t ds\<^sub>1 T1.p2\<^sub>f) (\<lambda>(b,ds\<^sub>2). b))))))))))"

definition
  wordarray_get_opt32 :: "32 word WordArrayGetOP\<^sub>T \<Rightarrow> 32 word Opt\<^sub>T"
where
  "wordarray_get_opt32 ds\<^sub>0 \<equiv> HOL.Let ds\<^sub>0 (\<lambda>args. (wordarray_get_opt :: 32 word WordArrayGetOP\<^sub>T \<Rightarrow> 32 word Opt\<^sub>T) args)"

end
