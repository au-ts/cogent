theory RepeatShallowTest
  imports RepeatShallow
begin

section "@{term repeat} Validation"

subsection "Fold Break using @{term repeatatl}"

fun fold_break :: "('a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
"fold_break f g xs acc = fold (\<lambda>a b. (if f b then b else g a b)) xs acc"

lemma "f (fold_break f g xs acc) \<Longrightarrow> fold_break f g (xs @ ys) acc = fold_break f g xs acc"
  apply (induct ys arbitrary: xs acc)
   apply clarsimp
  apply simp
  done

fun my_fold_break :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'a"
  where
"my_fold_break f g xs acc obsv = prod.fst (repeatatl (length xs) (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv))"

lemma my_fold_break_helper1:
  "\<lbrakk>n \<le> length xs; f' = (\<lambda>(a, _) (_, b). f a b); g' = (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i));
    \<not>f' (repeatatl n f' g' (acc, 0) (xs, obsv)) (xs, obsv)\<rbrakk>
    \<Longrightarrow> prod.snd (repeatatl n f' g' (acc, 0) (xs, obsv)) = n"
  apply (induct n)
   apply (simp add: repeatatl.simps)
  apply (clarsimp split: prod.splits)
  apply (insert repeatatl_not_stop_Suc)
  apply (drule_tac x = f' in meta_spec)
  apply (drule_tac x = n in meta_spec)
  apply (drule_tac x = g' in meta_spec)
  apply (drule_tac x = "(acc, 0)" in meta_spec)
  apply (drule_tac x = "(xs, obsv)" in meta_spec)
  apply (rotate_tac -1, drule meta_mp, simp)
  apply (frule_tac n = n and f = f' and g = g' in repeatatl_step; simp)
  apply (clarsimp split: prod.splits)
  done

lemma my_fold_break_helper1':
  "\<lbrakk>n \<le> length xs;
    \<not>(\<lambda>(a, _) (_, b). f a b) (repeatatl n (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv)) (xs, obsv)\<rbrakk>
    \<Longrightarrow> prod.snd (repeatatl n (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv)) = n"
  apply (rule my_fold_break_helper1; simp?)
  done

lemma my_fold_break_helper2:
  "\<lbrakk>n \<le> length xs; f' = (\<lambda>(a, _) (_, b). f a b); g' = (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i));
    repeatatl n f' g' (acc, 0) (xs, obsv) = (x, m);
    \<not>f x obsv\<rbrakk>
    \<Longrightarrow> repeatatl n f' g' (acc, 0) (xs @ ys, obsv) = (x, m)"
  apply (induct n arbitrary: x m)
   apply (simp add: repeatatl.simps)
  apply (clarsimp split: prod.splits)
  apply (insert repeatatl_not_stop_Suc)
  apply (drule_tac x = f' in meta_spec)
  apply (drule_tac x = n in meta_spec)
  apply (drule_tac x = g' in meta_spec)
  apply (drule_tac x = "(acc, 0)" in meta_spec)
  apply (drule_tac x = "(xs, obsv)" in meta_spec)
  apply (rotate_tac -1, drule meta_mp, simp)
  apply (frule_tac n = n and f = f' and g = g' in repeatatl_step; simp)
  apply (clarsimp split: prod.splits)
  apply (drule_tac x = x1 and y = x2 in meta_spec2)
  apply clarsimp
  apply (subst repeatatl_step; clarsimp)
  apply (cut_tac n = n and f = f and g = g and acc = acc and obsv = obsv and xs = xs in my_fold_break_helper1'; simp)
  apply (simp add: nth_append)
  done

lemma my_fold_break_helper2':
  "\<lbrakk>n \<le> length xs;
    repeatatl n  (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv) = (x, m);
    \<not>f x obsv\<rbrakk>
    \<Longrightarrow> repeatatl n (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs @ ys, obsv) = (x, m)"
  apply (rule my_fold_break_helper2; simp)
  done

lemma my_fold_break_helper3:
  "\<lbrakk>n \<le> length xs; f' = (\<lambda>(a, _) (_, b). f a b); g' = (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i));
    repeatatl n f' g' (acc, 0) (xs, obsv) = (x, m);
    f x obsv\<rbrakk>
    \<Longrightarrow> repeatatl n f' g' (acc, 0) (xs @ ys, obsv) = (x, m)"
  apply (induct n arbitrary: x m)
   apply (simp add: repeatatl.simps)
  apply (clarsimp split: prod.splits)
  apply (case_tac "f' (repeatatl n f' g' (acc, 0) (xs, obsv)) (xs, obsv)")
   apply (drule_tac n = n and f = f' and g = g' and a = "(acc, 0)" and b = "(xs, obsv)" in repeatatl_step_stop_Suc; clarsimp)
   apply (drule_tac x = x and y = m in meta_spec2)
   apply (drule meta_mp; simp)
   apply (subst repeatatl_step_stop_Suc; clarsimp split: prod.split)
  apply (frule_tac n = n and f = f and g = g and acc = acc and xs = xs and obsv = obsv in my_fold_break_helper1[rotated -1], simp, simp, simp)
  apply (frule_tac n = n and f = f' and g = g' and a = "(acc, 0)" and b = "(xs, obsv)" in repeatatl_step; clarsimp split: prod.split)
  apply (cut_tac f = f and g = g and xs = xs and acc = acc and obsv = obsv and x = x1 and m = n and n = n and ys = ys in  my_fold_break_helper2')
     apply simp
    apply simp
   apply simp
  apply (subst repeatatl_step; clarsimp split: prod.split)
  apply (drule_tac x = x1 and y = n in meta_spec2; clarsimp)
  apply (simp add: nth_append)
  done

lemma my_fold_break_helper3':
  "\<lbrakk>n \<le> length xs;
    repeatatl n (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv) = (x, m);
    f x obsv\<rbrakk>
    \<Longrightarrow> repeatatl n (\<lambda>(a, _) (_, b). f a b) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs @ ys, obsv) = (x, m)"
  apply (rule_tac f = f in my_fold_break_helper3; simp)
  done

lemma fold_break_my_fold_break_eq:
  "fold_break (\<lambda>a. f a obsv) (\<lambda>a b. g a b obsv) xs acc = my_fold_break f g xs acc obsv"
  apply (induct rule: rev_induct[where xs = xs])
   apply (simp add: repeatatl.simps)
  apply clarsimp
  apply (cut_tac p = "repeatatl (length xs) (\<lambda>(a, _) (_, y). f a y) (\<lambda>(a, i) (xs, b). (g (xs ! i) a b, Suc i)) (acc, 0) (xs, obsv)" in surj_pair)
  apply (erule exE)+
  apply (rename_tac y m)
  apply (rule conjI; rule impI)
   apply (frule_tac n = "length xs" and xs = xs and x = y and ys = "[x]" and m = m in my_fold_break_helper3'[rotated 1])
     apply simp
    apply simp
   apply simp
   apply (subst repeatatl_step_stop_Suc; clarsimp split: prod.splits)
  apply (frule_tac n = "length xs" and xs = xs and x = y and ys = "[x]" and m = m in my_fold_break_helper2'[rotated 1])
    apply simp
   apply simp                                                                                     
  apply (cut_tac n = "length xs" and xs = xs and f = f and g = g and acc = acc and obsv = obsv in my_fold_break_helper1'[rotated 1])
    apply simp
   apply simp
  apply (subst repeatatl_step; clarsimp split: prod.splits)
  done

end