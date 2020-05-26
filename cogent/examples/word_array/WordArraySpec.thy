theory WordArraySpec
  imports "HOL-Word.Word" Word_Lib.HOL_Lemmas
begin

type_synonym u32 = "32 word"

datatype ('a, 'b) LoopResult = Iterate 'a | Break 'b
section \<open> List helper lemmas \<close>


lemma take_1_drop:
  "i < length xs \<Longrightarrow> take (Suc 0) (drop i xs) = [xs ! i]"
  apply (induct xs arbitrary: i)
   apply (simp add: take_Suc_conv_app_nth)
  by (simp add: drop_Suc_nth)

lemma take_drop_Suc:
  "i < l \<and> i < length xs \<Longrightarrow> 
    take (l - i) (drop i xs) = (xs ! i) # take (l - Suc i) (drop (Suc i) xs)"
  apply clarsimp
  by (metis Cons_nth_drop_Suc Suc_diff_Suc take_Suc_Cons)

section \<open> wordarray_length specification \<close>

definition w_length :: "u32 list \<Rightarrow> nat"
  where
"w_length w = length w"

subsection \<open> Correctness \<close>

lemma w_length_length_eq: 
  "w_length xs = length xs"
  by (simp add: w_length_def)

section \<open> wordarray_get specification \<close>

definition w_get :: "u32 list \<Rightarrow> nat \<Rightarrow> u32"
  where
"w_get w i = (if length w \<le> i then 0 else w ! i)"

subsection \<open> Correctness \<close>

lemma w_get_get_eq:
  "i < length xs \<Longrightarrow> w_get xs i = xs ! i"
  by (simp add: w_get_def)

section \<open> wordarray_put2 specification \<close>

definition w_put :: "u32 list \<Rightarrow> nat \<Rightarrow> 
                      u32 \<Rightarrow> u32 list"
  where
"w_put w i v = w[i := v]"

subsection \<open> Correctness \<close>

lemma w_put_listupdate_eq:
  "w_put xs i v= xs[i := v]"
  by (simp add: w_put_def)

section \<open> wordarray_fold_no_break specification \<close>

definition w_fold :: "u32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (u32 \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 
                      'a \<Rightarrow> 'b \<Rightarrow> 'a"
  where
"w_fold w frm to f acc obs =
  (if to \<le> frm
    then acc 
  else
    fold (\<lambda>x y. f x y obs)  
    (take (to - frm) (drop frm w)) acc)"

subsection \<open>w_fold helper lemmas \<close>

lemma w_fold_step: "\<lbrakk>frm < length xs; frm < to\<rbrakk> \<Longrightarrow>
  w_fold xs frm to f acc obsv = w_fold xs (Suc frm) to f (f (xs ! frm) acc obsv) obsv"
  by (simp add: w_fold_def take_drop_Suc)


lemma w_fold_preserve: 
  "\<lbrakk>frm \<le> i; i < min (length xs) to; w_fold xs frm to f acc obsv = w_fold xs i to f nacc obsv\<rbrakk> \<Longrightarrow>
   w_fold xs frm to f acc obsv = w_fold xs (Suc i) to f (f (xs ! i) nacc obsv) obsv "
  apply (simp add: w_fold_def)
  apply safe
   apply (simp add: take_drop_Suc)
   apply (simp add: take_drop_Suc)
  done

lemma w_fold_end: 
  "\<lbrakk>frm \<le> i; i \<ge> min (length xs) to; w_fold xs frm to f acc obsv = w_fold xs i to f nacc obsv\<rbrakk> \<Longrightarrow>
   w_fold xs frm to f acc obsv = nacc "
  apply (simp add: w_fold_def)
  done

subsection \<open> w_fold test \<close>

primrec summer :: "u32 \<Rightarrow> u32 \<Rightarrow> unit \<Rightarrow> u32" where
"summer elem acc () = elem + acc"

value "w_fold [0, 1, 2, 3, 4, 5] 1 1 summer 0 ()"

subsection \<open> Correctness \<close>

lemma w_fold_fold_eq_whole: 
  "w_fold xs 0 (length xs) f acc obsv = fold (\<lambda>a b. f a b obsv) xs acc"
  apply (simp add: w_fold_def)
  done

lemma w_fold_fold_eq_slice: 
  "w_fold xs frm to f acc obsv = fold (\<lambda>a b. f a b obsv) (take (to - frm) (drop frm xs)) acc"
  apply (simp add: w_fold_def)
  done

section \<open> wordarray_fold specification \<close>
definition w_fold_break :: "u32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
                            (u32 \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'c) LoopResult ) \<Rightarrow> 
                            'a \<Rightarrow> 'b \<Rightarrow> ('a, 'c) LoopResult"
  where
"w_fold_break w frm to f acc obs =
  (if to \<le> frm
    then (Iterate acc)
  else
    fold (\<lambda>x y. (case y of 
                    Iterate acc \<Rightarrow> f x acc obs | 
                    Break acc \<Rightarrow> Break acc))  
    (take (to - frm) (drop frm w)) (Iterate acc))"


section \<open> wordarray_map_no_break specification \<close>

definition w_map :: "u32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (u32 \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> u32 \<times> 'a) \<Rightarrow> 
                      'a \<Rightarrow> 'b \<Rightarrow> u32 list \<times> 'a"
  where
"w_map w frm to f acc obs =
  (if to \<le> frm
    then (w, acc) 
  else
    let (ys, vacc) =
      fold (\<lambda>x (xs, vacc'). 
        let (y, vacc'') = f x vacc' obs
         in (xs @ [y], vacc''))
        (take (to - frm) (drop frm w)) ([], acc)
     in ((take frm w) @ ys @ (drop to w), vacc))"

subsection \<open> w_map helper lemmas \<close>

lemma w_map_bounds: 
  "to \<ge> length xs \<Longrightarrow> w_map xs frm to f acc obsv = w_map xs frm (length xs) f acc obsv"
  apply (simp add: w_map_def)
  done
lemma w_map_internal: 
  "length (fst (fold (\<lambda>x p. (fst p @ [fst (f x (snd p) obsv)], snd (f x (snd p) obsv))) xs (ls, acc))) 
    = length ls + length xs"
  apply (induct rule: rev_induct)
   apply simp
  apply (simp add: split_def)
  done

lemma w_map_length: 
  "length (fst (w_map xs frm to f acc obsv)) = length xs"
  apply (induct rule: rev_induct)
   apply (simp add: w_map_def)
  apply (clarsimp simp add: w_map_def)
  apply (case_tac "frm > length xs")
   apply simp
  apply (case_tac "frm = length xs") thm split_def
   apply (simp add: split_def)
  apply simp
  apply (case_tac "to < length xs")
   apply simp
   apply (simp add: split_def)
  apply (case_tac "to = length xs")
   apply simp
   apply (simp add: split_def)
  apply simp
  apply (simp add: split_def)
  done

lemma w_map_length_same:
  "length xs = length ys \<Longrightarrow> length (fst (w_map xs frm to f acc obsv)) 
    = length (fst (w_map ys frm' to' f' acc' obsv'))"
  apply (induct xs arbitrary: ys rule: rev_induct)
   apply simp
   apply (simp add: w_map_def)
  by (simp add: w_map_length)

lemma w_map_length_Cons: 
  "length (fst (w_map (x # xs) frm to f acc obsv)) 
    = Suc (length (fst (w_map xs frm' to' f' acc' obsv')))"
  apply (induct xs)
   apply (subst w_map_length)
   apply (subst w_map_length)
   apply simp
  apply (subst w_map_length)
  apply (subst w_map_length)
  apply simp
  done

lemma w_map_length_append: 
  "length (fst (w_map (xs @ [x]) frm to f acc obsv)) 
    = Suc (length (fst (w_map xs frm' to' f' acc' obsv')))"
  apply (induct xs)
   apply (subst w_map_length)
   apply (subst w_map_length)
   apply simp
  apply (subst w_map_length)
  apply (subst w_map_length)
  apply simp
  done

lemma w_map_append_list:
  "to \<le> length xs \<Longrightarrow> 
    fst (w_map (xs @ ys) frm to f acc obsv) = fst (w_map xs frm to f acc obsv) @ ys"
  apply (simp add: w_map_def)
  apply clarsimp
  apply (simp add: split_def)
  done

lemma w_map_append_acc:
  "to \<le> length xs \<Longrightarrow> 
    snd (w_map (xs @ ys) frm to f acc obsv) = snd (w_map xs frm to f acc obsv)"
  apply (simp add: w_map_def)
  apply (simp add: split_def)
  done

lemmas w_map_append = w_map_append_list w_map_append_acc

lemma w_map_step_list:
  "frm \<le> to \<Longrightarrow> fst (w_map xs frm (Suc to) f acc obsv) = 
  (fst (w_map xs frm to f acc obsv))[to := fst (f (xs ! to) (snd (w_map xs frm to f acc obsv)) obsv)]"
  apply (induct xs rule: rev_induct)
   apply (simp add: w_map_def)
  apply (case_tac "to \<ge> length xs")
   apply (case_tac "to \<ge> length (xs @ [x])")
    apply (subst (asm) w_map_length[where frm = frm and to = to and f = "f" and acc = acc and obsv = obsv,symmetric])
    apply simp
    apply (subgoal_tac "length (fst (w_map (xs @ [x]) frm to f acc obsv)) = Suc (length xs)")
     apply simp
     apply (subst w_map_def)
     apply (subst w_map_def)
     apply simp
    apply (simp add: w_map_length)
   apply (subgoal_tac "to = length xs")
  defer
    apply simp
   defer
   apply simp
   apply (simp (no_asm) add: w_map_def)
   apply (rule conjI)
    apply clarsimp
    apply (simp add: split_def)
   apply clarsimp
   apply (simp add: split_def)
   apply (subst upd_conv_take_nth_drop)
    apply simp
    apply (subst w_map_internal)
    apply simp
   apply simp
   apply (subgoal_tac "length (fst (fold (\<lambda>x p. (fst p @ [fst (f x (snd p) obsv)], snd (f x (snd p) obsv))) (drop frm xs) ([], acc))) = length xs - frm")
    apply simp
   apply (subst w_map_internal)
   apply simp
  apply simp
  apply (subgoal_tac "snd (w_map (xs @ [x]) frm to f acc obsv) = snd (w_map xs frm to f acc obsv)")
   apply simp
   apply (subgoal_tac "(xs @ [x]) ! to = xs ! to")
    apply simp
    apply (subst w_map_append)
     apply linarith
    apply (subst w_map_append)
     apply simp
    apply clarsimp
    apply (subst list_update_append1)
     apply (simp add: w_map_length)
    apply simp
   apply (simp add: nth_append)
  apply (simp add: w_map_append)
  done

lemma w_map_step_acc:
  "\<lbrakk>frm \<le> to; Suc to \<le> length xs\<rbrakk> 
    \<Longrightarrow> snd (w_map xs frm (Suc to) f acc obsv) 
      = snd (f (xs ! to) (snd (w_map xs frm to f acc obsv)) obsv)"
  apply (induct xs rule: rev_induct)
   apply (clarsimp simp add: w_map_def)
  apply clarsimp
  apply (case_tac "Suc to \<le> length xs")
   apply (simp add: w_map_append)
   apply (simp add: nth_append)
  apply (simp add: nth_append)
  apply (simp add: w_map_def)
  apply (simp add: split_def)
  done

lemmas w_map_step = w_map_step_list w_map_step_acc

lemma w_map_endpoint: 
  "to < length xs \<Longrightarrow> fst (w_map xs frm to f acc obsv) ! to = xs ! to"
  apply (induct xs rule: rev_induct)
  apply (simp add: w_map_def)
  apply clarsimp
  apply (simp add: w_map_append)
  apply (case_tac "to = length xs")
   apply simp
   apply (metis w_map_length nth_append_length)
  apply (subgoal_tac "to < length xs")
   apply simp
   apply (simp add: w_map_length nth_append)
  apply arith
  done

subsection \<open> Correctness \<close>

lemma no_update_acc: 
  "\<lbrakk>\<forall>x ob a. snd (f x a ob) = a; xs \<noteq> []\<rbrakk>
    \<Longrightarrow> snd (fold (\<lambda>x p. (fst p @ [fst (f x (snd p) obsv)], snd p)) xs ([], acc)) = acc"
  apply (induct xs rule: rev_induct)
   apply simp
  apply simp
  apply (case_tac "xs = []")
   apply simp
  apply simp
  done

lemma w_map_map_eq_whole:
  "\<lbrakk>\<forall>x ob a. snd (f x a ob) = a \<rbrakk> 
    \<Longrightarrow> fst (w_map xs 0 (length xs) f acc obsv) = map (\<lambda>x. fst (f x acc obsv)) xs"
  apply (induct xs rule: rev_induct)
   apply (simp add: w_map_def)
  apply simp
  apply (subst w_map_step)
   apply simp
  apply (subst w_map_append)
   apply simp
  apply (subst list_update_append)
  apply (subst w_map_length)
  apply simp
  apply (subst w_map_append)
   apply simp
  apply (simp (no_asm) add: w_map_def)
  apply (simp add: split_def)
  apply clarsimp
  apply (subgoal_tac "snd (fold (\<lambda>x p. (fst p @ [fst (f x (snd p) obsv)], snd p)) xs ([], acc)) = acc")
   apply simp
  apply (rule no_update_acc)
   apply simp
  apply simp
  done

section \<open> wordarray_map specification \<close>

definition w_map_break :: "u32 list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
                      (u32 \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> (u32 \<times> 'a, 'c) LoopResult) \<Rightarrow> 
                      'a \<Rightarrow> 'b \<Rightarrow> (u32 list \<times> 'a, 'c) LoopResult"
  where
"w_map_break w frm to f acc obs =
  (if to \<le> frm
    then Iterate (w, acc) 
  else
   let ret = fold
      (\<lambda>x r.
        case r of
            Iterate (xs, vacc) \<Rightarrow>
              let r' = f x vacc obs
               in
                  (case r' of
                      Iterate (x', vacc') \<Rightarrow> Iterate (xs @ [x'], vacc') |
                      Break v \<Rightarrow> Break v) |
            Break v \<Rightarrow> Break v)
      (take (to - frm) (drop frm w))  (Iterate ([], acc))
   in 
     case ret of
          Iterate (ys, acc') \<Rightarrow> Iterate ((take frm w) @ ys @ (drop to w), acc') |
          Break v \<Rightarrow> Break v)"
end
