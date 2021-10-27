(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory CogentCorres
imports "CogentMonad"
        "../adt/BilbyT"
begin

definition
  cogent_corres :: "('a \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a cogent_monad \<Rightarrow> 'c \<Rightarrow> bool"
where
  "cogent_corres R ma sc \<equiv>(\<exists>ra\<in> ma. R ra sc)"

lemma cogent_corres_if:
  assumes b: "a \<Longrightarrow> cogent_corres R b b'"
  assumes c: "\<not>a \<Longrightarrow> cogent_corres R c c'"
  assumes a: "a' = a"
  shows "cogent_corres R (if a then b else c) (if a' then b' else c')"
proof (cases a)
  case True
  thus "?thesis"
   using a b unfolding cogent_corres_def by fastforce
next
  case False
  thus "?thesis"
    using a c unfolding cogent_corres_def by fastforce
qed

lemma cogent_corres_conc_let_exec:
assumes "\<And>v'. v' = v \<Longrightarrow> cogent_corres R a (c v')"
shows
  "cogent_corres R a (Let v (\<lambda>v'. c v'))"
 using assms unfolding  return_def cogent_corres_def
  by clarsimp

lemma cogent_corres_return:
  "(R x y) \<Longrightarrow> cogent_corres R (return x) y"
  unfolding  return_def cogent_corres_def
  by clarsimp

lemma cogent_corres_select:
fixes v
assumes "v\<in>S"
and "cogent_corres R (a v) c"
shows
  "cogent_corres R (CogentMonad.select S >>= (\<lambda>v. a v)) c"
  using assms
  unfolding return_def cogent_corres_def CogentMonad.select_def
  by (fastforce simp: ex_in_conv[symmetric] bind_def)

lemma cogent_corres_R:
assumes b: "\<And>rc. r = R.Error rc \<Longrightarrow> cogent_corres R a (c rc)"
assumes c: "\<And>rc. r = R.Success rc \<Longrightarrow> cogent_corres R a (d rc)"
shows "cogent_corres R a (case r of R.Error rc \<Rightarrow> c rc | R.Success rd \<Rightarrow> d rd)"
proof (cases r)
  case (Error rc)
  thus ?thesis
    using b[OF Error] by simp
next
  case (Success rc)
  thus ?thesis
    using c[OF Success] by simp
qed

(* Sometimes, we need more specialised lemmas than cogent_corres_R *)
lemma cogent_corres_R_pair:
assumes b: "\<And>rc1 rc2. r = (rc1, R.Error rc2) \<Longrightarrow> cogent_corres R a (c rc1 rc2)"
assumes c: "\<And>rd1 rd2. r = (rd1, R.Success rd2) \<Longrightarrow> cogent_corres R a (d rd1 rd2)"
shows 
  "cogent_corres R a (case r of (rc1, R.Error rc2) \<Rightarrow> c rc1 rc2 | (rd1, R.Success rd2) \<Rightarrow> d rd1 rd2)"
proof (cases r)
  case (Pair r1 r2)
    thus ?thesis
    apply (cases r2)
     using b apply (simp)
     using c apply (simp)
    done
qed

(* Sometimes, we need more specialised lemmas than cogent_corres_R *)
lemma cogent_corres_R_pair2:
assumes b: "\<And>rc11 rc12 rc2. r = ((rc11, rc12), R.Error rc2) \<Longrightarrow> cogent_corres R a (c rc11 rc12 rc2)"
assumes c: "\<And>rd11 rd12 rd2. r = ((rd11, rd12), R.Success rd2) \<Longrightarrow> cogent_corres R a (d rd11 rd12 rd2)"
shows 
  "cogent_corres R a 
   (case r of 
    ((rc11, rc12), R.Error rc2)   \<Rightarrow> c rc11 rc12 rc2 
  | ((rd11, rd12), R.Success rd2) \<Rightarrow> d rd11 rd12 rd2)"
proof (cases r)
  case (Pair r1 r2)
    thus ?thesis
    proof (cases r2) print_cases
      case(Error rc2)
        thus ?thesis using Pair b[of "fst r1" "snd r1"] by (cases r, clarsimp)
    next
      case (Success rd2)
        thus ?thesis using Pair c[of "fst r1" "snd r1"] by (cases r, clarsimp)
    qed
qed

end (* a comment *)