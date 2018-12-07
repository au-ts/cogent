(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

(*
 * Proving refinement between Cogent shallow embeddings
 * with tuples and without tuples (desugared to records).
 *)
theory ShallowTuples
  imports ShallowUtil
begin

(* shallow_tuples_rel: relation between tupled and non-tupled values (and functions).
 * By convention, the non-tupled value is the first argument. *)
consts shallow_tuples_rel :: "'a \<Rightarrow> 'at \<Rightarrow> bool"

(* Basic types. *)
overloading shallow_tuples_rel_unit \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_unit (x :: unit) (y :: unit) \<equiv> x = y"
end
overloading shallow_tuples_rel_bool \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_bool (x :: bool) (y :: bool) \<equiv> x = y"
end
overloading shallow_tuples_rel_word \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_word (x :: 'a word) (y :: 'a word) \<equiv> x = y"
end
overloading shallow_tuples_rel_fun \<equiv> shallow_tuples_rel begin
  definition "shallow_tuples_rel_fun (f :: 'a \<Rightarrow> 'b) (ft :: 'at \<Rightarrow> 'bt) \<equiv>
                \<forall>a at. shallow_tuples_rel a at \<longrightarrow> shallow_tuples_rel (f a) (ft at)"
end

(* Proof rules for programs. *)
(* Prove function call to obtain function rel *)
lemma shallow_tuples_rel_funI:
  "(\<And>x xt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel (f x) (ft xt)) \<Longrightarrow>
   shallow_tuples_rel f ft"
  by (simp add: shallow_tuples_rel_fun_def)

(* Dest rule: obtain function call rule from function rel *)
lemma shallow_tuples_rel_funD:
  "shallow_tuples_rel f ft \<Longrightarrow> (\<And>x xt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel (f x) (ft xt))"
  by (simp add: shallow_tuples_rel_fun_def)

lemma shallow_tuples_Let:
  "\<lbrakk> shallow_tuples_rel a at;
     \<And>x xt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel (b x) (bt xt)
   \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Let a b) (Let at bt)"
  by simp

lemma shallow_tuples_Let\<^sub>d\<^sub>s:
  "\<lbrakk> shallow_tuples_rel a at;
     \<And>x xt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel (b x) (bt xt)
   \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Let\<^sub>d\<^sub>s a b) (Let\<^sub>d\<^sub>s at bt)"
  by (simp add: Let\<^sub>d\<^sub>s_def)

lemma shallow_tuples_take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t:
  "\<lbrakk> shallow_tuples_rel a at;
     \<And>x xt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel (field x) (fieldt xt);
     \<And>x y xt yt. shallow_tuples_rel x xt \<Longrightarrow> shallow_tuples_rel y yt \<Longrightarrow> shallow_tuples_rel (b x y) (bt xt yt)
   \<rbrakk> \<Longrightarrow> shallow_tuples_rel (Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t a field) (case_prod b)) (Let (take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t at fieldt) (case_prod bt))"
  by (simp add: take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t_def)

lemma shallow_tuples_If:
  "\<lbrakk> shallow_tuples_rel a at;
     shallow_tuples_rel b bt;
     shallow_tuples_rel c ct
   \<rbrakk> \<Longrightarrow> shallow_tuples_rel (If a b c) (If at bt ct)"
  by (simp add: shallow_tuples_rel_bool_def)

lemma shallow_tuples_unit:
  "shallow_tuples_rel (a :: unit) (at :: unit)"
  by (simp add: shallow_tuples_rel_unit_def)


(* Templates for primop rules. *)
lemma shallow_tuples_unop_word_word:
  "\<And>(x :: 'a word) xt.
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel (f x :: 'a word) (f xt)"
  by (simp add: shallow_tuples_rel_word_def)

lemma shallow_tuples_binop_word_word:
  "\<And>(x :: 'a word) (y :: 'a word) xt yt.
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel y yt \<Longrightarrow>
     shallow_tuples_rel (f x y :: 'a word) (f xt yt)"
  by (simp add: shallow_tuples_rel_word_def)

lemma shallow_tuples_binop_word_bool:
  "\<And>(x :: 'a word) (y :: 'a word) xt yt.
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel y yt \<Longrightarrow>
     shallow_tuples_rel (f x y :: bool) (f xt yt)"
  by (simp add: shallow_tuples_rel_word_def shallow_tuples_rel_bool_def)

lemma shallow_tuples_unop_bool_bool:
  "\<And>(x :: bool) xt.
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel (f x :: bool) (f xt)"
  by (simp add: shallow_tuples_rel_bool_def)

lemma shallow_tuples_binop_bool_bool:
  "\<And>(x :: bool) (y :: bool) xt yt.
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel y yt \<Longrightarrow>
     shallow_tuples_rel (f x y :: bool) (f xt yt)"
  by (simp add: shallow_tuples_rel_bool_def)

lemma shallow_tuples_ucast:
  "\<And>(x :: ('a::len0) word) (xt :: 'a word).
     shallow_tuples_rel x xt \<Longrightarrow>
     shallow_tuples_rel (ucast x :: ('b::len0) word) (ucast xt :: 'b word)"
  by (simp add: shallow_tuples_rel_word_def)

(* Primop rules *)
lemmas shallow_tuples_primop =
  shallow_tuples_binop_word_word[where f="plus"]
  shallow_tuples_binop_word_word[where f="minus"]
  shallow_tuples_binop_word_word[where f="times"]
  shallow_tuples_binop_word_word[where f="checked_div"]
  shallow_tuples_binop_word_word[where f="checked_mod"]
  shallow_tuples_unop_bool_bool[where f="HOL.Not"]
  shallow_tuples_binop_bool_bool[where f="HOL.conj"]
  shallow_tuples_binop_bool_bool[where f="HOL.disj"]
  shallow_tuples_binop_word_bool[where f="greater"]
  shallow_tuples_binop_word_bool[where f="less"]
  shallow_tuples_binop_word_bool[where f="less_eq"]
  shallow_tuples_binop_word_bool[where f="greater_eq"]
  shallow_tuples_binop_bool_bool[where f="HOL.eq"]
  shallow_tuples_binop_word_bool[where f="HOL.eq"]
  shallow_tuples_binop_bool_bool[where f="HOL.not_equal"]
  shallow_tuples_binop_word_bool[where f="HOL.not_equal"]
  shallow_tuples_binop_word_word[where f="bitAND"]
  shallow_tuples_binop_word_word[where f="bitOR"]
  shallow_tuples_binop_word_word[where f="bitXOR"]
  shallow_tuples_binop_word_word[where f="checked_shift shiftl"]
  shallow_tuples_binop_word_word[where f="checked_shift shiftr"]
  shallow_tuples_unop_word_word[where f="bitNOT"]
  shallow_tuples_ucast

lemma shallow_tuples_lit:
  "\<And>x :: 'a word. shallow_tuples_rel x x"
  "\<And>x :: bool. shallow_tuples_rel x x"
  by (auto simp: shallow_tuples_rel_word_def shallow_tuples_rel_bool_def)


(* All basic rules *)
lemmas shallow_tuples_basic_bucket =
  shallow_tuples_take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t (* before Let *)
  shallow_tuples_Let (* after take\<^sub>c\<^sub>o\<^sub>g\<^sub>e\<^sub>n\<^sub>t *)
  shallow_tuples_Let\<^sub>d\<^sub>s
  shallow_tuples_If
  shallow_tuples_primop
  shallow_tuples_unit
  shallow_tuples_lit

end