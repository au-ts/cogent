theory Detuple
  imports Cogent
begin

fun detuple_type :: "type \<Rightarrow> type" where
  "detuple_type (TVar i)         = TVar i"
| "detuple_type (TVarBang i)     = TVarBang i"
| "detuple_type (TCon n ts s)    = TCon n (map detuple_type ts) s"
| "detuple_type (TFun ta tb)     = TFun (detuple_type ta) (detuple_type tb)"
| "detuple_type (TPrim p)        = TPrim p"
| "detuple_type (TSum ts)        = TSum (map (\<lambda>(n,t,b). (n, detuple_type t, b)) ts)"
| "detuple_type (TProduct ta tb) = TRecord [(''fst'', detuple_type ta, Present), (''snd'', detuple_type tb, Present)] Unboxed"
| "detuple_type (TRecord ts s)   = TRecord (map (\<lambda>(n,t,b). (n, detuple_type t, b)) ts) s"
| "detuple_type TUnit            = TUnit"

fun detuple_expr :: "'f expr \<Rightarrow> 'f expr" where
  "detuple_expr (Var i)           = Var i"
| "detuple_expr (Fun f ts)        = Fun f (map detuple_type ts)"
| "detuple_expr (AFun f ts)       = AFun f (map detuple_type ts)"
| "detuple_expr (Prim p es)       = Prim p (map detuple_expr es)"
| "detuple_expr (App a b)         = App (detuple_expr a) (detuple_expr b)"
| "detuple_expr (Con as t e)      = Con (map (\<lambda>(n,t,b). (n, detuple_type t, b)) as) t (detuple_expr e)"
| "detuple_expr (Struct ts vs)    = Struct (map detuple_type ts) (map detuple_expr vs)"
| "detuple_expr (Member v f)      = Member (detuple_expr v) f"
| "detuple_expr (Unit)            = Unit"
| "detuple_expr (Cast t e)        = Cast t (detuple_expr e)"
| "detuple_expr (Lit v)           = Lit v"
| "detuple_expr (SLit s)          = SLit s"
| "detuple_expr (Tuple a b)       = Tuple (detuple_expr a) (detuple_expr b)"
| "detuple_expr (Put e f e')      = Put (detuple_expr e) f (detuple_expr e')"
| "detuple_expr (Let e e')        = Let (detuple_expr e) (detuple_expr e')"
| "detuple_expr (LetBang vs e e') = LetBang vs (detuple_expr e) (detuple_expr e')"
| "detuple_expr (Case e t a b)    = Case (detuple_expr e) t (detuple_expr a) (detuple_expr b)"
| "detuple_expr (Esac e t)        = Esac (detuple_expr e) t"
| "detuple_expr (If c t e)        = If (detuple_expr c) (detuple_expr t) (detuple_expr e)"
| "detuple_expr (Take e f e')     = Take (detuple_expr e) f (detuple_expr e')"
| "detuple_expr (Split v va)      = Split (detuple_expr v) (detuple_expr va)"
| "detuple_expr (Promote t x)     = Promote (detuple_type t) (detuple_expr x)"



definition detuple_xi :: "('a \<Rightarrow> 'b \<times> Cogent.type \<times> Cogent.type) \<Rightarrow> ('a \<Rightarrow> 'b \<times> Cogent.type \<times> Cogent.type)" where
  "detuple_xi \<Xi> = ((\<lambda>(n,s,t). (n, detuple_type s, detuple_type t)) \<circ> \<Xi>)"

abbreviation detuple_gamma :: "ctx \<Rightarrow> ctx" where
  "detuple_gamma \<equiv> map (map_option detuple_type)"

section {* Lemmas About Detuple *}

subsection {* Wellformed and Kinding *}

lemma detuple_type_preserves_type_wellformed:
  assumes "type_wellformed n t"
  shows "type_wellformed n (detuple_type t)"
  using assms
proof (induct t)
  case TCon then show ?case
    by (clarsimp simp add: list_all_length)
next
  case TSum then show ?case
    by (fastforce simp add: list_all_length in_set_conv_nth split: prod.splits)
next
  case TRecord then show ?case
    by (fastforce simp add: list_all_length in_set_conv_nth split: prod.splits)
qed auto

lemma detuple_type_preserves_wellformed:
  assumes "K \<turnstile> t wellformed"
  shows "K \<turnstile> detuple_type t wellformed"
  using assms
  by (clarsimp simp add: detuple_type_preserves_type_wellformed)

lemma detuple_kinding_fn_eq:
  shows "kinding_fn K t = kinding_fn K (detuple_type t)"
proof (induct t)
  case TCon then show ?case
    by (auto simp add: list_all_length split: prod.splits record_state.splits)
next
  case TSum then show ?case
    apply (auto simp add: list_all_length split: prod.splits record_state.splits)
     apply (case_tac b; force)
    apply (case_tac b; force)
    done
next
  case TProduct then show ?case
    using kind_top by auto
next
  case TRecord then show ?case
    by (auto simp add: list_all_length split: prod.splits record_state.splits)
qed auto

lemma detuple_type_preserves_kinding:
  assumes "K \<turnstile> t :\<kappa> k"
  shows"K \<turnstile> detuple_type t :\<kappa> k"
  using assms detuple_kinding_fn_eq detuple_type_preserves_wellformed kinding_def
  by fastforce

subsection {* Splitting and Weakening *}

lemma detuple_gamma_preserves_splitting:
  assumes "K \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows "K \<turnstile> detuple_gamma \<Gamma> \<leadsto> detuple_gamma \<Gamma>1 | detuple_gamma \<Gamma>2"
  using assms
proof (induct rule: split_induct)
  case (split_cons x xs y ys z zs)
  then show ?case
    using detuple_type_preserves_kinding
    by (force
        intro!: Cogent.split_cons
        simp add:  detuple_type_preserves_type_wellformed split_comp.simps)
qed (simp add: Cogent.split_empty)

lemma detuple_gamma_preserves_weakening:
  assumes "K \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
  shows "K \<turnstile> detuple_gamma \<Gamma> \<leadsto>w detuple_gamma \<Gamma>'"
  using assms
proof (induct rule: weakening_induct)
  case (weakening_cons x xs y ys)
  then show ?case
    using detuple_type_preserves_kinding
    by (auto
        intro!: Cogent.weakening_cons
        simp add:  detuple_type_preserves_type_wellformed weakening_comp.simps)
qed (simp add: Cogent.weakening_nil)

subsection {* Misc *} 

lemma detuple_type_idem:
  "detuple_type (detuple_type t) = detuple_type t"
  by (induct t, auto)

lemma detuple_type_bang_eq_bang_detuple_type:
  "detuple_type (bang t) = bang (detuple_type t)"
  by (induct t, auto)

lemma detuple_type_instantiate_eq_instantiate_detuple_type:
  "detuple_type (instantiate ts t) = instantiate (map detuple_type ts) (detuple_type t)"
  by (induct t arbitrary: ts, auto simp add: detuple_type_bang_eq_bang_detuple_type)

lemma detuple_gamma_empty_eq_empty:
  "detuple_gamma (Cogent.empty n) = Cogent.empty n"
  by (clarsimp simp add: empty_def)

lemma detuple_type_preserves_subtyping:
  assumes "K \<turnstile> t' \<sqsubseteq> t"
  shows "K \<turnstile> detuple_type t' \<sqsubseteq> detuple_type t"
  using assms
proof (induct rule: subtyping.inducts)
  case (subty_trecord K ts1 ts2 s1 s2)
  then show ?case sorry
next
  case (subty_tsum K ts1 ts2)
  then show ?case sorry
qed (auto intro!: subtyping.intros)


lemma
  shows "\<Xi>, K, \<Gamma> \<turnstile> e : \<tau>
    \<Longrightarrow> detuple_xi \<Xi>, K, detuple_gamma \<Gamma> \<turnstile> detuple_expr e : detuple_type \<tau>"
  and "\<Xi>, K, \<Gamma> \<turnstile>* es : \<tau>s
    \<Longrightarrow> detuple_xi \<Xi>, K, detuple_gamma \<Gamma> \<turnstile>* map detuple_expr es : map detuple_type \<tau>s"
proof (induct rule: typing_typing_all.inducts)
  (* TODO cleanup *)
  case (typing_var K \<Gamma> i t \<Xi>)
  then show ?case
    apply (auto intro!: typing_typing_all.intros simp add: weakening_conv_all_nth Cogent.empty_def nth_list_update)
     apply (drule_tac x=i in spec)
     apply (auto elim!: weakening_comp.cases simp add: weakening_comp.simps)
     apply (force dest: detuple_type_preserves_type_wellformed)
    apply (case_tac "\<Gamma> ! ia")
     apply clarsimp
    apply clarsimp
    apply (drule_tac x=ia in spec)
    apply clarsimp
    apply (force dest: detuple_type_preserves_kinding)
    done
next
  (* TODO cleanup *)
  case (typing_afun \<Xi> f K' t u t' ts u' K \<Gamma>)
  then show ?case
    apply (auto
        intro!: typing_typing_all.intros
        simp add: weakening_conv_all_nth Cogent.empty_def
        nth_list_update detuple_type_instantiate_eq_instantiate_detuple_type
        detuple_type_preserves_kinding list_all2_conv_all_nth
        detuple_type_preserves_type_wellformed
        weakening_comp.simps
        detuple_xi_def)
    using detuple_type_preserves_kinding
    apply blast
    done
next
  case (typing_fun \<Xi> K' t f u t' ts u' K \<Gamma>)
  then show ?case
apply (auto
        intro!: typing_typing_all.intros
        simp add: weakening_conv_all_nth Cogent.empty_def
        nth_list_update detuple_type_instantiate_eq_instantiate_detuple_type
        detuple_type_preserves_kinding list_all2_conv_all_nth
        detuple_type_preserves_type_wellformed
        weakening_comp.simps)

    sorry
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y b)
  then show ?case
    by (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
next
  case (typing_cast \<Xi> K \<Gamma> e \<tau> \<tau>')
  then show ?case by (auto intro!: typing_typing_all.intros)
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> t T u U)
  then show ?case
    apply (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
    sorry
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  then show ?case
    apply (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
    sorry
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  then show ?case
    apply (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
    sorry
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then show ?case
    apply (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
    sorry
next
  (* TODO cleanup *)
  case (typing_con \<Xi> K \<Gamma> x t tag ts ts')
  moreover have
    "\<And>t1 t2 b. (tag, t1, b) \<in> set ts' \<Longrightarrow> (tag, t2, b) \<in> set ts' \<Longrightarrow> t1 = t2"
    using typing_con distinct_fst by fastforce
  moreover then have "(tag, detuple_type t, Unchecked) \<in> (\<lambda>(n, t, b). (n, detuple_type t, b)) ` set ts'"
    using typing_con
    by (clarsimp simp add: image_iff split: prod.split, blast)
  ultimately show ?case
    apply (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
    using \<open>(tag, detuple_type t, Unchecked) \<in> (\<lambda>(n, t, b). (n, detuple_type t, b)) ` set ts'\<close>
     apply blast
    apply (metis detuple_type.simps(6) detuple_type_preserves_type_wellformed type_wellformed.simps(6))
    done
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then show ?case sorry
next
  case (typing_esac \<Xi> K \<Gamma> x ts n t)
  then show ?case
    apply (auto intro!: typing_typing_all.intros)
    sorry
next
  case typing_if then show ?case
    by (auto intro!: typing_typing_all.intros dest: detuple_gamma_preserves_splitting)
next
  case typing_prim then show ?case
    by (auto
        intro!: typing_typing_all.intros
        dest: detuple_gamma_preserves_splitting
        simp add: comp_def)
next
  case typing_lit then show ?case
    by (auto
        intro!: typing_typing_all.intros
        dest: detuple_gamma_preserves_weakening
        simp add: detuple_gamma_empty_eq_empty)
next
  case typing_slit then show ?case
    by (auto
        intro!: typing_typing_all.intros
        dest: detuple_gamma_preserves_weakening
        simp add: detuple_gamma_empty_eq_empty)
next
  case typing_unit then show ?case
    by (auto
        intro!: typing_typing_all.intros
        dest: detuple_gamma_preserves_weakening
        simp add: detuple_gamma_empty_eq_empty)
next
  case typing_struct then show ?case
    by (auto intro!: typing_typing_all.intros)
next
  case typing_member then show ?case
    by (auto dest: detuple_type_preserves_kinding intro!: typing_typing_all.intros)
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  then show ?case
    apply (auto
        dest: detuple_type_preserves_kinding detuple_gamma_preserves_splitting
        intro!: typing_typing_all.intros)
    sorry
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  then show ?case
    apply (auto
        dest: detuple_type_preserves_kinding detuple_gamma_preserves_splitting
        intro!: typing_typing_all.intros)
    sorry
next
  case typing_promote then show ?case
    by (auto
        dest: detuple_type_preserves_subtyping
        intro!: typing_typing_all.intros)
next
  case typing_all_empty then show ?case
    by (auto
        simp add: detuple_gamma_empty_eq_empty
        intro!: typing_typing_all.intros)
next
  case typing_all_cons then show ?case
    by (auto
        dest: detuple_type_preserves_kinding detuple_gamma_preserves_splitting
        intro!: typing_typing_all.intros)
qed

end