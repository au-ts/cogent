theory TypeInfer
  imports Cogent
  "../../autocorres/lib/Apply_Trace_Cmd"
begin

(* misc lemmas: to move *)

lemma meta_eq_mp:
  "\<lbrakk>P \<equiv> Q; Q\<rbrakk> \<Longrightarrow> P"
  by blast

lemma singleton_filter_iff:
  "[x] = filter P xs \<longleftrightarrow> (\<exists>i<length xs. xs ! i = x \<and> (\<forall>j<length xs. i \<noteq> j \<longrightarrow> \<not> P (xs ! j))) \<and> P x"
  apply (induct xs)
   apply force
  apply (simp add: Ex_less_Suc2 All_less_Suc2 filter_empty_conv2[simplified in_set_conv_nth Ball_def], blast) 
  done


lemma distinct_upd_sameI:
  "distinct (map f xs) \<Longrightarrow> f (xs ! i) = x \<Longrightarrow> distinct ((map f xs)[i := x])"
  apply (induct xs arbitrary: i)
   apply simp
  apply (clarsimp simp add:  split: nat.splits)
  apply (metis image_set list_update_id map_update)
  done

lemma prod_eq_iff_proj_eq: "p = (a,b) \<longleftrightarrow> (fst p = a \<and> snd p = b)"
  by fastforce

lemma filter_to_singleton_unique[dest, consumes 2]: "[x] = filter P xs \<Longrightarrow> [y] = filter P xs \<Longrightarrow> x = y"
  by (metis list.inject)

(* Cogent lemmas *)

lemma weakening_comp_trans:
  "weakening_comp K a b \<Longrightarrow> weakening_comp K b c \<Longrightarrow> weakening_comp K a c"
  by (force simp add: weakening_comp.simps)

lemma weakening_trans:
  "K \<turnstile> xs \<leadsto>w ys \<Longrightarrow> K \<turnstile> ys \<leadsto>w zs \<Longrightarrow> K \<turnstile> xs \<leadsto>w zs"
  by (fastforce simp add: weakening_conv_all_nth weakening_comp.simps)

lemma consume_weakening:
  "\<lbrakk>K \<turnstile> xs \<leadsto>w ys; K \<turnstile> ys consumed\<rbrakk> \<Longrightarrow> K \<turnstile> xs consumed"
  by (metis is_consumed_def weakening_length weakening_trans)


lemma typing_weaken_context:
shows "\<Xi>, K, \<Gamma> \<turnstile>  e  : t  \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>  e  : t"
and   "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> K \<turnstile> \<Gamma>' \<leadsto>w \<Gamma> \<Longrightarrow> \<Xi>, K, \<Gamma>' \<turnstile>* es : ts"
proof (induct arbitrary: \<Gamma>' rule: typing_typing_all.inducts)
  case typing_var then show ?case
    by (bestsimp
        intro!: typing_typing_all.intros
        simp add: weakening_conv_all_nth Cogent.empty_def
        dest: weakening_comp_trans)
next
  case typing_afun then show ?case
    by (fastforce intro!: typing_typing_all.intros dest: consume_weakening)
next
  case typing_fun then show ?case
    by (fastforce intro!: typing_typing_all.intros dest: consume_weakening)
next
  case (typing_app K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> a x y b)
  then show ?case
    sorry
next
  case (typing_cast \<Xi> K \<Gamma> e \<tau> \<tau>')
  then show ?case sorry
next
  case (typing_tuple K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> t T u U)
  then show ?case sorry
next
  case (typing_split K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t u y t')
  then show ?case sorry
next
  case (typing_let K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u)
  then show ?case sorry
next
  case (typing_letb K "is" \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x t y u k)
  then show ?case sorry
next
  case (typing_con \<Xi> K \<Gamma> x t tag ts ts')
  then show ?case sorry
next
  case (typing_case K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then show ?case sorry
next
  case (typing_esac \<Xi> K \<Gamma> x ts n t)
  then show ?case sorry
next
  case (typing_if K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x a t b)
  then show ?case sorry
next
  case (typing_prim \<Xi> K \<Gamma> args ts oper t)
  then show ?case sorry
next
  case (typing_lit K \<Gamma> \<Xi> l)
  then show ?case sorry
next
  case (typing_slit K \<Gamma> \<Xi> s)
  then show ?case sorry
next
  case (typing_unit K \<Gamma> \<Xi>)
  then show ?case sorry
next
  case (typing_struct \<Xi> K \<Gamma> es ts ns ts' ts'')
  then show ?case sorry
next
  case (typing_member \<Xi> K \<Gamma> e ts s k f n t)
  then show ?case sorry
next
  case (typing_take K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  then show ?case sorry
next
  case (typing_put K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  then show ?case sorry
next
  case (typing_promote \<Xi> K \<Gamma> x t' t)
  then show ?case sorry
next
  case (typing_all_empty \<Gamma> n \<Xi> K)
  then show ?case sorry
next
  case (typing_all_cons K \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e t es ts)
  then show ?case sorry
qed

(* main theory *)


definition countPlus :: "('a :: plus) list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<oplus>" 75) where
  "xs \<oplus> ys \<equiv> map2 (+) xs ys"

lemma countPlus_simps[simp]:
  "countPlus [] [] = []"
  "countPlus (x # xs) (y # ys) = (x+y) # (xs \<oplus> ys)"
  "countPlus [] (y # ys) = []"
  "countPlus (x # xs) [] = []"
  by (simp add: countPlus_def)+

lemma countPlus_length[simp]:
  "length (C1 \<oplus> C2) = min (length C1) (length C2)"
  by (simp add: countPlus_def)

lemma countPlus_eq_Nil[simp]:
  "(C1 \<oplus> C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)
lemma countPlus_eq_Nil2[simp]:
  "([] = C1 \<oplus> C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countPlus_length length_greater_0_conv min_less_iff_conj)

lemma countPlus_eq_Cons:
  "(C1 \<oplus> C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)
lemma countPlus_eq_Cons2:
  "(x # xs = C1 \<oplus> C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = y + z \<and> xs = ys \<oplus> zs)"
  by (case_tac C1; case_tac C2; force)


lemma countPlus_nth[simp]:
  "i < length C1 \<Longrightarrow> i < length C2 \<Longrightarrow> (C1 \<oplus> C2) ! i = C1 ! i + C2 ! i"
  by (simp add: countPlus_def)


definition countMax :: "('a :: sup) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "countMax xs ys \<equiv> map2 sup xs ys"

lemma countMax_simps[simp]:
  "countMax [] [] = []"
  "countMax (x # xs) (y # ys) = (sup x y) # (countMax xs ys)"
  "countMax [] (y # ys) = []"
  "countMax (x # xs) [] = []"
  by (simp add: countMax_def)+

lemma countMax_length[simp]:
  "length (countMax C1 C2) = min (length C1) (length C2)"
  by (simp add: countMax_def)

lemma countMax_eq_Nil[simp]:
  "(countMax C1 C2 = []) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)
lemma countMax_eq_Nil2[simp]:
  "([] = countMax C1 C2) \<longleftrightarrow> (C1 = []) \<or> (C2 = [])"
  by (metis countMax_length length_greater_0_conv min_less_iff_conj)

lemma countMax_eq_Cons:
  "(countMax C1 C2 = x # xs) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)
lemma countMax_eq_Cons2:
  "(x # xs = countMax C1 C2) \<longleftrightarrow> (\<exists>y ys z zs. C1 = y # ys \<and> C2 = z # zs \<and> x = sup y z \<and> xs = countMax ys zs)"
  by (case_tac C1; case_tac C2; force)




datatype linearity = LMany ("\<omega>") | LOne | LNone

instantiation linearity :: "{one, linorder, bounded_lattice, comm_monoid_add, canonically_ordered_monoid_add}"
begin

definition "bot_linearity \<equiv> LNone"
fun sup_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "sup_linearity LNone b = b"
| "sup_linearity LOne LNone = LOne"
| "sup_linearity LOne b = b"
| "sup_linearity LMany b = LMany"
definition "top_linearity \<equiv> LMany"
fun inf_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "inf_linearity LMany b = b"
| "inf_linearity LOne LMany = LOne"
| "inf_linearity LOne b = b"
| "inf_linearity LNone b = LNone"

definition "zero_linearity \<equiv> LNone"

definition "one_linearity \<equiv> LOne"

fun less_eq_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_eq_linearity LNone _ = True"
| "less_eq_linearity LOne LNone = False"
| "less_eq_linearity LOne _ = True"
| "less_eq_linearity LMany LMany = True"
| "less_eq_linearity LMany _ = False"

fun less_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> bool" where
  "less_linearity LNone LNone = False"
| "less_linearity LNone _ = True"
| "less_linearity LOne LOne = False"
| "less_linearity LOne LNone = False"
| "less_linearity LOne _ = True"
| "less_linearity LMany _ = False"

fun plus_linearity :: "linearity \<Rightarrow> linearity \<Rightarrow> linearity" where
  "plus_linearity LNone x = x"
| "plus_linearity LOne LNone = LOne"
| "plus_linearity LOne LOne = LMany"
| "plus_linearity LOne LMany = LMany"
| "plus_linearity LMany x = LMany"


lemma lin_add_sym: "a + b = b + (a :: linearity)"
  by (cases a; cases b; simp)

lemma lin_sup_sym: "sup a b = sup b (a :: linearity)"
  by (cases a; cases b; simp)


lemma linearity_1plus1: "1 + 1 = \<omega>"
  by (simp add: one_linearity_def)

lemma linearity_add_to_none_are_nones[simp]: "a + b = LNone \<longleftrightarrow> (a = LNone \<and> b = LNone)"
  using plus_linearity.elims by auto
lemmas linearity_add_to_none_are_nones2[simp] =
  trans[OF eq_commute linearity_add_to_none_are_nones]

lemma linearity_add_to_one_has_nonzero: "a + b = LOne \<Longrightarrow> (a \<noteq> LNone \<or> b \<noteq> LNone)"
  by auto

lemma linearity_sup_to_many_some_many[simp]: "sup a b = \<omega> \<longleftrightarrow> (a = \<omega> \<or> b = \<omega>)"
  using sup_linearity.elims
  by (cases a; cases b; simp)
lemmas linearity_sup_to_many_some_many2[simp] =
  trans[OF eq_commute linearity_sup_to_many_some_many]



instance
proof
  fix x y z :: linearity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y; simp)
  show "x \<le> x"
    by (cases x; simp)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y; simp)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y; simp)
next
  fix a b c :: linearity
  show "a + b + c = a + (b + c)"
    by (cases a; cases b; cases c; simp)
  show "a + b = b + a"
    by (cases a; cases b; simp)
  show "0 + a = a"
    by (cases a; simp add: zero_linearity_def)+
next
  fix a :: linearity
  show "bot \<le> a"
    by (simp add: bot_linearity_def)
  show "a \<le> top"
    by (cases a; simp add: top_linearity_def)
next
  fix x y z :: linearity
  show "inf x y \<le> x"
    by (cases x; cases y; simp)
  show "inf x y \<le> y"
    by (cases x; cases y; simp)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (cases x; cases y; cases z; simp)
  show "x \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> sup x y"
    by (cases x; cases y; simp)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (cases x; cases y; cases z; simp)
next
  fix a b :: linearity
  show "(a \<le> b) = (\<exists>c. b = a + c)"
    by (cases "(a,b)" rule: less_eq_linearity.cases
        ; simp, (metis plus_linearity.simps(2-3))?)
qed

end


lemma plus_linearity_simps[simp]:
  "x + LNone = x"
  "x + \<omega> = \<omega>"
  by (simp add: lin_add_sym)+

lemma linearity_zero_case[simp]: "case_linearity p q r 0 = r"
  by (simp add: zero_linearity_def)

lemma linearity_one_case[simp]: "case_linearity p q r 1 = q"
  by (simp add: one_linearity_def)

lemmas linearity_order_simps[simp] =
  order_top_class.top_greatest[where a="a :: linearity" for a, simplified top_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def]
  order_bot_class.bot_least[where a="a :: linearity" for a, simplified bot_linearity_def zero_linearity_def[symmetric]]

lemma linearity_neq_none_iff: "x \<noteq> LNone \<longleftrightarrow> x = \<omega> \<or> x = LOne"
  by (cases x; simp)

lemma linearity_neq_one_iff: "x \<noteq> LOne \<longleftrightarrow> x = \<omega> \<or> x = LNone"
  by (cases x; simp)

lemma linearity_neq_many_iff: "x \<noteq> \<omega> \<longleftrightarrow> x = LOne \<or> x = LNone"
  by (cases x; simp)



definition droppable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "droppable K t \<equiv> D \<in> kinding_fn K t"

lemma droppable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> droppable K (TVar i) \<longleftrightarrow> D \<in> K ! i"
  "\<And>K i. droppable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. droppable K (TCon n ts s) \<longleftrightarrow> list_all (droppable K) ts \<and> D \<in> sigil_kind s"
  "\<And>K ta tb. droppable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. droppable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. droppable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (droppable K t) y) ts"
  "\<And>K ta tb. droppable K (TProduct ta tb) \<longleftrightarrow> droppable K ta \<and> droppable K tb"
  "\<And>K ts s. droppable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (droppable K t) y) ts \<and> D \<in> sigil_kind s"
  "\<And>K. droppable K TUnit \<longleftrightarrow> True"
  by (force simp add: droppable_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+

definition sharable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "sharable K t \<equiv> S \<in> kinding_fn K t"

lemma sharable_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> sharable K (TVar i) \<longleftrightarrow> S \<in> K ! i"
  "\<And>K i. sharable K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. sharable K (TCon n ts s) \<longleftrightarrow> list_all (sharable K) ts \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. sharable K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. sharable K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. sharable K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (sharable K t) y) ts"
  "\<And>K ta tb. sharable K (TProduct ta tb) \<longleftrightarrow> sharable K ta \<and> sharable K tb"
  "\<And>K ts s. sharable K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (sharable K t) y) ts \<and> S \<in> sigil_kind s"
  "\<And>K. sharable K TUnit \<longleftrightarrow> True"
  by (force simp add: sharable_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+

definition nonlinear :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "nonlinear K t \<equiv> droppable K t \<and> sharable K t"

lemma nonlinear_simps[simp]:
  "\<And>K i. i < length K \<Longrightarrow> nonlinear K (TVar i) \<longleftrightarrow> D \<in> K ! i \<and> S \<in> K ! i"
  "\<And>K i. nonlinear K (TVarBang i) \<longleftrightarrow> True"
  "\<And>K n ts s. nonlinear K (TCon n ts s) \<longleftrightarrow> list_all (nonlinear K) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K ta tb. nonlinear K (TFun ta tb) \<longleftrightarrow> True"
  "\<And>K p. nonlinear K (TPrim p) \<longleftrightarrow> True"
  "\<And>K ts. nonlinear K (TSum ts) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_variant_state True (nonlinear K t) y) ts"
  "\<And>K ta tb. nonlinear K (TProduct ta tb) \<longleftrightarrow> nonlinear K ta \<and> nonlinear K tb"
  "\<And>K ts s. nonlinear K (TRecord ts s) \<longleftrightarrow> list_all (\<lambda>(_, t, y). case_record_state True (nonlinear K t) y) ts \<and> D \<in> sigil_kind s \<and> S \<in> sigil_kind s"
  "\<And>K. nonlinear K TUnit \<longleftrightarrow> True"
  by (force simp add: nonlinear_def all_set_conv_all_nth list_all_length split: variant_state.splits record_state.splits)+



lemma sigil_kind_drop_impl_share:
  "D \<in> sigil_kind s \<Longrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_share_impl_drop:
  "S \<in> sigil_kind s \<Longrightarrow> D \<in> sigil_kind s"
  using sigil_kind.elims by auto

lemma sigil_kind_drop_iff_share:
  "D \<in> sigil_kind s \<longleftrightarrow> S \<in> sigil_kind s"
  using sigil_kind.elims by auto


definition well_kinded :: "kind \<Rightarrow> bool" where
  "well_kinded k \<equiv> D \<in> k \<longleftrightarrow> S \<in> k"

definition well_kinded_all :: "kind list \<Rightarrow> bool" where
  "well_kinded_all \<equiv> list_all well_kinded"


lemma droppable_iff_nonlinear[simp]:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> droppable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth
        split: prod.splits variant_state.splits record_state.splits; metis)+

lemma sharable_iff_nonlinear[simp]:
  "well_kinded_all K \<Longrightarrow> K \<turnstile> t wellformed \<Longrightarrow> sharable K t \<longleftrightarrow> nonlinear K t"
  by (induct t)
      (clarsimp
        simp add: list_all_length well_kinded_all_def well_kinded_def sigil_kind_drop_iff_share
        prod_eq_iff_proj_eq in_set_conv_nth
        split: prod.splits variant_state.splits record_state.splits; metis)+



definition is_used :: "kind env \<Rightarrow> type \<Rightarrow> ('a :: {one, order}) \<Rightarrow> bool" where
  "is_used K t c \<equiv> (c \<ge> 1) \<and> (c \<noteq> 1 \<longrightarrow> droppable K t)"

lemma is_used_linearity_iff[simp]:
  "is_used K t (c :: linearity) \<longleftrightarrow> c = 1 \<or> (c = \<omega> \<and> droppable K t)"
  by (cases c; clarsimp simp add: one_linearity_def is_used_def)

(*
\<Gamma> is input.
C is output.
The expression is input.
For synthesising, the type is output.
For checking, the type is input.

Not that C being output means that in an assumption, C should be a variable.
If you want to enforce a structure on C, you have to use an equality so it can do computation.
*)
inductive tyinf_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<down> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_check :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<up> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_all_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _, _ \<turnstile>\<down>* _ : _" [30,0,0,0,0,20] 60) where

(* synthesising *)

  tyinf_var    : "\<lbrakk> i < length \<Gamma>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, (replicate (length \<Gamma>) 0)[i := 1] \<turnstile>\<down> Var i : (\<Gamma> ! i)"

| tyinf_tuple  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> t : \<tau>1
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down> u : \<tau>2
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Tuple t u : TProduct \<tau>1 \<tau>2"

| tyinf_con    : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t
                  ; (tag, t, Unchecked) \<in> set ts
                  ; K \<turnstile> TSum ts wellformed
                  ; ts = ts'
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : TSum ts'"

| tyinf_esac   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : TSum ts
                  ; [(n, t, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"


| tyinf_lit    : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Lit l : TPrim (lit_type l)"

| tyinf_slit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> SLit s : TPrim String"

| tyinf_unit   : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down> Unit : TUnit"

| tyinf_member : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : TRecord ts s
                  ; sharable K (TRecord ts s)
                  ; f < length ts
                  ; snd (snd (ts ! f)) = Present
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : fst (snd (ts ! f))"

| tyinf_put    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, taken)
                  ; D \<in> kinding_fn K t \<or> taken = Taken
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> e' : t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Put e f e' : TRecord (ts[f := (n,t,Present)]) s"

| tyinf_prim   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* args : map TPrim ts
                  ; prim_op_type oper = (ts,t)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper args : TPrim t"

| tyinf_struct : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts
                  ; ts = ts' \<^cancel>\<open>FIXME: remove ts'\<close>
                  ; length ns = length ts'
                  ; distinct ns
                  ; vs = zip ns (map (\<lambda>t. (t,Present)) ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts' es : TRecord vs Unboxed"

(* checking *)

| tyinf_cast   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TPrim (Num nt)
                  ; upcast_valid nt nt1
                  ; nt1 = nt2 \<^cancel>\<open>FIXME: nt1 is unecessary\<close>
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nt1 e : TPrim (Num nt2)"

| tyinf_app    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> a : \<tau>1
                  ; \<tau>1 = TFun x y
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> b : x
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> App a b : y"

| tyinf_split  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : TProduct t u
                  ; \<Xi>, K, (t # u # \<Gamma>), C2o \<turnstile>\<up> y : t'
                  ; C2o = ct # cu # C2
                  ; is_used K t ct
                  ; is_used K u cu
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Split x y : t'"

| tyinf_let    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), C2o \<turnstile>\<up> y : u
                  ; C2o = ct # C2
                  ; is_used K t ct
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Let x y : u"

| tyinf_letb   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : t
                  ; \<Xi>, K, (t # \<Gamma>), (ct # C2) \<turnstile>\<up> y : u
                  ; is_used K t ct
                  ; E \<in> kinding_fn K t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> LetBang is x y : u"

| tyinf_case   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>1
                  ; \<tau>1 = TSum ts
                  ; (tag, t, Unchecked) \<in> set ts
                  ; \<Xi>, K, (t # \<Gamma>), C2ao \<turnstile>\<up> a : u
                  ; C2ao = ct # C2a
                  ; \<Xi>, K, (TSum (tagged_list_update tag (t, Checked) ts) # \<Gamma>), C2bo \<turnstile>\<up> b : u
                  ; C2bo = csum # C2b
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> (countMax C2a C2b) \<turnstile>\<up> Case x tag a b : u"

| tyinf_if     : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> x : \<tau>
                  ; \<tau> = TPrim Bool
                  ; \<Xi>, K, \<Gamma>, C2a \<turnstile>\<up> a : t
                  ; \<Xi>, K, \<Gamma>, C2b \<turnstile>\<up> b : t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> (countMax C2a C2b) \<turnstile>\<up> If x a b : t"

| tyinf_take   : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, Present)
                  ; sharable K t \<or> taken = Taken
                  ; \<Xi>, K, (t # TRecord (ts [f := (n,t,taken)]) s # \<Gamma>), C2o \<turnstile>\<up> e' : u
                  ; C2o = ct # cr # C2
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<up> Take e f e' : u"

| tyinf_switch: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : \<tau>
                 ; \<tau> = \<tau>'
                 \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> x : \<tau>'"

(* TODO: we don't need promote expressions *)
| tyinf_promote: "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> x : t'
                  ; K \<turnstile> t' \<sqsubseteq> t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t x : t"

| tyinf_all_empty : "\<Xi>, K, \<Gamma>, replicate (length \<Gamma>) 0 \<turnstile>\<down>* [] : []"

| tyinf_all_cons  : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : t
                     ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<down>* es : ts
                     \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down>* (e # es) : (t # ts)"

(*
| tyinf_afun   : "\<lbrakk> \<Xi> f = (K', t, u)
                   ; t' = instantiate ts t
                   ; u' = instantiate ts u
                   ; list_all2 (kinding K) ts K'
                   ; K' \<turnstile> TFun t u wellformed
                   ; K \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile> AFun f ts : TFun t' u'"

| tyinf_fun    : "\<lbrakk> \<Xi>, K', [Some t] \<turnstile> f : u
                   ; t' = instantiate ts t
                   ; u' = instantiate ts u
                   ; K \<turnstile> \<Gamma> consumed
                   ; K' \<turnstile> t wellformed
                   ; list_all2 (kinding K) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Fun f ts : TFun t' u'"
*)

inductive_cases tyinf_synth_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Var i : t"
inductive_cases tyinf_synth_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Tuple e1 e2 : t"
inductive_cases tyinf_synth_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Con ts tag x : t"
inductive_cases tyinf_synth_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Esac x n : t"
inductive_cases tyinf_synth_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Lit l : t"
inductive_cases tyinf_synth_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> SLit s : t"
inductive_cases tyinf_synth_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Unit : t"
inductive_cases tyinf_synth_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : t"
inductive_cases tyinf_synth_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Put e f e' : t"
inductive_cases tyinf_synth_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper arg : t"
inductive_cases tyinf_synth_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts es : t"

inductive_cases tyinf_check_castE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nm e : t"
inductive_cases tyinf_check_appE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> App x y : t"
inductive_cases tyinf_check_splitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Split x y : t"
inductive_cases tyinf_check_letE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Let x y : t"
inductive_cases tyinf_check_letbE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> LetBang is x y : t"
inductive_cases tyinf_check_caseE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Case x tag a b : t"
inductive_cases tyinf_check_ifE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> If x a b : t"
inductive_cases tyinf_check_takeE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Take e f e' : t"

inductive_cases tyinf_check_varE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Var i : t"
inductive_cases tyinf_check_tupleE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Tuple e1 e2 : t"
inductive_cases tyinf_check_conE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Con ts tag x : t"
inductive_cases tyinf_check_esacE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Esac x n : t"
inductive_cases tyinf_check_litE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Lit l : t"
inductive_cases tyinf_check_slitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> SLit s : t"
inductive_cases tyinf_check_unitE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Unit : t"
inductive_cases tyinf_check_memberE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Member e f : t"
inductive_cases tyinf_check_putE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Put e f e' : t"
inductive_cases tyinf_check_primE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Prim oper arg : t"
inductive_cases tyinf_check_structE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Struct ns ts es : t"

inductive_cases tyinf_check_promoteE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> Promote t x : t"

inductive_cases tyinf_all_synth_consE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* (e # es) : ts"
inductive_cases tyinf_all_synth_nilE[elim]: "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* [] : ts"

lemmas tyinf_synth_safe_intros =
  tyinf_var tyinf_tuple tyinf_con tyinf_esac tyinf_lit tyinf_slit tyinf_unit tyinf_member tyinf_put
  tyinf_prim tyinf_struct

lemmas tyinf_checking_safe_intros =
  tyinf_cast tyinf_app tyinf_split tyinf_let tyinf_letb tyinf_case tyinf_if tyinf_take
  tyinf_promote tyinf_all_empty tyinf_all_cons
  tyinf_synth_safe_intros[THEN tyinf_switch]

lemmas tyinf_safe_intros = tyinf_synth_safe_intros tyinf_checking_safe_intros



(* Obviously true, but ensures C' and t' are schematic *)
lemma tyinf_checkI:
  "\<lbrakk> \<Xi>, K, \<Gamma>, C' \<turnstile>\<down> e : t'
   ; C = C'
   ; t = t'
   \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t"
  by fast

ML \<open>
fun trace_tac ctxt (st : thm) = print_tac ctxt (@{make_string} st) st
fun trace_tac' ctxt  _ = trace_tac ctxt

  fun typinfer_tac (ctxt : Proof.context) : tactic =
    let val tac = (resolve_tac ctxt @{thms tyinf_safe_intros} ORELSE'
                  fast_force_tac (ctxt addsimps @{thms kinding_simps}));
     in REPEAT_FIRST tac
     end
\<close>






definition
  ty1 :: " Cogent.type"
where
  "ty1 \<equiv> TRecord [(''b'', (TPrim (Num U8), Present)), (''a'', (TPrim (Num U32), Present))] Unboxed"

definition
  expr1 :: "string Cogent.expr"
where
  "expr1 \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Struct [''b'',''a''] [TPrim (Num U8), TPrim (Num U32)] [Var 2, Var 0]))"

schematic_goal typing1: "\<Xi>, [], [ty1], ?C \<turnstile>\<up> expr1 : ty1"
  unfolding expr1_def ty1_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac @{context}\<close>)
  done
thm typing1[simplified]

definition
  ty2a :: "Cogent.type"
where
  "ty2a \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Present)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Taken)]
            Unboxed"

definition
  ty2b :: "Cogent.type"
where
  "ty2b \<equiv> TRecord
            [ (''a'', TCon ''A'' [] (Boxed Writable undefined), Taken)
            , (''b'', TCon ''A'' [] (Boxed Writable undefined), Present)]
            Unboxed"

definition
  expr2 :: "string Cogent.expr"
where
  "expr2 \<equiv> Take (Var 0) 0 (Put (Var 1) 1 (Var 0))"

schematic_goal typing2: "\<Xi>, [], [ty2a], ?C \<turnstile>\<up> expr2 : ty2b"
  unfolding expr2_def ty2a_def ty2b_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac @{context}\<close>)
  done
thm typing2[simplified]

schematic_goal typing3:
  "\<exists>ts. \<Xi>, [], [TCon ''A'' [] (Boxed Writable undefined)], ?C \<turnstile>\<down> Struct [''a'',''b''] ts [Var 0, Var 0] : ?t"
  apply (rule exI)
  apply (rule tyinf_checkI)
    apply (tactic \<open>typinfer_tac @{context}\<close>)
  done
thm typing3[simplified]










definition sharable_constraint :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "sharable_constraint K \<equiv> list_all2 (\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t)"

lemmas sharable_constraint_conv_all_nth =
  list_all2_conv_all_nth[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                         simplified sharable_constraint_def[symmetric]]

lemmas sharable_constraint_Nil1[simp] =
  list_all2_Nil[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                 simplified sharable_constraint_def[symmetric]]
lemmas sharable_constraint_Nil2[simp] =
  list_all2_Nil2[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                 simplified sharable_constraint_def[symmetric]]

lemmas sharable_constraint_Cons[simp] =
  list_all2_Cons[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                 simplified sharable_constraint_def[symmetric]]
lemmas sharable_constraint_Cons1 =
  list_all2_Cons1[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                  simplified sharable_constraint_def[symmetric]]
lemmas sharable_constraint_Cons2 =
  list_all2_Cons2[where P=\<open>\<lambda>t c. c = \<omega> \<longrightarrow> sharable K t\<close> for K,
                  simplified sharable_constraint_def[symmetric]]



lemma sharable_constraint_add[dest]:
  assumes "length C1 = length C2"
  shows
    "sharable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> sharable_constraint K \<Gamma> C1"
    "sharable_constraint K \<Gamma> (C1 \<oplus> C2) \<Longrightarrow> sharable_constraint K \<Gamma> C2"
  using assms
  by (clarsimp simp add: sharable_constraint_conv_all_nth lin_add_sym)+



definition tycount_to_context :: "type list \<Rightarrow> linearity list \<Rightarrow> type option list" where
  "tycount_to_context ts cs \<equiv> map2 (\<lambda>t c. case c of LNone \<Rightarrow> None | _ \<Rightarrow> Some t) ts cs"

lemma tycount_to_context_Nil[simp]:
  "tycount_to_context [] [] = []"
  by (simp add: tycount_to_context_def)

lemma tycount_to_context_Nil1[simp]:
  "tycount_to_context [] cs = []"
  by (simp add: tycount_to_context_def)

lemma tycount_to_context_Cons[simp]:
  "tycount_to_context (t # ts) (c # cs) = (case c of LNone \<Rightarrow> None | _ \<Rightarrow> Some t) # tycount_to_context ts cs"
  by (simp add: tycount_to_context_def)

lemma tycount_to_context_length[simp]:
  "length (tycount_to_context xs ys) = min (length xs) (length ys)"
  by (induct xs arbitrary: ys) (simp add: tycount_to_context_def)+

lemma tycount_to_context_upd_cs[simp]:
  assumes
    "length ts = length cs"
    "i < length cs"
  shows "tycount_to_context ts (cs[i := c]) = (tycount_to_context ts cs)[i := case c of LNone \<Rightarrow> None | _ \<Rightarrow> Some (ts ! i)]"
  using assms
  apply (induct cs arbitrary: ts i)
   apply simp
  apply (clarsimp simp add: length_Suc_conv split: nat.splits, clarsimp split: linearity.splits)
  done


lemma tycount_to_context_replicate_count:
  "tycount_to_context ts (replicate (length ts) c) = map (\<lambda>t. case c of LNone \<Rightarrow> None | _ \<Rightarrow> Some t) ts"
  by (induct ts) (simp add: tycount_to_context_def)+

lemma tycount_to_context_replicate_zero[simp]:
  "tycount_to_context ts (replicate (length ts) 0) = replicate (length ts) None"
  by (simp add: tycount_to_context_replicate_count map_replicate_const)

lemma tycount_to_context_replicate_one[simp]:
  "tycount_to_context ts (replicate (length ts) 1) = map Some ts"
  by (simp add: tycount_to_context_replicate_count)

lemma tycount_to_context_replicate_many[simp]:
  "tycount_to_context ts (replicate (length ts) \<omega>) = map Some ts"
  by (simp add: tycount_to_context_replicate_count)


definition new_sharable_constraints :: "kind list \<Rightarrow> type list \<Rightarrow> linearity list \<Rightarrow> linearity list \<Rightarrow> bool" where
  "new_sharable_constraints K \<equiv> list_all3 (\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t)"

lemmas new_sharable_constraints_Nil[simp,intro!] =
  all3Nil[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
         , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Nil1[simp] =
  list_all3_Nil1[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Nil2[simp] =
  list_all3_Nil2[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Nil3[simp] =
  list_all3_Nil3[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                , simplified new_sharable_constraints_def[symmetric]]

lemmas new_sharable_constraints_Cons =
  list_all3_Cons[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Cons1 =
  list_all3_Cons1[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                 , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Cons2 =
  list_all3_Cons2[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                 , simplified new_sharable_constraints_def[symmetric]]
lemmas new_sharable_constraints_Cons3 =
  list_all3_Cons3[ where P=\<open>\<lambda>t c1 c2. c1 = LOne \<longrightarrow> c2 = LOne \<longrightarrow> sharable K t\<close> for K
                 , simplified new_sharable_constraints_def[symmetric]]

lemma sharable_constraint_plus_iff:
  assumes "length C1 = length C2"
  shows "sharable_constraint K \<Gamma> (C1 \<oplus> C2) \<longleftrightarrow> sharable_constraint K \<Gamma> C1 \<and> sharable_constraint K \<Gamma> C2 \<and> new_sharable_constraints K \<Gamma> C1 C2"
  using assms
  by (induct \<Gamma> arbitrary: C1 C2)
     (fastforce simp add: new_sharable_constraints_Cons1 sharable_constraint_Cons1
                          countPlus_eq_Cons linearity_neq_many_iff)+

lemma sharable_constraint_max_iff:
  assumes "length C1 = length C2"
  shows "sharable_constraint K \<Gamma> (countMax C1 C2) \<longleftrightarrow> sharable_constraint K \<Gamma> C1 \<and> sharable_constraint K \<Gamma> C2"
  using assms
  by (induct \<Gamma> arbitrary: C1 C2)
     (fastforce simp add: sharable_constraint_Cons1 countMax_eq_Cons linearity_neq_many_iff)+






lemma tycount_to_context_split:
  assumes
    "length C1 = length \<G>"
    "length C2 = length \<G>"
    "K \<turnstile>* \<G> wellformed"
    "sharable_constraint K \<G> (C1 \<oplus> C2)"
  shows
    "K \<turnstile> tycount_to_context \<G> (C1 \<oplus> C2) \<leadsto> tycount_to_context \<G> C1 | tycount_to_context \<G> C2"
  using assms
  by (induct \<G> arbitrary: C1 C2)
     (fastforce simp add: split_empty length_Suc_conv split_Cons
                kinding_def split_comp.simps sharable_def split: linearity.splits)+




lemma tyinf_context_lengths:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> length C = length \<Gamma>"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> length C = length \<Gamma>"
  by (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts) simp+


lemma tyinf_preserves_wellformed[dest]:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile> t wellformed"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> K \<turnstile>* ts wellformed"
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_esac then show ?case
    by (force simp add: list_all_length map_fst_zip_take less_Suc_eq_0_disj singleton_filter_iff)
next
  case tyinf_put then show ?case
    by (force intro: distinct_upd_sameI simp add: map_update list_all_length nth_list_update)
next
  case tyinf_case then show ?case
    by (force simp add: type_wellformed_all_length list_all_length in_set_conv_nth All_less_Suc2)
next
  case tyinf_take then show ?case
    by (clarsimp simp add: prod_eq_iff_proj_eq distinct_fst_tags_update list_all_length nth_list_update)
next
  case tyinf_promote then show ?case
    by (force dest: subtyping_wellformed_preservation)
qed (simp; simp add: type_wellformed_all_length list_all_length map_fst_zip_take less_Suc_eq_0_disj)+


theorem tyinf_to_typing:
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : t    \<Longrightarrow> well_kinded_all K \<Longrightarrow> sharable_constraint K \<Gamma> C \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> \<Xi>, K, tycount_to_context \<Gamma> C \<turnstile> e : t"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<up> e : t    \<Longrightarrow> well_kinded_all K \<Longrightarrow> sharable_constraint K \<Gamma> C \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> \<Xi>, K, tycount_to_context \<Gamma> C \<turnstile> e : t"
  "\<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts \<Longrightarrow> well_kinded_all K \<Longrightarrow> sharable_constraint K \<Gamma> C \<Longrightarrow> K \<turnstile>* \<Gamma> wellformed \<Longrightarrow> \<Xi>, K, tycount_to_context \<Gamma> C \<turnstile>* es : ts"
proof (induct rule: tyinf_synth_tyinf_check_tyinf_all_synth.inducts)
  case tyinf_var then show ?case
    by (fastforce
        intro!: typing_typing_all.intros weakening_refl
        simp add: Cogent.empty_def type_wellformed_all_length)
next case tyinf_tuple then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_to_context_split kinding_kinding_allI
        dest: tyinf_context_lengths
        simp add: sharable_constraint_plus_iff)
next
  case tyinf_member then show ?case
    by (force intro!: typing_typing_all.intros kinding_kinding_allI
              simp add: prod_eq_iff_proj_eq sharable_def tyinf_context_lengths sharable_constraint_plus_iff)
next
  case tyinf_put then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_to_context_split kinding_kinding_allI
        dest: tyinf_context_lengths
        simp add: sharable_constraint_plus_iff)
next
  case tyinf_struct then show ?case
    by (force intro!: typing_typing_all.intros simp add: zip_map2)
next
  case tyinf_app then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_to_context_split kinding_kinding_allI
        dest: tyinf_context_lengths
        simp add: sharable_constraint_plus_iff)
next
  case tyinf_split then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_to_context_split kinding_kinding_allI
        dest: tyinf_context_lengths
        simp add: sharable_constraint_plus_iff one_linearity_def)
      (* slow: ~3s *)
next
  case tyinf_let then show ?case
    by (fastforce
        intro!: typing_typing_all.intros tycount_to_context_split kinding_kinding_allI
        dest: tyinf_context_lengths
        simp add: sharable_constraint_plus_iff one_linearity_def)
      (* slow: ~3s *)
next
  case (tyinf_letb \<Xi> K \<Gamma> C1 x t ct C2 y u "is")
  then show ?case
    sorry
next
  case (tyinf_case \<Xi> K \<Gamma> C1 x \<tau>1 ts tag t C2ao a u c2a C2a C2bo b c2b C2b)
  moreover then have "length C2a = length \<Gamma>" "length C2b = length \<Gamma>" "length C1 = length \<Gamma>"
    by (force dest!: tyinf_context_lengths)+
  ultimately show ?case
    apply (clarsimp simp add: sharable_constraint_plus_iff sharable_constraint_max_iff)
    apply (safe intro!: typing_typing_all.intros)
        apply (force intro!: tycount_to_context_split simp add: sharable_constraint_plus_iff sharable_constraint_max_iff)
       apply blast
      apply blast

    sorry
next
  case (tyinf_if \<Xi> K \<Gamma> C1 x \<tau> C2a a t C2b b)
  then show ?case sorry
next
  case (tyinf_take \<Xi> K \<Gamma> C1 e \<tau>1 ts s f n t taken C2o e' u ct cr C2)
  then show ?case sorry
next
  case (tyinf_switch \<Xi> K \<Gamma> C x \<tau> \<tau>')
  then show ?case sorry
next
  case (tyinf_promote \<Xi> K \<Gamma> C x t' t)
  then show ?case sorry
next
  case (tyinf_all_empty \<Xi> K \<Gamma>)
  then show ?case sorry
next
  case (tyinf_all_cons \<Xi> K \<Gamma> C1 e t C2 es ts)
  then show ?case sorry
qed (fastforce intro!: typing_typing_all.intros)+

end
