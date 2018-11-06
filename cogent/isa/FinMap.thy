theory FinMap
  imports Main
begin

section {* Finite Maps *}

typedef ('i,'a) finmap = "{ m :: 'i \<rightharpoonup> 'a. finite (ran m) }"
  morphisms get_finmap Abs_finmap
  by (clarsimp intro!: exI[where x="Map.empty"])

setup_lifting type_definition_finmap

subsection {* Definitions *}

lift_definition empty_finmap :: "('i,'a) finmap" is "Map.empty"
  by simp

lift_definition dom_finmap :: "('i,'a) finmap \<Rightarrow> 'i set" is "dom" .
lift_definition ran_finmap :: "('i,'a) finmap \<Rightarrow> 'a set" is "ran" .

lift_definition map_finmap :: "('a \<Rightarrow> 'b) \<Rightarrow> ('i,'a) finmap \<Rightarrow> ('i,'b) finmap" is "\<lambda>f m i. map_option f (m i)"
  by (simp add: ran_map_option)

lift_definition upd_finmap :: "('i,'a) finmap \<Rightarrow> 'i \<Rightarrow> 'a  \<Rightarrow> ('i,'a) finmap" is "\<lambda>m x y. m(x \<mapsto> y)"
proof -
  fix "m" :: "'i \<Rightarrow> 'a option" and i :: 'i and a :: 'a
  assume "finite (ran m)"
  moreover have "ran (m(i \<mapsto> a)) \<subseteq> insert a (ran m)"
  proof (cases "m i")
    case (Some a)
    then show ?thesis
      by (metis fun_upd_same fun_upd_triv fun_upd_upd insert_mono ran_map_upd subset_insertI)
  qed simp
  ultimately show "finite (ran (m(i \<mapsto> a)))"
    by (simp add: finite_subset)
qed

definition rel_finmap :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('i,'a) finmap \<Rightarrow> ('i,'b) finmap \<Rightarrow> bool" where
  "rel_finmap P ma mb \<equiv> dom_finmap ma = dom_finmap mb \<and> (\<forall>i\<in>dom_finmap ma. \<exists>a b. get_finmap ma i = Some a \<and> get_finmap mb i = Some b \<and> P a b)"

definition pred_finmap :: "('a \<Rightarrow> bool) \<Rightarrow> ('i,'a) finmap \<Rightarrow> bool" where
  "pred_finmap P ma \<equiv> \<forall>i \<in> dom_finmap ma. \<exists>a. get_finmap ma i = Some a \<and> P a"

lift_definition int_finmap :: "('i,'a) finmap \<Rightarrow> ('i,'b) finmap \<Rightarrow> ('i, 'a \<times> 'b) finmap"
  is "(\<lambda>ma mb i. Option.bind (ma i) (\<lambda>a. map_option (\<lambda>b. (a, b)) (mb i)))"
  unfolding ran_def
proof (clarsimp simp add: bind_eq_Some_conv)
  fix ma :: "'i \<rightharpoonup> 'a" and mb :: "'i \<rightharpoonup> 'b"
  assume
    "finite {a. \<exists>i. ma i = Some a}"
    "finite {b. \<exists>i. mb i = Some b}"
  moreover have "{b. \<exists>a y. ma a = Some y \<and> (\<exists>z. mb a = Some z \<and> (y, z) = b)} = {(y, z) | i y z. ma i = Some y \<and> mb i = Some z}"
    by auto
  moreover have "{(y, z) | i y z. ma i = Some y \<and> mb i = Some z} \<subseteq> {a. \<exists>i. ma i = Some a} \<times> {b. \<exists>i. mb i = Some b}"
    by blast
  ultimately show "finite {b. \<exists>a y. ma a = Some y \<and> (\<exists>z. mb a = Some z \<and> (y, z) = b)}"
    using finite_subset by fastforce
qed

lift_definition un_finmap :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('i,'a) finmap \<Rightarrow> ('i,'a) finmap \<Rightarrow> ('i,'a) finmap"
  is "(\<lambda>f ma mb i. case ma i of
                      Some a \<Rightarrow> case mb i of
                          Some b \<Rightarrow> Some (f a b)
                        | None \<Rightarrow> Some a
                    | None \<Rightarrow> mb i)"
  unfolding ran_def
proof -
  fix f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and ma mb :: "'i \<rightharpoonup> 'a"
  assume assms:
    "finite {a. \<exists>i. ma i = Some a}"
    "finite {b. \<exists>i. mb i = Some b}"
  have
    "{c. \<exists>i. ma i = Some c \<and> mb i = None} \<subseteq> {a. \<exists>i. ma i = Some a}"
    "{c. \<exists>i. ma i = None \<and> mb i = Some c} \<subseteq> {b. \<exists>i. mb i = Some b}"
    "{c. \<exists>i a. ma i = Some a \<and> (\<exists>b. mb i = Some b \<and> c = f a b)} = case_prod f ` {(a,b). \<exists>i. ma i = Some a \<and> mb i = Some b}"
    "{(a,b). \<exists>i. ma i = Some a \<and> mb i = Some b} \<subseteq> {a. \<exists>i. ma i = Some a} \<times> {b. \<exists>i. mb i = Some b}"
    by auto
  then have
    "finite {c. \<exists>i. ma i = Some c \<and> mb i = None}"
    "finite {c. \<exists>i. ma i = None \<and> mb i = Some c}"
    "finite {c. \<exists>i a. ma i = Some a \<and> (\<exists>b. mb i = Some b \<and> c = f a b)}"
    using assms
    by (auto simp add: finite_subset)+
  moreover have "{c. \<exists>i. (case ma i of None \<Rightarrow> mb i | Some a \<Rightarrow> (case mb i of None \<Rightarrow> Some a | Some b \<Rightarrow> Some (f a b))) = Some c} =
        {c. \<exists>i. (\<exists>a.   ma i = Some a \<and> mb i = None   \<and> c = a) \<or>
                (\<exists>b.   ma i = None   \<and> mb i = Some b \<and> c = b) \<or>
                (\<exists>a b. ma i = Some a \<and> mb i = Some b \<and> c = f a b)}"
    by (intro Collect_cong iff_exI, case_tac "ma i"; case_tac "mb i"; force)
  ultimately show "finite {c. \<exists>i. (case ma i of None \<Rightarrow> mb i | Some a \<Rightarrow> case mb i of None \<Rightarrow> Some a | Some b \<Rightarrow> Some (f a b)) = Some c}"
    by (simp add: ex_disj_distrib)
qed

lift_definition finmap_le :: "('i,'a) finmap \<Rightarrow> ('i,'a) finmap \<Rightarrow> bool" is "(\<subseteq>\<^sub>m)" .

subsection {* BNF *}

bnf "('i,'a) finmap"
  map: map_finmap
  sets: ran_finmap
  bd: natLeq
  wits: empty_finmap
  rel: rel_finmap
  pred: pred_finmap
proof -
  fix x
  show "ordLeq3 (card_of (ran_finmap x)) natLeq"
    by transfer (metis ordLess_imp_ordLeq finite_iff_ordLess_natLeq)
next
  fix R S
  show "rel_finmap R OO rel_finmap S \<le> rel_finmap (R OO S)"
    unfolding rel_finmap_def OO_def
    by (clarsimp, transfer, metis option.sel)
next
  fix R
  show "rel_finmap R = (\<lambda>x y. \<exists>z. ran_finmap z \<subseteq> {(x, y). R x y} \<and> map_finmap fst z = x \<and> map_finmap snd z = y)"
    unfolding rel_finmap_def
    apply (intro ext iffI)
    apply (rule_tac x="int_finmap ma mb" in exI)
     apply transfer
     apply (intro conjI ext)
       apply (force simp add: ran_def bind_eq_Some_conv)
      apply (case_tac "ma i"; force)
     apply (case_tac "mb i"; force)
    apply transfer
    apply (force simp add: ran_def dom_def)
    done
next
  fix P
  show "pred_finmap P = (\<lambda>x. Ball (ran_finmap x) P)"
    unfolding pred_finmap_def
    by transfer' (fastforce simp add: ran_def dom_def)
qed ((simp add: natLeq_card_order natLeq_cinfinite) |
    (transfer', fastforce simp add: map_option.id map_option.compositionality ran_map_option
      intro!: ranI option.map_cong0))+

lemma finmap_cong:
  assumes
    "dom_finmap ma = dom_finmap mb"
    "\<And>i. i \<in> dom_finmap ma \<Longrightarrow> get_finmap ma i = get_finmap mb i"
  shows
    "ma = mb"
  using assms
  by (transfer, simp add: map_le_antisym map_le_def)

end