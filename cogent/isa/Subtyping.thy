theory Subtyping
  imports Cogent
begin

text \<open>
  This file covers the interpretation of the subtyping relation as a lattice. This is how the
  compiler computes subtyping (as of late 2018), and these proofs give assurance we've formalised
  the correct relation.
\<close>

inductive type_lub :: "kind env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<leftarrow> _ \<squnion> _" [60,0,0,60] 60)
  and type_glb :: "kind env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ \<leftarrow> _ \<sqinter> _" [60,0,0,60] 60)
  where
  lub_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVar n \<leftarrow> TVar n1 \<squnion> TVar n2"
| lub_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<squnion> TVarBang n2"
| lub_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<squnion> TCon n2 ts2 s2"
| lub_tfun   : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; K \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<squnion> TFun t2 u2"
| lub_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TPrim p \<leftarrow> TPrim p1 \<squnion> TPrim p2"
| lub_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          (if (K \<turnstile> fst (snd p1) :\<kappa> {D})
                                          then b1 \<le> b
                                          else b1 = b) \<and>
                                          (if (K \<turnstile> fst (snd p2) :\<kappa> {D})
                                          then b2 \<le> b
                                          else b2 = b)) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
| lub_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; K \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<squnion> TProduct t2 u2"
| lub_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = sup (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
| lub_tunit  : "K \<turnstile> TUnit \<leftarrow> TUnit \<squnion> TUnit"

| glb_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVar n \<leftarrow> TVar n1 \<sqinter> TVar n2"
| glb_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<sqinter> TVarBang n2"
| glb_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<sqinter> TCon n2 ts2 s2"
| glb_tfun   : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; K \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<sqinter> TFun t2 u2"
| glb_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> K \<turnstile> TPrim p \<leftarrow> TPrim p1 \<sqinter> TPrim p2"
| glb_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          (if (K \<turnstile> fst (snd p) :\<kappa> {D})
                                          then b \<le> b1 \<and> b \<le> b2
                                          else b = b2 \<and> b1 = b2)) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
| glb_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; K \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<sqinter> TProduct t2 u2"
| glb_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = inf (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; distinct (map fst ts)
                \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
| glb_tunit  : "K \<turnstile> TUnit \<leftarrow> TUnit \<sqinter> TUnit"

(*
(* This should not be true *)
lemma test5:
"\<And>i. i < length ts \<Longrightarrow> {D} \<subseteq> kinding_fn K (TSum ts) \<Longrightarrow> {D} \<subseteq> kinding_fn K (fst (snd (ts ! i)))"
  apply (drule_tac xs=ts and P="\<lambda>x. D \<in> (case x of (uu_, t, Checked) \<Rightarrow> UNIV | (uu_, t, Unchecked) \<Rightarrow> kinding_fn K t)" in  List.list_ball_nth)
   apply simp
  apply simp
  apply (subgoal_tac "\<exists>a b c. ts ! i = (a, b, c)")
   apply (erule exE)+
   apply simp
   apply (case_tac "c = Unchecked")
    apply simp
   apply (subgoal_tac "c = Checked")
    apply simp

  sorry

(* This should not be true *)
lemma test:
"K \<turnstile> TSum ts :\<kappa> {D} \<Longrightarrow> \<forall>i < length ts. K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}"
  apply (rule allI)
  apply (rule impI)
  apply (unfold kinding_def)
  apply (rule conjI)
  using test2 apply auto[1]
  apply (erule conjE) 
  apply simp thm List.list_ball_nth
  apply (drule_tac xs=ts and P="\<lambda>x. D \<in> (case x of (uu_, t, Checked) \<Rightarrow> UNIV | (uu_, t, Unchecked) \<Rightarrow> kinding_fn K t)" in  List.list_ball_nth)
   apply simp
  
  sorry
*)

value "sup Taken Present"
value "sup Checked Unchecked"
lemma type_lub_type_glb_idem:
  assumes "K \<turnstile> t wellformed"
  shows
    "K \<turnstile> t \<leftarrow> t \<squnion> t"
    "K \<turnstile> t \<leftarrow> t \<sqinter> t"
  using assms
proof (induct t)
  case (TSum ts)
  moreover assume ts_wellformed: "K \<turnstile> TSum ts wellformed"
  ultimately show
    "K \<turnstile> TSum ts \<leftarrow> TSum ts \<squnion> TSum ts"
    "K \<turnstile> TSum ts \<leftarrow> TSum ts \<sqinter> TSum ts"
    by (fastforce simp add: list_all3_same list_all_iff intro!: type_lub_type_glb.intros)+
next
  case (TRecord ts s)
  moreover assume ts_wellformed: "K \<turnstile> TRecord ts s wellformed"
  ultimately show
  "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
  "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
     apply -
     apply (rule_tac lub_trecord)
           apply (metis (no_types, lifting) fsts.intros wellformed_record_wellformed_elem list_all3_same snds.intros surjective_pairing)
          apply (simp add: list_all3_same)
         apply (simp+)[5]
    apply (rule_tac glb_trecord)
          apply (metis (no_types, lifting) fsts.intros wellformed_record_wellformed_elem list_all3_same snds.intros surjective_pairing)
         apply (simp add: list_all3_same)
        apply (simp+)[5]
    done
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_commut:
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<squnion> a"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<sqinter> a"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
    apply (intro type_lub_type_glb.intros)
          apply (clarsimp simp add: list_all3_conv_all_nth)
         apply (clarsimp simp add: list_all3_conv_all_nth, metis)
        apply (simp+)[5]
    done
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
    by (simp add: list_all3_conv_all_nth sup_commute type_lub_type_glb.lub_tsum)
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
    apply (intro type_lub_type_glb.intros)
          apply (clarsimp simp add: list_all3_conv_all_nth)
         apply (clarsimp simp add: list_all3_conv_all_nth, metis)
        apply (simp+)[5]
    done
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
    by (simp add: inf_sup_aci(1) list_all3_conv_all_nth type_lub_type_glb.glb_tsum)
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_wellformed:
  assumes
    "K \<turnstile> t1 wellformed"
    "K \<turnstile> t2 wellformed"
  shows
    "K \<turnstile> t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> K \<turnstile> t wellformed"
    "K \<turnstile> t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> K \<turnstile> t wellformed"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
qed (auto simp add: list_all_length list_all3_conv_all_nth)

(*
TODO: not used atm, but might be useful

lemma type_glb_drop_produce_drop:
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D} \<Longrightarrow> K \<turnstile> a :\<kappa> {D} \<and> K \<turnstile> b :\<kappa> {D}"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a :\<kappa> {D} \<Longrightarrow> K \<turnstile> b :\<kappa> {D} \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tvar n n1 n2 K)
  then show ?case sorry
next
  case (lub_tvarb n n1 n2 K)
  then show ?case sorry
next
  case (lub_tcon n n1 n2 s s1 s2 ts ts1 ts2 K)
  then show ?case sorry
next
  case (lub_tfun K t t1 t2 u u1 u2)
  then show ?case sorry
next
  case (lub_tprim p p1 p2 K)
  then show ?case sorry
next
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case sorry
next
  case (lub_tprod K t t1 t2 u u1 u2)
  then show ?case sorry
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case sorry
next
  case (lub_tunit K)
  then show ?case sorry
next
  case (glb_tcon n n1 n2 s s1 s2 ts ts1 ts2 K)
  then show ?case
    by (clarsimp simp add: list_all3_conv_all_nth kinding_simps)
next
  case (glb_tfun K t t1 t2 u u1 u2)
  then show ?case
    by (meson kinding_simps type_lub_type_glb_wellformed)
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
    apply (clarsimp simp add: list_all3_conv_all_nth kinding_simps kinding_record_conv_all_nth)
    apply (drule_tac x=i in spec, clarsimp)+
    apply (case_tac "snd (snd (ts ! i))"; case_tac "snd (snd (ts1 ! i))"; case_tac "snd (snd (ts2 ! i))"; clarsimp)
    using type_lub_type_glb_wellformed(2) type_wellformed_pretty_def apply blast
        apply (meson less_eq_record_state.simps(3) record_state.distinct(1))
       apply (meson less_eq_record_state.simps(3) record_state.simps(2))
      apply (meson record_state.simps(2))
     apply (meson record_state.distinct(1))
    by (meson record_state.simps(2))
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
    apply (clarsimp simp add: list_all3_conv_all_nth kinding_simps kinding_variant_conv_all_nth)
    apply (case_tac "inf (snd (snd (ts1 ! i))) (snd (snd (ts2 ! i)))")
     apply clarsimp
     apply (metis glb_tsum.prems(1) glb_tsum.prems(2) kinding_simps(6) kinding_variant_wellformed_elem nth_mem prod.collapse type_lub_type_glb_wellformed(2) type_wellformed_pretty_def)
    apply clarsimp
    by (smt inf.orderE inf_bot_right less_eq_variant_state.elims(3) variant_state.simps(4))
qed (auto simp add: kinding_simps)
*)


lemma type_lub_type_glb_absorb:
  shows
    "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> a \<leftarrow> a \<sqinter> c"
    "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a \<leftarrow> a \<squnion> c"
proof (induct rule: type_lub_type_glb.inducts)
qed (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth Let_def)+

lemma type_lub_type_glb_order_correct: "K \<turnstile> a \<leftarrow> a \<squnion> b \<longleftrightarrow> K \<turnstile> b \<leftarrow> a \<sqinter> b"
  by (auto intro: type_lub_type_glb_absorb type_lub_type_glb_commut)

lemma glb_lub_subtyping_order_correct:
  shows
    "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> (K \<turnstile> a \<sqsubseteq> c) \<and> (K \<turnstile> b \<sqsubseteq> c)"
    "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> (K \<turnstile> c \<sqsubseteq> a) \<and> (K \<turnstile> c \<sqsubseteq> b)"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case 
  proof -
    have "K \<turnstile> TRecord ts1 s1 \<sqsubseteq> TRecord ts s"
      using lub_trecord.hyps list_all3_conv_all_nth list_all2_conv_all_nth
      by (metis (mono_tags, lifting) subtyping_simps(6))
    moreover have "K \<turnstile> TRecord ts2 s2 \<sqsubseteq> TRecord ts s"
      using lub_trecord.hyps list_all3_conv_all_nth list_all2_conv_all_nth
      by (metis (mono_tags, lifting) subtyping_simps(6))
    ultimately show ?thesis
      by simp
  qed 
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof -
    have "K \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts1 s1"
      using glb_trecord.hyps subtyping_simps(6)
      apply (clarsimp simp add: list_all3_conv_all_nth list_all2_conv_all_nth)
      by metis
    moreover have "K \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts2 s2"
      using glb_trecord.hyps subtyping_simps(6)
      apply (clarsimp simp add: list_all3_conv_all_nth list_all2_conv_all_nth)
      by metis
    ultimately show ?thesis
      by simp
  qed
qed (auto simp add: subtyping_simps list_all3_conv_all_nth list_all2_conv_all_nth)


lemma type_lub_type_glb_to_subtyping:
  shows
    "K \<turnstile> a \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> a \<sqsubseteq> b"
    "K \<turnstile> b \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a \<sqsubseteq> b"
  using glb_lub_subtyping_order_correct
  by fast+

(* this would be nice:
theorem type_glb_type_lub_subtyping_equivalent:
  shows
    "a \<leftarrow> a \<squnion> b \<longleftrightarrow> a \<sqsubseteq> b"
    "b \<leftarrow> a \<sqinter> b \<longleftrightarrow> a \<sqsubseteq> b"
  sorry
*)

end