theory Subtyping
  imports
    Cogent
    ValueSemantics
begin

text \<open>
  This file covers the interpretation of the subtyping relation as a lattice. This is how the
  compiler computes subtyping (as of late 2018), and these proofs give assurance we've formalised
  the correct relation.
\<close>

section \<open>Subtyping As An Order and As A Lattice\<close>

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
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
| lub_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; K \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<squnion> TProduct t2 u2"
| lub_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = sup (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
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
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
| glb_tprod  : "\<lbrakk> K \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; K \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<sqinter> TProduct t2 u2"
| glb_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (K \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = inf (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                \<rbrakk> \<Longrightarrow> K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
| glb_tunit  : "K \<turnstile> TUnit \<leftarrow> TUnit \<sqinter> TUnit"


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
  proof -
    have tWellformed: "\<And>i. i < length ts \<Longrightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed"
      by (metis nth_mem prod.collapse ts_wellformed wellformed_record_wellformed_elem)
    show "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
    proof (rule_tac lub_trecord)
      show "list_all3 (\<lambda>p p1 p2. K \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<squnion> fst (snd p2)) ts ts ts"
        using TRecord.hyps
        by (metis (no_types, lifting) fsts.intros in_set_conv_nth list_all3_same snds.intros tWellformed)
    qed (simp add: list_all3_same)+
    show "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
    proof (rule_tac glb_trecord)
      show "list_all3 (\<lambda>p p1 p2. K \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<sqinter> fst (snd p2)) ts ts ts"
        using TRecord.hyps
        by (metis (no_types, lifting) fsts.intros in_set_conv_nth list_all3_same snds.intros tWellformed)
    qed (simp add: list_all3_same)+
  qed
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_commut:
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<squnion> a"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c \<leftarrow> b \<sqinter> a"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.lub_trecord)
    show "list_all3 (\<lambda>p p1 p2. K \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<squnion> fst (snd p2)) ts ts2 ts1"
      using list_all3_comm2 list_all3_mono lub_trecord.hyps by fastforce
    show "list_all3 (\<lambda>p p1 p2. let b = snd (snd p); b1 = snd (snd p1); b2 = snd (snd p2) in 
          (if K \<turnstile> fst (snd p1) :\<kappa> {D} then b1 \<le> b else b1 = b) \<and> 
          (if K \<turnstile> fst (snd p2) :\<kappa> {D} then b2 \<le> b else b2 = b)) ts ts2 ts1"
      using lub_trecord.hyps
      by (clarsimp simp add: list_all3_conv_all_nth, meson)
  qed (simp)+
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
    by (simp add: list_all3_conv_all_nth sup_commute type_lub_type_glb.lub_tsum)
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.glb_trecord)
    show "list_all3 (\<lambda>p p1 p2. K \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<sqinter> fst (snd p2)) ts ts2 ts1"
      using glb_trecord.hyps list_all3_comm2 list_all3_mono by fastforce
    show "list_all3 (\<lambda>p p1 p2.  let b = snd (snd p); b1 = snd (snd p1); b2 = snd (snd p2) in 
          if K \<turnstile> fst (snd p) :\<kappa> {D} then b \<le> b1 \<and> b \<le> b2 
          else b = b2 \<and> b1 = b2) ts ts2 ts1"
      using glb_trecord.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      by metis
  qed (simp)+
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

lemma type_lub_type_glb_wellformed_produce_wellformed:
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c wellformed \<Longrightarrow> (K \<turnstile> a wellformed) \<and> (K \<turnstile> b wellformed)"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> c wellformed \<Longrightarrow> (K \<turnstile> a wellformed) \<and> (K \<turnstile> b wellformed)"
proof (induct rule: type_lub_type_glb.inducts)                
qed (auto simp add: list_all3_conv_all_nth list_all_length)

lemma type_glb_drop_produce_drop:
  shows
  "K \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> c :\<kappa> {D} \<Longrightarrow> K \<turnstile> a :\<kappa> {D} \<and> K \<turnstile> b :\<kappa> {D}"
  "K \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> a :\<kappa> {D} \<Longrightarrow> K \<turnstile> b :\<kappa> {D} \<Longrightarrow> K \<turnstile> c :\<kappa> {D}"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tfun K t t1 t2 u u1 u2)
  then show ?case
    using kinding_simps(4) type_lub_type_glb_wellformed_produce_wellformed by auto
next
  case (lub_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof -
    have "K \<turnstile> TRecord ts s wellformed"
      using kinding_def lub_trecord.prems by blast
    then have ts1ts2Wellformed:
      "K \<turnstile> TRecord ts1 s wellformed"
      "K \<turnstile> TRecord ts2 s wellformed"
      using lub_trecord.hyps type_lub_type_glb_wellformed_produce_wellformed
      by (metis (mono_tags, lifting) list_all3_conv_all_nth list_all_length type_wellformed.simps(8) type_wellformed_pretty_def)+
    have "K \<turnstile> TRecord ts1 s1 :\<kappa> {D}"
      using lub_trecord
    proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts1"
      let ?t1 = "fst (snd (ts1 ! i))"
      let ?b1 = "snd (snd (ts1 ! i))"
      show "case ?b1 of Taken \<Rightarrow> K \<turnstile> ?t1 wellformed | Present \<Rightarrow> K \<turnstile> ?t1 :\<kappa> {D}"
      proof (cases ?b1)
        case Taken
        moreover have "length ts = length ts1"
          using lub_trecord.hyps
          by (metis length_map)
        ultimately show ?thesis
          using  ts1ts2Wellformed tsLength
          by (auto simp add: list_all_length)
      next
        case Present
        then show ?thesis
          using lub_trecord.hyps lub_trecord.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_record_conv_all_nth
              split: record_state.splits)
          apply metis
          done
      qed
    qed
    moreover have "K \<turnstile> TRecord ts2 s2 :\<kappa> {D}"
      using lub_trecord
    proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts2"
      let ?t2 = "fst (snd (ts2 ! i))"
      let ?b2 = "snd (snd (ts2 ! i))"
      show "case ?b2 of Taken \<Rightarrow> K \<turnstile> ?t2 wellformed | Present \<Rightarrow> K \<turnstile> ?t2 :\<kappa> {D}"
      proof (cases ?b2)
        case Taken
        moreover have "length ts = length ts2"
          using lub_trecord.hyps
          by (metis length_map)
        ultimately show ?thesis
          using  ts1ts2Wellformed tsLength
          by (auto simp add: list_all_length)
      next
        case Present
        then show ?thesis
          using lub_trecord.hyps lub_trecord.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_record_conv_all_nth
              split: record_state.splits)
          apply metis
          done
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
  proof -
    have "K \<turnstile> TSum ts wellformed"
      using kinding_def lub_tsum.prems by blast
    then have ts1ts2Wellformed:
      "K \<turnstile> TSum ts1 wellformed"
      "K \<turnstile> TSum ts2 wellformed"
      using lub_tsum.hyps type_lub_type_glb_wellformed_produce_wellformed
      by (metis (mono_tags, lifting) list_all3_conv_all_nth list_all_length 
                type_wellformed.simps(6) type_wellformed_pretty_def)+
    have "K \<turnstile> TSum ts1 :\<kappa> {D}"
      using lub_tsum
    proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts1"
      let ?t1 = "fst (snd (ts1 ! i))"
      let ?b1 = "snd (snd (ts1 ! i))"
      show "case ?b1 of Checked \<Rightarrow> K \<turnstile> ?t1 wellformed | Unchecked \<Rightarrow> K \<turnstile> ?t1 :\<kappa> {D}"
      proof (cases ?b1)
        case Checked
        moreover have "length ts = length ts1"
          using lub_tsum.hyps
          by (metis length_map)
        ultimately show ?thesis
          using  ts1ts2Wellformed tsLength
          by (auto simp add: list_all_length)
      next
        case Unchecked
        then show ?thesis
          using lub_tsum.hyps lub_tsum.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_variant_conv_all_nth
              split: variant_state.splits)
          done
      qed
    qed
    moreover have "K \<turnstile> TSum ts2 :\<kappa> {D}"
      using lub_tsum
    proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts2"
      let ?t2 = "fst (snd (ts2 ! i))"
      let ?b2 = "snd (snd (ts2 ! i))"
      show "case ?b2 of Checked \<Rightarrow> K \<turnstile> ?t2 wellformed | Unchecked \<Rightarrow> K \<turnstile> ?t2 :\<kappa> {D}"
      proof (cases ?b2)
        case Checked
        moreover have "length ts = length ts2"
          using lub_tsum.hyps
          by (metis length_map)
        ultimately show ?thesis
          using  ts1ts2Wellformed tsLength
          by (auto simp add: list_all_length)
      next
        case Unchecked
        then show ?thesis
          using lub_tsum.hyps lub_tsum.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_variant_conv_all_nth sup_commute
              split: variant_state.splits)
          done
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
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
    using glb_trecord
  proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps)
    have 
      "(K \<turnstile> TRecord ts1 s1 wellformed)" 
      "(K \<turnstile> TRecord ts2 s2 wellformed)"
      using glb_trecord.prems kinding_to_wellformedD(1) by blast+
    then have tsWellformed: "K \<turnstile> TRecord ts s wellformed"
      using glb_trecord.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      using type_lub_type_glb_wellformed
      by (metis (no_types, lifting) list_all_length type_wellformed_pretty_def)
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      let ?t = "fst (snd (ts ! i))"
      let ?b = "snd (snd (ts ! i))"
      show "case ?b of Taken \<Rightarrow> K \<turnstile> ?t wellformed | Present \<Rightarrow> K \<turnstile> ?t :\<kappa> {D}"
      proof (cases ?b)
        case Taken
        then show ?thesis
          using tsWellformed tsLength
          apply (simp add: list_all_length)
          done
      next
        case Present
        then show ?thesis
          using glb_trecord.hyps glb_trecord.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_record_conv_all_nth sup_commute
              split: record_state.splits)
          apply metis
          done
      qed
    }
  qed
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
   using glb_tsum
  proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
    have 
      "(K \<turnstile> TSum ts1 wellformed)" 
      "(K \<turnstile> TSum ts2 wellformed)"
      using glb_tsum.prems kinding_to_wellformedD(1) by blast+
    then have tsWellformed: "K \<turnstile> TSum ts wellformed"
      using glb_tsum.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      using type_lub_type_glb_wellformed
      by (metis (no_types, lifting) list_all_length type_wellformed_pretty_def)
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      let ?t = "fst (snd (ts ! i))"
      let ?b = "snd (snd (ts ! i))"
      show "case ?b of Checked \<Rightarrow> K \<turnstile> ?t wellformed | Unchecked \<Rightarrow> K \<turnstile> ?t :\<kappa> {D}"
      proof (cases ?b)
        case Checked
        then show ?thesis
          using tsWellformed tsLength
          apply (simp add: list_all_length)
          done
      next
        case Unchecked
        then show ?thesis
          using glb_tsum.hyps glb_tsum.prems tsLength
          apply (clarsimp
              simp add: kinding_simps list_all3_conv_all_nth kinding_variant_conv_all_nth
              split: variant_state.splits)
          apply (blast elim: inf_variant_state.elims)
          done
      qed
    }
  qed
qed (auto simp add: kinding_simps)

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
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. K \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts1 ts"
        using lub_trecord.hyps 
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty K) ts1 ts"
        using lub_trecord.hyps le_neq_trans
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by fastforce
    qed (simp add: lub_trecord.hyps)+
    moreover have "K \<turnstile> TRecord ts2 s2 \<sqsubseteq> TRecord ts s"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. K \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts2 ts"
        using lub_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty K) ts2 ts"
        using lub_trecord.hyps le_neq_trans
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by fastforce
    qed (simp add: lub_trecord.hyps)+
    ultimately show ?thesis
      by simp
  qed
next
  case (glb_trecord K ts ts1 ts2 s s1 s2)
  then show ?case
  proof -
    have "K \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts1 s1"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. K \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts1"
        using glb_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty K) ts ts1"
        using glb_trecord.hyps
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by (metis (no_types) le_less)
    qed (simp add: glb_trecord.hyps)+
    moreover have "K \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts2 s2"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. K \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts2"
        using glb_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty K) ts ts2"
        using glb_trecord.hyps
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by (meson le_less)
    qed (simp add: glb_trecord.hyps)+
    ultimately show ?thesis
      by simp
  qed
qed (auto simp add: subtyping_simps list_all3_conv_all_nth list_all2_conv_all_nth)

lemma type_lub_type_glb_to_subtyping:
  shows
    "K \<turnstile> a \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> b \<sqsubseteq> a"
    "K \<turnstile> b \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> b \<sqsubseteq> a"
  using glb_lub_subtyping_order_correct
  by fast+

lemma subtyping_to_type_lub:
  shows
    "K \<turnstile> b \<sqsubseteq> a \<Longrightarrow> K \<turnstile> a \<leftarrow> a \<squnion> b"
proof (induct rule: subtyping.inducts)
  case (subty_tfun K t2 t1 u1 u2)
  then show ?case
    by (simp add: glb_tfun type_lub_type_glb_commut(1) type_lub_type_glb_order_correct)
next
  case (subty_trecord K ts1 ts2 s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.lub_trecord)  
  qed (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth, auto)+
next
  case (subty_tsum K ts1 ts2)
  then show ?case
    by (simp add: list_all2_conv_all_nth list_all3_conv_all_nth lub_tsum sup.absorb_iff1)
qed (auto intro: type_lub_type_glb.intros)

lemma subtyping_to_type_glb:
  shows
    "K \<turnstile> b \<sqsubseteq> a \<Longrightarrow> K \<turnstile> b \<leftarrow> a \<sqinter> b"
proof (induct rule: subtyping.induct)
case (subty_tfun K t2 t1 u1 u2)
  then show ?case 
    by (simp add: subty_tfun.hyps(2) glb_tfun subtyping_to_type_lub type_lub_type_glb_commut(2))
next
  case (subty_trecord K ts1 ts2 s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.glb_trecord)
  qed (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth, auto)+
next
  case (subty_tsum K ts1 ts2)
  then show ?case
    by (simp add: glb_tsum inf.absorb2 list_all2_conv_all_nth list_all3_conv_all_nth)
qed (auto intro: type_lub_type_glb.intros)

theorem type_glb_type_lub_subtyping_equivalent:
  shows
    "K \<turnstile> a \<leftarrow> a \<squnion> b \<longleftrightarrow> K \<turnstile> b \<sqsubseteq> a"
    "K \<turnstile> b \<leftarrow> a \<sqinter> b \<longleftrightarrow> K \<turnstile> b \<sqsubseteq> a"
  using subtyping_to_type_lub type_lub_type_glb_to_subtyping subtyping_to_type_glb by blast+

lemmas weakening_append1 = list_all2_append1[where P="weakening_comp K" for K, simplified weakening_def[symmetric]]
lemmas weakening_append2 = list_all2_append2[where P="weakening_comp K" for K, simplified weakening_def[symmetric]]

lemma take_empty:
  assumes \<open>m < n\<close>
  shows \<open>take m (empty n) = empty m\<close>
  unfolding empty_def
  using assms by auto

lemma drop_empty:
  assumes \<open>m < n\<close>
  shows \<open>drop m (empty n) = empty (n - m)\<close>
  unfolding empty_def
  using assms by auto

lemma weaken_to_singleton_split:
  assumes
    \<open>i < length \<Gamma>\<close>
  shows
    \<open>(K \<turnstile> \<Gamma> \<leadsto>w (singleton (length \<Gamma>) i t))
     \<longleftrightarrow>
     (\<exists>\<Gamma>a \<Gamma>b.
       \<Gamma> = \<Gamma>a @ [\<Gamma> ! i] @ \<Gamma>b \<and>
       (K \<turnstile> \<Gamma>a \<leadsto>w empty i) \<and>
       weakening_comp K (\<Gamma> ! i) (Some t) \<and>
       (K \<turnstile> \<Gamma>b \<leadsto>w empty (length \<Gamma> - Suc i)))\<close>
  using assms
  apply (clarsimp simp add:
      singleton_def upd_conv_take_nth_drop empty_length
      weakening_append2 weakening_Cons2 min_absorb2 take_empty drop_empty)
  apply safe
   apply (metis Cogent.empty_def drop_replicate nth_append_length)
  apply (metis (mono_tags, lifting) Cogent.empty_def drop_replicate empty_length length_Cons weakening_length)
  done

section \<open>Subtyping and Value Semantics\<close>

fun strip_promote :: \<open>'f expr \<Rightarrow> 'f expr\<close> where
  \<open>strip_promote (Var i) = (Var i)\<close>
| \<open>strip_promote (AFun n ts) = (AFun n ts)\<close>
| \<open>strip_promote (Fun e ts) = (Fun (strip_promote e) ts)\<close>
| \<open>strip_promote (Prim p es) = (Prim p (map strip_promote es))\<close>
| \<open>strip_promote (App ef ea) = (App (strip_promote ef) (strip_promote ea))\<close>
| \<open>strip_promote (Con vs n e) = (Con vs n (strip_promote e))\<close>
| \<open>strip_promote (Struct fs es) = (Struct fs (map strip_promote es))\<close>
| \<open>strip_promote (Member e n) = (Member (strip_promote e) n)\<close>
| \<open>strip_promote Unit = Unit\<close>
| \<open>strip_promote (Lit l) = Lit l\<close>
| \<open>strip_promote (SLit s) = SLit s\<close>
| \<open>strip_promote (Cast m e) = (Cast m (strip_promote e))\<close>
| \<open>strip_promote (Tuple ea eb) = (Tuple (strip_promote ea) (strip_promote eb))\<close>
| \<open>strip_promote (Put er n ec) = (Put (strip_promote er) n (strip_promote ec))\<close>
| \<open>strip_promote (Let ea ec) = (Let (strip_promote ea) (strip_promote ec))\<close>
| \<open>strip_promote (LetBang is ea ec) = (LetBang is (strip_promote ea) (strip_promote ec))\<close>
| \<open>strip_promote (Case ev n ecm ecnm) = (Case (strip_promote ev) n (strip_promote ecm) (strip_promote ecnm))\<close>
| \<open>strip_promote (Esac ec n) = (Esac (strip_promote ec) n)\<close>
| \<open>strip_promote (If ec et ef) = (If (strip_promote ec) (strip_promote et) (strip_promote ef))\<close>
| \<open>strip_promote (Take er n ec) = (Take (strip_promote er) n (strip_promote ec))\<close>
| \<open>strip_promote (Split et ec) = (Split (strip_promote et) (strip_promote ec))\<close>
| \<open>strip_promote (Promote type e) = strip_promote e\<close>


fun strip_promote_val :: \<open>('a, 'b) vval \<Rightarrow> ('a, 'b) vval\<close> where
  \<open>strip_promote_val (VPrim l) = VPrim l\<close>
| \<open>strip_promote_val (VProduct v1 v2) = VProduct (strip_promote_val v1) (strip_promote_val v2)\<close>
| \<open>strip_promote_val (VSum n v) = VSum n (strip_promote_val v)\<close>
| \<open>strip_promote_val (VRecord vs) = VRecord (map strip_promote_val vs)\<close>
| \<open>strip_promote_val (VAbstract a) = (VAbstract a)\<close>
| \<open>strip_promote_val (VFunction f ts) = VFunction (strip_promote f) ts\<close>
| \<open>strip_promote_val (VAFunction n ts) = VAFunction n ts\<close>
| \<open>strip_promote_val VUnit = VUnit\<close>

lemma typing_promote_idem:
  "\<Xi>, K, \<Gamma> \<turnstile> e' : t \<Longrightarrow> e' = Promote t1 (Promote t2 e) \<Longrightarrow> \<Xi>, K, \<Gamma> \<turnstile> Promote t1 e : t"
  "\<Xi>, K, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> True"
  using subtyping_trans typing_promote
  by (induct arbitrary: t1 t2 e rule: typing_typing_all.inducts) blast+

context value_sem
begin

lemma strip_promote_val_eval_prim:
  shows "strip_promote_val (eval_prim p vs) = eval_prim p (map strip_promote_val vs)"
  unfolding eval_prim_def
  apply clarsimp
  apply (rule_tac f=\<open>\<lambda>f. eval_prim_op p (map f vs)\<close> in cong, simp)
  apply (rule ext)
  apply (rename_tac v)
  apply (case_tac v; clarsimp)
  done

lemma specialise_strip_promote_eq_stip_promote_specialise:
  shows "specialise ts (strip_promote e) = strip_promote (specialise ts e)"
  by (induct e; clarsimp)

lemma strip_promote_eval_same: 
    \<open>\<xi> , \<gamma> \<turnstile> e \<Down> v \<Longrightarrow>
      (\<And>f a r. \<xi> f a r \<Longrightarrow> \<xi> f (strip_promote_val a) (strip_promote_val r)) \<Longrightarrow>
     \<xi> , map strip_promote_val \<gamma> \<turnstile> strip_promote e \<Down> strip_promote_val v\<close>
    \<open>\<xi> , \<gamma> \<turnstile>* es \<Down> vs \<Longrightarrow>
     (\<And>f a r. \<xi> f a r \<Longrightarrow> \<xi> f (strip_promote_val a) (strip_promote_val r)) \<Longrightarrow>
     \<xi> , map strip_promote_val \<gamma> \<turnstile>* map strip_promote es \<Down> map strip_promote_val vs\<close>
proof (induct rule: v_sem_v_sem_all.inducts)
  case (v_sem_var i \<gamma> \<xi>)
  then show ?case 
    by (simp add: v_sem_var_mapped_ctx)
next
  case (v_sem_prim \<xi> \<gamma> as as' p)
  then show ?case 
    by (simp add: strip_promote_val_eval_prim v_sem_v_sem_all.v_sem_prim)
next
  case (v_sem_app \<xi> \<gamma> x e ts y a r)
  then show ?case 
    by (fastforce 
        simp: specialise_strip_promote_eq_stip_promote_specialise 
        intro!:v_sem_v_sem_all.v_sem_app) 
next
  case (v_sem_member f fs \<xi> \<gamma> e)
  then show ?case 
    by (simp add: v_sem_member_mapped_fields) 
next
  case (v_sem_if \<xi> \<gamma> x b t e r)
  then show ?case 
    by (fastforce intro!:v_sem_v_sem_all.intros)
next
  case (v_sem_put \<xi> \<gamma> x fs e e' f)
  then show ?case 
    by (simp add: map_update v_sem_v_sem_all.v_sem_put)
qed (simp_all add: v_sem_v_sem_all.intros)

lemma val_eval_deterministic:
  assumes "\<And>f a r r'. \<xi> f a r \<Longrightarrow> \<xi> f a r' \<Longrightarrow> r = r'"
  shows   "\<xi>, \<gamma> \<turnstile> e \<Down> v \<Longrightarrow> \<xi>, \<gamma> \<turnstile> e \<Down> v' \<Longrightarrow> v' = v"
  and     "\<xi>, \<gamma> \<turnstile>* es \<Down> vs \<Longrightarrow>  \<xi>, \<gamma> \<turnstile>* es \<Down> vs' \<Longrightarrow> vs' = vs"
  using assms
proof (induct arbitrary: v' and vs' rule: v_sem_v_sem_all.inducts)
  case (v_sem_cast \<xi> \<gamma> e l \<tau> l')
  then show ?case by fastforce
next
  case (v_sem_case_nm \<xi> \<gamma> x t' v t n n' m)
  then show ?case 
    by (blast elim!: v_sem_caseE) 
qed blast+


lemma coherence_of_subsumption:
  assumes  
     \<open> \<xi> , \<gamma> \<turnstile> e \<Down> v \<close>
     \<open> \<xi> , \<gamma> \<turnstile> e' \<Down> v' \<close>
     \<open> strip_promote e' = strip_promote e \<close>
     \<open> \<And>f a r. \<xi> f a r \<Longrightarrow> \<xi> f (strip_promote_val a) (strip_promote_val r) \<close>
     \<open> \<And>f a r r'. \<xi> f a r\<Longrightarrow> \<xi> f a r'  \<Longrightarrow> r = r' \<close>
   shows  \<open> strip_promote_val v = strip_promote_val v' \<close>
  apply (insert assms)
  apply (drule strip_promote_eval_same(1), simp)
  apply (drule strip_promote_eval_same(1), simp)
  by (rule val_eval_deterministic[where \<xi> = \<xi>], simp_all)  

lemma coherence_of_subsumption_list:
  assumes  
     \<open> \<xi> , \<gamma> \<turnstile>* es \<Down> vs \<close>
     \<open> \<xi> , \<gamma> \<turnstile>* es' \<Down> vs' \<close>
     \<open> map strip_promote es' = map strip_promote es \<close>
     \<open> \<And>f a r. \<xi> f a r \<Longrightarrow> \<xi> f (strip_promote_val a) (strip_promote_val r) \<close>
     \<open> \<And>f a r r'. \<xi> f a r\<Longrightarrow> \<xi> f a r'  \<Longrightarrow> r = r' \<close>
   shows  \<open> map strip_promote_val vs = map strip_promote_val vs' \<close>
  apply (insert assms)
  apply (drule strip_promote_eval_same(2), simp)
  apply (drule strip_promote_eval_same(2), simp)
  by (rule val_eval_deterministic[where \<xi> = \<xi>], simp_all)

end

end