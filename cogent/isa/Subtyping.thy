theory Subtyping
  imports Cogent
begin

text \<open>
  This file covers the interpretation of the subtyping relation as a lattice. This is how the
  compiler computes subtyping (as of late 2018), and these proofs give assurance we've formalised
  the correct relation.
\<close>

inductive type_lub :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<leftarrow> _ \<squnion> _" [60,0,60] 60)
  and type_glb :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_ \<leftarrow> _ \<sqinter> _" [60,0,60] 60)
  where
  lub_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> TVar n \<leftarrow> TVar n1 \<squnion> TVar n2"
| lub_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> TVarBang n \<leftarrow> TVarBang n1 \<squnion> TVarBang n2"
| lub_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; list_all3 type_lub ts ts1 ts2
                \<rbrakk> \<Longrightarrow> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<squnion> TCon n2 ts2 s2"
| lub_tfun   : "\<lbrakk> t \<leftarrow> t1 \<sqinter> t2
                ; u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> TFun t u \<leftarrow> TFun t1 u1 \<squnion> TFun t2 u2"
| lub_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> TPrim p \<leftarrow> TPrim p1 \<squnion> TPrim p2"
| lub_trecord: "\<lbrakk> \<And>n t b t1 t2 b1 b2. \<lbrakk> (n,t,b) \<in> set ts; (n,t1,b1) \<in> set ts1; (n,t2,b2) \<in> set ts2 \<rbrakk> \<Longrightarrow> t \<leftarrow> t1 \<squnion> t2 \<and> (b = inf b1 b2)
                ; distinct (map fst ts)
                ; distinct (map fst ts1)
                ; distinct (map fst ts2)
                ; fst ` set ts = fst ` set ts1
                ; fst ` set ts2 = fst ` set ts1
                ; s = s1
                ; s1 = s2
                \<rbrakk> \<Longrightarrow> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
| lub_tprod  : "\<lbrakk> t \<leftarrow> t1 \<squnion> t2
                ; u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> TProduct t u \<leftarrow> TProduct t1 u1 \<squnion> TProduct t2 u2"
| lub_tsum   : "\<lbrakk> \<And>n t b t1 t2 b1 b2. \<lbrakk> (n,t,b) \<in> set ts; (n,t1,b1) \<in> set ts1; (n,t2,b2) \<in> set ts2 \<rbrakk> \<Longrightarrow> t \<leftarrow> t1 \<squnion> t2 \<and> (b = inf b1 b2)
                ; distinct (map fst ts)
                ; distinct (map fst ts1)
                ; distinct (map fst ts2)
                ; fst ` set ts = fst ` set ts1
                ; fst ` set ts2 = fst ` set ts1
                \<rbrakk> \<Longrightarrow> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
| lub_tunit  : "TUnit \<leftarrow> TUnit \<squnion> TUnit"

| glb_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> TVar n \<leftarrow> TVar n1 \<sqinter> TVar n2"
| glb_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> TVarBang n \<leftarrow> TVarBang n1 \<sqinter> TVarBang n2"
| glb_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; list_all3 type_glb ts ts1 ts2
                \<rbrakk> \<Longrightarrow> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<sqinter> TCon n2 ts2 s2"
| glb_tfun   : "\<lbrakk> t \<leftarrow> t1 \<squnion> t2
                ; u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> TFun t u \<leftarrow> TFun t1 u1 \<sqinter> TFun t2 u2"
| glb_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> TPrim p \<leftarrow> TPrim p1 \<sqinter> TPrim p2"
| glb_trecord: "\<lbrakk> \<And>n t b t1 t2 b1 b2. \<lbrakk> (n,t,b) \<in> set ts; (n,t1,b1) \<in> set ts1; (n,t2,b2) \<in> set ts2 \<rbrakk> \<Longrightarrow> t \<leftarrow> t1 \<sqinter> t2 \<and> (b = sup b1 b2)
                ; distinct (map fst ts)
                ; distinct (map fst ts1)
                ; distinct (map fst ts2)
                ; fst ` set ts = fst ` set ts1
                ; fst ` set ts2 = fst ` set ts1
                ; s = s1
                ; s1 = s2
                \<rbrakk> \<Longrightarrow> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
| glb_tprod  : "\<lbrakk> t \<leftarrow> t1 \<sqinter> t2
                ; u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> TProduct t u \<leftarrow> TProduct t1 u1 \<sqinter> TProduct t2 u2"
| glb_tsum   : "\<lbrakk> \<And>n t b t1 t2 b1 b2. \<lbrakk> (n,t,b) \<in> set ts; (n,t1,b1) \<in> set ts1; (n,t2,b2) \<in> set ts2 \<rbrakk> \<Longrightarrow> t \<leftarrow> t1 \<sqinter> t2 \<and> (b = sup b1 b2)
                ; distinct (map fst ts)
                ; distinct (map fst ts1)
                ; distinct (map fst ts2)
                ; fst ` set ts = fst ` set ts1
                ; fst ` set ts2 = fst ` set ts1
                \<rbrakk> \<Longrightarrow> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
| glb_tunit  : "TUnit \<leftarrow> TUnit \<sqinter> TUnit"


lemma type_lub_type_glb_wellformed:
  assumes
    "K \<turnstile> t1 wellformed"
    "K \<turnstile> t2 wellformed"
  shows
    "t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> K \<turnstile> t wellformed"
    "t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> K \<turnstile> t wellformed"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
  case lub_tcon then show ?case
    by (fastforce simp add: list_all3_conv_all_nth Ball_def in_set_conv_nth)
next
  case (lub_trecord ts ts1 ts2 s s1 s2)
  { fix n t b
    assume n_in_ts: "(n,t,b) \<in> set ts"
    obtain t1 b1 where "(n,t1,b1) \<in> set ts1"
      using n_in_ts lub_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    moreover obtain t2 b2 where "(n,t2,b2) \<in> set ts2"
      using n_in_ts lub_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "type_wellformed (length K) t"
      using lub_trecord n_in_ts
      by fastforce
  } then show ?case
    using lub_trecord by auto
next
  case (lub_tsum ts ts1 ts2)
  { fix n t b
    assume n_in_ts: "(n,t,b) \<in> set ts"
    obtain t1 b1 where "(n,t1,b1) \<in> set ts1"
      using n_in_ts lub_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    moreover obtain t2 b2 where "(n,t2,b2) \<in> set ts2"
      using n_in_ts lub_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "type_wellformed (length K) t"
      using lub_tsum n_in_ts
      by fastforce
  } then show ?case
    using lub_tsum by auto
next
  case glb_tcon then show ?case
    by (fastforce simp add: list_all3_conv_all_nth Ball_def in_set_conv_nth)
next
  case (glb_trecord ts ts1 ts2 s s1 s2)
  { fix n t b
    assume n_in_ts: "(n,t,b) \<in> set ts"
    obtain t1 b1 where "(n,t1,b1) \<in> set ts1"
      using n_in_ts glb_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    moreover obtain t2 b2 where "(n,t2,b2) \<in> set ts2"
      using n_in_ts glb_trecord.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "type_wellformed (length K) t"
      using glb_trecord n_in_ts
      by fastforce
  } then show ?case
    using glb_trecord by auto
next
  case (glb_tsum ts ts1 ts2)
  { fix n t b
    assume n_in_ts: "(n,t,b) \<in> set ts"
    obtain t1 b1 where "(n,t1,b1) \<in> set ts1"
      using n_in_ts glb_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    moreover obtain t2 b2 where "(n,t2,b2) \<in> set ts2"
      using n_in_ts glb_tsum.hyps
      by (metis (no_types, hide_lams) eq_fst_iff image_iff)
    ultimately have "type_wellformed (length K) t"
      using glb_tsum n_in_ts
      by fastforce
  } then show ?case
    using glb_tsum by auto
qed auto

lemma type_lub_type_glb_idem:
  assumes "K \<turnstile> t wellformed"
  shows
    "t \<leftarrow> t \<squnion> t"
    "t \<leftarrow> t \<sqinter> t"
  using assms
proof (induct t)
  case (TCon ns ts s)
  moreover assume "K \<turnstile> TCon ns ts s wellformed"
  ultimately show
    "TCon ns ts s \<leftarrow> TCon ns ts s \<squnion> TCon ns ts s"
    "TCon ns ts s \<leftarrow> TCon ns ts s \<sqinter> TCon ns ts s"
     by (simp, fastforce simp add: list_all3_same kinding_all_set intro!: type_lub_type_glb.intros)+
next
  case (TSum ts)
  assume ts_wellformed: "K \<turnstile> TSum ts wellformed"
  {
    fix n t t1 t2 b b1 b2
    assume assms1:
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts"
      "(n, t2, b2) \<in> set ts"
    moreover have "t1 = t" "t2 = t" "b1 = b" "b2 = b"
      using assms1 ts_wellformed
        distinct_fst[where xs=ts and b="(p, q)" and b'="(p', q')" for p q p' q']
      by fastforce+
    ultimately have
      "b1 = b" "b2 = b"
      "t \<leftarrow> t1 \<squnion> t2 \<and> (b = inf b1 b2)"
      "t \<leftarrow> t1 \<sqinter> t2 \<and> (b = sup b1 b2)"
      using TSum ts_wellformed kinding_variant_all_wellformed
      by auto
  }
  then show
    "TSum ts \<leftarrow> TSum ts \<squnion> TSum ts"
    "TSum ts \<leftarrow> TSum ts \<sqinter> TSum ts"
    using ts_wellformed
    by (auto intro!: type_lub_type_glb.intros)
next
  case (TRecord ts s)
  assume ts_wellformed: "K \<turnstile> TRecord ts s wellformed"
  {
    fix n t t1 t2 b b1 b2
    assume assms1:
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts"
      "(n, t2, b2) \<in> set ts"
    moreover have "t1 = t" "t2 = t" "b1 = b" "b2 = b"
      using assms1 ts_wellformed
        distinct_fst[where xs=ts and b="(p, q)" and b'="(p', q')" for p q p' q']
      by fastforce+
    ultimately have
      "b1 = b" "b2 = b"
      "t \<leftarrow> t1 \<squnion> t2 \<and> (b = inf b1 b2)"
      "t \<leftarrow> t1 \<sqinter> t2 \<and> (b = sup b1 b2)"
      using TRecord ts_wellformed
      by auto
  }
  then show
    "TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
    "TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
    using ts_wellformed
    by (auto intro!: type_lub_type_glb.intros)
qed (force intro: type_lub_type_glb.intros)+

lemma type_lub_type_glb_commut:
  shows
  "t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> t \<leftarrow> t2 \<squnion> t1"
  "t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> t \<leftarrow> t2 \<sqinter> t1"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tcon ns ns1 ns2 s s2 s1 ts ts1 ts2)
  then show ?case
    by (fastforce simp add: list_all3_conv_all_nth kinding_all_set
        intro!: type_lub_type_glb.intros)
next
  case (lub_trecord ts ts1 ts2 s s2 s1)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t t1 t2 b b1 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
      "(n, t2, b2) \<in> set ts2"
    then show "t \<leftarrow> t2 \<squnion> t1 \<and> b = inf b2 b1"
      using lub_trecord
      by (auto simp add: inf_commute)
  qed simp+
next
  case (lub_tsum ts ts1 ts2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t t1 t2 b b1 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
      "(n, t2, b2) \<in> set ts2"
    then show "t \<leftarrow> t2 \<squnion> t1 \<and> b = inf b2 b1"
      using lub_tsum
      by (auto simp add: inf_commute)
  qed simp+
next
  case (glb_tcon ns ns1 ns2 s s1 s2 ts ts1 ts2)
  then show ?case
    using kinding_typelist_wellformed_elem
    by (auto intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
next
  case (glb_trecord ts ts1 ts2 s s2 s1)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t t1 t2 b b1 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
      "(n, t2, b2) \<in> set ts2"
    then show "t \<leftarrow> t2 \<sqinter> t1 \<and> b = sup b2 b1"
      using glb_trecord
      by (auto simp add: sup_commute)
  qed simp+
next
  case (glb_tsum ts ts1 ts2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t t1 t2 b b1 b2
    assume
      "(n, t, b) \<in> set ts"
      "(n, t1, b1) \<in> set ts1"
      "(n, t2, b2) \<in> set ts2"
    then show "t \<leftarrow> t2 \<sqinter> t1 \<and> b = sup b2 b1"
      using glb_tsum
      by (auto simp add: sup_commute)
  qed simp+
qed (force intro: type_lub_type_glb.intros)+

lemma type_lub_type_glb_absorb:
  shows
    "c \<leftarrow> a \<squnion> b \<Longrightarrow> a \<leftarrow> a \<sqinter> c"
    "c \<leftarrow> a \<sqinter> b \<Longrightarrow> a \<leftarrow> a \<squnion> c"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
next
  case (lub_trecord ts ts1 ts2 s s1 s2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_trecord.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<squnion> t2 \<and> t1 \<leftarrow> t1 \<sqinter> t) \<and> b = inf b1 b2"
      using lub_trecord.hyps by blast+
    then show "t1' \<leftarrow> t1 \<sqinter> t \<and> b1' = sup b1 b"
      using lub_trecord.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
next
  case (lub_tsum ts ts1 ts2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using lub_tsum.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<squnion> t2 \<and> t1 \<leftarrow> t1 \<sqinter> t) \<and> b = inf b1 b2"
      using lub_tsum.hyps by blast+
    then show "t1' \<leftarrow> t1 \<sqinter> t \<and> b1' = sup b1 b"
      using lub_tsum.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
next
  case (glb_tcon n n1 n2 s s1 s2 ts ts1 ts2)
  then show ?case by (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth)
next
  case (glb_trecord ts ts1 ts2 s s1 s2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_trecord.hyps assms1
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<sqinter> t2 \<and> t1 \<leftarrow> t1 \<squnion> t) \<and> b = sup b1 b2"
      using glb_trecord.hyps by blast+
    then show "t1' \<leftarrow> t1 \<squnion> t \<and> b1' = inf b1 b"
      using glb_trecord.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
next
  case (glb_tsum ts ts1 ts2)
  then show ?case
  proof (intro type_lub_type_glb.intros)
    fix n t1' b1' t1 b1 t b
    assume assms1:
      "(n, t1, b1) \<in> set ts1"
      "(n, t1', b1') \<in> set ts1"
      "(n, t, b) \<in> set ts"
    moreover obtain t2 b2 where "(n, t2, b2) \<in> set ts2"
      using glb_tsum.hyps assms1 
      by (metis (mono_tags, hide_lams) fst_conv image_iff surjective_pairing)
    ultimately have
      "(t \<leftarrow> t1 \<sqinter> t2 \<and> t1 \<leftarrow> t1 \<squnion> t) \<and> b = sup b1 b2"
      using glb_tsum.hyps by blast+
    then show "t1' \<leftarrow> t1 \<squnion> t \<and> b1' = inf b1 b"
      using glb_tsum.hyps assms1 distinct_fst[where xs=ts1] by fastforce
  qed auto
qed (force intro: type_lub_type_glb.intros)+

lemma type_lub_type_glb_order_same: "a \<leftarrow> a \<squnion> b \<longleftrightarrow> b \<leftarrow> a \<sqinter> b"
  by (auto intro: type_lub_type_glb_absorb type_lub_type_glb_commut)


end