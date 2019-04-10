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
    moreover have "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
      by (metis (no_types, lifting) list_all3_mono lub_trecord.hyps type_lub_type_glb.lub_trecord)
    moreover have ts1Wellformed: "K \<turnstile> TRecord ts1 s wellformed"
      using calculation(1) calculation(2) lub_trecord.hyps(6) type_lub_type_glb_wellformed_produce_wellformed(1) by blast
    moreover have ts2Wellformed: "K \<turnstile> TRecord ts2 s wellformed"
      using calculation(1) calculation(2) lub_trecord.hyps(6) lub_trecord.hyps(7) type_lub_type_glb_wellformed_produce_wellformed(1) by blast
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t1 b1 where dummy:		
      "(c, t1, b1) = (ts1 ! i)"
        by (metis prod_cases3)
      have "b1 = Present \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
        using lub_trecord.hyps(1) lub_trecord.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv kinding_record_conv_all_nth kinding_simps(8) lub_trecord.prems record_state.simps(4) snd_conv tsLength)
      moreover have "b1 = Taken \<Longrightarrow> K \<turnstile> t1 wellformed"
        by (metis dummy length_map lub_trecord.hyps(3) nth_mem ts1Wellformed tsLength wellformed_record_wellformed_elem)
      moreover have "case b1 of Taken \<Rightarrow> K \<turnstile> t1 wellformed | Present \<Rightarrow> K \<turnstile> t1 :\<kappa> {D}"
        by (metis calculation(2) calculation(3) record_state.exhaust record_state.simps(3) record_state.simps(4))
      ultimately have "case snd (snd (ts1 ! i)) of Taken \<Rightarrow> K \<turnstile> fst (snd (ts1 ! i)) wellformed | Present \<Rightarrow> K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}"
        by (metis dummy fst_conv snd_conv)
    }
    moreover have "K \<turnstile> TRecord ts1 s1 :\<kappa> {D}"
      by (metis calculation(4) kinding_record_conv_all_nth kinding_simps(8) length_map lub_trecord.hyps(3) lub_trecord.hyps(6) lub_trecord.prems)
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t2 b2 where dummy:		
      "(c, t2, b2) = (ts2 ! i)"
        by (metis prod_cases3)
      have "b2 = Present \<Longrightarrow> K \<turnstile> t2 :\<kappa> {D}"
        using lub_trecord.hyps(1) lub_trecord.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv kinding_record_conv_all_nth kinding_simps(8) lub_trecord.prems record_state.simps(4) snd_conv tsLength)
      moreover have "b2 = Taken \<Longrightarrow> K \<turnstile> t2 wellformed"
        by (metis dummy length_map lub_trecord.hyps(3) lub_trecord.hyps(4) nth_mem ts2Wellformed tsLength wellformed_record_wellformed_elem)
      moreover have "case b2 of Taken \<Rightarrow> K \<turnstile> t2 wellformed | Present \<Rightarrow> K \<turnstile> t2 :\<kappa> {D}"
        by (metis calculation(2) calculation(3) record_state.exhaust record_state.simps(3) record_state.simps(4))
      ultimately have "case snd (snd (ts2 ! i)) of Taken \<Rightarrow> K \<turnstile> fst (snd (ts2 ! i)) wellformed | Present \<Rightarrow> K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}"
        by (metis dummy fst_conv snd_conv)
    }
    moreover have "K \<turnstile> TRecord ts2 s2 :\<kappa> {D}"
      by (metis calculation(5) kinding_record_conv_all_nth kinding_simps(8) length_map lub_trecord.hyps(3) lub_trecord.hyps(4) lub_trecord.hyps(6) lub_trecord.hyps(7) lub_trecord.prems)
    show ?thesis
      by (simp add: \<open>K \<turnstile> TRecord ts1 s1 :\<kappa> {D}\<close> \<open>K \<turnstile> TRecord ts2 s2 :\<kappa> {D}\<close>)
  qed
next
  case (lub_tsum K ts ts1 ts2)
  then show ?case
  proof -
    have "K \<turnstile> TSum ts wellformed"
      using kinding_defs(1) lub_tsum.prems by blast
    moreover have "K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
      by (metis (no_types, lifting) list_all3_mono lub_tsum.hyps type_lub_type_glb.lub_tsum)
    moreover have ts1Wellformed: "K \<turnstile> TSum ts1 wellformed"
      using calculation(1) calculation(2) lub_tsum.hyps(5) type_lub_type_glb_wellformed_produce_wellformed(1) by blast
    moreover have ts2Wellformed: "K \<turnstile> TSum ts2 wellformed"
      using calculation(1) calculation(2) lub_tsum.hyps(4) lub_tsum.hyps(5) type_lub_type_glb_wellformed_produce_wellformed(1) by blast
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t1 b1 where dummy:		
      "(c, t1, b1) = (ts1 ! i)"
        by (metis prod_cases3)
      have "b1 = Unchecked \<Longrightarrow> K \<turnstile> t1 :\<kappa> {D}"
        using lub_tsum.hyps(1) lub_tsum.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv kinding_simps(6) kinding_variant_conv_all_nth lub_tsum.prems snd_conv sup_variant_state.simps(1) tsLength variant_state.simps(4))
      moreover have "b1 = Checked \<Longrightarrow> K \<turnstile> t1 wellformed"
        by (metis dummy length_map lub_tsum.hyps(3) nth_mem ts1Wellformed tsLength wellformed_sum_wellformed_elem)
      moreover have "case b1 of Checked \<Rightarrow> K \<turnstile> t1 wellformed | Unchecked \<Rightarrow> K \<turnstile> t1 :\<kappa> {D}"
        by (metis calculation(2) calculation(3) variant_state.exhaust variant_state.simps(3) variant_state.simps(4))
      ultimately have "case snd (snd (ts1 ! i)) of Checked \<Rightarrow> K \<turnstile> fst (snd (ts1 ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts1 ! i)) :\<kappa> {D}"
        by (metis dummy fst_conv snd_conv)
    }
    moreover have "K \<turnstile> TSum ts1 :\<kappa> {D}"
      by (metis calculation(4) kinding_simps(6) kinding_variant_conv_all_nth length_map lub_tsum.hyps(3) lub_tsum.hyps(5))
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t2 b2 where dummy:		
      "(c, t2, b2) = (ts2 ! i)"
        by (metis prod_cases3)
      have "b2 = Unchecked \<Longrightarrow> K \<turnstile> t2 :\<kappa> {D}"
        using lub_tsum.hyps(1) lub_tsum.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv inf_sup_aci(5) kinding_simps(6) kinding_variant_conv_all_nth lub_tsum.prems snd_conv sup_variant_state.simps(1) tsLength variant_state.simps(4))
      moreover have "b2 = Checked \<Longrightarrow> K \<turnstile> t2 wellformed"
        by (metis dummy length_map lub_tsum.hyps(3) lub_tsum.hyps(4) nth_mem ts2Wellformed tsLength wellformed_sum_wellformed_elem)
      moreover have "case b2 of Checked \<Rightarrow> K \<turnstile> t2 wellformed | Unchecked \<Rightarrow> K \<turnstile> t2 :\<kappa> {D}"
        by (metis calculation(2) calculation(3) variant_state.exhaust variant_state.simps(3) variant_state.simps(4))
      ultimately have "case snd (snd (ts2 ! i)) of Checked \<Rightarrow> K \<turnstile> fst (snd (ts2 ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts2 ! i)) :\<kappa> {D}"
        by (metis dummy fst_conv snd_conv)
    }
    moreover have "K \<turnstile> TSum ts2 :\<kappa> {D}"
      by (metis calculation(5) kinding_simps(6) kinding_variant_conv_all_nth length_map lub_tsum.hyps(3) lub_tsum.hyps(4) lub_tsum.hyps(5))
    show ?thesis
      by (simp add: \<open>K \<turnstile> TSum ts1 :\<kappa> {D}\<close> \<open>K \<turnstile> TSum ts2 :\<kappa> {D}\<close>)
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
  proof -
    have assms1: "(K \<turnstile> TRecord ts1 s1 wellformed) \<and> (K \<turnstile> TRecord ts2 s2 wellformed)"
      using glb_trecord.prems kinding_to_wellformedD(1) by blast
    have assms2: "K \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
      by (metis (mono_tags, lifting) glb_trecord.hyps list_all3_mono type_lub_type_glb.glb_trecord)
    have tsWellformed: "K \<turnstile> TRecord ts s wellformed"
      using assms1 assms2 type_lub_type_glb_wellformed(2) by blast
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t b where dummy:		
      "(c, t, b) = (ts ! i)"
        by (metis prod_cases3)
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy nth_mem tsLength tsWellformed wellformed_record_wellformed_elem)
      moreover have "b = Present \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
        using glb_trecord.hyps(1) glb_trecord.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv glb_trecord.prems kinding_record_conv_all_nth kinding_simps(8) record_state.simps(4) snd_conv tsLength)
      ultimately have "case snd (snd (ts ! i)) of Taken \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed | Present \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}" 
        by (metis (mono_tags, lifting) tWellformed dummy fst_conv record_state.exhaust record_state.simps(3) record_state.simps(4) snd_conv)
    }
    then show ?thesis
      using glb_trecord.hyps(5) glb_trecord.hyps(6) glb_trecord.prems(1) kinding_record_conv_all_nth kinding_simps(8) by auto
  qed
next
  case (glb_tsum K ts ts1 ts2)
  then show ?case
  proof -
    have assms1: "(K \<turnstile> TSum ts1 wellformed) \<and> (K \<turnstile> TSum ts2 wellformed)"
      using glb_tsum.prems kinding_to_wellformedD(1) by blast
    have assms2: "K \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
      by (metis (mono_tags, lifting) glb_tsum.hyps list_all3_mono type_lub_type_glb.glb_tsum)
    have tsWellformed: "K \<turnstile> TSum ts wellformed"
      using assms1 assms2 type_lub_type_glb_wellformed(2) by blast
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      moreover obtain c t b where dummy:		
      "(c, t, b) = (ts ! i)"
        by (metis prod_cases3)
      have tWellformed: "K \<turnstile> t wellformed"
        by (metis dummy nth_mem tsLength tsWellformed wellformed_sum_wellformed_elem)
      moreover have "b = Unchecked \<Longrightarrow> K \<turnstile> t :\<kappa> {D}"
        using glb_tsum.hyps(1) glb_tsum.hyps(2) 
        apply (clarsimp simp add: list_all3_conv_all_nth)
        by (metis dummy fst_conv glb_tsum.prems inf_sup_aci(1) kinding_simps(6) kinding_variant_conv_all_nth snd_conv sup_commute sup_inf_absorb sup_variant_state.simps(1) tsLength variant_state.simps(4))
      ultimately have "case snd (snd (ts ! i)) of Checked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) wellformed | Unchecked \<Rightarrow> K \<turnstile> fst (snd (ts ! i)) :\<kappa> {D}" 
        by (metis (mono_tags, hide_lams) dummy fst_conv snd_conv variant_state.exhaust variant_state.simps(3) variant_state.simps(4))
    }
    then show ?thesis
      by (simp add: glb_tsum.hyps(5) kinding_simps(6) kinding_variant_conv_all_nth)
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
    "K \<turnstile> a \<leftarrow> a \<squnion> b \<Longrightarrow> K \<turnstile> b \<sqsubseteq> a"
    "K \<turnstile> b \<leftarrow> a \<sqinter> b \<Longrightarrow> K \<turnstile> b \<sqsubseteq> a"
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