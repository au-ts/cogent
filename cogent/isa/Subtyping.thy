theory Subtyping
  imports Cogent
begin

text \<open>
  This file covers the interpretation of the subtyping relation as a lattice. This is how the
  compiler computes subtyping (as of late 2018), and these proofs give assurance we've formalised
  the correct relation.
\<close>

inductive type_lub :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_, _, _ \<turnstile> _ \<leftarrow> _ \<squnion> _" [60,0,0,60] 60)
  and type_glb :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_, _, _ \<turnstile> _ \<leftarrow> _ \<sqinter> _" [60,0,0,60] 60)
  where
  lub_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TVar n \<leftarrow> TVar n1 \<squnion> TVar n2"
| lub_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<squnion> TVarBang n2"
| lub_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<squnion> TCon n2 ts2 s2"
| lub_tfun   : "\<lbrakk> L, K, C \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; L, K, C \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<squnion> TFun t2 u2"
| lub_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TPrim p \<leftarrow> TPrim p1 \<squnion> TPrim p2"
| lub_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (L, K, C \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          (if (L, K, C \<turnstile> fst (snd p1) :\<kappa> {D})
                                          then b1 \<le> b
                                          else b1 = b) \<and>
                                          (if (L, K, C \<turnstile> fst (snd p2) :\<kappa> {D})
                                          then b2 \<le> b
                                          else b2 = b)) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<squnion> TRecord ts2 s2"
| lub_tprod  : "\<lbrakk> L, K, C \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; L, K, C \<turnstile> u \<leftarrow> u1 \<squnion> u2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<squnion> TProduct t2 u2"
| lub_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (L, K, C \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<squnion> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = sup (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TSum ts \<leftarrow> TSum ts1 \<squnion> TSum ts2"
| lub_tunit  : "L, K, C \<turnstile> TUnit \<leftarrow> TUnit \<squnion> TUnit"

| glb_tvar   : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TVar n \<leftarrow> TVar n1 \<sqinter> TVar n2"
| glb_tvarb  : "\<lbrakk> n = n1
                ; n2 = n1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TVarBang n \<leftarrow> TVarBang n1 \<sqinter> TVarBang n2"
| glb_tcon   : "\<lbrakk> n = n1 ; n2 = n1
                ; s = s1 ; s2 = s1
                ; ts = ts1 ; ts1 = ts2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TCon n ts s \<leftarrow> TCon n1 ts1 s1 \<sqinter> TCon n2 ts2 s2"
| glb_tfun   : "\<lbrakk> L, K, C \<turnstile> t \<leftarrow> t1 \<squnion> t2
                ; L, K, C \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TFun t u \<leftarrow> TFun t1 u1 \<sqinter> TFun t2 u2"
| glb_tprim  : "\<lbrakk> p = p1
                ; p2 = p1
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TPrim p \<leftarrow> TPrim p1 \<sqinter> TPrim p2"
| glb_trecord: "\<lbrakk> list_all3 (\<lambda>p p1 p2. (L, K, C \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. let b = snd (snd p)
                                         ; b1 = snd (snd p1)
                                         ; b2 = snd (snd p2)
                                        in
                                          (if (L, K, C \<turnstile> fst (snd p) :\<kappa> {D})
                                          then b \<le> b1 \<and> b \<le> b2
                                          else b = b2 \<and> b1 = b2)) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                ; s = s1 ; s1 = s2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts1 s1 \<sqinter> TRecord ts2 s2"
| glb_tprod  : "\<lbrakk> L, K, C \<turnstile> t \<leftarrow> t1 \<sqinter> t2
                ; L, K, C \<turnstile> u \<leftarrow> u1 \<sqinter> u2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TProduct t u \<leftarrow> TProduct t1 u1 \<sqinter> TProduct t2 u2"
| glb_tsum   : "\<lbrakk> list_all3 (\<lambda>p p1 p2. (L, K, C \<turnstile> (fst (snd p)) \<leftarrow> (fst (snd p1)) \<sqinter> (fst (snd p2)))) ts ts1 ts2
                ; list_all3 (\<lambda>p p1 p2. snd (snd p) = inf (snd (snd p1)) (snd (snd p2))) ts ts1 ts2
                ; map fst ts = map fst ts1
                ; map fst ts1 = map fst ts2
                \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TSum ts \<leftarrow> TSum ts1 \<sqinter> TSum ts2"
| glb_tunit  : "L, K, C \<turnstile> TUnit \<leftarrow> TUnit \<sqinter> TUnit"


lemma type_lub_type_glb_idem:
  assumes "L, K, C \<turnstile> t wellformed"
  shows
    "L, K, C \<turnstile> t \<leftarrow> t \<squnion> t"
    "L, K, C \<turnstile> t \<leftarrow> t \<sqinter> t"
  using assms
proof (induct t)
  case (TSum ts)
  moreover assume ts_wellformed: "L, K, C \<turnstile> TSum ts wellformed"
  ultimately show
    "L, K, C \<turnstile> TSum ts \<leftarrow> TSum ts \<squnion> TSum ts"
    "L, K, C \<turnstile> TSum ts \<leftarrow> TSum ts \<sqinter> TSum ts"
    by (fastforce simp add: list_all3_same list_all_iff intro!: type_lub_type_glb.intros)+
next
  case (TRecord ts s)
  moreover assume ts_wellformed: "L, K, C \<turnstile> TRecord ts s wellformed"
  ultimately show
  "L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
  "L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
  proof -
    have tWellformed: "\<And>i. i < length ts \<Longrightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) wellformed"
      by (metis nth_mem prod.collapse ts_wellformed wellformed_record_wellformed_elem)
    show "L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<squnion> TRecord ts s"
    proof (rule_tac lub_trecord)
      show "list_all3 (\<lambda>p p1 p2. L, K, C \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<squnion> fst (snd p2)) ts ts ts"
        using TRecord.hyps
        by (metis (no_types, lifting) fsts.intros in_set_conv_nth list_all3_same snds.intros tWellformed)
    qed (simp add: list_all3_same)+
    show "L, K, C \<turnstile> TRecord ts s \<leftarrow> TRecord ts s \<sqinter> TRecord ts s"
    proof (rule_tac glb_trecord)
      show "list_all3 (\<lambda>p p1 p2. L, K, C \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<sqinter> fst (snd p2)) ts ts ts"
        using TRecord.hyps
        by (metis (no_types, lifting) fsts.intros in_set_conv_nth list_all3_same snds.intros tWellformed)
    qed (simp add: list_all3_same)+
  qed
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_commut:
  shows
  "L, K, C \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> L, K, C \<turnstile> c \<leftarrow> b \<squnion> a"
  "L, K, C \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> L, K, C \<turnstile> c \<leftarrow> b \<sqinter> a"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.lub_trecord)
    show "list_all3 (\<lambda>p p1 p2. L, K, C \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<squnion> fst (snd p2)) ts ts2 ts1"
      using list_all3_comm2 list_all3_mono lub_trecord.hyps by fastforce
    show "list_all3 (\<lambda>p p1 p2. let b = snd (snd p); b1 = snd (snd p1); b2 = snd (snd p2) in 
          (if L, K, C \<turnstile> fst (snd p1) :\<kappa> {D} then b1 \<le> b else b1 = b) \<and> 
          (if L, K, C \<turnstile> fst (snd p2) :\<kappa> {D} then b2 \<le> b else b2 = b)) ts ts2 ts1"
      using lub_trecord.hyps
      by (clarsimp simp add: list_all3_conv_all_nth, meson)
  qed (simp)+
next
  case (lub_tsum L K C ts ts1 ts2)
  then show ?case
    by (simp add: list_all3_conv_all_nth sup_commute type_lub_type_glb.lub_tsum)
next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.glb_trecord)
    show "list_all3 (\<lambda>p p1 p2. L, K, C \<turnstile> fst (snd p) \<leftarrow> fst (snd p1) \<sqinter> fst (snd p2)) ts ts2 ts1"
      using glb_trecord.hyps list_all3_comm2 list_all3_mono by fastforce
    show "list_all3 (\<lambda>p p1 p2.  let b = snd (snd p); b1 = snd (snd p1); b2 = snd (snd p2) in 
          if L, K, C \<turnstile> fst (snd p) :\<kappa> {D} then b \<le> b1 \<and> b \<le> b2 
          else b = b2 \<and> b1 = b2) ts ts2 ts1"
      using glb_trecord.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      by metis
  qed (simp)+
next
  case (glb_tsum L K C ts ts1 ts2)
  then show ?case
    by (simp add: inf_sup_aci(1) list_all3_conv_all_nth type_lub_type_glb.glb_tsum)
qed (fastforce intro!: type_lub_type_glb.intros)+

lemma type_lub_type_glb_lrepr_right: 
  shows
    "L, K, C \<turnstile> t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> type_lrepr t = type_lrepr t2"
    "L, K, C \<turnstile> t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> type_lrepr t = type_lrepr t2"
proof (induct rule: type_lub_type_glb.inducts)
 case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case 
  by (cases s2)
     ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  by (cases s2)
     ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (lub_tsum L K C ts ts1 ts2)
  then show ?case
    by  ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (glb_tsum L K C ts ts1 ts2)
  then show ?case 
    by ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
qed (simp+)

lemma type_lub_type_glb_lrepr_left: 
  shows
    "L, K, C \<turnstile> t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> type_lrepr t = type_lrepr t1"
    "L, K, C \<turnstile> t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> type_lrepr t = type_lrepr t1"
proof (induct rule: type_lub_type_glb.inducts)
 case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case 
  by (cases s2)
     ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  by (cases s2)
     ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (lub_tsum L K C ts ts1 ts2)
  then show ?case
    by  ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
next
  case (glb_tsum L K C ts ts1 ts2)
  then show ?case 
    by ( simp add: case_prod_beta' map_eq_iff_nth_eq
    list_all2_conv_all_nth list_all3_conv_all_nth  )+
  qed (simp+)

lemma type_lub_type_glb_wellformed:
  assumes
    "L, K, C \<turnstile> t1 wellformed"
    "L, K, C \<turnstile> t2 wellformed"
  shows
    "L, K, C \<turnstile> t \<leftarrow> t1 \<squnion> t2 \<Longrightarrow> L, K, C \<turnstile> t wellformed"
    "L, K, C \<turnstile> t \<leftarrow> t1 \<sqinter> t2 \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  using assms
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using lub_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
  
  ultimately show ?case 
    by (auto simp add: list_all_length list_all3_conv_all_nth)

next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using glb_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
  
  ultimately show ?case 
    by (auto simp add: list_all_length list_all3_conv_all_nth)


qed (auto simp add: list_all_length list_all3_conv_all_nth)

lemma type_lub_type_glb_wellformed_produce_wellformed:
  "L, K, C \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> L, K, C \<turnstile> c wellformed \<Longrightarrow> (L, K, C \<turnstile> a wellformed) \<and> (L, K, C \<turnstile> b wellformed)"
  "L, K, C \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> L, K, C \<turnstile> c wellformed \<Longrightarrow> (L, K, C \<turnstile> a wellformed) \<and> (L, K, C \<turnstile> b wellformed)"
proof (induct rule: type_lub_type_glb.inducts)     
  case (lub_trecord L K C ts ts1 ts2 s s1 s2)

  moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using lub_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
    moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1"
    using lub_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_left split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
  ultimately show ?case  

    by(auto simp add: list_all_length list_all3_conv_all_nth) 

next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
   moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using glb_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
    moreover have "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts =
          map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1"
    using glb_trecord
    by(fastforce dest:type_lub_type_glb_lrepr_left split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)
  
  ultimately show ?case  
    by (auto simp add: list_all_length list_all3_conv_all_nth)
qed (auto simp add: list_all3_conv_all_nth list_all_length)

lemma type_glb_drop_produce_drop:
  shows
  "L, K, C \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> L, K, C \<turnstile> c :\<kappa> {D} \<Longrightarrow> L, K, C \<turnstile> a :\<kappa> {D} \<and> L, K, C \<turnstile> b :\<kappa> {D}"
  "L, K, C \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> L, K, C \<turnstile> a :\<kappa> {D} \<Longrightarrow> L, K, C \<turnstile> b :\<kappa> {D} \<Longrightarrow> L, K, C \<turnstile> c :\<kappa> {D}"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_tfun K t t1 t2 u u1 u2)
  then show ?case
    using kinding_simps(4) type_lub_type_glb_wellformed_produce_wellformed by auto
next
  case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  proof -
    have "L, K, C \<turnstile> TRecord ts s wellformed"
      using kinding_def lub_trecord.prems by blast
    moreover have lrepr_ts12:
    "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts = map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1"
    "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts = map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using lub_trecord
      by(fastforce dest:type_lub_type_glb_lrepr_left type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)+
  ultimately have ts1ts2Wellformed:
      "L, K, C \<turnstile> TRecord ts1 s wellformed"
      "L, K, C \<turnstile> TRecord ts2 s wellformed"  
      using lub_trecord.hyps type_lub_type_glb_wellformed_produce_wellformed
      by (metis (mono_tags, lifting) list_all3_conv_all_nth list_all_length type_wellformed.simps(8) type_wellformed_pretty_def)+
    have "L, K, C \<turnstile> TRecord ts1 s1 :\<kappa> {D}"
      using lub_trecord
    proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps, intro conjI allI impI)
      fix i :: nat
      assume tsLength: "i < length ts1"
      let ?t1 = "fst (snd (ts1 ! i))"
      let ?b1 = "snd (snd (ts1 ! i))"
      show "case ?b1 of Taken \<Rightarrow> L, K, C \<turnstile> ?t1 wellformed | Present \<Rightarrow> L, K, C \<turnstile> ?t1 :\<kappa> {D}"
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
    next
      assume "matches_type_sigil L C (LRRecord (map (\<lambda>(n, t, _). (n, type_lrepr t)) ts)) s2 "
      then show "matches_type_sigil L C (LRRecord (map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1)) s2"
        by (simp add:lrepr_ts12)
    qed
    moreover have "L, K, C \<turnstile> TRecord ts2 s2 :\<kappa> {D}"
      using lub_trecord
    proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps, intro conjI allI impI)
      fix i :: nat
      assume tsLength: "i < length ts2"
      let ?t2 = "fst (snd (ts2 ! i))"
      let ?b2 = "snd (snd (ts2 ! i))"
      show "case ?b2 of Taken \<Rightarrow> L, K, C \<turnstile> ?t2 wellformed | Present \<Rightarrow> L, K, C \<turnstile> ?t2 :\<kappa> {D}"
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
   next
      assume "matches_type_sigil L C (LRRecord (map (\<lambda>(n, t, _). (n, type_lrepr t)) ts)) s2 "
      then show "matches_type_sigil L C (LRRecord (map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2)) s2"
        using lrepr_ts12
        by simp            
    qed
    ultimately show ?thesis
      by blast
  qed
next
  case (lub_tsum L K C ts ts1 ts2)
  then show ?case
  proof -
    have "L, K, C \<turnstile> TSum ts wellformed"
      using kinding_def lub_tsum.prems by blast
    then have ts1ts2Wellformed:
      "L, K, C \<turnstile> TSum ts1 wellformed"
      "L, K, C \<turnstile> TSum ts2 wellformed"
      using lub_tsum.hyps type_lub_type_glb_wellformed_produce_wellformed
      by (metis (mono_tags, lifting) list_all3_conv_all_nth list_all_length type_wellformed.simps(6) type_wellformed_pretty_def)+
    have "L, K, C \<turnstile> TSum ts1 :\<kappa> {D}"
      using lub_tsum
    proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts1"
      let ?t1 = "fst (snd (ts1 ! i))"
      let ?b1 = "snd (snd (ts1 ! i))"
      show "case ?b1 of Checked \<Rightarrow> L, K, C \<turnstile> ?t1 wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> ?t1 :\<kappa> {D}"
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
    moreover have "L, K, C \<turnstile> TSum ts2 :\<kappa> {D}"
      using lub_tsum
    proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
      fix i :: nat
      assume tsLength: "i < length ts2"
      let ?t2 = "fst (snd (ts2 ! i))"
      let ?b2 = "snd (snd (ts2 ! i))"
      show "case ?b2 of Checked \<Rightarrow> L, K, C \<turnstile> ?t2 wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> ?t2 :\<kappa> {D}"
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
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  
have lrepr_ts12:
    "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts = map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1"
    "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts = map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"
    using glb_trecord
      by(fastforce dest:type_lub_type_glb_lrepr_left type_lub_type_glb_lrepr_right split:prod.split simp add:
  list_all3_conv_all_nth map_eq_iff_nth_eq)+
    moreover have 
      "(L, K, C \<turnstile> TRecord ts1 s1 wellformed)" 
      "(L, K, C \<turnstile> TRecord ts2 s2 wellformed)"
      using glb_trecord.prems kinding_to_wellformedD(1) by blast+
    ultimately have tsWellformed: "L, K, C \<turnstile> TRecord ts s wellformed"
      using glb_trecord.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      using type_lub_type_glb_wellformed
      by (metis (no_types, lifting) list_all_length type_wellformed_pretty_def)
    then show ?case
    using glb_trecord
  proof (clarsimp simp: kinding_record_conv_all_nth kinding_simps)
    
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      let ?t = "fst (snd (ts ! i))"
      let ?b = "snd (snd (ts ! i))"
      show "case ?b of Taken \<Rightarrow> L, K, C \<turnstile> ?t wellformed | Present \<Rightarrow> L, K, C \<turnstile> ?t :\<kappa> {D}"
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
  case (glb_tsum L K C ts ts1 ts2)
  then show ?case
   using glb_tsum
  proof (clarsimp simp: kinding_variant_conv_all_nth kinding_simps)
    have 
      "(L, K, C \<turnstile> TSum ts1 wellformed)" 
      "(L, K, C \<turnstile> TSum ts2 wellformed)"
      using glb_tsum.prems kinding_to_wellformedD(1) by blast+
    then have tsWellformed: "L, K, C \<turnstile> TSum ts wellformed"
      using glb_tsum.hyps
      apply (clarsimp simp add: list_all3_conv_all_nth)
      using type_lub_type_glb_wellformed
      by (metis (no_types, lifting) list_all_length type_wellformed_pretty_def)
    {
      fix i :: nat
      assume tsLength: "i < length ts"
      let ?t = "fst (snd (ts ! i))"
      let ?b = "snd (snd (ts ! i))"
      show "case ?b of Checked \<Rightarrow> L, K, C \<turnstile> ?t wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> ?t :\<kappa> {D}"
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
    "L, K, C \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> L, K, C \<turnstile> a \<leftarrow> a \<sqinter> c"
    "L, K, C \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> L, K, C \<turnstile> a \<leftarrow> a \<squnion> c"
proof (induct rule: type_lub_type_glb.inducts)
qed (force intro!: type_lub_type_glb.intros simp add: list_all3_conv_all_nth Let_def)+

lemma type_lub_type_glb_order_correct: "L, K, C \<turnstile> a \<leftarrow> a \<squnion> b \<longleftrightarrow> L, K, C \<turnstile> b \<leftarrow> a \<sqinter> b"
  by (auto intro: type_lub_type_glb_absorb type_lub_type_glb_commut)

lemma glb_lub_subtyping_order_correct:
  shows
    "L, K, C \<turnstile> c \<leftarrow> a \<squnion> b \<Longrightarrow> (L, K, C \<turnstile> a \<sqsubseteq> c) \<and> (L, K, C \<turnstile> b \<sqsubseteq> c)"
    "L, K, C \<turnstile> c \<leftarrow> a \<sqinter> b \<Longrightarrow> (L, K, C \<turnstile> c \<sqsubseteq> a) \<and> (L, K, C \<turnstile> c \<sqsubseteq> b)"
proof (induct rule: type_lub_type_glb.inducts)
  case (lub_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case 
  proof -
    have "L, K, C \<turnstile> TRecord ts1 s1 \<sqsubseteq> TRecord ts s"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. L, K, C \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts1 ts"
        using lub_trecord.hyps 
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty L K C) ts1 ts"
        using lub_trecord.hyps le_neq_trans 
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by fastforce
    qed (simp add: lub_trecord.hyps)+
    moreover have "L, K, C \<turnstile> TRecord ts2 s2 \<sqsubseteq> TRecord ts s"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. L, K, C \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts2 ts"
        using lub_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty L K C) ts2 ts"
        using lub_trecord.hyps le_neq_trans
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by fastforce
    qed (simp add: lub_trecord.hyps)+
    ultimately show ?thesis
      by simp
  qed
next
  case (glb_trecord L K C ts ts1 ts2 s s1 s2)
  then show ?case
  proof -
    have "L, K, C \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts1 s1"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. L, K, C \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts1"
        using glb_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty L K C) ts ts1"
        using glb_trecord.hyps
        apply (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
        by (metis (no_types) le_less)
    qed (simp add: glb_trecord.hyps)+
    moreover have "L, K, C \<turnstile> TRecord ts s \<sqsubseteq> TRecord ts2 s2"
    proof (rule subty_trecord)
      show "list_all2 (\<lambda>p1 p2. L, K, C \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) ts ts2"
        using glb_trecord.hyps
        by (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth)
      show "list_all2 (record_kind_subty L K C) ts ts2"
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
    "L, K, C \<turnstile> a \<leftarrow> a \<squnion> b \<Longrightarrow> L, K, C \<turnstile> b \<sqsubseteq> a"
    "L, K, C \<turnstile> b \<leftarrow> a \<sqinter> b \<Longrightarrow> L, K, C \<turnstile> b \<sqsubseteq> a"
  using glb_lub_subtyping_order_correct
  by fast+

lemma subtyping_to_type_lub:
  shows
    "L, K, C \<turnstile> b \<sqsubseteq> a \<Longrightarrow> L, K, C \<turnstile> a \<leftarrow> a \<squnion> b"
proof (induct rule: subtyping.inducts)
  case (subty_tfun K t2 t1 u1 u2)
  then show ?case
    by (simp add: glb_tfun type_lub_type_glb_commut(1) type_lub_type_glb_order_correct)
next
  case (subty_trecord L K C ts1 ts2 s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.lub_trecord)  
  qed (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth, auto)+
next
  case (subty_tsum L K C ts1 ts2)
  then show ?case
    by (simp add: list_all2_conv_all_nth list_all3_conv_all_nth lub_tsum sup.absorb_iff1)
qed (auto intro: type_lub_type_glb.intros)

lemma subtyping_to_type_glb:
  shows
    "L, K, C \<turnstile> b \<sqsubseteq> a \<Longrightarrow> L, K, C \<turnstile> b \<leftarrow> a \<sqinter> b"
proof (induct rule: subtyping.induct)
case (subty_tfun K t2 t1 u1 u2)
  then show ?case 
    by (simp add: subty_tfun.hyps(2) glb_tfun subtyping_to_type_lub type_lub_type_glb_commut(2))
next
  case (subty_trecord L K C ts1 ts2 s1 s2)
  then show ?case
  proof (rule_tac type_lub_type_glb.glb_trecord)
  qed (clarsimp simp add: list_all2_conv_all_nth list_all3_conv_all_nth, auto)+
next
  case (subty_tsum L K C ts1 ts2)
  then show ?case
    by (simp add: glb_tsum inf.absorb2 list_all2_conv_all_nth list_all3_conv_all_nth)
qed (auto intro: type_lub_type_glb.intros)

theorem type_glb_type_lub_subtyping_equivalent:
  shows
    "L, K, C \<turnstile> a \<leftarrow> a \<squnion> b \<longleftrightarrow> L, K, C \<turnstile> b \<sqsubseteq> a"
    "L, K, C \<turnstile> b \<leftarrow> a \<sqinter> b \<longleftrightarrow> L, K, C \<turnstile> b \<sqsubseteq> a"
  using subtyping_to_type_lub type_lub_type_glb_to_subtyping subtyping_to_type_glb by blast+

end