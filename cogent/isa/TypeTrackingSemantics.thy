(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypeTrackingSemantics imports
  TypeTrackingTyping
  UpdateSemantics
begin

context update_sem begin

inductive u_tt_sem_pres :: "('f \<Rightarrow> poly_type)
                          \<Rightarrow> ('f,'a,'l) uabsfuns 
                          \<Rightarrow> ('f,'a,'l) uval env
                          \<Rightarrow> kind env
                          \<Rightarrow> tree_ctx
                          \<Rightarrow> type
                          \<Rightarrow> ('f,'a,'l) store \<times> 'f expr 
                          \<Rightarrow> ('f,'a,'l) store \<times> ('f,'a,'l) uval
                          \<Rightarrow> bool"  ("_, _, _, _, _, _ T\<turnstile> _ \<Down>! _" [30,0,0,0,0,20] 60)
where 
  u_tt_sem_pres_default : "\<lbrakk> \<not> composite_anormal_expr x
                           ; \<xi> , \<gamma> \<turnstile> (\<sigma>, x) \<Down>! st
                           ; \<Xi>, K, snd \<Gamma> \<turnstile> x : \<tau>
                           ; \<exists>rs ws. matches_ptrs \<Xi> \<sigma> \<gamma> (snd \<Gamma>) rs ws
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! st"

| u_tt_sem_pres_let     : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t] \<Gamma>2 
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a')
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st 
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Let a b) \<Down>! st" 

| u_tt_sem_pres_letbang : "\<lbrakk> ttsplit_bang is sps K \<Gamma> [] \<Gamma>1 [Some t] \<Gamma>2
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, t T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', a') 
                           ; \<Xi>, \<xi> , (a' # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', b) \<Down>! st 
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, LetBang vs a b) \<Down>! st"

| u_tt_sem_pres_case_m  : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t v rs)
                           ; \<Xi>, \<xi> , (v # \<gamma>),K,  \<Gamma>3, \<tau> T\<turnstile> (\<sigma>', m) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_case_nm : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [typ1] \<Gamma>3 [typ2] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TSum ts T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', USum t' v rs)
                           ; t' \<noteq> t
                           ; \<Xi>, \<xi> , (USum t' v [x \<leftarrow> rs. fst x \<noteq> t] # \<gamma>), K, \<Gamma>4, \<tau> T\<turnstile> (\<sigma>', n) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Case x t m n) \<Down>! st"

| u_tt_sem_pres_if      : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [] \<Gamma>2
                           ; ttsplit_triv \<Gamma>2 [] \<Gamma>3 [] \<Gamma>4
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TPrim Bool T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPrim (LBool b))
                           ; \<Xi>, \<xi> , \<gamma>, K, (if b then \<Gamma>3 else \<Gamma>4), \<tau> T\<turnstile> (\<sigma>', if b then t else e) \<Down>! st
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, If x t e) \<Down>! st" 

| u_tt_sem_pres_take    : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_fs Writable)] \<Gamma>2 
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts Writable T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UPtr p rp)
                           ; \<sigma>' p = Some (URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # UPtr p rp # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st 
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_take_ub : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some f_ty, Some (TRecord tak_ts Unboxed)] \<Gamma>2 
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TRecord ts Unboxed T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', URecord fs)
                           ; \<Xi>, \<xi> , (fst (fs ! f) # URecord fs # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st 
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! st"

| u_tt_sem_pres_split   : "\<lbrakk> ttsplit K \<Gamma> sps [] \<Gamma>1 [Some t, Some u] \<Gamma>2 
                           ; \<Xi>, \<xi> , \<gamma>, K, \<Gamma>1, TProduct t u T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', UProduct a b)
                           ; \<Xi>, \<xi> , (a # b # \<gamma>), K, \<Gamma>2, \<tau> T\<turnstile> (\<sigma>', e) \<Down>! st 
                           \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Split x e) \<Down>! st"


theorem intermediate_preservation: 
assumes "proc_ctx_wellformed \<Xi>"
and     "\<Xi>, \<sigma> \<turnstile> \<gamma> matches (snd \<Gamma>) \<langle>r, w\<rangle>"
and     "\<xi> matches-u \<Xi>"
shows   "\<lbrakk> \<xi>, \<gamma> \<turnstile>  (\<sigma>, e) \<Down>! (\<sigma>', v)
         ; \<Xi>, [], \<Gamma> T\<turnstile> e : \<tau> 
         \<rbrakk> \<Longrightarrow> \<Xi>, \<xi> , \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, e) \<Down>! (\<sigma>', v)"
and     "\<lbrakk> \<xi>, \<gamma> \<turnstile>* (\<sigma>, es) \<Down>! (\<sigma>', vs)
         ; \<Xi>, [], (snd \<Gamma>) \<turnstile>* es : \<tau>s'
         \<rbrakk> \<Longrightarrow> True"
using assms proof (induct "(\<sigma>, e)"        "(\<sigma>', v )" 
                      and "(\<sigma>, es)" "(\<sigma>', vs)" 
                      arbitrary:  e   \<tau>   \<Gamma> r w v  \<sigma>' \<sigma>
                             and  es  \<tau>s' \<Gamma> r w vs \<sigma>' \<sigma>
                      rule: u_sem_u_sem_all.inducts)

  case u_sem_let show ?case using u_sem_let.prems u_sem_let.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_let)
     apply (rule u_sem_let.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_let.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule(1) u_sem_let.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next 

  case u_sem_letbang show ?case using u_sem_letbang.prems u_sem_letbang.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_bang_imp_split_bang)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split_bang', clarsimp)
    apply (erule u_tt_sem_pres_letbang)
     apply (rule u_sem_letbang.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_letbang.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (frule(2) escapable_no_readers(1))
    apply (erule(1) u_sem_letbang.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(1) matches_ptrs_frame, blast)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (rule frame_noalias_matches_ptrs(1), simp+, blast)
      apply (rule frame_noalias_matches_ptrs(2), simp+, blast)
     apply auto[1]
    apply assumption
    done

next

  case u_sem_split show ?case using u_sem_split.prems u_sem_split.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule u_tt_sem_pres_split)
     apply (rule u_sem_split.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_split.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule u_t_productE)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (erule(1) u_sem_split.hyps(4))
     apply simp
      apply (rule matches_ptrs_some, simp, rule matches_ptrs_some, assumption)
            apply (erule(2) matches_ptrs_frame)
           apply blast+
    done

next

  note if_split[split del]
  case u_sem_if show ?case using u_sem_if.prems u_sem_if.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_if)
     apply (rule u_sem_if.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_if.hyps(1)]
        , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (rule u_sem_if.hyps(4), simp split: if_split, assumption)
     apply (simp split: if_split, erule(2) matches_ptrs_frame)
     apply blast
    apply assumption
    done

next

  case u_sem_case_m show ?case using u_sem_case_m.prems u_sem_case_m.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_case_m)
     apply (rule u_sem_case_m.hyps(2), simp+)[1]
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_case_m.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (erule u_t_sumE, clarsimp)
    apply (drule(1) distinct_fst[rotated 1], simp, simp)
    apply (erule(1) u_sem_case_m.hyps(4))
     apply simp
     apply (erule matches_ptrs_some)
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply simp
    done

next

  case u_sem_case_nm show ?case using u_sem_case_nm.prems u_sem_case_nm.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (erule(1) u_tt_sem_pres_case_nm)
      apply (rule u_sem_case_nm.hyps(2), simp+)[1]
     apply assumption
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_case_nm.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply (clarsimp simp: ttsplit_triv_def)
    apply (erule u_t_sumE, clarsimp)
    apply (erule(1) u_sem_case_nm.hyps(5))
     apply simp
     apply (rule matches_ptrs_some)
         apply (erule sum_downcast_u[rotated -1])
         apply (rule, assumption, auto)[1]
        apply (erule(2) matches_ptrs_frame)
        apply (drule(1) frame_noalias_matches_ptrs(2), blast, blast)
       apply (force dest: frame_noalias_matches_ptrs(1))
      apply (force dest!: frame_noalias_matches_ptrs(2))
     apply blast
    apply assumption
    done

next
  case (u_sem_take \<xi> \<gamma> \<sigma> x \<sigma>'' p r' fs f e)

  show ?case
    using u_sem_take.prems(1)
  proof (cases rule: ttyping.cases)
    case (ttyping_take ijs t\<Gamma>3 t ts taken s t\<Gamma>4 k)

    obtain \<Gamma>1 \<Gamma>2
      where "[] \<turnstile> snd \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
        and snd_t\<Gamma>3_is: "snd t\<Gamma>3 = [] @ \<Gamma>1"
        and snd_t\<Gamma>4_is: "snd t\<Gamma>4 = [Some t, Some (TRecord (ts[f := (t, taken)]) s)] @ \<Gamma>2"
      using ttsplit_imp_split ttyping_take by blast
    moreover then obtain r1 w1 r2 w2
      where matches1: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>1 \<langle>r1, w1\<rangle>"
        and matches2: "\<Xi>, \<sigma> \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
        and r_as_un: "r = r1 \<union> r2"
        and w_as_un: "w = w1 \<union> w2"
        and w1_w2_disjoint: "w1 \<inter> w2 = {}"
      using matches_ptrs_split' u_sem_take.prems(3) by blast
    moreover then have
      w1_r2_noalias: "w1 \<inter> r2 = {}"
      and w2_r1_noalias: "w2 \<inter> r1 = {}"
      using matches_ptrs_noalias u_sem_take.prems(3) by blast+

    have "\<Xi>, [], \<Gamma>1 \<turnstile> x : TRecord ts s"
      using snd_t\<Gamma>3_is ttyping_imp_typing ttyping_take by fastforce
    then obtain r1' w1'
      where uptr_p_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord ts s \<langle>r1', w1'\<rangle>"
        and r1'_sub: "r1' \<subseteq> r1"
        and frame1: "frame \<sigma> w1 \<sigma>'' w1'"
      using preservation(1)[where \<tau>s=Nil, simplified]
        u_sem_take.prems(2,4) matches1 u_sem_take.hyps(1)
      by blast

    have matches2_under_\<sigma>'': "\<Xi>, \<sigma>'' \<turnstile> \<gamma> matches \<Gamma>2 \<langle>r2, w2\<rangle>"
      using matches2 frame1 matches_ptrs_frame w1_w2_disjoint w1_r2_noalias
      by blast

    obtain w1'' fs'
      where uptr_p_elim_lemmas:
        "w1' = insert p w1''"
        "\<Xi>, \<sigma>'' \<turnstile>* fs' :ur ts \<langle>r1', w1''\<rangle>"
        "\<sigma>'' p = Some (URecord fs')"
        "r' = RRecord (map (\<lambda>(a, b). type_repr a) ts)"
        "s = Writable"
        "p \<notin> w1''"
        "p \<notin> r1'"
      using uptr_p_under_\<sigma>''
      by (auto simp add: ttyping_take)
    then have t_wellformed: "[] \<turnstile> t wellformed"
      using uval_typing_record_nth' ttyping_take
      by auto
    then obtain rf wf r1a w1a
      where ut_fs_at_f: "\<Xi>, \<sigma>'' \<turnstile> fst (fs' ! f) :u t \<langle>rf, wf\<rangle>"
        and ut_fs_taken_f: "\<Xi>, \<sigma>'' \<turnstile>* fs' :ur ts[f := (t, True)] \<langle>r1a, w1a\<rangle>"
        and r1'_is: "r1' = rf \<union> r1a"
        and w1''_is: "w1'' = wf \<union> w1a"
        and "wf \<inter> w1a = {}"
      using uval_typing_record_take uptr_p_elim_lemmas ttyping_take t_wellformed
      by blast
    then have uval_fs_f: "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) :u t \<langle>rf, wf\<rangle>"
      using u_sem_take.hyps uptr_p_elim_lemmas ut_fs_at_f by auto

    have disjointness_lemmas:
      "({p} \<union> wf \<union> w1a) \<inter> w2 = {}"
      "({p} \<union> wf \<union> w1a) \<inter> r2 = {}"
      "(rf \<union> r1a) \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (wf \<union> w1a) = {}"
      "{p} \<inter> (rf \<union> r1a) = {}"
      "wf \<inter> w1a = {}"
      "w2 \<inter> (rf \<union> r1a) = {}"
      using frame_noalias_matches_ptrs(1)[OF frame1 matches2 w1_w2_disjoint]
        frame_noalias_matches_ptrs(2)[OF frame1 matches2 w1_r2_noalias]
        r1'_is  w1''_is uptr_p_elim_lemmas
            apply (force+)[2]
      using uptr_p_elim_lemmas uval_typing_pointers_noalias(2) r1'_is  w1''_is
          apply metis
      using uptr_p_elim_lemmas u_t_p_rec_w w1''_is r1'_is
         apply (blast+)[2]
      using \<open>wf \<inter> w1a = {}\<close>
       apply assumption
      using r1'_is r1'_sub w2_r1_noalias
      apply blast
      done

    have "\<Xi>, \<xi>, fst (fs ! f) # UPtr p r' # \<gamma>, [], t\<Gamma>4, \<tau> T\<turnstile> (\<sigma>'', e) \<Down>! (\<sigma>', v)"
    proof (cases taken)
      case True

      show ?thesis
        using u_sem_take.prems ttyping_take
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> (r1a \<union> r2), wf \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "\<Xi>, \<sigma>'' \<turnstile>* fs :ur ts[f := (t, taken)] \<langle>r1a, w1a\<rangle>"
            using True u_sem_take.hyps uptr_p_elim_lemmas ut_fs_taken_f by auto
          moreover have "r' = RRecord (map (type_repr \<circ> fst) (ts[f := (t, taken)]))"
            using uptr_p_elim_lemmas ttyping_take
            by (simp add: case_prod_beta' list_helper map_update)
          ultimately show "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (t, taken)]) s \<langle>r1a, insert p w1a\<rangle>"
            using u_sem_take.hyps uptr_p_elim_lemmas uptr_p_under_\<sigma>'' ut_fs_taken_f r1'_is w1''_is
            by (fastforce
                simp add: uptr_p_elim_lemmas ttyping_take map_update
                intro!: u_t_p_rec_w' distinct_list_update)
        qed (force simp add: uval_fs_f)+
      qed simp+
    next
      case False
      then have wf_empty: "wf = {}"
        using shareable_not_writable(1) ut_fs_at_f ttyping_take
        by blast

      show ?thesis
        using u_sem_take.prems ttyping_take uval_fs_f
      proof (intro u_sem_take.hyps(5))
        show "\<Xi>, \<sigma>'' \<turnstile> fst (fs ! f) # UPtr p r' # \<gamma> matches snd t\<Gamma>4 \<langle>rf \<union> ((rf \<union> r1a) \<union> r2), {} \<union> (insert p w1a \<union> w2)\<rangle>"
          using ut_fs_at_f matches2_under_\<sigma>'' disjointness_lemmas wf_empty
        proof (simp only: snd_t\<Gamma>4_is append_Cons append.left_neutral, intro matches_ptrs_some[OF _ matches_ptrs_some])
          have "ts[f := (t, False)] = ts"
            by (simp add: list_helper ttyping_take)
          thus "\<Xi>, \<sigma>'' \<turnstile> UPtr p r' :u TRecord (ts[f := (t, taken)]) s \<langle>rf \<union> r1a, insert p w1a\<rangle>"
            using uptr_p_elim_lemmas wf_empty r1'_is uptr_p_under_\<sigma>'' w1''_is False by auto
        qed (force simp add: uval_fs_f[simplified wf_empty])+
      qed simp+
    qed
    moreover have "\<Xi>, \<xi>, \<gamma>, [], t\<Gamma>3, TRecord ts s T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>'', UPtr p r')"
      using u_sem_take.hyps(2) u_sem_take.prems ttyping_take matches1 snd_t\<Gamma>3_is by auto
    ultimately show "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, Take x f e) \<Down>! (\<sigma>', v)"
      using ttyping_take u_sem_take.hyps uptr_p_elim_lemmas
      by (slowsimp intro!: u_tt_sem_pres_take)
  qed (simp add: composite_anormal_expr_def)
next

  case u_sem_take_ub show ?case using u_sem_take_ub.prems u_sem_take_ub.hyps(1, 3)
    apply -
    apply (erule ttyping.cases, simp_all)
     apply (auto simp: composite_anormal_expr_def)[1]
    apply (frule ttsplit_imp_split)
    apply (frule matches_ptrs_noalias)
    apply clarsimp
    apply (frule(1) matches_ptrs_split', clarsimp)
    apply (frule(2) preservation(1)[where \<tau>s=Nil, simplified, OF refl, OF _ _ _ u_sem_take_ub.hyps(1)]
     , erule ttyping_eq_typing[THEN iffD2, OF exI])
    apply clarsimp
    apply (erule u_t_recE, simp_all)
    apply (erule u_tt_sem_pres_take_ub)
     apply (rule u_sem_take_ub.hyps(2), simp+)[1]
    apply (frule(2) frame_noalias_matches_ptrs)
    apply (frule(1) frame_noalias_matches_ptrs(2), blast)
    apply (frule(1) uval_typing_record_take, force, simp)
    apply (elim conjE exE )
    apply (frule(2) matches_ptrs_frame, blast)
    apply (simp, erule disjE)
     apply (clarsimp)
     apply (frule(2) shareable_not_writable(1))
     apply simp
     apply (erule(1) u_sem_take_ub.hyps)
      apply simp
      apply (case_tac taken)
       apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
               apply (simp)
              apply (force intro!: u_t_struct simp: map_update)
             apply (simp)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (clarsimp)
      apply (rule pointerset_helper_matches_ptrs)
        apply (rule matches_ptrs_some [OF _ matches_ptrs_some])
                apply (simp)
               apply (force intro!: u_t_struct simp: list_helper)
              apply (simp)
             apply (blast)
            apply (blast)
           apply (blast)
          apply (blast)
         apply (blast)
        apply (blast)
       apply (blast)
      apply (blast)
    apply (clarsimp)
  apply (erule(1) u_sem_take_ub.hyps)
   apply simp
   apply (rule matches_ptrs_some [OF _ matches_ptrs_some], assumption, erule(1) u_t_struct)
         apply blast+
   done

next

  case u_sem_abs_app show ?case using u_sem_abs_app.prems u_sem_abs_app.hyps(5)
      UpdateSemantics.u_sem_abs_app[OF u_sem_abs_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done

next

  case u_sem_app show ?case using u_sem_app.prems u_sem_app.hyps(5)
      UpdateSemantics.u_sem_app[OF u_sem_app.hyps(1, 3, 5)]
    apply -
    apply (rule u_tt_sem_pres_default, simp add: composite_anormal_expr_def)
      apply simp
     apply (auto dest: ttyping_imp_typing)
    done

qed  (auto intro!: u_tt_sem_pres_default
           intro: u_sem_u_sem_all.intros
           simp: composite_anormal_expr_def
           dest: ttyping_imp_typing)+

lemma u_tt_sem_pres_imp_u_sem:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)
    \<Longrightarrow> \<xi>, \<gamma> \<turnstile> (\<sigma>, x) \<Down>! (\<sigma>', uv)"
  by (induct rule: u_tt_sem_pres.induct, auto intro: u_sem_u_sem_all.intros)

end


context update_sem begin

lemma matches_ptrs_replicate_None:
  "length \<gamma> = n \<Longrightarrow> \<Xi>, \<sigma>' \<turnstile> \<gamma> matches replicate n None \<langle>{}, {}\<rangle>"
  by (hypsubst_thin, induct \<gamma>, auto intro: matches_ptrs.intros)

lemma u_tt_sem_pres_type_wellformed:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> \<forall>t. Some t \<in> set (snd \<Gamma>) \<longrightarrow> K \<turnstile>  t wellformed"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: ttsplit_imp_split ttsplit_bang_imp_split_bang
      dest: split_bang_type_wellformed split_type_wellformed typing_to_kinding_env)

lemma u_tt_sem_pres_type_wellformed2:
  "\<lbrakk> \<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x) \<rbrakk>
    \<Longrightarrow> K \<turnstile>  \<tau> wellformed"
  by (induct rule: u_tt_sem_pres.induct,
    auto dest!: typing_to_kinding)

lemma u_tt_sem_pres_preservation:
  "\<Xi>, \<xi>, \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> st \<Down>! st' \<Longrightarrow> K = [] \<Longrightarrow>
    proc_ctx_wellformed \<Xi> \<Longrightarrow> \<xi> matches-u \<Xi> \<Longrightarrow>
    \<exists>rs ws. \<Xi>, fst st' \<turnstile> snd st' :u \<tau> \<langle>rs, ws\<rangle>"
  apply (induct rule: u_tt_sem_pres.induct, simp_all)
  apply clarsimp
  apply (frule(4) preservation(1)[where \<tau>s=Nil and K=Nil, simplified])
  apply auto
  done

lemma u_tt_sem_pres_length:
  "\<Xi>, \<xi>, \<gamma>, [], \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x)
    \<Longrightarrow> length \<gamma> = length (snd \<Gamma>)"
  by (induct rule: u_tt_sem_pres.induct,
      auto simp: ttsplit_def ttsplit_bang_def
               ttsplit_inner_conv_all_nth
               ttsplit_bang_inner_conv_all_nth
         dest: matches_ptrs_length)


lemma let_elaborate_u_tt_sem_pres:
  assumes
    "\<Xi>, \<xi> , \<gamma>, K, \<Gamma>, \<tau> T\<turnstile> (\<sigma>, a) \<Down>! (\<sigma>', x)"
    "K = []"
    "proc_ctx_wellformed \<Xi>"
    "\<xi> matches-u \<Xi>"
  shows "\<Xi>, \<xi> , \<gamma>, K, (TyTrSplit (map (map_option (\<lambda>_. TSK_L)) (snd \<Gamma>)) [] (fst \<Gamma>)
    [Some \<tau>] TyTrLeaf, snd \<Gamma>), \<tau> T\<turnstile> (\<sigma>, Let a (Var 0)) \<Down>! (\<sigma>', x)"
  using assms
proof (intro u_tt_sem_pres_let[OF ttsplitI])
  have "\<forall>i < length (snd \<Gamma>). \<forall>t. (snd \<Gamma>) ! i = Some t \<longrightarrow> K \<turnstile> t wellformed"
    using assms
    by (fastforce dest: nth_mem u_tt_sem_pres_type_wellformed)
  then show "ttsplit_inner K (map (map_option (\<lambda>_. TSK_L)) (snd \<Gamma>)) True (snd \<Gamma>) (snd \<Gamma>) (replicate (length (snd \<Gamma>)) None)"
    by (force simp add: ttsplit_inner_conv_all_nth ttsplit_inner_comp.simps)
next
  show "\<Xi>, \<xi>, x # \<gamma>, K, (TyTrLeaf, Some \<tau> # replicate (length (snd \<Gamma>)) None), \<tau> T\<turnstile> (\<sigma>', Var 0) \<Down>! (\<sigma>', x)"
    using assms
    apply (auto
        intro!: u_tt_sem_pres_default typing_var
        intro: u_sem_var[where \<gamma>="x # xs" and i=0 for x xs, simplified]
        dest: u_tt_sem_pres_type_wellformed2
        simp add: composite_anormal_expr_def empty_def weakening_def weakening_comp.simps
        list_all2_same)
    apply (frule u_tt_sem_pres_preservation, (simp+)[3])
    apply (force dest: u_tt_sem_pres_length intro: matches_ptrs_some matches_ptrs_replicate_None)
    done
qed auto

end

end
