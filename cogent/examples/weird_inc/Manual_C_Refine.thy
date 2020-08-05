theory Manual_C_Refine
  imports Weird_inc_CorresProof
begin
context Weird_inc begin

lemma inc_corres_0:
  "\<And>a a' \<sigma> s. val_rel a a' \<Longrightarrow> corres state_rel inc (inc' a') \<xi>_0 [a] \<Xi> [Some (fst (snd inc_type))] \<sigma> s "
  apply (monad_eq simp: corres_def inc'_def val_rel_simp inc_def state_rel_def heap_rel_def)
  apply (rule_tac x = \<sigma> in exI)
  apply (rule_tac x = "URecord [(UPrim (LU32 (elem_C a' + 1)), _), (UUnit, _)]" in exI)
  apply (rule conjI)
   apply (rule u_sem_take_ub)
    apply (rule u_sem_var[where \<gamma> = "[_]" and i = 0, simplified])
   apply clarsimp
   apply (rule u_sem_take_ub)
    apply (rule u_sem_var[where \<gamma> = "[_, _, _]" and i = 1, simplified])
   apply clarsimp
   apply (rule u_sem_take_ub)
    apply (rule u_sem_var[where \<gamma> = "[_, _, _, _, _]" and i = 1, simplified])
   apply clarsimp
   apply (rule u_sem_let)
    apply (rule u_sem_lit)
   apply (rule u_sem_let)
    apply (rule u_sem_prim)
    apply (rule u_sem_all_cons)
     apply (rule u_sem_var)
    apply (rule u_sem_all_cons)
     apply (rule u_sem_var)
    apply (rule u_sem_all_empty)
   apply (clarsimp simp: eval_prim_u_def)
   apply (rule u_sem_struct[where vs = "[_,_]" and xs = "[_,_]" and ts = "[TPrim (Num U32), TUnit]" , simplified])
   apply (rule u_sem_all_cons)
    apply (rule u_sem_var[where \<gamma> = "[_,_,_,_,_,_,_,_,_]" and i = 0, simplified])
   apply (rule u_sem_all_cons)
    apply (rule u_sem_var[where \<gamma> = "[_,_,_,_,_,_,_,_,_]" and i = 4, simplified])
   apply (rule u_sem_all_empty)
  apply clarsimp
  done

end (* of context *)
end