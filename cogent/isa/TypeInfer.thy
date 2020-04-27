theory TypeInfer
  imports Cogent
begin

fun zipWith :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list" where
  "zipWith f [] [] = []"
| "zipWith f (a # as) (b # bs) = f a b # zipWith f as bs"

definition countPlus :: "('a :: plus) list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixl "\<oplus>" 75) where
  "xs \<oplus> ys \<equiv> zipWith (+) xs ys"

lemma countPlus_simps[simp]:
  "countPlus [] [] = []"
  "countPlus (x # xs) (y # ys) = (x+y) # (xs \<oplus> ys)"
  by (simp add: countPlus_def)+

definition countMax :: "('a :: sup) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "countMax xs ys \<equiv> zipWith sup xs ys"

lemma countMax_simps[simp]:
  "countMax [] [] = []"
  "countMax (x # xs) (y # ys) = (sup x y) # (countMax xs ys)"
  by (simp add: countMax_def)+




definition droppable :: "kind env \<Rightarrow> type \<Rightarrow> bool" where
  "droppable K t \<equiv> D \<in> kinding_fn K t"


definition is_used :: "kind env \<Rightarrow> type \<Rightarrow> ('a :: {zero, one, order}) \<Rightarrow> bool" where
  "is_used K t c \<equiv> (c = 1) \<or> (c > 1 \<and> droppable K t)"


(*
\<Gamma> is input.
C is output.
The expression is input.
For synthesising, the type is output.
For checking, the type is input.

Not that C being output means that in an assumption, C should be a variable.
If you want to enforce a structure on C, you have to use an equality so it can do computation.
*)
inductive tyinf_synth :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> nat list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<down> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_check :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> nat list \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _ , _ \<turnstile>\<up> _ : _" [30,0,0,0,0,20] 60)
      and tyinf_synth_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> kind env \<Rightarrow> type list \<Rightarrow> nat list \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
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
                  ; K \<turnstile> TRecord ts s :\<kappa> k
                  ; S \<in> k
                  ; f < length ts
                  ; snd (snd (ts ! f)) = Present
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Member e f : fst (snd (ts ! f))"

| tyinf_put    : "\<lbrakk> \<Xi>, K, \<Gamma>, C1 \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TRecord ts s
                  ; sigil_perm s \<noteq> Some ReadOnly
                  ; f < length ts
                  ; ts ! f = (n, t, taken)
                  ; K \<turnstile> t :\<kappa> k
                  ; D \<in> k \<or> taken = Taken
                  ; \<Xi>, K, \<Gamma>, C2 \<turnstile>\<up> e' : t
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C1 \<oplus> C2 \<turnstile>\<down> Put e f e' : TRecord (ts[f := (n,t,Present)]) s"

| tyinf_prim   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* args : map TPrim ts
                  ; prim_op_type oper = (ts,t)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Prim oper args : TPrim t"

| tyinf_struct : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down>* es : ts
                  ; ts = ts' \<^cancel>\<open>FIXME: remove ts'\<close>
                  ; distinct ns
                  ; vs = zip ns (map (\<lambda>t. (t,Present)) ts)
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> Struct ns ts' es : TRecord vs Unboxed"

(* checking *)

| tyinf_cast   : "\<lbrakk> \<Xi>, K, \<Gamma>, C \<turnstile>\<down> e : \<tau>1
                  ; \<tau>1 = TPrim (Num nt)
                  ; upcast_valid nt nt'
                  \<rbrakk> \<Longrightarrow> \<Xi>, K, \<Gamma>, C \<turnstile>\<up> Cast nm e : TPrim (Num nt')"

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
                  ; K \<turnstile> t :\<kappa> k
                  ; S \<in> k \<or> taken = Taken
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



lemma zip_map2_simps:
  "zip [] (map f []) = []"
  "zip (x # xs) (map f (y # ys)) = (x, f y) # zip xs (map f ys)"
  by simp+




definition
  abbreviatedType1 :: " Cogent.type"
where
  "abbreviatedType1 \<equiv> TRecord [(''b'', (TPrim (Num U8), Present)), (''a'', (TPrim (Num U32), Present))] Unboxed"

lemmas abbreviated_type_defs[intro!] =
  abbreviatedType1_def

definition
  foo_type :: " Cogent.kind list \<times>  Cogent.type \<times>  Cogent.type"
where
  "foo_type \<equiv> ([], (abbreviatedType1, abbreviatedType1))"

definition
  foo :: "string Cogent.expr"
where
  "foo \<equiv> Take (Var 0) 0 (Take (Var 1) 1 (Struct [''b'',''a''] [TPrim (Num U8), TPrim (Num U32)] [Var 2, Var 0]))"

ML \<open>
  fun typinfer_tac (ctxt : Proof.context) : tactic =
    REPEAT_FIRST (resolve_tac ctxt @{thms tyinf_safe_intros} ORELSE' force_tac (ctxt addsimps @{thms kinding_simps}))
\<close>

schematic_goal ty1: "\<Xi>, [], [fst (snd foo_type)], (?C :: nat list) \<turnstile>\<up> foo : snd (snd foo_type)"
  unfolding foo_def foo_type_def abbreviatedType1_def
  apply clarsimp
  apply (tactic \<open>typinfer_tac @{context}\<close>)
  done

thm ty1[simplified]

end
