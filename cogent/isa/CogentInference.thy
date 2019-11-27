theory CogentInference
  imports Util
begin


datatype num_type = U8 | U16 | U32 | U64

datatype prim_type = Num num_type | Bool (* | String *)
                                  
datatype prim_op
  = Plus num_type
  | Minus num_type
  | Times num_type
  | Divide num_type
  | Mod num_type
  | Not | And | Or
  | Gt num_type
  | Lt num_type
  | Le num_type
  | Ge num_type
  | Eq prim_type
  | NEq prim_type
  | BitAnd num_type
  | BitOr num_type
  | BitXor num_type
  | LShift num_type
  | RShift num_type
  | Complement num_type


datatype usage_tag = Used | Unused

instantiation usage_tag :: "{boolean_algebra, linorder}"
begin

fun uminus_usage_tag :: "usage_tag \<Rightarrow> usage_tag" where
  "uminus_usage_tag Used   = Unused"
| "uminus_usage_tag Unused = Used"

definition top_usage_tag :: usage_tag where
  "top_usage_tag \<equiv> Unused"
declare top_usage_tag_def[simp]

definition bot_usage_tag :: usage_tag where
  "bot_usage_tag \<equiv> Used"
declare bot_usage_tag_def[simp]

fun inf_usage_tag :: "usage_tag \<Rightarrow> usage_tag \<Rightarrow> usage_tag" where
  "inf_usage_tag Used   _      = Used"
| "inf_usage_tag Unused Used   = Used"
| "inf_usage_tag Unused Unused = Unused"

fun sup_usage_tag :: "usage_tag \<Rightarrow> usage_tag \<Rightarrow> usage_tag" where
  "sup_usage_tag Unused _      = Unused"
| "sup_usage_tag Used   Unused = Unused"
| "sup_usage_tag Used   Used   = Used"

fun less_eq_usage_tag :: "usage_tag \<Rightarrow> usage_tag \<Rightarrow> bool" where
  "less_eq_usage_tag _      Unused = True"
| "less_eq_usage_tag Used   Used   = True"
| "less_eq_usage_tag Unused Used   = False"

fun less_usage_tag :: "usage_tag \<Rightarrow> usage_tag \<Rightarrow> bool" where
  "less_usage_tag _      Used   = False"
| "less_usage_tag Unused Unused = False"
| "less_usage_tag Used   Unused = True"

definition minus_usage_tag :: "usage_tag \<Rightarrow> usage_tag \<Rightarrow> usage_tag" where
  "minus_usage_tag x y \<equiv> inf x (- y)"
declare minus_usage_tag_def[simp]

instance proof
  fix x y z :: usage_tag

  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y; clarsimp)
  show "x \<le> x"
    by (cases x; clarsimp)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z; clarsimp)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y; clarsimp)
  show "inf x y \<le> x" "inf x y \<le> y"
    by (cases x; cases y; clarsimp)+
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z"
    by (cases x; cases y; cases z; clarsimp)
  show "x \<le> sup x y"
    by (cases x; cases y; clarsimp)
  show "y \<le> sup x y"
    by (cases x; cases y; clarsimp)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x"
    by (cases x; cases y; cases z; clarsimp)
  show "bot \<le> x" "x \<le> top"
    by (cases x; simp)+
  show "sup x (inf y z) = inf (sup x y) (sup x z)"
    by (cases x; cases y; cases z; simp)
  show
    "inf x (- x) = bot"
    "sup x (- x) = top"
    by (cases x; simp)+
  show "x - y = inf x (- y)"
    by simp
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y; simp)
qed
end

type_synonym name = string
type_synonym index = nat
type_synonym row_var = nat

datatype type = TVar index
              | TFun type type
              | TPrim prim_type
              | TProduct type type
              | TUnit
              | TUnknown index
              | TVariant "(name \<times> type \<times> usage_tag) list" "row_var option"


datatype lit = LBool bool
             | LNat nat

fun abs :: "num_type \<Rightarrow> nat" where
"abs U8 = 256"
| "abs U16 = 512"
| "abs U32 = 1024"
| "abs U64 = 2048"


fun subst_ty :: "type list \<Rightarrow> type \<Rightarrow> type" where
  "subst_ty \<delta> (TVar i)          = (if i < length \<delta> then \<delta> ! i else TVar i)"
| "subst_ty \<delta> (TFun a b)        = TFun (subst_ty \<delta> a) (subst_ty \<delta> b)"
| "subst_ty \<delta> (TPrim p)         = TPrim p"
| "subst_ty \<delta> (TProduct t u)    = TProduct (subst_ty \<delta> t) (subst_ty \<delta> u)"
| "subst_ty \<delta> (TUnit)           = TUnit"
| "subst_ty \<delta> (TUnknown i)      = TUnknown i"
| "subst_ty \<delta> (TVariant Ks \<alpha>)   = TVariant (map (\<lambda>(nm, t, u). (nm, subst_ty \<delta> t, u)) Ks) \<alpha>"


fun max_type_var :: "type \<Rightarrow> nat" where
  "max_type_var (TVar i)          = i"
| "max_type_var (TFun a b)        = max (max_type_var a) (max_type_var b)"
| "max_type_var (TPrim p)         = 0"
| "max_type_var (TProduct t u)    = max (max_type_var t) (max_type_var u)"
| "max_type_var (TUnit)           = 0"
| "max_type_var (TUnknown i)      = 0"
| "max_type_var (TVariant Ks \<alpha>)   = Max (set (map (max_type_var \<circ> fst \<circ> snd) Ks))"


datatype constraint =
  CtConj constraint constraint
  | CtIBound lit type
  | CtEq type type
  | CtSub type type
  | CtTop 
  | CtBot
  | CtShare type
  | CtDrop type
  | CtExhausted type

type_synonym axm_set = "constraint set"


fun map_types_ct :: "(type \<Rightarrow> type) \<Rightarrow> constraint \<Rightarrow> constraint" where
  "map_types_ct f (CtConj a b)    = CtConj (map_types_ct f a) (map_types_ct f b)"
| "map_types_ct f (CtIBound l t)  = CtIBound l (f t)"
| "map_types_ct f (CtEq a b)      = CtEq (f a) (f b)"
| "map_types_ct f (CtSub a b)     = CtSub (f a) (f b)"
| "map_types_ct f (CtTop)         = CtTop"
| "map_types_ct f (CtBot)         = CtBot"
| "map_types_ct f (CtShare t)     = CtShare (f t)"
| "map_types_ct f (CtDrop t)      = CtDrop (f t)"
| "map_types_ct f (CtExhausted t) = CtExhausted (f t)"

definition subst_ct :: "type list \<Rightarrow> constraint \<Rightarrow> constraint" where
  "subst_ct \<delta> \<equiv> map_types_ct (subst_ty \<delta>)"


inductive known_ty :: "type \<Rightarrow> bool" where
known_tvar:
  "known_ty (TVar n)"
| known_tfun:
  "\<lbrakk> known_ty t1
   ; known_ty t2
   \<rbrakk> \<Longrightarrow> known_ty (TFun t1 t2)"
| known_tprim:
  "known_ty (TPrim pt)"
| known_tproduct:
  "\<lbrakk> known_ty t1
   ; known_ty t2
   \<rbrakk> \<Longrightarrow> known_ty (TProduct t1 t2)"
| known_tunit:
  "known_ty TUnit"
| known_tvariant_nil:
  "known_ty (TVariant [] None)"
| known_tvariant_cons:
  "\<lbrakk> known_ty ((fst \<circ> snd) K)
   ; known_ty (TVariant Ks None)
   \<rbrakk> \<Longrightarrow> known_ty (TVariant (K # Ks) None)"

inductive_cases known_tfunE: "known_ty (TFun t1 t2)"
inductive_cases known_tproductE: "known_ty (TProduct t1 t2)"

inductive known_ct :: "constraint \<Rightarrow> bool" where
known_ctconj:
  "\<lbrakk> known_ct C1
   ; known_ct C2
   \<rbrakk> \<Longrightarrow> known_ct (CtConj C1 C2)"
| known_ctibound:
  "known_ty \<tau> \<Longrightarrow> known_ct (CtIBound l \<tau>)"
| known_cteq:
  "\<lbrakk> known_ty \<tau>
   ; known_ty \<rho>
   \<rbrakk> \<Longrightarrow> known_ct (CtEq \<tau> \<rho>)" 
| known_ctsub:
  "\<lbrakk> known_ty \<tau>
   ; known_ty \<rho>
   \<rbrakk> \<Longrightarrow> known_ct (CtSub \<tau> \<rho>)"
| known_cttop:
  "known_ct CtTop"
| known_ctbot:
  "known_ct CtBot"
| known_ctshare:
  "known_ty \<tau> \<Longrightarrow> known_ct (CtShare \<tau>)"
| known_ctdrop:
  "known_ty \<tau> \<Longrightarrow> known_ct (CtDrop \<tau>)"
| known_ctexhausted:
  "known_ty \<tau> \<Longrightarrow> known_ct (CtExhausted \<tau>)"

inductive_cases known_ctconjE: "known_ct (CtConj C1 C2)"
inductive_cases known_cteqE: "known_ct (CtEq C1 C2)"
inductive_cases known_ctsubE: "known_ct (CtSub C1 C2)"


locale type_infer =
  fixes type_of :: "'fnname \<Rightarrow> constraint \<times> type"
  assumes type_of_known: "type_of e = (C, \<rho>) \<Longrightarrow> known_ct C \<and> known_ty \<rho>"
begin

datatype 'f expr = Var index
                 | TypeApp 'f "type list"
                 | Prim prim_op "'f expr list"
                 | App "'f expr" "'f expr"
                 | Unit
                 | Lit lit
                 | Cast num_type "'f expr"
                 | Let "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type

type_synonym cg_ctx = "(type \<times> nat) list"
type_synonym ctx = "(type option) list"


definition empty :: "nat \<Rightarrow> ctx" where
  "empty \<equiv> (\<lambda> x. replicate x None)"

lemma empty_none:
  "i < n \<Longrightarrow> (empty n) ! i = None"
  by (simp add: local.empty_def)


definition singleton :: "nat \<Rightarrow> index \<Rightarrow> type \<Rightarrow> ctx" where
  "singleton n i t \<equiv> (empty n)[i := Some t]"

lemma singleton_len:
  "length (singleton n i t) = n"
  by (simp add: empty_def singleton_def)

lemma singleton_some:
  "i < n \<Longrightarrow> (singleton n i t) ! i = Some t"
  by (simp add: empty_def singleton_def)

lemma singleton_none:
  "j < n \<Longrightarrow> j \<noteq> i \<Longrightarrow> (singleton n i t) ! j = None"
  by (simp add: empty_def singleton_def)


section {* Algorithmic Context Join (Fig 3.5) *}
inductive alg_ctx_jn :: "cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> cg_ctx \<Rightarrow> constraint \<Rightarrow> bool"
  ("_ \<Join> _ \<leadsto> _ | _" [30,0,0,30] 60) where
  alg_ctx_jn: 
  "\<lbrakk> map fst G = map fst G'
   ; list_all3 (\<lambda>m g g'. m = max (snd g) (snd g')) M G G'
   ; list_all3 (\<lambda>g2 g m. g2 = (fst g, m)) G2 G M
   ; C = List.map2 (\<lambda>g g'. if (snd g) = (snd g') then CtTop else CtDrop (fst g)) G G'
   ; C2 = foldr CtConj C CtTop
   \<rbrakk> \<Longrightarrow> G \<Join> G' \<leadsto> G2 | C2"

lemma alg_ctx_jn_length:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
  shows "length G1 = length G1'"
   and  "length G1 = length G2"
  using assms by (metis (no_types, lifting) alg_ctx_jn.simps list_all3_conv_all_nth)+

lemma alg_ctx_jn_type_same:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1"
  shows "fst (G1 ! i) = fst (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_nondec_1:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1" 
  shows "snd (G1 ! i) \<le> snd (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_nondec_2:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
  shows "snd (G1' ! i) \<le> snd (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_max:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
  shows "snd (G2 ! i) = max (snd (G1 ! i)) (snd (G1' ! i))"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_same:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
    and "snd (G1 ! i) = snd (G1' ! i)"
  shows "snd (G2 ! i) = snd (G1 ! i)"
  using assms alg_ctx_jn_type_used_max by auto


section {* Constraint Semantics (Fig 3.6) *}
inductive constraint_sem :: "axm_set \<Rightarrow> constraint \<Rightarrow> bool"
          ("_ \<turnstile> _" [40, 40] 60) where
ct_sem_share:
  "CtShare \<rho> \<in> A \<Longrightarrow> A \<turnstile> CtShare \<rho>"
| ct_sem_drop:
  "CtDrop \<rho> \<in> A \<Longrightarrow> A \<turnstile> CtDrop \<rho>"
| ct_sem_conj:
  "\<lbrakk> A \<turnstile> C1
   ; A \<turnstile> C2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtConj C1 C2"
| ct_sem_int:
  "m < abs n \<Longrightarrow> A \<turnstile> CtIBound (LNat m) (TPrim (Num n))"
| ct_sem_top:
  "A \<turnstile> CtTop"
| ct_sem_refl:
  "A \<turnstile> CtEq \<tau> \<tau>"
| ct_sem_equal:
  "A \<turnstile> CtEq \<tau> \<rho> \<Longrightarrow> A \<turnstile> CtSub \<tau> \<rho>"
| ct_sem_fun:
  "\<lbrakk> A \<turnstile> CtSub \<rho>1 \<tau>1 
   ; A \<turnstile> CtSub \<tau>2 \<rho>2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) (TFun \<rho>1 \<rho>2)"
| ct_sem_funS:
  "A \<turnstile> CtShare (TFun \<tau>1 \<tau>2)"
| ct_sem_funD:
  "A \<turnstile> CtDrop (TFun \<tau>1 \<tau>2)"
| ct_sem_primS:
  "A \<turnstile> CtShare (TPrim pt)"
| ct_sem_primD:
  "A \<turnstile> CtDrop (TPrim pt)"

inductive_cases ct_sem_conjE: "A \<turnstile> CtConj C1 C2"
inductive_cases ct_sem_intE: "A \<turnstile> CtIBound (LNat m) (TPrim pt)"
inductive_cases ct_sem_funE: "A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) (TFun \<rho>1 \<rho>2)"

lemma ct_sem_conj_iff: "A \<turnstile> CtConj C1 C2 \<longleftrightarrow> A \<turnstile> C1 \<and> A \<turnstile> C2"
  using ct_sem_conj ct_sem_conjE by blast

lemma ct_sem_conj_fold: 
  assumes"A \<turnstile> foldr CtConj Cs CtTop"
    and "i < length Cs"
  shows "A \<turnstile> (Cs ! i)"
  using assms
proof (induct Cs arbitrary: i)
  case (Cons a Cs)
  then show ?case
  proof -
    have "A \<turnstile> ((CtConj a) \<circ> (foldr CtConj Cs)) CtTop"
      using Cons.prems by auto
    then show ?thesis
      using Cons.prems Cons.hyps One_nat_def Suc_less_eq Suc_pred comp_apply ct_sem_conjE 
      by (metis length_Cons less_nat_zero_code linorder_neqE_nat nth_Cons')
  qed
qed (simp)

lemma ct_sem_eq_iff: "A \<turnstile> CtEq \<tau> \<rho> \<longleftrightarrow> \<tau> = \<rho>"
  using constraint_sem.cases ct_sem_refl by fastforce

lemma ct_sem_int_iff: "A \<turnstile> CtIBound (LNat m) (TPrim pt) \<longleftrightarrow> (\<exists>n. pt = Num n \<and> m < abs n)"
  using ct_sem_intE ct_sem_int by blast

lemma ct_sem_int_exI: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<exists>pt. \<tau> = TPrim pt"
proof (induct \<tau>)
qed (fastforce intro: constraint_sem.cases)+

lemma ct_sem_int_imp: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<exists>n. \<tau> = TPrim (Num n) \<and> m < abs n"
  using ct_sem_int_iff ct_sem_int_exI by metis

lemma ct_sem_int_not_bool: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<tau> \<noteq> TPrim Bool"
  using ct_sem_intE by blast


section {* Context relations (Fig 3.2) *}
inductive ctx_split_comp :: "axm_set \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none  : "ctx_split_comp K None None None"
| left  : "ctx_split_comp K (Some \<tau>) (Some \<tau>) None"
| right : "ctx_split_comp K (Some \<tau>) None (Some \<tau>)"
| share : "\<lbrakk> A \<turnstile> CtShare \<tau> \<rbrakk> \<Longrightarrow> ctx_split_comp K (Some \<tau>) (Some \<tau>) (Some \<tau>)"

definition context_splitting :: "axm_set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"
           ("_ \<turnstile> _ \<leadsto> _ \<box> _" [30,0,0,30] 60) where
  "context_splitting K \<equiv> list_all3 (ctx_split_comp K)"

lemma context_splitting_none:
  assumes "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    and "i < length \<Gamma>"
    and "\<Gamma> ! i = None"
  shows "\<Gamma>1 ! i = None \<and> \<Gamma>2 ! i = None"
  using assms ctx_split_comp.simps 
  by (clarsimp simp add: context_splitting_def list_all3_conv_all_nth; auto)

inductive weakening_comp :: "axm_set \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none : "weakening_comp K None None"
| keep : "weakening_comp K (Some \<tau>) (Some \<tau>)"
| drop : "\<lbrakk> A \<turnstile> CtDrop \<tau> \<rbrakk> \<Longrightarrow> weakening_comp K (Some \<tau>) None"

definition weakening :: "axm_set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" 
           ("_ \<turnstile> _ \<leadsto>w _" [40,0,40] 60) where
  "weakening K \<equiv> list_all2 (weakening_comp K)"

lemma weak_keep_refl: "weakening_comp K (Some \<tau>) (Some \<rho>) \<Longrightarrow> \<tau> = \<rho>"
  using weakening_comp.cases by auto


section {* Typing Rules (Fig 3.3) *}
inductive typing :: "axm_set \<Rightarrow> ctx \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> bool"
          ("_ \<ddagger> _ \<turnstile> _ : _" [40,0,0,40] 60) where
typing_var:
  "\<lbrakk> A \<turnstile> \<Gamma>  \<leadsto>w singleton (length \<Gamma>) i \<tau>
   ; i < length \<Gamma>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> (Var i) : \<tau>"
| typing_sig:
  "A \<ddagger> \<Gamma> \<turnstile> e : \<tau>' \<Longrightarrow> A \<turnstile> CtSub \<tau>' \<tau> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Sig e \<tau> : \<tau>"
| typing_app:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : (TFun \<tau>1 \<tau>2)
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : \<tau>1  
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> App e1 e2 : \<tau>2"
| typing_tapp:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)
   ; type_of name = (C, \<tau>)
   ; A \<turnstile> subst_ct ts C
   ; \<tau>' = subst_ty ts \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> TypeApp name ts : \<tau>'"
| typing_let:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : \<tau>1
   ; A \<ddagger> ((Some \<tau>1) # \<Gamma>2) \<turnstile> e2 : \<tau>2
  \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Let e1 e2 : \<tau>2"
| typing_if:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : TPrim Bool
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : \<tau>
   ; A \<ddagger> \<Gamma>2 \<turnstile> e3 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> If e1 e2 e3 : \<tau>"
| typing_iop:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; T \<noteq> TPrim Bool
   ; x \<in> {Plus nt, Minus nt, Times nt, Divide nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : T
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : T
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2] : T"
| typing_cop:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; T \<noteq> TPrim Bool
   ; x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : T 
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : T
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2]: \<tau>"
| typing_bop:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; x \<in> {BitAnd nt, BitOr nt}
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : TPrim Bool
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : TPrim Bool
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Prim x [e1, e2] : \<tau>"
| typing_ilit:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)
   ; l < abs n
   ; \<tau> = TPrim (Num n)
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Lit (LNat l) : \<tau>"
| typing_blit:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)
   ; \<tau> = TPrim Bool
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Lit (LBool l) : \<tau>"

lemma typing_sig_refl:
  "A \<ddagger> \<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Sig e \<tau> : \<tau>"
  using ct_sem_equal ct_sem_refl type_infer_axioms typing_sig by blast


section {* Elementary Constraint Generation Rules (Fig 3.4) *}
inductive constraint_gen_elab :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> 'fnname expr \<Rightarrow> bool"
  ("_,_ \<turnstile> _ : _ \<leadsto> _,_ | _ | _" [30,0,0,0,0,0,0,30] 60) where
cg_var1: 
  "\<lbrakk> G!i = (\<rho>,0)
   ; i < length G 
   ; G' = G[i := (\<rho>,1)] 
   ; C = CtSub \<rho> \<tau>
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C | Sig (Var i) \<tau>"
| cg_var2: 
  "\<lbrakk> G!i = (\<rho>,n) 
   ; i < length G
   ; n > 0 
   ; G' = G[i := (\<rho>,Suc n)] 
   ; C = CtConj (CtSub \<rho> \<tau>) (CtShare \<rho>) 
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> Var i : \<tau> \<leadsto> G',n | C | Sig (Var i) \<tau>"
| cg_sig: 
  "\<lbrakk> G1,n1 \<turnstile> e : \<tau>' \<leadsto> G2,n2 | C | e'
   ; C' = CtConj C (CtSub \<tau>' \<tau>)
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> (Sig e \<tau>') : \<tau> \<leadsto> G2,n2 | C' | Sig (Sig e' \<tau>') \<tau>"
| cg_app:
  "\<lbrakk> \<alpha> = TUnknown n1
   ; G1,(Suc n1) \<turnstile> e1 : TFun \<alpha> \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj C1 C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> App e1 e2 : \<tau> \<leadsto> G3,n3 | C3 | Sig (App e1' e2') \<tau>"
| cg_let:
  "\<lbrakk> \<alpha> = TUnknown n1
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'
   ; ((\<alpha>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 | e2' 
   ; if m = 0 then C3 = CtDrop \<alpha> else C3 = CtTop
   ; C4 = CtConj (CtConj C1 C2) C3
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Let e1 e2 : \<tau> \<leadsto> G3,n3 | C4 | Sig (Let e1' e2') \<tau>"
| cg_blit:
  "C = CtEq \<tau> (TPrim Bool) \<Longrightarrow> G,n \<turnstile> Lit (LBool l) : \<tau> \<leadsto> G,n | C | Sig (Lit (LBool l)) \<tau>"
| cg_ilit:
  "C = CtIBound (LNat m) \<tau> \<Longrightarrow> G,n \<turnstile> Lit (LNat m) : \<tau> \<leadsto> G,n | C | Sig (Lit (LNat m)) \<tau>"
| cg_if:
  "\<lbrakk> G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'
   ; G3 \<Join> G3' \<leadsto> G4 | C4 
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> If e1 e2 e3 : \<tau> \<leadsto> G4,n4 | C5 | Sig (If e1' e2' e3') \<tau>"
| cg_iop:
  "\<lbrakk> x \<in> {Plus nt, Minus nt, Times nt, Divide nt}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; C5 = CtConj (CtConj (CtIBound (LNat 0) \<tau>) C1) C2
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C5 | Sig (Prim x [e1', e2']) \<tau>"
| cg_cop:
  "\<lbrakk> \<alpha> = TUnknown n1
   ; x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}
   ; G1,(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<alpha> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj (CtConj (CtConj (CtIBound (LNat 0) \<alpha>) (CtEq \<tau> (TPrim Bool))) C1) C2 
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C3 | Sig (Prim x [e1', e2']) \<tau>"
| cg_bop:
  "\<lbrakk> x \<in> {BitAnd nt, BitOr nt}
   ; G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'
   ; G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'
   ; C3 = CtConj (CtConj (CtEq \<tau> (TPrim Bool)) C1) C2
  \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Prim x [e1, e2] : \<tau> \<leadsto> G3,n3 | C3 | Sig (Prim x [e1', e2']) \<tau>"
| cg_tapp:
  "\<lbrakk> type_of name = (C, \<rho>)
   (* make fresh unknown \<beta>s for each variable past those we are substituting into the type *)
   ; m = Suc (max_type_var \<rho>) - length ts
   ; \<beta>s = map (TUnknown \<circ> (+) (Suc n1)) [0..<m]
   ; \<rho>' = subst_ty (ts @ \<beta>s) \<rho>
   ; C' = subst_ct (ts @ \<beta>s) C
   ; C2 = CtConj (CtSub \<rho>' \<tau>) C'
   ; n' = n + m
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> TypeApp name ts : \<tau> \<leadsto> G,n' | C2 | Sig (TypeApp name (ts @ \<beta>s)) \<tau>"

lemma cg_num_fresh_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "n \<le> n'"
  using assms by (induct rule: constraint_gen_elab.inducts) force+

lemma cg_ctx_length:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "length G = length G'"
  using assms
proof (induct rule: constraint_gen_elab.inducts)
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using alg_ctx_jn_length by auto
qed (simp+)

lemma cg_ctx_idx_size:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "i < length G"
  shows "i < length G'"
  using assms cg_ctx_length by auto

lemma cg_ctx_type_same:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "\<And>i. i < length G \<Longrightarrow> fst (G ! i) = fst (G' ! i)"
  using assms
proof (induct rule: constraint_gen_elab.inducts)
  case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
    by (metis fst_conv nth_list_update_eq nth_list_update_neq)
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    by (metis length_list_update map_fst_update nth_map)
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
    by (metis Suc_mono cg_ctx_length length_Cons nth_Cons_Suc)
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using cg_ctx_length alg_ctx_jn_type_same by auto
next
qed (auto simp add: cg_ctx_length)+

lemma cg_ctx_type_used_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "i < length G"
  shows "snd (G ! i) \<le> snd (G' ! i)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
    by (metis le0 nth_list_update_neq order_refl snd_conv) 
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    by (metis Suc_n_not_le_n nat_le_linear nth_list_update_eq nth_list_update_neq snd_conv)
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
    using cg_ctx_length by fastforce
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    have "(\<And>i. i < length ((\<alpha>, 0) # G2) \<Longrightarrow> snd (((\<alpha>, 0) # G2) ! i) \<le> snd (((\<alpha>, m) # G3) ! i))
                 \<Longrightarrow> (\<And>i. i < length G2 \<Longrightarrow> snd (G2 ! i) \<le> snd (G3 ! i))"
      using nth_Cons_Suc by force
    then show ?thesis
      using cg_let cg_ctx_length le_trans by fastforce
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using cg_ctx_length alg_ctx_jn_type_used_nondec_1 le_trans by fastforce
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
    using cg_ctx_length by (metis dec_induct le_SucI)
next
case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
    using cg_ctx_length le_trans by fastforce
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
    using cg_ctx_length by fastforce
qed (blast)+


section {* Assignment Definition *}
(* when we are assigning an unknown type a type, the assigned type should not contain any
   unknown types itself *)
fun assign_app_ty :: "(nat \<Rightarrow> type) \<Rightarrow> type \<Rightarrow> type" where
  "assign_app_ty S (TVar n)          = TVar n"
| "assign_app_ty S (TFun t1 t2)      = TFun (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_ty S (TPrim pt)        = TPrim pt"
| "assign_app_ty S (TProduct t1 t2)  = TProduct (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_ty S TUnit             = TUnit"
| "assign_app_ty S (TUnknown n)      = S n"


fun assign_app_expr :: "(nat \<Rightarrow> type) \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where
  "assign_app_expr S (Var n)            = Var n" 
| "assign_app_expr S (TypeApp e ts)     = TypeApp e (map (assign_app_ty S) ts)"
| "assign_app_expr S (Prim prim_op ts)  = Prim prim_op (map (assign_app_expr S) ts)"
| "assign_app_expr S (App e1 e2)        = App (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S Unit               = Unit"
| "assign_app_expr S (Lit l)            = Lit l"
| "assign_app_expr S (Cast nt e)        = Cast nt (assign_app_expr S e)"
| "assign_app_expr S (Let e1 e2)        = Let (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S (If e1 e2 e3)      = If (assign_app_expr S e1) (assign_app_expr S e2) (assign_app_expr S e3)"
| "assign_app_expr S (Sig e t)          = Sig (assign_app_expr S e) (assign_app_ty S t)"


fun "assign_app_constr" :: "(nat \<Rightarrow> type) \<Rightarrow> constraint \<Rightarrow> constraint" where
  "assign_app_constr S (CtConj c1 c2) = CtConj (assign_app_constr S c1) (assign_app_constr S c2)"
| "assign_app_constr S (CtIBound l t) = CtIBound l (assign_app_ty S t)"
| "assign_app_constr S (CtEq t1 t2) = CtEq (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S (CtSub t1 t2) = CtSub (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S CtTop = CtTop"
| "assign_app_constr S CtBot = CtBot"
| "assign_app_constr S (CtShare t) = CtShare (assign_app_ty S t)"
| "assign_app_constr S (CtDrop t) = CtDrop (assign_app_ty S t)"

definition assign_app_ctx :: "(nat \<Rightarrow> type) \<Rightarrow> ctx \<Rightarrow> ctx" where
  "assign_app_ctx S G = map (map_option (assign_app_ty S)) G"

lemma assign_app_ctx_none_iff:
  assumes "i < length G"
  shows "assign_app_ctx S G ! i = None \<longleftrightarrow> G ! i = None"
  using assms assign_app_ctx_def by simp

lemma assign_app_ctx_nth:
  assumes
    "i < length G"
  shows "assign_app_ctx S G ! i = map_option (assign_app_ty S) (G ! i)"
  using assms assign_app_ctx_def by simp

lemma assign_app_ctx_len:
  "length (assign_app_ctx S G) = length G"
  by (induct G arbitrary: S; simp add: assign_app_ctx_def)

lemma assign_app_ty_subst_ty_commute: 
  assumes "known_ty \<tau>"
  shows "assign_app_ty S (subst_ty xs \<tau>) = subst_ty (map (assign_app_ty S) xs) \<tau>"
  using assms 
proof (induct \<tau>)
  case (known_tfun t1 t2)
  then show ?case
    using known_tfunE by auto
next
  case (known_tproduct t1 t2)
  then show ?case
    using known_tproductE by auto
next
  case known_tvariant_nil
  then show ?case sorry
next
  case (known_tvariant_cons K Ks)
  then show ?case sorry
qed (simp)+ 

lemma assign_app_constr_subst_ct_commute: 
  assumes "known_ct C"
  shows "assign_app_constr S (subst_ct xs C) = subst_ct (map (assign_app_ty S) xs) C"
  using assms
proof (induct C)
  case (known_ctexhausted \<tau>)
  then show ?case sorry
qed (auto simp add: subst_ct_def assign_app_ty_subst_ty_commute)+


lemma ct_sem_assign_conj_foldr:
  assumes "A \<turnstile> assign_app_constr S (foldr CtConj Cs CtTop)"
    and  "i < length Cs" 
  shows "A \<turnstile> assign_app_constr S (Cs ! i)"
  using assms
proof (induct Cs arbitrary: i)
  case (Cons a Cs)
  then show ?case
  proof -
    have constr_sem_rearrange: "A \<turnstile> assign_app_constr S (CtConj a ((foldr CtConj Cs) CtTop))"
      using Cons.prems by auto
    then show ?thesis
    proof (cases "i = 0")
      case True
      then show ?thesis
        using constr_sem_rearrange ct_sem_conj_iff by force
    next
      case False
      then show ?thesis
        using Cons.hyps Cons.prems assign_app_constr.simps constr_sem_rearrange ct_sem_conj_iff
        by auto
    qed
  qed
qed (simp)

lemma alg_ctx_jn_type_used_diff:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
    and "snd (G1 ! i) \<noteq> snd (G1' ! i)"
    and "A \<turnstile> assign_app_constr S C" 
  shows "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
  using assms
proof -
  let ?Cs = "List.map2 (\<lambda>x y. if snd x = snd y then CtTop else CtDrop (fst x)) G1 G1'"
  have "length G1' = length G1"
    using alg_ctx_jn_length assms by auto
  moreover have "length ?Cs = min (length G1) (length G1')"
    by simp
  moreover have i_size: "i < length ?Cs"
    using calculation assms by simp
  moreover have "A \<turnstile> assign_app_constr S (foldr CtConj ?Cs CtTop)"
    using assms by (simp add: alg_ctx_jn.simps; metis map2_def)
  moreover have "A \<turnstile> assign_app_constr S (?Cs ! i)"
    using calculation ct_sem_assign_conj_foldr by blast
  moreover then have "A \<turnstile> assign_app_constr S ((\<lambda>x y. if snd x = snd y then CtTop else CtDrop (fst x)) (G1 ! i) (G1' ! i))"
    using i_size by (clarsimp simp add: map2_nth)
  ultimately show ?thesis
    using alg_ctx_jn_type_same assms by auto
qed

section {* split_used (Lemma 3.1) *}
(* Free Variables *)
fun fv' :: "nat \<Rightarrow> 'f expr \<Rightarrow> index set" where
  fv'_var:      "fv' n (Var i) = (if i \<ge> n then {i - n} else {})"
| fv'_typeapp:  "fv' n (TypeApp f ts) = {}"
| fv'_prim:     "fv' n (Prim prim_op es) = (\<Union>x\<in>set es. fv' n x)"
| fv'_app:      "fv' n (App e1 e2) = (fv' n e1) \<union> (fv' n e2)"
| fv'_unit:     "fv' n Unit = {}"
| fv'_lit:      "fv' n (Lit l) = {}"
| fv'_cast:     "fv' n (Cast nt e) = fv' n e"
| fv'_let:      "fv' n (Let e1 e2) = (fv' n e1) \<union> (fv' (Suc n) e2)"
| fv'_if:       "fv' n (If e1 e2 e3) = (fv' n e1) \<union> (fv' n e2) \<union> (fv' n e3)"
| fv'_sig:      "fv' n (Sig e t) = fv' n e"

lemmas fv'_induct = fv'.induct[case_names fv'_var fv'_typeapp fv'_prim fv'_app fv'_unit fv'_lit 
                                          fv'_cast fv'_let fv'_if fv'_sig]

abbreviation fv :: "'s expr \<Rightarrow> index set" where
  "fv t \<equiv> fv' 0 t" 

lemma i_fv'_suc_iff_suc_i_fv':
  "i \<in> fv' (Suc m) e \<longleftrightarrow> Suc i \<in> fv' m e"
proof (induct m e arbitrary: i rule: fv'_induct)
  case (fv'_var n i)
  then show ?case
    by (force split: if_splits)
qed auto

lemma fv'_suc_eq_minus_fv':
  "fv' (Suc m) e = image (\<lambda>x. x - 1) (fv' m e - {0})"
proof -
  have "\<forall>i \<in> fv' (Suc m) e.  i \<in> image (\<lambda>x. x - 1) (fv' m e - {0})"
    using i_fv'_suc_iff_suc_i_fv'
    by (metis Diff_empty Diff_insert0 diff_Suc_1 image_iff insertE insert_Diff nat.simps(3))
  moreover have "\<forall>i \<in> image (\<lambda>x. x - 1) (fv' m e - {0}). Suc i \<in> (fv' m e - {0})"
    by simp
  moreover have "\<forall>i \<in> image (\<lambda>x. x - 1) (fv' m e - {0}). i \<in> fv' (Suc m) e"
    by (simp add: i_fv'_suc_iff_suc_i_fv')
  ultimately show ?thesis
    by blast
qed


definition ctx_restrict :: "cg_ctx \<Rightarrow> index set \<Rightarrow> ctx" (infixr "\<bar>" 60) where
"(G\<bar>ns) = List.map2 (\<lambda>g i. (if i \<in> ns then Some (fst g) else None)) G [0..<length G]"

lemma ctx_restrict_len:
  "length (G\<bar>ns) = length G"
  using ctx_restrict_def by simp

lemma ctx_restrict_nth_none:
  assumes "i \<notin> ns"
    and "i < length G"
  shows "(G\<bar>ns) ! i = None"
  using assms
proof -
  let ?P="\<lambda>g i. (if i \<in> ns then Some (fst g) else None)"
  let ?r="[0..<length G]"
  have "G\<bar>ns = List.map2 ?P G ?r"
    using ctx_restrict_def by simp
  moreover have "\<forall>i < length (G\<bar>ns). ?P (G ! i) (?r ! i) = ((G\<bar>ns) ! i)"
    using ctx_restrict_def by (rule_tac xs="G" in map2_imp_fun_nth; simp)
  then show ?thesis
    using assms ctx_restrict_len by auto
qed
     
lemma ctx_restrict_nth_some:
  assumes "i \<in> ns"
    and "i < length G"
  shows "(G\<bar>ns) ! i = Some (fst (G ! i))"
  using assms
proof -
  let ?P="\<lambda>g i. (if i \<in> ns then Some (fst g) else None)"
  let ?r="[0..<length G]"
  have "G\<bar>ns = List.map2 ?P G ?r"
    using ctx_restrict_def by simp
  moreover have "\<forall>i < length (G\<bar>ns). ?P (G ! i) (?r ! i) = ((G\<bar>ns) ! i)"
    using ctx_restrict_def by (rule_tac xs="G" in map2_imp_fun_nth; simp)
  then show ?thesis
    using assms ctx_restrict_len by auto
qed

lemma ctx_restrict_nth_none_iff:
  assumes "i < length G"
  shows "(G\<bar>ns) ! i = None \<longleftrightarrow> i \<notin> ns"
  using assms ctx_restrict_nth_none ctx_restrict_nth_some by auto

lemma ctx_restrict_nth_some_iff:
  assumes "i < length G"
  shows "(G\<bar>ns) ! i \<noteq> None \<longleftrightarrow> i \<in> ns"
  using assms ctx_restrict_nth_none_iff by auto

lemma ctx_restrict_un_elem_same:
  assumes "i \<notin> ns'"
    and "i < length G"
  shows "(G\<bar>ns) ! i = (G\<bar>ns \<union> ns') ! i"
  by (metis Un_iff assms(1) assms(2) ctx_restrict_nth_none ctx_restrict_nth_some)

lemma assign_app_ctx_restrict_some:
  assumes "i \<in> ns"
    and "i < length G"
  shows "assign_app_ctx S (G\<bar>ns) ! i = Some (assign_app_ty S (fst (G ! i)))"
  by (simp add: assign_app_ctx_def assms ctx_restrict_len ctx_restrict_nth_some)

lemma assign_app_ctx_restrict_some_val:
  assumes "i < length G"
    and "assign_app_ctx S (G\<bar>ns) ! i = Some y"
  shows "y = assign_app_ty S (fst (G ! i))"
  using assign_app_ctx_none_iff assign_app_ctx_restrict_some assms ctx_restrict_len 
    ctx_restrict_nth_none by (metis option.distinct(1) option.sel)

lemma assign_app_ctx_restrict_some_ex:
  assumes "i < length G"
    and "assign_app_ctx S (G\<bar>ns) ! i = Some y"
  shows "i \<in> ns"
  using assign_app_ctx_nth assms ctx_restrict_len ctx_restrict_nth_none ctx_restrict_nth_some 
  by fastforce

lemma cg_gen_fv_elem_size:
  assumes
    "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    "i \<in> fv' m e"
  shows "i < length G1"
proof -
  have "\<And>x e1 e2. fv (Prim x [e1, e2]) = fv e1 \<union> fv e2"
    by (simp add: Un_commute)
  moreover have fv_prim_disj: "\<And>e1 e2 x. i \<in> fv (Prim x [e1, e2]) \<Longrightarrow> i \<in> fv e1 \<or> i \<in> fv e2"
    by auto          
  show ?thesis
    using assms
  proof (induct arbitrary: i m rule: constraint_gen_elab.induct)
    case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
    then show ?case
      by (force simp add: i_fv'_suc_iff_suc_i_fv' cg_ctx_length)
  qed (auto simp add: cg_ctx_length split: if_splits)
qed

lemma cg_gen_output_type_used_nonzero:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
  shows "snd (G2 ! i) > 0"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
    using cg_ctx_length cg_ctx_type_used_nondec gt_or_eq_0 not_le cg_gen_fv_elem_size fv'_app
    by (metis Un_iff)
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using fv'_let cg_let.prems by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size cg_let cg_let.hyps
        by (metis Suc_mono gt_or_eq_0 length_Cons not_le nth_Cons_Suc)
    next
      case i_in_e2                
      then show ?thesis
        using cg_let.hyps i_fv'_suc_iff_suc_i_fv' by fastforce
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"
      using cg_if.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_if.hyps alg_ctx_jn_type_used_nondec_2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size
        by (metis le_less not_le not_less0)
    next
      case i_in_e2
      then show ?thesis 
        using cg_if.hyps not_less0 alg_ctx_jn_type_used_nondec_1 cg_ctx_length cg_gen_fv_elem_size
        by (metis le_less not_le not_less0)
    next
      case i_in_e3
      then show ?thesis 
        using cg_if.hyps not_less0 alg_ctx_jn_type_used_nondec_2 cg_ctx_length cg_gen_fv_elem_size
        by (metis (full_types) neq0_conv not_le)
    qed
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_iop.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_iop.hyps cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size
        by (metis gt_or_eq_0 not_le)
    next
      case i_in_e2
      then show ?thesis
        using cg_iop.hyps cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size by simp
    qed
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_cop.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_cop.hyps cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_ctx_length
        by (metis gr_zeroI not_le)
    qed (blast intro: cg_cop.hyps)
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case 
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_bop.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_bop.hyps cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_ctx_length
        by (metis gr_zeroI not_le)
    qed (blast intro: cg_bop.hyps)
  qed
qed (simp)+

lemma cg_gen_output_type_used_inc:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
  shows "snd (G2 ! i) > snd (G1 ! i)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_app.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_app.hyps cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          constraint_gen_elab.cg_app 
        by (metis (no_types, lifting) dual_order.strict_iff_order leD)
    next
      case i_in_e2
      then show ?thesis 
        using cg_app.hyps cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          constraint_gen_elab.cg_app
        by (metis dual_order.strict_iff_order leD)
    qed
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    have i_in_e1e2: "i \<in> fv' 0 e1 \<or> i \<in> fv' (Suc 0) e2"
      using fv'_let cg_let.prems by blast
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using i_in_e1e2 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then have "snd (G1 ! i) < snd (G2 ! i)"
        using cg_let.hyps by blast
      moreover  have "snd (G2 ! i) \<le> snd (G3 ! i)"
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_let
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons nth_Cons_Suc)
      ultimately show ?thesis
        by simp
    next
      case i_in_e2
      have "snd (G1 ! i) \<le> snd (G2 ! i)"
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_let.hyps
        by (metis i_fv'_suc_iff_suc_i_fv' length_Cons not_less_eq)
      moreover have "snd (G2 ! i) < snd (G3 ! i)"
        using cg_let.hyps i_fv'_suc_iff_suc_i_fv' i_in_e2 by fastforce
      ultimately show ?thesis
        using le_less_trans by blast
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
  proof -
    have i_in_e1e2e3: "i \<in> fv e1 \<or> i \<in> fv e2 \<or> i \<in> fv e3"
      using cg_if.prems by auto
    have snd_G1_le_G2: "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e1e2e3 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_if.hyps
      by metis
    have snd_G2_le_G3: "snd (G2 ! i) \<le> snd (G3 ! i)"
      using i_in_e1e2e3 cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_if.hyps
        type_infer.cg_ctx_length type_infer_axioms by metis
    have snd_G3_le_G4: "snd (G3 ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 alg_ctx_jn_type_used_nondec_1 cg_gen_fv_elem_size cg_if.hyps 
        cg_ctx_length type_infer_axioms by metis
    have snd_G3'_le_G4: "snd (G3' ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 alg_ctx_jn_type_used_nondec_2 cg_gen_fv_elem_size cg_if.hyps 
        cg_ctx_length type_infer_axioms by metis
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"
      using i_in_e1e2e3 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_if.hyps snd_G2_le_G3 snd_G3_le_G4 by force
    next
      case i_in_e2
      then show ?thesis
        using cg_if.hyps snd_G1_le_G2 snd_G3_le_G4 by force
    next
      case i_in_e3
      then show ?thesis 
        using cg_if.hyps snd_G1_le_G2 snd_G3'_le_G4 by force
    qed
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
      using cg_iop.prems by auto
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using i_in_e1e2 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      have "snd (G2 ! i) \<le> snd (G3 ! i)"      
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_iop.hyps
        by metis
      then show ?thesis
        using cg_iop.hyps i_in_e1 by fastforce
    next
      case i_in_e2
      have "snd (G1 ! i) \<le> snd (G2 ! i)"
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_iop.hyps
        by metis
      then show ?thesis
        using cg_iop.hyps i_in_e2 by fastforce
    qed
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
      using cg_cop.prems by auto
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using i_in_e1e2 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      have "snd (G2 ! i) \<le> snd (G3 ! i)" 
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_cop.hyps
        by metis
      then show ?thesis
        using i_in_e1 cg_cop.hyps by force
    next
      case i_in_e2
      have "snd (G1 ! i) \<le> snd (G2 ! i)"      
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_cop.hyps
        by metis
      then show ?thesis
        using i_in_e2 cg_cop.hyps by force    
    qed
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case 
  proof -
    have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
      using cg_bop.prems by auto
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using i_in_e1e2 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      have "snd (G2 ! i) \<le> snd (G3 ! i)"      
        using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_bop.hyps
        by metis
      then show ?thesis
        using i_in_e1 cg_bop.hyps by force
    next
      case i_in_e2
        have "snd (G1 ! i) \<le> snd (G2 ! i)"      
          using i_in_e1e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_bop.hyps
          by metis
        then show ?thesis
          using i_in_e2 cg_bop.hyps by force
      qed
  qed 
qed (simp)+

lemma cg_gen_output_type_used_diff:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
  shows "snd (G2 ! i) \<noteq> snd (G1 ! i)"
  using assms cg_gen_output_type_used_inc by fastforce

lemma cg_gen_type_used_nonzero_imp_share:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
      and "snd (G1 ! i) > 0"
      and "\<rho> = fst (G1 ! i)"
      and "A \<turnstile> C1"
    shows "A \<turnstile> CtShare \<rho>"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    using ct_sem_conj_iff by simp
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C e' C' \<tau>)
  then show ?case
    using ct_sem_conjE by force
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_app.prems fv'_app by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_app ct_sem_conjE by blast
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_type_same cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size
          cg_app by (metis neq0_conv not_le ct_sem_conjE)
    qed
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using cg_let.prems fv'_let by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis using 
          cg_let ct_sem_conj_iff by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          ct_sem_conjE i_fv'_suc_iff_suc_i_fv' cg_let
        by (metis Suc_less_eq gt_or_eq_0 leD length_Cons cg_let nth_Cons_Suc)
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"
      using cg_if.prems fv'_if by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE by (metis (no_types, lifting) gt_or_eq_0 leD)
    next
      case i_in_e3
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE by (metis (no_types, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_iop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
      using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
        cg_iop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_iop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_cop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -    
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using cg_bop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
qed (simp)+

lemma cg_gen_output_type_unused_same:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<notin> fv(e)"
      and "i < length G1"
  shows "snd (G2 ! i) = snd (G1 ! i)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
    using cg_ctx_length i_fv'_suc_iff_suc_i_fv' fv'_let
    by (metis Un_iff length_Cons less_eq_Suc_le not_less nth_Cons_Suc)
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case     
    using alg_ctx_jn_type_used_max cg_ctx_idx_size by simp
qed (simp add: cg_ctx_idx_size)+

lemma cg_assign_type_used_nonzero_imp_share:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
      and "snd (G1 ! i) > 0"
      and "\<rho> = fst (G1 ! i)"
      and "A \<turnstile> assign_app_constr S C1"
      and "\<forall>i. known_ty (S i)"
    shows "A \<turnstile> CtShare (assign_app_ty S \<rho>)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
    using ct_sem_conj_iff by simp
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C e' C' \<tau>)
  then show ?case
    using ct_sem_conjE  by (simp, blast)
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
      using fv'_app cg_app.prems by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_app ct_sem_conjE  by (simp, blast)
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_type_same cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size
          cg_app assign_app_constr.simps by (metis (no_types, lifting) gt_or_eq_0 leD ct_sem_conjE)
    qed
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using fv'_let cg_let.prems by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_let ct_sem_conj_iff assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          ct_sem_conjE i_fv'_suc_iff_suc_i_fv' cg_let assign_app_constr.simps
        by (metis (no_types, lifting) Suc_less_eq gr0I leD length_Cons nth_Cons_Suc)
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"  
      using fv'_if cg_if.prems by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE assign_app_constr.simps by (metis (no_types, lifting) leD not_gr_zero)
    next
      case i_in_e3
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE assign_app_constr.simps by (metis (no_types, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
      using cg_iop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_iop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_iop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
      using cg_cop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
      using cg_bop.prems fv'_prim by auto
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
qed (simp)+

lemma split_unionR:
  assumes "ns = ns1 \<union> ns2"
    and "\<And>i. i < length G1 \<Longrightarrow> fst (G1 ! i) = fst (G2 ! i)"
    and "A \<turnstile> assign_app_ctx S (G1\<bar>ns) \<leadsto> assign_app_ctx S (G1\<bar>ns1) \<box> assign_app_ctx S (G2\<bar>ns2)"
    and "\<forall>i\<in>I. i < length G1 \<and> i \<notin> ns"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(ns \<union> I)) \<leadsto> assign_app_ctx S (G1\<bar>ns1) \<box> assign_app_ctx S (G2\<bar>ns2 \<union> I)"
  using assms
proof -
  let ?SG1ns = "assign_app_ctx S (G1\<bar>ns)"
  let ?SG1ns' = "assign_app_ctx S (G1\<bar>(ns \<union> I))"
  let ?SG1ns1 = "assign_app_ctx S (G1\<bar>ns1)"
  let ?SG2ns2 = "assign_app_ctx S (G2\<bar>ns2)"
  let ?SG2ns2' = "assign_app_ctx S (G2\<bar>(ns2 \<union> I))"
  {
    fix j :: nat
    assume j_size: "j < length G1"
    assume j_not_in_I: "j \<notin> I"
    have "ctx_split_comp A (?SG1ns ! j) (?SG1ns1 ! j) (?SG2ns2 ! j)"
      using j_size j_not_in_I assms assign_app_ctx_len context_splitting_def ctx_restrict_len 
        list_all3_conv_all_nth by metis
    moreover have "(?SG2ns2 ! j) = (?SG2ns2' ! j)"
      using j_size j_not_in_I assign_app_ctx_len assign_app_ctx_nth assms context_splitting_def 
        ctx_restrict_len ctx_restrict_un_elem_same by (metis (full_types) list_all3_conv_all_nth)
    ultimately have "ctx_split_comp A (?SG1ns ! j) (?SG1ns1 ! j) (?SG2ns2' ! j)"
      using ctx_restrict_len ctx_restrict_un_elem_same assign_app_ctx_def type_infer_axioms
      by (metis)
    moreover have "(?SG1ns ! j) = (?SG1ns' ! j)"
      using j_size j_not_in_I assign_app_ctx_len assign_app_ctx_nth assms context_splitting_def 
        ctx_restrict_len ctx_restrict_un_elem_same by (metis (full_types))
    ultimately have "ctx_split_comp A (?SG1ns' ! j) (?SG1ns1 ! j) (?SG2ns2' ! j)"
      by auto
  }
  moreover {
    fix i :: nat
    assume i_in_I: "i \<in> I"
    have SG1ns1_none: "?SG1ns1 ! i = None"
      using i_in_I assms ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
    have "(G1\<bar>(ns \<union> I)) ! i = (G2\<bar>(ns2 \<union> I)) ! i"
      using i_in_I assign_app_ctx_len assms  context_splitting_def ctx_restrict_len 
        ctx_restrict_nth_some by (metis UnCI list_all3_conv_all_nth)
    then have "?SG1ns' ! i =  ?SG2ns2' ! i"
      using i_in_I assign_app_ctx_len assign_app_ctx_nth assms context_splitting_def 
        ctx_restrict_len by (metis list_all3_conv_all_nth)
    then have "ctx_split_comp A (?SG1ns' ! i) (?SG1ns1 ! i) (?SG2ns2' ! i)"
      using SG1ns1_none ctx_split_comp.simps by auto
  }
  ultimately show ?thesis
    using assign_app_ctx_len assms context_splitting_def ctx_restrict_len 
    by (metis (full_types) list_all3_conv_all_nth)
qed


section {* Lemma 3.1 *}
lemma split_used:
  assumes "fv e = (fv e1) \<union> (fv e2)"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<rho> \<leadsto> G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>(fv e2))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2 = "assign_app_ctx S (G2\<bar>(fv e2))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
    using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
    using G1_G2_length ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have "\<And>i. i < length G1 \<Longrightarrow> i \<notin> (fv e) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
  proof -
    fix i :: nat 
    assume i_size: "i < length G1"
    assume i_not_in_e: "i \<notin> (fv e)"
    have "(i \<notin> (fv e1)) \<and> (i \<notin> (fv e2))"
      using assms i_not_in_e by simp
    then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
      using ctx_split_comp.none
      using i_not_in_e i_size no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2_none no_i_in_e_SG1e_none by auto
  qed
  moreover have "\<And>i. i < length G1 \<Longrightarrow> i \<in> (fv e) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
  proof -
    fix i :: nat
    assume i_size: "i < length G1"
    assume i_in_e: "i \<in> (fv e)" 
    have "i \<in> (fv e1) \<or> i \<in> (fv e2)"
      using assms i_in_e by auto
    moreover have "i \<in> (fv e1) \<and> i \<notin> (fv e2) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_not_in_e2: "i \<notin> (fv e2)"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        using ctx_split_comp.left i_in_e i_in_e1 i_size no_i_in_e2_SG2e2_none ctx_restrict_len 
          ctx_restrict_nth_some assign_app_ctx_def by auto
    qed
    moreover have "i \<notin> (fv e1) \<and> i \<in> (fv e2) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_not_in_e1: "i \<notin> (fv e1)"
      assume i_in_e2: "i \<in> (fv e2)"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        using assms cg_ctx_type_same i_in_e i_in_e2_SG2e2_some i_in_e_SG1e_some i_not_in_e1 i_size
          no_i_in_e1_SG1e1_none right by auto
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> (fv e2) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2: "i \<in> (fv e2)"
      have i_type_used: "snd (G2!i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2!i)))"
        using assms i_in_e2 cg_assign_type_used_nonzero_imp_share by simp
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2 i_size G1_G2_length cg_ctx_type_same 
          ctx_restrict_len ctx_restrict_nth_some by (metis (no_types, lifting) nth_map)
      ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        using G1_G2_length i_in_e2 i_size ctx_restrict_len ctx_restrict_nth_some share assign_app_ctx_def
        by auto
    qed
    ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
      by blast
  qed
  ultimately show ?thesis
    using G1_G2_length context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed

lemma split_used_let:
  assumes "e = Let e1 e2"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "((\<tau>,m) # G2),n2 \<turnstile> e2 : \<rho> \<leadsto> ((\<tau>,m') # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>image (\<lambda>x. x-1) (fv e2 - {0}))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?SG2e2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2)"
  have fv_e: "fv e = fv e1 \<union> (image (\<lambda>x. x-1) (fv e2 - {0}))"
    using assms fv'_suc_eq_minus_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2_none: "\<And>i. i < length G1 \<Longrightarrow> Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
  proof -
    have "\<And>i. Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
      using fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' by blast
    then show "\<And>i. i < length G1 \<Longrightarrow> Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  qed
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
  proof -
    have "\<And>i. Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
      using fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' by blast
    then show "\<And>i. i < length G1 \<Longrightarrow> Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
      by (metis G1_G2_length assign_app_ctx_restrict_some fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv')
  qed
  have "\<And>i. i < length G1 \<Longrightarrow> i \<notin> (fv e) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
  proof -
    fix i :: nat 
    assume i_size: "i < length G1"
    assume i_not_in_e: "i \<notin> (fv e)"
    have "(i \<notin> (fv e1)) \<and> (i \<notin> ?dec_fv_e2)"
      using fv_e i_not_in_e by auto
    then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
      using ctx_split_comp.none fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' i_not_in_e i_size 
        no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2_none no_i_in_e_SG1e_none by metis
  qed
  moreover have "\<And>i. i < length G1 \<Longrightarrow> i \<in> (fv e) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
  proof -
    fix i :: nat
    assume i_size: "i < length G1"
    assume i_in_e: "i \<in> (fv e)" 
    have "i \<in> (fv e1) \<or> i \<in> ?dec_fv_e2"
      using assms i_in_e fv_e by blast
    moreover have "i \<in> (fv e1) \<and> i \<notin> ?dec_fv_e2 \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_not_in_e2: "i \<notin> ?dec_fv_e2"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        using ctx_split_comp.left fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' i_in_e i_in_e1 
          i_size no_i_in_e2_SG2e2_none i_in_e1_SG1e1_some i_in_e_SG1e_some by metis
    qed
    moreover have "i \<notin> (fv e1) \<and> i \<in> ?dec_fv_e2 \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_not_in_e1: "i \<notin> (fv e1)"
      assume i_in_e2: "i \<in> ?dec_fv_e2"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        by (metis G1_G2_length assign_app_ctx_restrict_some assms(2) cg_ctx_type_same i_in_e i_not_in_e1 i_size no_i_in_e1_SG1e1_none right)
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> ?dec_fv_e2 \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2: "i \<in> ?dec_fv_e2"
      have i_type_used: "snd (G2!i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2!i)))"
        using assms i_in_e2 cg_assign_type_used_nonzero_imp_share
        by (metis fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' nth_Cons_Suc)
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2 i_size G1_G2_length cg_ctx_type_same 
          ctx_restrict_len ctx_restrict_nth_some by (metis (no_types, lifting) nth_map)
      ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
        using G1_G2_length i_in_e2 i_size ctx_restrict_len ctx_restrict_nth_some share assign_app_ctx_def
        by auto
    qed
    ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
      by blast
  qed
  ultimately show ?thesis
    using G1_G2_length context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed

lemma split_used_if:
  assumes "e = If e1 e2 e3"
    and "G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'"
    and "G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2e3 = "assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2e3_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = None"
    using G1_G2_length assign_app_ctx_nth ctx_restrict_len ctx_restrict_nth_none
    by (metis assign_app_ctx_none_iff)
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = Some (assign_app_ty S (fst (G2!i)))"
    by (metis G1_G2_length assign_app_ctx_restrict_some)
  have "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
  proof -
    fix i :: nat 
    assume i_size: "i < length G1"
    assume i_not_in_e: "i \<notin> fv e"
    have "(i \<notin> fv e1) \<and> (i \<notin> fv e2 \<union> fv e3)"
      using assms i_not_in_e by simp
    then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
      using ctx_split_comp.none i_not_in_e i_size no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2e3_none 
        no_i_in_e_SG1e_none by auto
  qed
  moreover have "\<And>i. i < length G1 \<Longrightarrow> i \<in> (fv e) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
  proof -
    fix i :: nat
    assume i_size: "i < length G1"
    assume i_in_e: "i \<in> (fv e)" 
    have "i \<in> (fv e1) \<or> i \<in> (fv e2 \<union> fv e3)"
      using assms i_in_e by auto
    moreover have "i \<in> (fv e1) \<and> i \<notin> (fv e2 \<union> fv e3) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_not_in_e2e3: "i \<notin> (fv e2 \<union> fv e3)"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
        using ctx_split_comp.left i_in_e i_in_e1 i_size no_i_in_e2_SG2e2e3_none ctx_restrict_len 
          ctx_restrict_nth_some assign_app_ctx_def by auto
    qed
    moreover have "i \<notin> (fv e1) \<and> i \<in> (fv e2 \<union> fv e3) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (erule conjE)
      assume i_not_in_e1: "i \<notin> (fv e1)"
      assume i_in_e2: "i \<in> (fv e2 \<union> fv e3)"
      then show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
        by (metis assign_app_ctx_restrict_some assms(2) i_in_e i_in_e2_SG2e2_some i_not_in_e1 i_size
            no_i_in_e1_SG1e1_none type_infer.cg_ctx_type_same type_infer.right type_infer_axioms)
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> (fv e2 \<union> fv e3) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2e3: "i \<in> (fv e2 \<union> fv e3)"
      have i_type_used: "snd (G2 ! i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2 ! i)))"
        using assms i_in_e2e3 cg_assign_type_used_nonzero_imp_share by blast
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def
        by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2e3 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2e3 i_size G1_G2_length cg_ctx_type_same 
          ctx_restrict_len ctx_restrict_nth_some by (metis (no_types, lifting) nth_map)
      ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
        using G1_G2_length i_in_e2e3 i_size ctx_restrict_len ctx_restrict_nth_some share 
          i_in_e2_SG2e2_some by auto
    qed
    ultimately show "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
      by blast
  qed
  ultimately show ?thesis
    using G1_G2_length context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed 

lemma split_used_extR:
  assumes "fv e = (fv e1) \<union> (fv e2)"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<rho> \<leadsto> G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> idxs))"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2)"
    using split_used assms by blast
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2 \<union> idxs)"
    using assms by (rule_tac split_unionR; force intro: cg_ctx_type_same)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof (rule nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_len by presburger
    moreover {
      fix i :: nat
      assume i_size: "i < length G1"
      have "\<Gamma> ! i = assign_app_ctx S (G1\<bar>fv e \<union> idxs) ! i"
      proof (cases "i \<in> fv e")
        case True
        then show ?thesis
          using assign_app_ctx_restrict_some assms i_size
          by (metis (no_types, lifting) Un_iff)
      next
        case False
        then show ?thesis
        proof (cases "\<Gamma> ! i = None")
          case True
          have "i \<notin> fv e \<union> idxs"
            using assms False True by simp
          then show ?thesis
            using True assign_app_ctx_none_iff ctx_restrict_len ctx_restrict_nth_none i_size
            by (metis (no_types, lifting))
        next
          case False
          have "i \<in> fv e \<union> idxs"
            using False i_size assms by force
          then show ?thesis
            using False assign_app_ctx_restrict_some assms i_size 
            by (metis (no_types, lifting))
        qed
      qed
    }
    then show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
      using assms by presburger
  qed
  ultimately show ?thesis
    by auto
qed

lemma split_used_let_extR:
  assumes "e = Let e1 e2"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "((\<tau>,m) # G2),n2 \<turnstile> e2 : \<rho> \<leadsto> ((\<tau>,m') # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>dec_fv_e2)"
    using split_used_let assms by blast
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> idxs)"
    using assms fv'_suc_eq_minus_fv' by (rule_tac split_unionR; auto intro: cg_ctx_type_same)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof (rule nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assms ctx_restrict_len assign_app_ctx_len by presburger
    moreover { 
      fix i :: nat
      assume i_size: "i < length G1"
      have "\<Gamma> ! i = assign_app_ctx S (G1\<bar>fv e \<union> idxs) ! i"
      proof (cases "i \<in> fv e")
        case True
        then show ?thesis
          using Un_iff assign_app_ctx_restrict_some assms i_size
          by (metis (no_types, lifting))
      next
        case False
        assume i_not_in_e: "i \<notin> fv e"
        then show ?thesis
        proof (cases "\<Gamma> ! i = None")
          case True
          then have "i \<notin> fv e \<union> idxs"
            using i_not_in_e assms by simp
          then show ?thesis
            using True assign_app_ctx_none_iff ctx_restrict_len ctx_restrict_nth_none i_size
            by (metis (no_types, lifting))
        next
          case False
          then have "i \<in> fv e \<union> idxs"
            using i_size assms by auto
          then show ?thesis
            using False assign_app_ctx_restrict_some assms i_size
            by (metis (no_types, lifting))
        qed
      qed
    }
    ultimately show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
      using assms by presburger
  qed
  ultimately show ?thesis
    by auto
qed

lemma split_used_if_extR:
  assumes "e = If e1 e2 e3"
    and "G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'"
    and "G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
    using split_used_if assms by meson
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> idxs)"
    using assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof (intro nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      have "\<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
      proof (cases "i \<in> fv e")
        case True
        then show ?thesis
          using assms i_size 
          by (metis (no_types, lifting) Un_iff assign_app_ctx_restrict_some)
      next
        case False
        assume i_not_in_e: "i \<notin> fv e"
        then show ?thesis
        proof (cases "\<Gamma> ! i = None")
          case True
          have "i \<notin> fv e \<union> idxs"
            using True i_not_in_e assms by auto
          then show ?thesis
            using True assign_app_ctx_none_iff assms ctx_restrict_len
              ctx_restrict_nth_none i_size by (metis (no_types, lifting))
        next
          case False
          have "i \<in> fv e \<union> idxs"
            using False i_not_in_e assms i_size by auto 
          then show ?thesis
            using False i_size assms assign_app_ctx_restrict_some
            by (metis (no_types, lifting))
        qed
      qed
    }
    then show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
      by blast
  qed
  ultimately show ?thesis
    by auto
qed


section {* Soundness of Generation (Thm 3.2) *}
lemma cg_sound_induction:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "A \<turnstile> assign_app_constr S C" 
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G ! i)))
              else \<Gamma> ! i = None \<or>
                (\<Gamma> ! i = Some (assign_app_ty S (fst (G ! i))) \<and> A \<turnstile> assign_app_constr S (CtDrop (fst (G ! i))))"
    and "length G = length \<Gamma>"
  shows "A \<ddagger> \<Gamma> \<turnstile> (assign_app_expr S e') : (assign_app_ty S \<tau>)"
  using assms 
proof (induct arbitrary: S \<Gamma> rule: constraint_gen_elab.inducts)
case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
 proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Var i : (assign_app_ty S \<rho>)"
    proof -
      have "A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i (assign_app_ty S \<rho>)"
      proof -
        have "length \<Gamma> = length (singleton (length \<Gamma>) i (assign_app_ty S \<rho>))"
          by (simp add: singleton_len)
        moreover have "(\<And>ia. ia < length \<Gamma> \<Longrightarrow>
                        weakening_comp A (\<Gamma> ! ia) 
                        (singleton (length \<Gamma>) i (assign_app_ty S \<rho>) ! ia))"
        proof -
          have "\<Gamma> ! i = Some (assign_app_ty S (fst (G ! i)))"
            using cg_var1.hyps cg_var1.prems by fastforce
          then show "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ?thesis ia"
            using cg_var1 weakening_comp.simps
            by (case_tac "ia = i"; fastforce simp add: keep singleton_some singleton_none)
        qed
        ultimately show ?thesis
          using cg_var1.hyps cg_var1.prems weakening_def
          by (metis list_all2_all_nthI)
      qed
      then show ?thesis
        using cg_var1.prems cg_var1.hyps typing_var by auto
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S \<rho>) (assign_app_ty S \<tau>)"
      using cg_var1.prems cg_var1.hyps ct_sem_conjE assign_app_constr.simps by metis
    ultimately show ?thesis
      using typing_sig by simp
  qed
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
  proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Var i : (assign_app_ty S \<rho>)"
    proof -
      have "A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i (assign_app_ty S \<rho>)"
      proof -
        have "length \<Gamma> = length (singleton (length \<Gamma>) i (assign_app_ty S \<rho>))"
          by (simp add: singleton_len)
        moreover have "(\<And>ia. ia < length \<Gamma> \<Longrightarrow>
                        weakening_comp A (\<Gamma> ! ia) 
                        (singleton (length \<Gamma>) i (assign_app_ty S \<rho>) ! ia))"
        proof -
          have "\<Gamma> ! i = Some (assign_app_ty S (fst (G ! i)))"
            using cg_var2 by fastforce
          moreover have "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ia \<noteq> i \<Longrightarrow> 
                               singleton (length \<Gamma>) i (assign_app_ty S \<rho>) ! ia = None"
            by (simp add: singleton_none)
          moreover have "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ia \<noteq> i \<Longrightarrow> ?thesis ia"
            using assign_app_constr.simps(8) calculation cg_var2.hyps cg_var2.prems diff_zero drop 
              weakening_comp.none fv'_var by (metis leI less_nat_zero_code singletonD)
          ultimately show "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ?thesis ia"
            using cg_var2.hyps keep singleton_some by fastforce
        qed
        ultimately show ?thesis
          using cg_var2.hyps cg_var2.prems weakening_def by (metis list_all2_all_nthI)
      qed
      then show ?thesis
        using cg_var2.hyps cg_var2.prems ct_sem_conj_iff type_infer.typing_sig type_infer_axioms
          typing_var by fastforce
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S \<rho>) (assign_app_ty S \<tau>)"
      using cg_var2.prems cg_var2.hyps ct_sem_conjE assign_app_constr.simps by metis
    ultimately show ?thesis
      using typing_sig by simp
  qed
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C e' C' \<tau>)
  then show ?case
  proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Sig (assign_app_expr S e') (assign_app_ty S \<tau>') : (assign_app_ty S \<tau>')"
    proof -
      have "A \<turnstile> (assign_app_constr S C)"
        using cg_sig.prems cg_sig.hyps ct_sem_conjE assign_app_constr.simps by metis
      then have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S e' : (assign_app_ty S \<tau>')"
        using cg_sig.prems cg_sig.hyps(2) by auto
      then show ?thesis
        using typing_sig_refl by simp
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S \<tau>') (assign_app_ty S \<tau>)"
      using cg_sig.prems cg_sig.hyps ct_sem_conjE assign_app_constr.simps by metis
    ultimately show ?thesis 
      using typing_sig by simp
  qed
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
      proof -
    let ?e="App e1 e2"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_app 
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S C2"
        using cg_app assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "A \<ddagger>  assign_app_ctx S (G1 \<bar> fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S (TFun \<alpha> \<tau>)"
      using cg_app
    proof (intro cg_app.hyps(3))
      {
        fix i
        assume i_size: "i < length G1"
        show "if i \<in> fv' 0 e1 then assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S (fst (G1 ! i)))
         else assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = None \<or>
              assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_restrict_some i_size assign_app_ctx_none_iff ctx_restrict_len 
            ctx_restrict_nth_none_iff i_size by auto
      }
    qed (simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_def)+
    moreover have "A \<ddagger> assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<alpha>"
      using cg_app
    proof (intro cg_app.hyps(5))
      fix i
      assume i_size: "i < length G2"
      show "if i \<in> fv e2
         then assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i)))
         else assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
        using cg_app cg_ctx_type_same i_size ctx_restrict_def
        by (auto split: if_splits; clarsimp simp add: assign_app_ctx_nth; metis option.distinct(1) option.sel)
    qed (simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len)+
    ultimately show ?thesis
      using typing_sig_refl typing_app by simp
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  then show ?case
  proof -
    let ?e="Let e1 e2"
    let ?dec_fv_e2="image (\<lambda>x. x-1) (fv e2 - {0})"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>?dec_fv_e2 \<union> ?idxs)"
      using cg_let
    proof (rule_tac split_used_let_extR)
      show "A \<turnstile> assign_app_constr S C2"
        using cg_let assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "A \<ddagger> assign_app_ctx S (G1 \<bar> fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S \<alpha>"
      using cg_let
    proof (intro cg_let.hyps(3))
      fix i :: nat
      assume i_size: "i < length G1"
      show "if i \<in> fv e1 
        then assign_app_ctx S (G1 \<bar> fv e1) ! i = Some (assign_app_ty S (fst (G1 ! i)))
        else assign_app_ctx S (G1 \<bar> fv e1) ! i = None \<or>
             assign_app_ctx S (G1 \<bar> fv e1) ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
             A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
        using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by auto
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    moreover have "A \<ddagger> Some (S n1) # assign_app_ctx S (G2 \<bar> ?dec_fv_e2 \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
      using cg_let
    proof (intro cg_let.hyps(5))
      fix i :: nat
      assume i_size: "i < length ((\<alpha>, 0) # G2)"
      show "if i \<in> fv e2
        then (Some (S n1) # assign_app_ctx S (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i =
              Some (assign_app_ty S (fst (((\<alpha>, 0) # G2) ! i)))
        else (Some (S n1) # assign_app_ctx S (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i = None \<or>
             (Some (S n1) # assign_app_ctx S (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i =
              Some (assign_app_ty S (fst (((\<alpha>, 0) # G2) ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (((\<alpha>, 0) # G2) ! i)))"
      proof (cases "i = 0")
        case True
        then show ?thesis
          using cg_let cg_gen_output_type_unused_same 
          by (auto split: if_splits; fastforce simp add: ct_sem_conj_iff type_infer_axioms)
      next
        case False
        assume i_nonzero: "i \<noteq> 0"
        then show ?thesis
        proof (cases "i \<in> fv e2")
          case True
          then show ?thesis
            using False assign_app_ctx_restrict_some i_size by auto
        next
          case False
          {
            assume dec_i_notin_idxs: "i - 1 \<notin> ?idxs"
            have "i - 1 \<notin> ?dec_fv_e2 \<union> ?idxs"
              using False dec_i_notin_idxs i_nonzero less_Suc_eq_0_disj by fastforce
            then have ?thesis
              using False assign_app_ctx_none_iff ctx_restrict_len ctx_restrict_nth_none i_nonzero 
                i_size option.distinct(1) by (simp add: nth_Cons' i_nonzero; auto)
          }
          moreover {
            assume dec_i_in_idxs: "i - 1 \<in> ?idxs"
            have "i - 1 \<notin> fv ?e \<and> \<Gamma> ! (i - 1) \<noteq> None"
              using dec_i_in_idxs by auto
            then have "A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! (i - 1))))"
              by (meson atLeastLessThan_iff cg_let.prems(3) dec_i_in_idxs member_filter)
            then have "A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! (i - 1))))"
              using cg_ctx_type_same cg_let.hyps dec_i_in_idxs by auto
          }
          ultimately show ?thesis
            using assign_app_ctx_restrict_some i_nonzero i_size 
            by (simp only: nth_Cons' i_nonzero; case_tac "i - 1 \<notin> ?idxs"; fastforce)
        qed
      qed
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    ultimately show ?thesis
      using typing_sig_refl typing_let cg_let.hyps by simp
  qed
next
  case (cg_blit C \<tau> G n l)
  then show ?case
  proof -
    have "A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)"
    proof -
      {
        fix i :: nat
        assume i_size: "i < length \<Gamma>"
        have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
          using empty_def none i_size cg_blit.prems drop empty_none
          by (case_tac "\<Gamma> ! i = None"; fastforce)
      }
      then show ?thesis
        by (simp add: list_all2_all_nthI empty_def weakening_def)
    qed
    moreover have "assign_app_ty S \<tau> = TPrim Bool"
      using cg_blit ct_sem_eq_iff by auto
    ultimately show ?thesis
      using typing_sig_refl typing_blit by force 
  qed
next
  case (cg_ilit C m \<tau> G n)  
  then show ?case
  proof -
    obtain n where n_def: "(assign_app_ty S \<tau>) = TPrim (Num n)"
      using cg_ilit ct_sem_int_imp by fastforce 
    have "A \<turnstile> \<Gamma> \<leadsto>w local.empty (length \<Gamma>)"
    proof -
      {
        fix i :: nat
        assume i_size: "i < length \<Gamma>"
        have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
          using empty_def none i_size cg_ilit.prems drop empty_none
          by (case_tac "\<Gamma> ! i = None"; fastforce)
      }
      then show ?thesis
        by (simp add: list_all2_all_nthI empty_def weakening_def)
    qed
    moreover have "m < abs n"
      using cg_ilit ct_sem_int_imp n_def by force
    moreover have "assign_app_ty S \<tau> = TPrim (Num n)"
      using cg_ilit ct_sem_int_imp n_def by fast
    ultimately show ?thesis
      using typing_sig_refl typing_ilit by simp
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
  proof -
    let ?e="If e1 e2 e3"
    let ?fve2e3="fv e2 \<union> fv e3"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs)"
      using cg_if
    proof (rule_tac split_used_if_extR)
      show "A \<turnstile> assign_app_constr S C2"
        using cg_if assign_app_constr.simps ct_sem_conjE by metis
      show "A \<turnstile> assign_app_constr S C3"
        using cg_if assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "A \<ddagger> assign_app_ctx S (G1\<bar>fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S (TPrim Bool)"
      using cg_if
    proof (intro cg_if.hyps(2))
      {
        fix i :: nat
        assume i_size : "i < length G1"
        show "if i \<in> fv e1 
          then assign_app_ctx S (G1 \<bar> fv e1) ! i = Some (assign_app_ty S (fst (G1 ! i)))
          else assign_app_ctx S (G1 \<bar> fv e1) ! i = None \<or>
               assign_app_ctx S (G1 \<bar> fv e1) ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
               A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_nth i_size ctx_restrict_def by simp
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    moreover have "A \<ddagger> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
      using cg_if
    proof (intro cg_if.hyps(4))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        show "if i \<in> fv e2
         then assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i)))
         else assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
        proof (cases "i \<in> fv e2")
          case False
          consider (i_in_e3) "i \<in> fv e3" | (i_in_idxs) "i \<in> ?idxs" | (i_in_neither) "i \<notin> fv e3 \<union> ?idxs"
            by blast
          then show ?thesis
          proof cases
            case i_in_e3
            have "A \<turnstile> CtDrop (assign_app_ty S (fst (G4 ! i)))"
              using cg_if ct_sem_conj_iff i_size cg_ctx_idx_size
            proof (rule_tac alg_ctx_jn_type_used_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
              show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
                using cg_gen_output_type_used_diff cg_if False i_in_e3 i_size 
                  cg_gen_output_type_unused_same by metis
            qed (force)+
            then show ?thesis
              using cg_if.hyps assign_app_ctx_restrict_some i_in_e3 alg_ctx_jn_type_same 
                cg_ctx_length cg_ctx_type_same i_size by (auto simp add: False)
          next
            case i_in_idxs
            have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
              using cg_if assign_app_constr.simps cg_ctx_length cg_ctx_type_same i_in_idxs i_size 
                member_filter by (metis (mono_tags, lifting))
            then show ?thesis
              using assign_app_ctx_restrict_some i_in_idxs i_size False by simp
          next
            case i_in_neither
            then show ?thesis
              using False assign_app_ctx_none_iff ctx_restrict_len ctx_restrict_nth_none i_size 
                by auto
          qed
        qed (simp add: assign_app_ctx_restrict_some i_size)
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "A \<ddagger> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs) \<turnstile> assign_app_expr S e3' : assign_app_ty S \<tau>"
      using cg_if
    proof (intro cg_if.hyps(6))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        show "if i \<in> fv e3
         then assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i)))
         else assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
        proof (cases "i \<in> fv e3")
          case False
          consider (i_in_e2) "i \<in> fv e2" | (i_in_idxs) "i \<in> ?idxs" | (i_in_neither) "i \<notin> fv e2 \<union> ?idxs"
            by blast
          then show ?thesis
          proof cases
            case i_in_e2
            have "A \<turnstile> CtDrop (assign_app_ty S (fst (G4 ! i)))"
              using cg_if ct_sem_conj_iff i_size cg_ctx_idx_size
            proof (rule_tac alg_ctx_jn_type_used_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
              show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
                using cg_gen_output_type_used_diff cg_if False i_in_e2 i_size 
                  cg_gen_output_type_unused_same by metis
            qed (force)+
            then show ?thesis
              using cg_if.hyps assign_app_ctx_restrict_some i_in_e2 alg_ctx_jn_type_same 
                cg_ctx_length cg_ctx_type_same i_size by (auto simp add: False)
          next
            case i_in_idxs
            have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
              using cg_if assign_app_constr.simps cg_ctx_length cg_ctx_type_same i_in_idxs i_size 
                member_filter by (metis (mono_tags, lifting))
            then show ?thesis
              using assign_app_ctx_restrict_some i_in_idxs i_size False by simp
          next
            case i_in_neither
            then show ?thesis
              using False assign_app_ctx_none_iff ctx_restrict_len ctx_restrict_nth_none i_size 
                by auto
          qed
        qed (simp add: assign_app_ctx_restrict_some i_size)
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    ultimately show ?thesis
      using typing_sig_refl typing_if by simp
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    let ?e="Prim x [e1, e2]"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_iop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S C2"
        using cg_iop assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "assign_app_ty S \<tau> \<noteq> TPrim Bool"
      using ct_sem_int_not_bool cg_iop ct_sem_conj_iff assign_app_constr.simps by metis
    moreover have "x \<in> {Plus nt, Minus nt, Times nt, Divide nt}"
      using cg_iop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S (G1\<bar>fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S \<tau>"
      using cg_iop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len 
        assign_app_ctx_restrict_some ctx_restrict_nth_none by (intro cg_iop.hyps(3); simp)
    moreover have "A \<ddagger> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
      using cg_iop
   proof (intro cg_iop.hyps(5))
     {
       fix i :: nat
       assume i_size: "i < length G2"
       have "if i \<in> fv e2
         then map_option (assign_app_ty S) ((G2 \<bar> fv e2 \<union> ?idxs) ! i) =
              Some (assign_app_ty S (fst (G2 ! i)))
         else map_option (assign_app_ty S) ((G2 \<bar> fv e2 \<union> ?idxs) ! i) =
              None \<or>
              map_option (assign_app_ty S) ((G2 \<bar> fv e2 \<union> ?idxs) ! i) =
              Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
         using cg_iop cg_ctx_type_same i_size ctx_restrict_def by fastforce
        then show "if i \<in> fv e2
         then assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S (fst (G2 ! i)))
         else assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              None \<or>
              assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
          using assign_app_ctx_nth i_size ctx_restrict_def by simp
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    ultimately show ?thesis
      using typing_sig_refl typing_iop by force
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    let ?e="Prim x [e1, e2]"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_cop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S C2"
        using cg_cop assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "S n1 \<noteq> TPrim Bool" 
      using ct_sem_int_not_bool cg_cop ct_sem_conj_iff assign_app_constr.simps by auto
    moreover have "x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}"
      using cg_cop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S (G1\<bar>fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S \<alpha>"
      using cg_cop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len
      by (intro cg_cop(4); simp add: ctx_restrict_def)
    moreover have "A \<ddagger> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<alpha>"
      using cg_cop
    proof (intro cg_cop(6))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume "\<exists>y. assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) ! i = Some y"
          then have "i \<in> ?idxs"
            using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by fastforce
          then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
            using cg_cop.hyps(3) cg_cop.prems(3) cg_ctx_type_same by fastforce
        }
        then show "if i \<in> fv e2
         then assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S (fst (G2 ! i)))
         else assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S (G2 \<bar>fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
          using assign_app_ctx_restrict_some assign_app_ctx_restrict_some_val i_size by auto
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "assign_app_ty S \<tau> = TPrim Bool"
      using cg_cop ct_sem_conj_iff ct_sem_eq_iff by simp
    ultimately show ?thesis
      using typing_sig_refl typing_cop cg_cop.hyps by force
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  then show ?case
  proof -
    let ?e="Prim x [e1, e2]"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S (G1\<bar>fv e1) \<box> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_bop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S C2"
        using cg_bop assign_app_constr.simps ct_sem_conjE by metis
    qed (fastforce)+
    moreover have "x \<in> {BitAnd nt, BitOr nt}"
      using cg_bop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S (G1\<bar>fv e1) \<turnstile> assign_app_expr S e1' : assign_app_ty S \<tau>"
      using cg_bop
    proof (intro cg_bop.hyps(3))
      {
        fix i :: nat
        assume i_size: "i < length G1"
        show "if i \<in> fv' 0 e1
         then assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S (fst (G1 ! i)))
         else assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = None \<or>
              assign_app_ctx S (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
              A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by simp
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "A \<ddagger> assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
      using cg_bop
    proof (intro cg_bop.hyps(5))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume "\<exists>y. assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs) ! i = Some y"
          then have "i \<in> ?idxs"
            using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by fastforce
          then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
            using cg_bop.hyps(2) cg_bop.prems(3) cg_ctx_type_same by fastforce
        }
        then show "if i \<in> fv e2
          then assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i =
               Some (assign_app_ty S (fst (G2 ! i)))
          else assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i = None \<or>
               assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i =
               Some (assign_app_ty S (fst (G2 ! i))) \<and>
               A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
          using i_size assign_app_ctx_restrict_some_val assign_app_ctx_restrict_some by auto
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "assign_app_ty S \<tau> = TPrim Bool"
      using cg_bop ct_sem_conj_iff ct_sem_eq_iff by auto
    ultimately show ?thesis
      using typing_sig_refl typing_bop by force
  qed
next
  case (cg_tapp name C \<rho> m ts \<beta>s n1 \<rho>' C' C2 \<tau> n' n G)
  then show ?case
      proof -
    have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S (TypeApp name (ts @ \<beta>s)) : (assign_app_ty S \<rho>')"
    proof -
      have "A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)"
      proof -
        {
          fix i :: nat
          assume i_size: "i < length \<Gamma>"
          have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
            using local.empty_def weakening_comp.none i_size cg_tapp.prems drop empty_none i_size
            by (case_tac "\<Gamma> ! i = None"; fastforce)
        }
        then show ?thesis
          by (simp add: list_all2_all_nthI empty_def weakening_def)
      qed
      moreover have "type_of name = (C, \<rho>)"
        using cg_tapp.hyps by simp
      moreover have "A \<turnstile> assign_app_constr S (subst_ct (ts @ \<beta>s) C)"
        using cg_tapp.hyps cg_tapp.prems ct_sem_conjE by auto
      moreover have "assign_app_ty S \<rho>' = assign_app_ty S (subst_ty (ts @ \<beta>s) \<rho>)"
        using cg_tapp.hyps by blast
      ultimately show ?thesis
        using assign_app_constr_subst_ct_commute assign_app_ty_subst_ty_commute type_of_known
          typing_tapp by auto
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S \<rho>') (assign_app_ty S \<tau>)"
      using cg_tapp.hyps cg_tapp.prems ct_sem_conj_iff by auto
    ultimately show ?thesis
      using typing_sig by simp
  qed                                        
qed

lemma cg_sound:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "G = []"
    and "A \<turnstile> assign_app_constr S C"      
    and "\<forall>i. known_ty (S i)" 
  shows "A \<ddagger> [] \<turnstile> (assign_app_expr S e') : (assign_app_ty S \<tau>)"
  using assms cg_sound_induction by force

end
end