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


fun variant_elem_used :: "(name \<times> type \<times> usage_tag) \<Rightarrow> (name \<times> type \<times> usage_tag)" where
  "variant_elem_used (nm, t, _) = (nm, t, Used)"

lemma variant_elem_used_nm_eq: "y = variant_elem_used x \<Longrightarrow> fst y = fst x"
  by (metis fst_conv variant_elem_used.elims)

lemma variant_elem_used_type_eq: "y = variant_elem_used x \<Longrightarrow> (fst \<circ> snd) y = (fst \<circ> snd) x"
  by (metis comp_apply fst_conv snd_conv surjective_pairing variant_elem_used.simps)

lemma variant_elem_used_usage_used: "y = variant_elem_used x \<Longrightarrow> (snd \<circ> snd) y = Used"
  by (metis comp_apply snd_conv variant_elem_used.elims)

lemma variant_elem_used_usage_nondec: 
  assumes "y = variant_elem_used x"
  shows "(snd \<circ> snd) y \<le> (snd \<circ> snd) x"
  using assms
proof (cases "(snd \<circ> snd) x = Used")
  case True
  then show ?thesis using assms variant_elem_used_usage_used by auto 
next
  case False
  then show ?thesis using less_eq_usage_tag.elims by blast
qed


fun variant_nth_used :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "variant_nth_used n (TVar i)        = undefined"  
| "variant_nth_used n (TFun a b)      = undefined"
| "variant_nth_used n (TPrim p)       = undefined"
| "variant_nth_used n (TProduct t u)  = undefined"
| "variant_nth_used n (TUnit)         = undefined"
| "variant_nth_used n (TUnknown i)    = undefined"
| "variant_nth_used n (TVariant Ks \<alpha>) = TVariant (Ks[n := variant_elem_used (Ks ! n)]) \<alpha>"


fun variant_elem_unused :: "(name \<times> type \<times> usage_tag) \<Rightarrow> (name \<times> type \<times> usage_tag)" where
  "variant_elem_unused (nm, t, _) = (nm, t, Unused)"

lemma variant_elem_unused_nm_eq: "y = variant_elem_unused x \<Longrightarrow> fst y = fst x"
  by (metis fst_conv variant_elem_unused.elims)

lemma variant_elem_unused_type_eq: "y = variant_elem_unused x \<Longrightarrow> (fst \<circ> snd) y = (fst \<circ> snd) x"
  by (metis comp_apply fst_conv snd_conv surjective_pairing variant_elem_unused.simps)

lemma variant_elem_unused_usage_unused: "y = variant_elem_unused x \<Longrightarrow> (snd \<circ> snd) y = Unused"
  by (metis comp_apply snd_conv variant_elem_unused.elims)

lemma variant_elem_unused_usage_noninc: 
  assumes "y = variant_elem_unused x"
  shows "(snd \<circ> snd) y \<ge> (snd \<circ> snd) x"
  using assms
proof (cases "(snd \<circ> snd) x = Used")
  case True
  then show ?thesis using assms using less_eq_usage_tag.elims by auto
next
  case False
  then show ?thesis using assms variant_elem_unused_usage_unused by auto
qed


fun variant_nth_unused :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "variant_nth_unused n (TVar i)        = undefined"  
| "variant_nth_unused n (TFun a b)      = undefined"
| "variant_nth_unused n (TPrim p)       = undefined"
| "variant_nth_unused n (TProduct t u)  = undefined"
| "variant_nth_unused n (TUnit)         = undefined"
| "variant_nth_unused n (TUnknown i)    = undefined"
| "variant_nth_unused n (TVariant Ks \<alpha>) = TVariant (Ks[n := variant_elem_unused (Ks ! n)]) \<alpha>"


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
inductive_cases known_tvariant_consE: "known_ty (TVariant (K # Ks) None)"


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
                 | Con name "'f expr"
                 | Unit
                 | Lit lit
                 | Cast num_type "'f expr"
                 | Let "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type
                 | Case "'f expr" name "'f expr" "'f expr"
                 | Esac "'f expr" name "'f expr"

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
   ; list_all2 (\<lambda>g g'. fst g = fst g') G G'
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

lemma alg_ctx_jn_type_same1:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1"
  shows "fst (G1 ! i) = fst (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_same2:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
  shows "fst (G1' ! i) = fst (G2 ! i)"
  using assms 
  by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth list_all2_conv_all_nth) 

lemma alg_ctx_jn_type_used_nondec1:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1" 
  shows "snd (G1 ! i) \<le> snd (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_used_nondec2:
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
inductive constraint_sem :: "axm_set \<Rightarrow> constraint \<Rightarrow> bool" ("_ \<turnstile> _" [40, 40] 60) where
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
| ct_sem_exhaust:
  "\<lbrakk> \<forall>i < length Ks. ((snd \<circ> snd) (Ks ! i) = Used) \<rbrakk> \<Longrightarrow> A \<turnstile> CtExhausted (TVariant Ks None)"
| ct_sem_varsub_nil:
  "A \<turnstile> CtSub (TVariant [] None) (TVariant [] None)"
| ct_sem_varsub_cons:
  "\<lbrakk> fst K1 = fst K2
   ; A \<turnstile> CtSub ((fst \<circ> snd) K1) ((fst \<circ> snd) K2)
   ; (snd \<circ> snd) K1 \<le> (snd \<circ> snd) K2
   ; A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2 None)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtSub (TVariant (K1 # Ks1) None) (TVariant (K2 # Ks2) None)"
| ct_sem_varshare_nil:
  "A \<turnstile> CtShare (TVariant [] None)"
| ct_sem_varshare_cons:
  "\<lbrakk> (snd \<circ> snd) K = Unused \<longrightarrow> A \<turnstile> CtShare ((fst \<circ> snd) K)
   ; A \<turnstile> CtShare (TVariant Ks None)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtShare (TVariant (K # Ks) None)"
| ct_sem_vardrop_nil:
  "A \<turnstile> CtDrop (TVariant [] None)"
| ct_sem_vardrop_cons:
  "\<lbrakk> (snd \<circ> snd) K = Unused \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) K)
   ; A \<turnstile> CtDrop (TVariant Ks None)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtDrop (TVariant (K # Ks) None)"

inductive_cases ct_sem_conjE: "A \<turnstile> CtConj C1 C2"
inductive_cases ct_sem_intE: "A \<turnstile> CtIBound (LNat m) \<tau>"
inductive_cases ct_sem_reflE: "A \<turnstile> CtEq \<tau> \<rho>" 
inductive_cases ct_sem_funE1: "A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) \<rho>"
inductive_cases ct_sem_funE2: "A \<turnstile> CtSub \<rho> (TFun \<tau>1 \<tau>2)"
inductive_cases ct_sem_exhaust: "A \<turnstile> CtExhausted (TVariant Ks None)"
inductive_cases ct_sem_varsubE1: "A \<turnstile> CtSub (TVariant Ks \<alpha>) \<tau>"
inductive_cases ct_sem_varsubE2: "A \<turnstile> CtSub \<tau> (TVariant Ks \<alpha>)"

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
  using ct_sem_reflE ct_sem_refl by fastforce

lemma ct_sem_int_iff: "A \<turnstile> CtIBound (LNat m) (TPrim pt) \<longleftrightarrow> (\<exists>n. pt = Num n \<and> m < abs n)"
  using ct_sem_intE ct_sem_int by blast

lemma ct_sem_int_exI: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<exists>pt. \<tau> = TPrim pt"
  using ct_sem_intE by meson

lemma ct_sem_int_imp: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<exists>n. \<tau> = TPrim (Num n) \<and> m < abs n"
  using ct_sem_int_iff ct_sem_int_exI by metis

lemma ct_sem_int_not_bool: "A \<turnstile> CtIBound (LNat m) \<tau> \<Longrightarrow> \<tau> \<noteq> TPrim Bool"
  using ct_sem_intE by blast

lemma ct_sem_fun_exI1: 
  assumes "A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) \<rho>"
  shows "\<exists>\<rho>1 \<rho>2. \<rho> = TFun \<rho>1 \<rho>2"
  using assms ct_sem_eq_iff ct_sem_funE1 by metis

lemma ct_sem_fun_exI2: 
  assumes "A \<turnstile> CtSub \<rho> (TFun \<tau>1 \<tau>2)"
  shows "\<exists>\<rho>1 \<rho>2. \<rho> = TFun \<rho>1 \<rho>2"
  using assms ct_sem_eq_iff ct_sem_funE2 by metis

lemma ct_sem_exhaust_all_used: 
  assumes "A \<turnstile> CtExhausted (TVariant Ks None)"
  shows "\<forall>i < length Ks. (snd \<circ> snd) (Ks ! i) = Used"
  using assms ct_sem_exhaust by auto

lemma ct_sem_varsub_exI: "A \<turnstile> CtSub (TVariant Ks None) \<tau> \<Longrightarrow> \<exists>Ks'. \<tau> = TVariant Ks' None"
  using ct_sem_varsubE1 ct_sem_eq_iff by metis

lemma ct_sem_varsub_cons_exI1: 
  assumes "A \<turnstile> CtSub (TVariant (K # Ks) None) (TVariant Ks' None)"
  shows "\<exists>K' Ks''. Ks' = K' # Ks''"
  using assms ct_sem_eq_iff ct_sem_varsubE1 type.inject by metis

lemma ct_sem_varsub_cons_exI2: 
  assumes "A \<turnstile> CtSub (TVariant Ks None) (TVariant (K' # Ks') None)"
  shows "\<exists>K' Ks''. Ks = K' # Ks''"
  using assms ct_sem_eq_iff ct_sem_varsubE1 type.inject by metis

lemma ct_sem_varsub_imp_nm_eq:
  assumes "A \<turnstile> CtSub (TVariant (K1 # Ks1) None) (TVariant (K2 # Ks2) None)" 
  shows "fst K1 = fst K2"
  using assms
proof (induct rule: constraint_sem.cases)
  case (ct_sem_equal A \<tau> \<rho>)
  then show ?case
    using ct_sem_eq_iff by force
qed (fast)+

lemma ct_sem_varsub_imp_subhdtype:
  assumes "A \<turnstile> CtSub (TVariant (K1 # Ks1) None) (TVariant (K2 # Ks2) None)" 
  shows "A \<turnstile> CtSub ((fst \<circ> snd) K1) ((fst \<circ> snd) K2)"
  using assms 
proof (rule ct_sem_varsubE1)
qed (simp add: ct_sem_eq_iff ct_sem_equal)+

lemma ct_sem_varsub_imp_usage_nondec:
  assumes "A \<turnstile> CtSub (TVariant (K1 # Ks1) None) (TVariant (K2 # Ks2) None)" 
  shows "(snd \<circ> snd) K1 \<le> (snd \<circ> snd) K2"
  using assms
proof (rule ct_sem_varsubE1)
qed (simp add: ct_sem_eq_iff)+

lemma ct_sem_varsub_imp_subcons: 
  assumes "A \<turnstile> CtSub (TVariant (K1 # Ks1) None) (TVariant (K2 # Ks2) None)" 
  shows "A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2 None)"
  using assms
proof (rule ct_sem_varsubE1) 
qed (simp add: ct_sem_eq_iff ct_sem_equal)+

lemma ct_sem_varsub_conv_all_nth:
  "A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2 None) \<longleftrightarrow> length Ks1 = length Ks2 \<and>
                         (\<forall>i < length Ks1. fst (Ks1 ! i) = fst (Ks2 ! i)
                                         \<and> A \<turnstile> CtSub ((fst \<circ> snd) (Ks1 ! i)) ((fst \<circ> snd) (Ks2 ! i))
                                         \<and> ((snd \<circ> snd) (Ks1 ! i)) \<le> ((snd \<circ> snd) (Ks2 ! i)))"
proof (induct Ks1 arbitrary: Ks2)
case Nil
  then show ?case
    using ct_sem_varsub_cons_exI2 ct_sem_equal ct_sem_refl
    by (metis length_0_conv neq_Nil_conv not_less_zero)
next
  case (Cons K Ks1)
  show ?case
  proof (rule iffI)
    assume "A \<turnstile> CtSub (TVariant (K # Ks1) None) (TVariant Ks2 None)"
    then show "length (K # Ks1) = length Ks2 \<and> 
               (\<forall>i<length (K # Ks1). fst ((K # Ks1) ! i) = fst (Ks2 ! i) 
                                   \<and> A \<turnstile> CtSub ((fst \<circ> snd) ((K # Ks1) ! i)) ((fst \<circ> snd) (Ks2 ! i)) 
                                   \<and> (snd \<circ> snd) ((K # Ks1) ! i) \<le> (snd \<circ> snd) (Ks2 ! i))"
    proof (induct rule: constraint_sem.cases)
      case ct_sem_equal
      then show ?thesis
        using constraint_sem.ct_sem_equal ct_sem_eq_iff by force
    next
      case (ct_sem_varsub_cons K2 Ks2)
      then show ?thesis
        using Cons.hyps less_Suc_eq_0_disj by auto
    qed (simp)+
  next
    assume ks1_ks2_props: "length (K # Ks1) = length Ks2 \<and> 
               (\<forall>i<length (K # Ks1). fst ((K # Ks1) ! i) = fst (Ks2 ! i) 
                                   \<and> A \<turnstile> CtSub ((fst \<circ> snd) ((K # Ks1) ! i)) ((fst \<circ> snd) (Ks2 ! i)) 
                                   \<and> (snd \<circ> snd) ((K # Ks1) ! i) \<le> (snd \<circ> snd) (Ks2 ! i))"
    then obtain K2 Ks2' where ks2_def: "Ks2 = K2 # Ks2'" by (metis length_Suc_conv)
    moreover have "A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2' None)"
      using Cons.hyps[where ?Ks2.0 = Ks2'] ks1_ks2_props ks2_def by fastforce
    ultimately show "A \<turnstile> CtSub (TVariant (K # Ks1) None) (TVariant Ks2 None)"
      using ct_sem_varsub_cons ks1_ks2_props
      by (metis length_greater_0_conv list.distinct(1) nth_Cons_0)
  qed
qed

inductive_cases ct_sem_tvarsubE: "A \<turnstile> CtSub (TVar x) \<tau>"                                
inductive_cases ct_sem_tprimsubE: "A \<turnstile> CtSub (TPrim x) \<tau>"
inductive_cases ct_sem_tproductsubE: "A \<turnstile> CtSub (TProduct \<tau>1 \<tau>2) \<rho>"
inductive_cases ct_sem_tunitsubE: "A \<turnstile> CtSub TUnit \<tau>"
inductive_cases ct_sem_tunknownsubE: "A \<turnstile> CtSub (TUnknown n) \<tau>"
lemma ct_sem_sub_trans:
  assumes "A \<turnstile> CtSub \<tau>1 \<tau>2"
    and "A \<turnstile> CtSub \<tau>2 \<tau>3"
  shows "A \<turnstile> CtSub \<tau>1 \<tau>3"
  using assms
proof (induct \<tau>2 arbitrary: \<tau>1 \<tau>3)
  case (TVar x)
  then show ?case
    using ct_sem_tvarsubE ct_sem_eq_iff by auto
next
  case (TFun \<rho> \<rho>')
  then show ?case
  proof -
    obtain \<tau> \<tau>' where \<tau>_\<tau>'_def: "\<tau>1 = TFun \<tau> \<tau>'"
      using TFun.prems ct_sem_fun_exI2 by blast
    obtain \<mu> \<mu>' where \<mu>_\<mu>'_def: "\<tau>3 = TFun \<mu> \<mu>'"
      using TFun.prems ct_sem_fun_exI1 by blast
    consider (equal) "A \<turnstile> CtEq (TFun \<tau> \<tau>') (TFun \<rho> \<rho>')" | (sub) "A \<turnstile> CtSub \<rho> \<tau>" "A \<turnstile> CtSub \<tau>' \<rho>'"
      using \<tau>_\<tau>'_def TFun.prems ct_sem_funE1 by blast
    then show ?thesis
    proof cases
      case equal
      then show ?thesis
        using ct_sem_eq_iff TFun.prems \<tau>_\<tau>'_def by metis
    next
      case sub
      consider (equal2) "A \<turnstile> CtEq (TFun \<rho> \<rho>') (TFun \<mu> \<mu>')" | (sub2) "A \<turnstile> CtSub \<mu> \<rho>" "A \<turnstile> CtSub \<rho>' \<mu>'"
        using \<mu>_\<mu>'_def TFun.prems ct_sem_funE1 by blast
      then show ?thesis 
      proof cases
        case equal2
        then show ?thesis
          using ct_sem_eq_iff TFun.prems \<mu>_\<mu>'_def by force
      next
        case sub2
        then show ?thesis
          using sub TFun ct_sem_fun \<tau>_\<tau>'_def \<mu>_\<mu>'_def by blast
      qed
    qed
  qed
next
  case (TPrim x)
  then show ?case
    using ct_sem_tprimsubE ct_sem_eq_iff by auto
next
  case (TProduct \<tau>11 \<tau>12)
  then show ?case
    using ct_sem_tproductsubE ct_sem_eq_iff by metis
next
  case TUnit
  then show ?case 
    using ct_sem_tunitsubE ct_sem_eq_iff by auto
next
  case (TUnknown x)
  then show ?case
    using ct_sem_tunknownsubE ct_sem_eq_iff by auto
next
  case (TVariant Ks \<alpha>)
  then show ?case
  proof (induct Ks arbitrary: \<tau>1 \<tau>3)
    case Nil
    then show ?case
      using ct_sem_varsubE1 ct_sem_reflE by fast
  next
    case (Cons K2 Ks2)
    consider (equal) "A \<turnstile> CtEq \<tau>1 (TVariant (K2 # Ks2) \<alpha>)" | 
             (var_nil) "\<alpha> = None" "\<tau>1 = TVariant [] None" |
             (var_cons) "\<alpha> = None" "\<exists>K Ks. \<tau>1 = TVariant (K # Ks) None"
      using Cons.prems ct_sem_varsubE2 by metis
    then show ?case
    proof cases
      case equal
      then show ?thesis
        using Cons.prems ct_sem_eq_iff by metis
    next
      case var_nil
      then show ?thesis
        using Cons.prems ct_sem_varsub_cons_exI2 by blast
    next
      case var_cons
      obtain K1 Ks1 where k1_ks1_def: "\<tau>1 = TVariant (K1 # Ks1) None"
        using var_cons by presburger
      consider (equal2) "A \<turnstile> CtEq (TVariant (K2 # Ks2) None) \<tau>3" | (var_nil2) "\<tau>3 = TVariant [] None" |
        (var_cons2) "\<exists>K3 Ks3. \<tau>3 = TVariant (K3 # Ks3) None"
        using Cons.prems ct_sem_varsubE1 k1_ks1_def var_cons by blast
      then show ?thesis
      proof cases
        case equal2
        then show ?thesis
          using Cons.prems ct_sem_reflE k1_ks1_def var_cons by blast
      next
        case var_nil2
        then show ?thesis
          using Cons.prems ct_sem_varsub_cons_exI1 k1_ks1_def var_cons by blast
      next
        case var_cons2
        obtain K3 Ks3 where k3_ks3_def: "\<tau>3 = TVariant (K3 # Ks3) None"
          using var_cons2 by presburger
        moreover have "fst K1 = fst K3"
          using ct_sem_varsub_imp_nm_eq Cons.prems k1_ks1_def k3_ks3_def var_cons by simp
        moreover have "A \<turnstile> CtSub ((fst \<circ> snd) K1) ((fst \<circ> snd) K3)"
        proof -
          have "A \<turnstile> CtSub ((fst \<circ> snd) K1) ((fst \<circ> snd) K2)"
            using ct_sem_varsub_imp_subhdtype Cons.prems k1_ks1_def var_cons by blast
          moreover have "A \<turnstile> CtSub ((fst \<circ> snd) K2) ((fst \<circ> snd) K3)"
            using ct_sem_varsub_imp_subhdtype Cons.prems k1_ks1_def k3_ks3_def var_cons by blast
          ultimately show ?thesis
            by (metis Cons.prems(1) comp_def fsts.intros list.set_intros(1) snds.intros)
        qed
        moreover have "(snd \<circ> snd) K1 \<le> (snd \<circ> snd) K3"
        proof - 
          have "(snd \<circ> snd) K1 \<le> (snd \<circ> snd) K2"
            using ct_sem_varsub_imp_usage_nondec Cons.prems k1_ks1_def var_cons by blast
          moreover have "(snd \<circ> snd) K2 \<le> (snd \<circ> snd) K3"
            using ct_sem_varsub_imp_usage_nondec Cons.prems k1_ks1_def k3_ks3_def var_cons by blast
          ultimately show ?thesis
            by fastforce
        qed
        moreover have "A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks3 None)"
          using Cons ct_sem_varsub_imp_subcons k1_ks1_def k3_ks3_def
          by (metis (no_types, lifting) list.set_intros(2) var_cons(1))
        ultimately show ?thesis
          by (simp add: ct_sem_varsub_cons k1_ks1_def)
      qed
    qed
  qed
qed


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
| typing_sub:
  "\<lbrakk> A \<ddagger> \<Gamma> \<turnstile> e : \<tau>'
   ; A \<turnstile> CtSub \<tau>' \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> e : \<tau>"
| typing_vcon:
  "\<lbrakk> distinct (map fst Ks)
   ; i < length Ks
   ; fst (Ks ! i) = nm
   ; \<forall>j < length Ks. if j = i then (snd \<circ> snd) (Ks ! j) = Unused else (snd \<circ> snd) (Ks ! j) = Used
   ; A \<ddagger> \<Gamma> \<turnstile> e : (fst \<circ> snd) (Ks ! i)
   ; \<tau> = TVariant Ks None
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Con nm e: \<tau>"
| typing_case:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; distinct (map fst Ks)
   ; i < length Ks
   ; fst (Ks ! i) = nm
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : variant_nth_unused i (TVariant Ks None)
   ; A \<ddagger> (Some ((fst \<circ> snd) (Ks ! i))) # \<Gamma>2 \<turnstile> e2 : \<tau>
   ; A \<ddagger> (Some (variant_nth_used i (TVariant Ks None))) # \<Gamma>2 \<turnstile> e3 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Case e1 nm e2 e3 : \<tau>" 
| typing_irref:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; distinct (map fst Ks)
   ; i < length Ks
   ; fst (Ks ! i) = nm
   ; \<forall>j < length Ks. if j = i then (snd \<circ> snd) (Ks ! j) = Unused else (snd \<circ> snd) (Ks ! j) = Used
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : (TVariant Ks None)
   ; A \<ddagger> (Some ((fst \<circ> snd) (Ks ! i))) # \<Gamma>2 \<turnstile> e2 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Esac e1 nm e2 : \<tau>"

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
| cg_vcon:
  "\<lbrakk> \<alpha> = Suc n2
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e : \<beta> \<leadsto> G2,n2 | C | e'
   ; C' = CtConj C (CtSub (TVariant [(nm, \<beta>, Unused)] (Some \<alpha>)) \<tau>)
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Con nm e : \<tau> \<leadsto> G2,n2 | C' | Sig (Con nm e') \<tau>"
| cg_case:
  "\<lbrakk> \<alpha> = Suc n2
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e1 : TVariant [(nm, \<beta>, Unused)] (Some \<alpha>) \<leadsto> G2,n2 | C1 | e1'
   ; ((\<beta>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<beta>, m) # G3),n3 | C2 |e2'
   ; (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>)), 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>)), l) # G3'),n4 | C3 | e3'
   ; G3 \<Join> G3' \<leadsto> G4 | C4
   ; if m = 0 then C5 = CtDrop \<beta> else C5 = CtTop
   ; if l = 0 then C6 = CtDrop (TVariant [(nm, \<beta>, Used)] (Some \<alpha>)) else C6 = CtTop
   ; C7 = CtConj (CtConj (CtConj (CtConj (CtConj C1 C2) C3) C4) C5) C6
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Case e1 nm e2 e3 : \<tau> \<leadsto> G4,n4 | C7 | Sig (Case e1' nm e2' e3') \<tau>"
| cg_irref:
  "\<lbrakk> \<alpha> = Suc n2
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e1 : (TVariant [(nm, \<beta>, Unused)] (Some \<alpha>)) \<leadsto> G2,n2 | C1 | e1'
   ; ((\<beta>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<beta>, m) # G3),n3 | C2 | e2'
   ; C3 = CtExhausted (TVariant [(nm, \<beta>, Used)] (Some \<alpha>))
   ; if m = 0 then C4 = CtDrop \<beta> else C4 = CtTop
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Esac e1 nm e2 : \<tau> \<leadsto> G3,n3 | C5 | Sig (Esac e1' nm e2') \<tau>"

lemma cg_num_fresh_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "n \<le> n'"
  using assms by (induct rule: constraint_gen_elab.inducts) force+

lemma cg_ctx_length:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "length G = length G'"
  using assms alg_ctx_jn_length by (induct rule: constraint_gen_elab.inducts; auto)

lemma cg_ctx_idx_size:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "i < length G"
  shows "i < length G'"
  using assms cg_ctx_length by auto

lemma cg_ctx_type_same1:
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
    using cg_ctx_length alg_ctx_jn_type_same1 by auto
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
    using cg_ctx_length alg_ctx_jn_type_same1
    by (metis Suc_mono length_Cons nth_Cons_Suc size_Cons_lem_eq)
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
    by (metis Suc_mono cg_ctx_length length_Cons nth_Cons_Suc)
qed (auto simp add: cg_ctx_length)+

lemma cg_ctx_type_same2:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "\<And>i. i < length G' \<Longrightarrow> fst (G ! i) = fst (G' ! i)"
  using assms cg_ctx_type_same1 cg_ctx_idx_size cg_ctx_length by metis

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
    using cg_ctx_length alg_ctx_jn_type_used_nondec1 le_trans by fastforce
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
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    have "snd (G1 ! i) \<le> snd (G3 ! i)"
      using cg_case cg_ctx_length type_infer_axioms
      by (metis (no_types, lifting) Suc_less_eq le_trans length_Cons nth_Cons_Suc)
    then show ?thesis
      using alg_ctx_jn_type_used_nondec1 cg_case cg_ctx_length
      by (metis (no_types, lifting) Suc_less_eq le_trans length_Cons)
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
    using Suc_mono cg_ctx_length le_trans length_Cons nth_Cons_Suc by fastforce 
qed (blast)+


section {* Assignment Definition *}
(* when we are assigning an unknown type a type, the assigned type should not contain any
   unknown types itself *)
fun assign_app_ty :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> (string \<times> type \<times> usage_tag) list) \<Rightarrow> type \<Rightarrow> type" where
  "assign_app_ty S S' (TVar n)          = TVar n"
| "assign_app_ty S S' (TFun t1 t2)      = TFun (assign_app_ty S S' t1) (assign_app_ty S S' t2)"
| "assign_app_ty S S' (TPrim pt)        = TPrim pt"
| "assign_app_ty S S' (TProduct t1 t2)  = TProduct (assign_app_ty S S' t1) (assign_app_ty S S' t2)"
| "assign_app_ty S S' TUnit             = TUnit"
| "assign_app_ty S S' (TUnknown n)      = S n"
| "assign_app_ty S S' (TVariant Ks None)      = TVariant (map (\<lambda>(nm, t, u). (nm, assign_app_ty S S' t, u)) Ks) None"
| "assign_app_ty S S' (TVariant Ks (Some n))  = TVariant ((map (\<lambda>(nm, t, u). (nm, assign_app_ty S S' t, u)) Ks) @ (S' n)) None"

fun assign_app_expr :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> (string \<times> type \<times> usage_tag) list) \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where
  "assign_app_expr S S' (Var n)            = Var n" 
| "assign_app_expr S S' (TypeApp e ts)     = TypeApp e (map (assign_app_ty S S') ts)"
| "assign_app_expr S S' (Prim prim_op ts)  = Prim prim_op (map (assign_app_expr S S') ts)"
| "assign_app_expr S S' (App e1 e2)        = App (assign_app_expr S S' e1) (assign_app_expr S S' e2)"
| "assign_app_expr S S' Unit               = Unit"
| "assign_app_expr S S' (Lit l)            = Lit l"
| "assign_app_expr S S' (Cast nt e)        = Cast nt (assign_app_expr S S' e)"
| "assign_app_expr S S' (Let e1 e2)        = Let (assign_app_expr S S' e1) (assign_app_expr S S' e2)"
| "assign_app_expr S S' (If e1 e2 e3)      = If (assign_app_expr S S' e1) (assign_app_expr S S' e2) (assign_app_expr S S' e3)"
| "assign_app_expr S S' (Sig e t)          = Sig (assign_app_expr S S' e) (assign_app_ty S S' t)"
| "assign_app_expr S S' (Con nm e)         = Con nm (assign_app_expr S S' e)"
| "assign_app_expr S S' (Case e1 nm e2 e3) = Case (assign_app_expr S S' e1) nm (assign_app_expr S S' e2) (assign_app_expr S S' e3)"
| "assign_app_expr S S' (Esac e1 nm e2)    = Esac (assign_app_expr S S' e1) nm (assign_app_expr S S' e2)"

fun "assign_app_constr" :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> (string \<times> type \<times> usage_tag) list) \<Rightarrow> constraint \<Rightarrow> constraint" where
  "assign_app_constr S S' (CtConj c1 c2)   = CtConj (assign_app_constr S S' c1) (assign_app_constr S S' c2)"
| "assign_app_constr S S' (CtIBound l t)   = CtIBound l (assign_app_ty S S' t)"
| "assign_app_constr S S' (CtEq t1 t2)     = CtEq (assign_app_ty S S' t1) (assign_app_ty S S' t2)"
| "assign_app_constr S S' (CtSub t1 t2)    = CtSub (assign_app_ty S S' t1) (assign_app_ty S S' t2)"
| "assign_app_constr S S' CtTop            = CtTop"
| "assign_app_constr S S' CtBot            = CtBot"
| "assign_app_constr S S' (CtShare t)      = CtShare (assign_app_ty S S' t)"
| "assign_app_constr S S' (CtDrop t)       = CtDrop (assign_app_ty S S' t)"
| "assign_app_constr S S' (CtExhausted v)  = CtExhausted (assign_app_ty S S' v)"

definition assign_app_ctx :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> (string \<times> type \<times> usage_tag) list) \<Rightarrow> ctx \<Rightarrow> ctx" where
  "assign_app_ctx S S' G = map (map_option (assign_app_ty S S')) G"

lemma assign_app_ctx_none_iff:
  assumes "i < length G"
  shows "assign_app_ctx S S' G ! i = None \<longleftrightarrow> G ! i = None"
  using assms assign_app_ctx_def by simp

lemma assign_app_ctx_nth:
  assumes
    "i < length G"
  shows "assign_app_ctx S S' G ! i = map_option (assign_app_ty S S') (G ! i)"
  using assms assign_app_ctx_def by simp

lemma assign_app_ctx_len:
  "length (assign_app_ctx S S' G) = length G"
  by (induct G arbitrary: S; simp add: assign_app_ctx_def)

lemma assign_app_ty_subst_ty_commute: 
  assumes "known_ty \<tau>"
  shows "assign_app_ty S S' (subst_ty xs \<tau>) = subst_ty (map (assign_app_ty S S') xs) \<tau>"
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
  case (known_tvariant_cons K Ks)
  then show ?case
    by (simp add: case_prod_beta)
qed (simp)+ 

lemma assign_app_constr_subst_ct_commute: 
  assumes "known_ct C"
  shows "assign_app_constr S S' (subst_ct xs C) = subst_ct (map (assign_app_ty S S') xs) C"
  using assms
proof (induct C)
qed (auto simp add: subst_ct_def assign_app_ty_subst_ty_commute)+

lemma ct_sem_assign_conj_foldr:
  assumes "A \<turnstile> assign_app_constr S S' (foldr CtConj Cs CtTop)"
    and  "i < length Cs" 
  shows "A \<turnstile> assign_app_constr S S' (Cs ! i)"
  using assms
proof (induct Cs arbitrary: i)
  case (Cons a Cs)
  then show ?case
  proof -
    have constr_sem_rearrange: "A \<turnstile> assign_app_constr S S' (CtConj a ((foldr CtConj Cs) CtTop))"
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
    and "A \<turnstile> assign_app_constr S S' C" 
  shows "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
  using assms
proof -
  let ?Cs = "List.map2 (\<lambda>x y. if snd x = snd y then CtTop else CtDrop (fst x)) G1 G1'"
  have "length G1' = length G1"
    using alg_ctx_jn_length assms by auto
  moreover have "length ?Cs = min (length G1) (length G1')"
    by simp
  moreover have i_size: "i < length ?Cs"
    using calculation assms by simp
  moreover have "A \<turnstile> assign_app_constr S S' (foldr CtConj ?Cs CtTop)"
    using assms by (simp add: alg_ctx_jn.simps; metis map2_def)
  moreover have "A \<turnstile> assign_app_constr S S' (?Cs ! i)"
    using calculation ct_sem_assign_conj_foldr by blast
  moreover then have "A \<turnstile> assign_app_constr S S' ((\<lambda>x y. if snd x = snd y then CtTop else CtDrop (fst x)) (G1 ! i) (G1' ! i))"
    using i_size by (clarsimp simp add: map2_nth)
  ultimately show ?thesis
    using alg_ctx_jn_type_same1 assms by auto
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
| fv'_con:      "fv' n (Con nm e) = fv' n e"
| fv'_case:     "fv' n (Case e1 nm e2 e3) = (fv' n e1) \<union> (fv' (Suc n) e2) \<union> (fv' (Suc n) e3)"
| fv'_esac:     "fv' n (Esac e1 nm e2) = (fv' n e1) \<union> (fv' (Suc n) e2)"

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
  by (metis Un_iff assms ctx_restrict_nth_none ctx_restrict_nth_some)

lemma assign_app_ctx_restrict_none:
  assumes "i \<notin> ns"
    and "i < length G"
  shows "assign_app_ctx S S' (G\<bar>ns) ! i = None"
  by (simp add: assign_app_ctx_def assms ctx_restrict_len ctx_restrict_nth_none)

lemma assign_app_ctx_restrict_some:
  assumes "i \<in> ns"
    and "i < length G"
  shows "assign_app_ctx S S' (G\<bar>ns) ! i = Some (assign_app_ty S S' (fst (G ! i)))"
  by (simp add: assign_app_ctx_def assms ctx_restrict_len ctx_restrict_nth_some)

lemma assign_app_ctx_restrict_some_val:
  assumes "i < length G"
    and "assign_app_ctx S S' (G\<bar>ns) ! i = Some y"
  shows "y = assign_app_ty S S' (fst (G ! i))"
  using assign_app_ctx_none_iff assign_app_ctx_restrict_some assms ctx_restrict_len 
    ctx_restrict_nth_none by (metis option.distinct(1) option.sel)

lemma assign_app_ctx_restrict_some_ex:
  assumes "i < length G"
    and "assign_app_ctx S S' (G\<bar>ns) ! i = Some y"
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
  next
    case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
    then show ?case
      by (force simp add: i_fv'_suc_iff_suc_i_fv' cg_ctx_length)
  next
    case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
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
        using cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size cg_let
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
        using cg_if.hyps alg_ctx_jn_type_used_nondec2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size
        by (metis le_less not_le not_less0)
    next
      case i_in_e2
      then show ?thesis 
        using cg_if.hyps not_less0 alg_ctx_jn_type_used_nondec1 cg_ctx_length cg_gen_fv_elem_size
        by (metis le_less not_le not_less0)
    next
      case i_in_e3
      then show ?thesis 
        using cg_if.hyps not_less0 alg_ctx_jn_type_used_nondec2 cg_ctx_length cg_gen_fv_elem_size
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
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
      using cg_case.prems by auto
    then show ?thesis
    proof cases
      case i_in_e1
      have "snd (G2 ! i) \<le> snd (G3 ! i)" 
        using cg_case.hyps cg_ctx_type_used_nondec cg_gen_fv_elem_size i_in_e1 cg_ctx_length
        by (metis Suc_less_eq length_Cons nth_Cons_Suc)
      moreover have "snd (G3 ! i) \<le> snd (G4 ! i)"
        using alg_ctx_jn_type_used_nondec1 cg_case.hyps cg_ctx_length cg_gen_fv_elem_size i_in_e1 
          by (metis Suc_less_eq length_Cons)
      ultimately show ?thesis
        using cg_case.hyps i_in_e1 by fastforce
    next
      case i_in_e2
      have "snd (G3 ! i) \<le> snd (G4 ! i)"
        using alg_ctx_jn_type_used_nondec1 cg_case.hyps cg_ctx_length cg_gen_fv_elem_size i_in_e2 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons)
      then show ?thesis
        using i_fv'_suc_iff_suc_i_fv' i_in_e2 cg_case.hyps by fastforce
    next
      case i_in_e3
      have "snd (G3' ! i) \<le> snd (G4 ! i)"
        using alg_ctx_jn_type_used_nondec2 cg_case.hyps cg_ctx_length cg_gen_fv_elem_size i_in_e3 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons)
      then show ?thesis
        using i_fv'_suc_iff_suc_i_fv' i_in_e3 cg_case.hyps by fastforce
    qed
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using cg_irref.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size cg_irref.hyps
        by (metis Suc_mono gt_or_eq_0 length_Cons not_le nth_Cons_Suc)
    next
      case i_in_e2
      then show ?thesis
        using cg_irref.hyps i_fv'_suc_iff_suc_i_fv' by fastforce
    qed
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
        cg_ctx_length by metis
    have snd_G3_le_G4: "snd (G3 ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 alg_ctx_jn_type_used_nondec1 cg_gen_fv_elem_size cg_if.hyps 
        cg_ctx_length by metis
    have snd_G3'_le_G4: "snd (G3' ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 alg_ctx_jn_type_used_nondec2 cg_gen_fv_elem_size cg_if.hyps 
        cg_ctx_length by metis
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
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    have i_in_e1e2e3: "i \<in> fv e1 \<or> i \<in> fv' (Suc 0) e2 \<or> i \<in> fv' (Suc 0) e3"
      using cg_case.prems by fastforce
    have snd_G1_le_G2: "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e1e2e3 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_case.hyps
      by (metis i_fv'_suc_iff_suc_i_fv' length_Cons not_less_eq)
    have snd_G2_le_G3: "snd (G2 ! i) \<le> snd (G3 ! i)"
      using i_in_e1e2e3 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_case
        i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    have snd_G3_le_G4: "snd (G3 ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 cg_gen_fv_elem_size cg_case.hyps cg_ctx_length alg_ctx_jn_type_used_nondec1 
        cg_case.hyps i_fv'_suc_iff_suc_i_fv'
      by (metis Suc_le_lessD length_Cons less_Suc_eq_le old.nat.inject)
    have snd_G3'_le_G4: "snd (G3' ! i) \<le> snd (G4 ! i)"
      using i_in_e1e2e3 cg_gen_fv_elem_size cg_case.hyps cg_ctx_length alg_ctx_jn_type_used_nondec2 
        cg_case.hyps i_fv'_suc_iff_suc_i_fv'
      by (metis Suc_le_lessD length_Cons less_Suc_eq_le old.nat.inject)
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
      using i_in_e1e2e3 by blast
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_case.hyps snd_G2_le_G3 snd_G3_le_G4 by fastforce
    next
      case i_in_e2
      then show ?thesis
        using snd_G1_le_G2 snd_G3_le_G4 i_fv'_suc_iff_suc_i_fv' cg_case.hyps by fastforce
    next
      case i_in_e3
      then show ?thesis
        using snd_G1_le_G2 snd_G3'_le_G4 i_fv'_suc_iff_suc_i_fv' cg_case.hyps by fastforce
    qed
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using cg_irref.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then have "snd (G2 ! i) \<le> snd (G3 ! i)"
        using cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_irref.hyps
        by (metis Suc_less_eq length_Cons nth_Cons_Suc)
      then show ?thesis
        using cg_irref.hyps i_in_e1 by force
    next
      case i_in_e2
      then have "snd (G1 ! i) \<le> snd (G2 ! i)"
        using i_in_e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size cg_irref 
          i_fv'_suc_iff_suc_i_fv' by (metis length_Cons not_less_eq)
      then show ?thesis
        using cg_irref.hyps i_fv'_suc_iff_suc_i_fv' i_in_e2 by fastforce
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
        using cg_ctx_type_same1 cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          ct_sem_conjE i_fv'_suc_iff_suc_i_fv' cg_let
        by (metis Suc_less_eq gt_or_eq_0 leD length_Cons nth_Cons_Suc)
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE by (metis (no_types, lifting) gt_or_eq_0 leD)
    next
      case i_in_e3
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_iop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE by metis
    next
      case i_in_e2
      then show ?thesis
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_vcon \<alpha> n1 \<beta> n2 G1 e G2 C e' C' nm \<tau>)
  then show ?case
    using ct_sem_conjE fv'_con by blast
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
      using cg_case.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using ct_sem_conj_iff cg_case by presburger
    next
      case i_in_e2
      have "0 < snd (((\<beta>, 0) # G2) ! Suc i)"
        using cg_case i_in_e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
      moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
        using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e2 
          cg_ctx_type_same1
        by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
      ultimately show ?thesis
        using i_fv'_suc_iff_suc_i_fv' i_in_e2 cg_case ct_sem_conj_iff by metis
    next
      case i_in_e3
      have "0 < snd (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>), 0) # G2) ! Suc i)"
        using cg_case i_in_e3 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
      moreover have "\<rho> = fst (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>), 0) # G2) ! Suc i)"
        using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e3
          cg_ctx_type_same1
        by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
      ultimately show ?thesis
        using i_fv'_suc_iff_suc_i_fv' i_in_e3 cg_case ct_sem_conj_iff by metis
    qed
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using cg_irref.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_irref ct_sem_conj_iff by metis
    next
      case i_in_e2
      have "snd (G1 ! i) \<le> snd (G2 ! i)"
        using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_used_nondec 
          cg_gen_fv_elem_size by (metis Suc_less_SucD length_Cons)
      moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
        using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_same1 
          cg_gen_fv_elem_size 
        by (metis Suc_eq_plus1 length_Cons less_SucE not_add_less1 nth_Cons_Suc)
      ultimately show ?thesis
        using gr_zeroI leD ct_sem_conj_iff cg_irref i_fv'_suc_iff_suc_i_fv' by fastforce
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
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    have "i \<notin> fv e1" "(Suc i) \<notin> fv e2" "(Suc i) \<notin> fv e3"
      using i_fv'_suc_iff_suc_i_fv' cg_case by auto
    then moreover have "snd (G1 ! i) = snd (G3 ! i)" "snd (G3 ! i) = snd (G3' ! i)" "i < length G3"
      using cg_case cg_ctx_length by (metis (no_types) Suc_less_eq length_Cons nth_Cons_Suc)+
    ultimately show ?thesis
      using alg_ctx_jn_length alg_ctx_jn_type_used_same cg_case.hyps by auto
  qed
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
    using cg_ctx_length i_fv'_suc_iff_suc_i_fv' by fastforce
qed (simp add: cg_ctx_idx_size)+

lemma cg_assign_type_used_nonzero_imp_share:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
      and "snd (G1 ! i) > 0"
      and "\<rho> = fst (G1 ! i)"
      and "A \<turnstile> assign_app_constr S S' C1"
      and "\<forall>i. known_ty (S i)"
    shows "A \<turnstile> CtShare (assign_app_ty S S' \<rho>)"
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
        using cg_ctx_type_same1 cg_ctx_type_used_nondec cg_ctx_length cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_if ct_sem_conjE assign_app_constr.simps by (metis (no_types, lifting) leD not_gr_zero)
    next
      case i_in_e3
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_iop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_cop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
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
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE assign_app_constr.simps by metis
    next
      case i_in_e2
      then show ?thesis 
        using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_used_nondec cg_gen_fv_elem_size
          cg_bop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
    qed
  qed
next
  case (cg_vcon \<alpha> n1 \<beta> n2 G1 e G2 C e' C' nm \<tau>)
  then show ?case
    using ct_sem_conjE fv'_con assign_app_constr.simps by metis
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
      using cg_case.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using ct_sem_conj_iff cg_case assign_app_constr.simps by metis
    next
      case i_in_e2
      have "0 < snd (((\<beta>, 0) # G2) ! Suc i)"
        using cg_case i_in_e2 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
      moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
        using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e2 
          cg_ctx_type_same1
        by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
      ultimately show ?thesis
        using i_fv'_suc_iff_suc_i_fv' i_in_e2 cg_case ct_sem_conj_iff assign_app_constr.simps 
        by metis
    next
      case i_in_e3
      have "0 < snd (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>), 0) # G2) ! Suc i)"
        using cg_case i_in_e3 cg_ctx_length cg_ctx_type_used_nondec cg_gen_fv_elem_size 
          i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
      moreover have "\<rho> = fst (((TVariant [(nm, \<beta>, Used)] (Some \<alpha>), 0) # G2) ! Suc i)"
        using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e3
          cg_ctx_type_same1
        by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
      moreover have "A \<turnstile> assign_app_constr S S' C3"
        using cg_case ct_sem_conj_iff assign_app_constr.simps by metis
      ultimately show ?thesis
        using cg_case i_fv'_suc_iff_suc_i_fv' i_in_e3 by blast
    qed
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
  proof -
    consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
      using cg_irref.prems by fastforce
    then show ?thesis
    proof cases
      case i_in_e1
      then show ?thesis
        using cg_irref ct_sem_conj_iff assign_app_constr.simps by metis
    next
      case i_in_e2
      have "snd (G1 ! i) \<le> snd (G2 ! i)"
        using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_used_nondec 
          cg_gen_fv_elem_size by (metis Suc_less_SucD length_Cons)
      moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
        using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_same1 
          cg_gen_fv_elem_size 
        by (metis Suc_eq_plus1 length_Cons less_SucE not_add_less1 nth_Cons_Suc)
      ultimately show ?thesis
        using gr_zeroI leD ct_sem_conj_iff cg_irref i_fv'_suc_iff_suc_i_fv' by fastforce
    qed
  qed
qed (simp)+

lemma split_unionR:
  assumes "ns = ns1 \<union> ns2"
    and "\<And>i. i < length G1 \<Longrightarrow> fst (G1 ! i) = fst (G2 ! i)"
    and "A \<turnstile> assign_app_ctx S S' (G1\<bar>ns) \<leadsto> assign_app_ctx S S' (G1\<bar>ns1) \<box> assign_app_ctx S S' (G2\<bar>ns2)"
    and "\<forall>i\<in>I. i < length G1 \<and> i \<notin> ns"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(ns \<union> I)) \<leadsto> assign_app_ctx S S' (G1\<bar>ns1) \<box> assign_app_ctx S S' (G2\<bar>ns2 \<union> I)"
  using assms
proof -
  let ?SG1ns = "assign_app_ctx S S' (G1\<bar>ns)"
  let ?SG1ns' = "assign_app_ctx S S' (G1\<bar>(ns \<union> I))"
  let ?SG1ns1 = "assign_app_ctx S S' (G1\<bar>ns1)"
  let ?SG2ns2 = "assign_app_ctx S S' (G2\<bar>ns2)"
  let ?SG2ns2' = "assign_app_ctx S S' (G2\<bar>(ns2 \<union> I))"
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
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>(fv e2))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S S' (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S S' (G1\<bar>(fv e1))"
  let ?SG2e2 = "assign_app_ctx S S' (G2\<bar>(fv e2))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
    using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S S' (fst (G2!i)))"
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
        using assms cg_ctx_type_same1 i_in_e i_in_e2_SG2e2_some i_in_e_SG1e_some i_not_in_e1 i_size
          no_i_in_e1_SG1e1_none right by auto
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> (fv e2) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2: "i \<in> (fv e2)"
      have i_type_used: "snd (G2!i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S S' (fst (G2!i)))"
        using assms i_in_e2 cg_assign_type_used_nonzero_imp_share by simp
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2 i_size G1_G2_length cg_ctx_type_same1 
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
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>image (\<lambda>x. x-1) (fv e2 - {0}))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S S' (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S S' (G1\<bar>(fv e1))"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?SG2e2 = "assign_app_ctx S S' (G2\<bar>?dec_fv_e2)"
  have fv_e: "fv e = fv e1 \<union> (image (\<lambda>x. x-1) (fv e2 - {0}))"
    using assms fv'_suc_eq_minus_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2_none: "\<And>i. i < length G1 \<Longrightarrow> Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
  proof -
    have "\<And>i. Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
      using fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' by blast
    then show "\<And>i. i < length G1 \<Longrightarrow> Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  qed
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S S' (fst (G2!i)))"
  proof -
    have "\<And>i. Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
      using fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' by blast
    then show "\<And>i. i < length G1 \<Longrightarrow> Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S S' (fst (G2!i)))"
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
        by (metis G1_G2_length assign_app_ctx_restrict_some assms(2) cg_ctx_type_same1 i_in_e i_not_in_e1 i_size no_i_in_e1_SG1e1_none right)
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> ?dec_fv_e2 \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2: "i \<in> ?dec_fv_e2"
      have i_type_used: "snd (G2!i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S S' (fst (G2!i)))"
        using assms i_in_e2 cg_assign_type_used_nonzero_imp_share
        by (metis fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' nth_Cons_Suc)
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2 i_size G1_G2_length cg_ctx_type_same1 
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
    and "A \<turnstile> assign_app_constr S S' C2"
    and "A \<turnstile> assign_app_constr S S' C3"
    and "\<forall>i. known_ty (S i)"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S S' (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S S' (G1\<bar>(fv e1))"
  let ?SG2e2e3 = "assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  have no_i_in_e_SG1e_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e_SG1e_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e1_SG1e1_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
    using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def by auto
  have i_in_e1_SG1e1_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S S' (fst (G1!i)))"
    using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
  have no_i_in_e2_SG2e2e3_none: "\<And>i. i < length G1 \<Longrightarrow> i \<notin> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = None"
    using G1_G2_length assign_app_ctx_nth ctx_restrict_len ctx_restrict_nth_none
    by (metis assign_app_ctx_none_iff)
  have i_in_e2_SG2e2_some: "\<And>i. i < length G1 \<Longrightarrow> i \<in> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = Some (assign_app_ty S S' (fst (G2!i)))"
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
            no_i_in_e1_SG1e1_none type_infer.cg_ctx_type_same1 type_infer.right type_infer_axioms)
    qed
    moreover have "i \<in> (fv e1) \<and> i \<in> (fv e2 \<union> fv e3) \<Longrightarrow> ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (erule conjE)
      assume i_in_e1: "i \<in> (fv e1)"
      assume i_in_e2e3: "i \<in> (fv e2 \<union> fv e3)"
      have i_type_used: "snd (G2 ! i) > 0"
        using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
      then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S S' (fst (G2 ! i)))"
        using assms i_in_e2e3 cg_assign_type_used_nonzero_imp_share by blast
      moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
        using i_in_e i_in_e1 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def
        by auto
      moreover have "(?SG1e1 ! i) = (?SG2e2e3 ! i)"
        using assms assign_app_ctx_def i_in_e1 i_in_e2e3 i_size G1_G2_length cg_ctx_type_same1 
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

lemma split_used_case:
  assumes "e = Case e1 nm e2 e3"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "((\<gamma>, 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> ((\<gamma>, l) # G3'),n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "A \<turnstile> assign_app_constr S S' C3"
    and "\<forall>i. known_ty (S i)"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "dec_fv_e3 = image (\<lambda>x. x-1) (fv e3 - {0})"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> dec_fv_e3)"
  using assms 
proof -
  let ?SG1e = "assign_app_ctx S S' (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S S' (G1\<bar>(fv e1))"
  let ?SG2e2e3 = "assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> dec_fv_e3)"
  have fv_e: "fv e = fv e1 \<union> dec_fv_e2 \<union> dec_fv_e3"
    using assms fv'_suc_eq_minus_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms by (rule_tac cg_ctx_length; simp)
  {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by force
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by force 
    have no_i_in_e2e3_SG2e2e3_none: "i \<notin> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?SG2e2e3 ! i = None"
      using G1_G2_length assign_app_ctx_restrict_none i_size by auto
    have i_in_e2e3_SG2e2e3_some: "i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?SG2e2e3 ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using G1_G2_length assign_app_ctx_restrict_some i_size cg_ctx_type_same1 assms by auto
    have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (cases "i \<in> fv e")
      case True
      have "i \<in> fv e1 \<or> i \<in> dec_fv_e2 \<union> dec_fv_e3"
        using True fv_e by auto
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<notin> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
        using left True i_in_e_SG1e_some i_in_e1_SG1e1_some no_i_in_e2e3_SG2e2e3_none by auto
      moreover have "i \<notin> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
        using right True i_in_e_SG1e_some no_i_in_e1_SG1e1_none i_in_e2e3_SG2e2e3_some by presburger
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
      proof -
        assume i_in_e1: "i \<in> fv e1"
        assume i_in_e2e3: "i \<in> dec_fv_e2 \<union> dec_fv_e3"
        have "A \<turnstile> CtShare (assign_app_ty S S' (fst (G1 ! i)))"
        proof -
          have i_type_used: "snd (G2 ! i) > 0"
            using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
          consider (suc_i_in_e2) "Suc i \<in> fv e2" | (suc_i_in_e3) "Suc i \<in> fv e3"
            using i_in_e2e3 fv'_suc_eq_minus_fv'  assms by fastforce
          then show ?thesis
          proof cases
            case suc_i_in_e2
            have "A \<turnstile> CtShare (assign_app_ty S S' (fst (((\<beta>, 0) # G2) ! Suc i)))"
              using assms suc_i_in_e2 cg_assign_type_used_nonzero_imp_share i_type_used 
                nth_Cons_Suc by metis
            then show ?thesis
              using G1_G2_length cg_ctx_type_same1 i_size assms by force
          next
            case suc_i_in_e3
            have "A \<turnstile> CtShare (assign_app_ty S S' (fst (((\<gamma>, 0) # G2) ! Suc i)))"
              using assms suc_i_in_e3 cg_assign_type_used_nonzero_imp_share i_type_used 
                nth_Cons_Suc by metis
            then show ?thesis
              using G1_G2_length cg_ctx_type_same1 i_size assms by force
          qed
        qed
        then show "?thesis"
          using share True i_in_e1 i_in_e2e3 i_in_e_SG1e_some i_in_e1_SG1e1_some 
            i_in_e2e3_SG2e2e3_some by presburger
      qed
      ultimately show ?thesis
        using True by argo
    next
      case False
      have "i \<notin> fv e1" "i \<notin> dec_fv_e2 \<union> dec_fv_e3"
        using fv_e False by blast+
      then show ?thesis
        using ctx_split_comp.none False no_i_in_e2e3_SG2e2e3_none 
          no_i_in_e1_SG1e1_none no_i_in_e_SG1e_none by presburger
    qed
  }
  then show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len G1_G2_length assms
    by (simp add: list_all3_conv_all_nth)
      qed

lemma split_used_irref:
  assumes "e = Esac e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
  shows "A \<turnstile> assign_app_ctx S S' (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2)"
  using assms 
proof -
  let ?SG1e = "assign_app_ctx S S' (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S S' (G1\<bar>(fv e1))"
  let ?SG2e2 = "assign_app_ctx S S' (G2\<bar>dec_fv_e2)"
  have fv_e: "fv e = fv e1 \<union> dec_fv_e2"
    using assms fv'_suc_eq_minus_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms by (rule_tac cg_ctx_length; simp)
  {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by force
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by force
    have no_i_in_e2_SG2e2_none: "i \<notin> dec_fv_e2 \<Longrightarrow> ?SG2e2 ! i = None"
      using G1_G2_length assign_app_ctx_restrict_none i_size cg_ctx_type_same1 assms by metis
    have i_in_e2_SG2e2_some: "i \<in> dec_fv_e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
      using G1_G2_length assign_app_ctx_restrict_some i_size cg_ctx_type_same1 assms by metis
    have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (cases "i \<in> fv e")
      case True
      then have "i \<in> fv e1 \<or> i \<in> dec_fv_e2"
        using fv_e by simp
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<notin> dec_fv_e2 \<Longrightarrow> ?thesis"
        using left True i_in_e_SG1e_some i_in_e1_SG1e1_some no_i_in_e2_SG2e2_none by presburger
      moreover have "i \<notin> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<Longrightarrow> ?thesis"
        using right True i_in_e_SG1e_some no_i_in_e1_SG1e1_none i_in_e2_SG2e2_some by presburger
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<Longrightarrow> ?thesis"
      proof -
        assume i_in_e1: "i \<in> fv e1"
        assume i_in_e2: "i \<in> dec_fv_e2"
        have "A \<turnstile> CtShare (assign_app_ty S S' (fst (G1 ! i)))"
        proof -
          have i_type_used: "snd (G2 ! i) > 0"
            using cg_gen_output_type_used_nonzero assms i_in_e1 by auto
          then have "A \<turnstile> CtShare (assign_app_ty S S' (fst (((\<beta>, 0) # G2) ! Suc i)))"
            using assms fv'_suc_eq_minus_fv' i_fv'_suc_iff_suc_i_fv' i_in_e2 
            cg_assign_type_used_nonzero_imp_share nth_Cons_Suc by (metis nth_Cons_Suc)
          then show ?thesis
            using G1_G2_length cg_ctx_type_same1 i_size assms by force
        qed
        then show ?thesis
          using share True i_in_e1 i_in_e2 i_in_e_SG1e_some i_in_e1_SG1e1_some i_in_e2_SG2e2_some 
          by presburger
      qed
      ultimately show ?thesis
        by fast
    next
      case False
      then show ?thesis
        using ctx_split_comp.none fv_e no_i_in_e2_SG2e2_none no_i_in_e1_SG1e1_none no_i_in_e_SG1e_none 
        by auto
    qed
  }
  then show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len G1_G2_length assms
    by (simp add: list_all3_conv_all_nth)
      qed

lemma split_used_extR:
  assumes "fv e = (fv e1) \<union> (fv e2)"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<rho> \<leadsto> G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>(fv e1)) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> idxs))"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2)"
    using split_used assms by blast
  then have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2 \<union> idxs)"
    using assms by (rule_tac split_unionR; force intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs)"
  proof (rule nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S S' (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_len by presburger
    moreover {
      fix i :: nat
      assume i_size: "i < length G1"
      have "\<Gamma> ! i = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) ! i"
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
    then show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
      using assms by presburger
  qed
  ultimately show ?thesis
    by auto
qed

lemma split_used_let_extR:
  assumes "e = Let e1 e2"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "((\<tau>,m) # G2),n2 \<turnstile> e2 : \<rho> \<leadsto> ((\<tau>,m') # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2)"
    using split_used_let assms by simp
  then have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> idxs)"
    using assms fv'_suc_eq_minus_fv' by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs)"
  proof (rule nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S S' (G1\<bar>fv e \<union> idxs))"
      using assms ctx_restrict_len assign_app_ctx_len by presburger
    moreover { 
      fix i :: nat
      assume i_size: "i < length G1"
      have "\<Gamma> ! i = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) ! i"
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
    ultimately show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
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
    and "A \<turnstile> assign_app_constr S S' C2"
    and "A \<turnstile> assign_app_constr S S' C3"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3) \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3))"
    using split_used_if assms by meson
  then have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3) \<union> idxs)"
    using assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs)"
  proof (intro nth_equalityI)
    show "length \<Gamma> = length (assign_app_ctx S S' (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      have "\<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
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
    then show "\<forall>i < length \<Gamma>. \<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
      by blast
  qed
  ultimately show ?thesis
    by auto
qed

lemma split_used_case_extR:
  assumes "e = Case e1 nm e2 e3"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "((\<gamma>, 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> ((\<gamma>, l) # G3'),n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "A \<turnstile> assign_app_constr S S' C3"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "dec_fv_e3 = image (\<lambda>x. x-1) (fv e3 - {0})"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(dec_fv_e2 \<union> dec_fv_e3) \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(dec_fv_e2 \<union> dec_fv_e3))"
    using split_used_case assms by meson
  then have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(dec_fv_e2 \<union> dec_fv_e3) \<union> idxs)"
    using fv'_suc_eq_minus_fv' assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S S' (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    moreover { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      consider (case_1) "i \<in> fv e" | (case_2) "i \<notin> fv e" "\<Gamma> ! i = None" | (case_3) "i \<notin> fv e" "\<Gamma> ! i \<noteq> None"
        by fast
      then have "\<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
      proof cases
        case case_1
        then show ?thesis
          using assms i_size by (metis (no_types, lifting) Un_iff assign_app_ctx_restrict_some)
      next
        case case_2
        have "i \<notin> fv e \<union> idxs"
          using case_2 assms by auto
        then show ?thesis
          using case_2 assign_app_ctx_none_iff assms ctx_restrict_len ctx_restrict_nth_none i_size 
          by (metis (no_types, lifting))
      next
        case case_3
        have "i \<in> fv e \<union> idxs"
          using case_3 assms i_size by auto 
        then show ?thesis
          using case_3 i_size assms assign_app_ctx_restrict_some by (metis (no_types, lifting))
      qed
    }
    ultimately show ?thesis
      using nth_equalityI by blast
  qed
  ultimately show ?thesis
    by auto
qed

lemma split_used_irref_extR:
  assumes "e = Esac e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S S' C2"
    and "\<forall>i. known_ty (S i)"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
  shows "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> idxs)"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2)"
    using split_used_irref assms by meson
  then have "A \<turnstile> assign_app_ctx S S' (G1\<bar>fv e \<union> idxs) \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>dec_fv_e2 \<union> idxs)"
    using fv'_suc_eq_minus_fv' assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S S' (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S S' (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    moreover { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      consider (case_1) "i \<in> fv e" | (case_2) "i \<notin> fv e" "\<Gamma> ! i = None" | (case_3) "i \<notin> fv e" "\<Gamma> ! i \<noteq> None"
        by fast
      then have "\<Gamma> ! i = assign_app_ctx S S' (G1 \<bar> fv e \<union> idxs) ! i"
      proof cases
        case case_1
        then show ?thesis
          using assms i_size by (metis (no_types, lifting) Un_iff assign_app_ctx_restrict_some)
      next
        case case_2
        have "i \<notin> fv e \<union> idxs"
          using case_2 assms by auto
        then show ?thesis
          using case_2 assign_app_ctx_none_iff assms ctx_restrict_len ctx_restrict_nth_none i_size 
          by (metis (no_types, lifting))
      next
        case case_3
        have "i \<in> fv e \<union> idxs"
          using case_3 assms i_size by auto 
        then show ?thesis
          using case_3 i_size assms assign_app_ctx_restrict_some by (metis (no_types, lifting))
      qed
    }
    ultimately show ?thesis
      using nth_equalityI by blast
  qed
  ultimately show ?thesis
    by auto
qed


section {* Soundness of Generation (Thm 3.2) *}
definition assign_prop :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> (string \<times> type \<times> usage_tag) list) \<Rightarrow> bool" where
  "assign_prop S S' \<equiv> (\<forall>i. known_ty (S i)) & 
                      (\<forall>Ks Ks' m. assign_app_ty S S' (TVariant Ks (Some m)) = TVariant Ks' None 
                                  \<longrightarrow> distinct (map fst Ks')) &
                      (\<forall>i j. j < length (S' i) \<longrightarrow> known_ty ((fst \<circ> snd) ((S' i) ! j)))"

lemma cg_sound_induction:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "A \<turnstile> assign_app_constr S S' C" 
    and "assign_prop S S'"
    and "\<And>i. i < length G \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G ! i)))
              else \<Gamma> ! i = None \<or>
                (\<Gamma> ! i = Some (assign_app_ty S S' (fst (G ! i))) \<and> A \<turnstile> assign_app_constr S S' (CtDrop (fst (G ! i))))"
    and "length G = length \<Gamma>"
  shows "A \<ddagger> \<Gamma> \<turnstile> (assign_app_expr S S' e') : (assign_app_ty S S' \<tau>)"
  using assms 
proof (induct arbitrary: S S' \<Gamma> rule: constraint_gen_elab.inducts)
  case (cg_var1 G i \<rho> G' C \<tau> n)
  then show ?case
  proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Var i : (assign_app_ty S S' \<rho>)"
    proof -
      have "A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>)"
      proof -
        have "length \<Gamma> = length (singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>))"
          by (simp add: singleton_len)
        moreover have "(\<And>ia. ia < length \<Gamma> \<Longrightarrow>
                        weakening_comp A (\<Gamma> ! ia) 
                        (singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>) ! ia))"
        proof -
          {
            fix ia :: nat
            assume ia_size: "ia < length \<Gamma>"
            show "?thesis ia"
            proof (cases "ia = i")
              case True
              have "\<Gamma> ! i = Some (assign_app_ty S S' (fst (G ! i)))"
                using cg_var1.hyps cg_var1.prems by fastforce
              then show ?thesis
                using True cg_var1.hyps ia_size keep singleton_some by auto
            next
              case False
              then show ?thesis 
                using ia_size cg_var1 singleton_none weakening_comp.simps by fastforce
            qed
          }
        qed
        ultimately show ?thesis
          using cg_var1.hyps cg_var1.prems weakening_def
          by (metis list_all2_all_nthI)
      qed
      then show ?thesis
        using cg_var1.prems cg_var1.hyps typing_var by auto
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S S' \<rho>) (assign_app_ty S S' \<tau>)"
      using cg_var1.prems cg_var1.hyps ct_sem_conjE assign_app_constr.simps by metis
    ultimately show ?thesis
      using typing_sig by simp
  qed
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
  then show ?case
  proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Var i : (assign_app_ty S S' \<rho>)"
    proof -
      have "A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>)"
      proof -
        have "length \<Gamma> = length (singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>))"
          by (simp add: singleton_len)
        moreover have "(\<And>ia. ia < length \<Gamma> \<Longrightarrow>
                        weakening_comp A (\<Gamma> ! ia) 
                        (singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>) ! ia))"
        proof -
          have "\<Gamma> ! i = Some (assign_app_ty S S' (fst (G ! i)))"
            using cg_var2 by fastforce
          moreover have "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ia \<noteq> i \<Longrightarrow> 
                               singleton (length \<Gamma>) i (assign_app_ty S S' \<rho>) ! ia = None"
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
    moreover have "A \<turnstile> CtSub (assign_app_ty S S' \<rho>) (assign_app_ty S S' \<tau>)"
      using cg_var2.prems cg_var2.hyps ct_sem_conjE assign_app_constr.simps by metis
    ultimately show ?thesis
      using typing_sig by simp
  qed
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C e' C' \<tau>)
  then show ?case
  proof -
    have "A \<ddagger> \<Gamma> \<turnstile> Sig (assign_app_expr S S' e') (assign_app_ty S S' \<tau>') : (assign_app_ty S S' \<tau>')"
    proof -
      have "A \<turnstile> (assign_app_constr S S' C)"
        using cg_sig.prems cg_sig.hyps ct_sem_conjE assign_app_constr.simps by metis
      then have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S S' e' : (assign_app_ty S S' \<tau>')"
        using cg_sig.prems cg_sig.hyps(2) by auto
      then show ?thesis
        using typing_sig_refl by simp
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S S' \<tau>') (assign_app_ty S S' \<tau>)"
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
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_app assign_prop_def
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_app assign_app_constr.simps ct_sem_conjE by metis
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (App e1 e2) 
                                   then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_app by meson
    qed (fastforce)+
    moreover have "A \<ddagger>  assign_app_ctx S S' (G1 \<bar> fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' (TFun \<alpha> \<tau>)"
      using cg_app
    proof (intro cg_app.hyps(3))
      {
        fix i
        assume i_size: "i < length G1"
        show "if i \<in> fv' 0 e1 then assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
         else assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = None \<or>
              assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_restrict_some i_size assign_app_ctx_none_iff ctx_restrict_len 
            ctx_restrict_nth_none_iff i_size by auto
      }
    qed (force simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_def)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<alpha>"
      using cg_app
    proof (intro cg_app.hyps(5))
      fix i
      assume i_size: "i < length G2"
      show "if i \<in> fv e2
         then assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i)))
         else assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
        using cg_app cg_ctx_type_same1 i_size ctx_restrict_def
        by (auto split: if_splits; clarsimp simp add: assign_app_ctx_nth; metis option.distinct(1) option.sel)
    qed (force simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len)+
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
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>?dec_fv_e2 \<union> ?idxs)"
      using cg_let assign_prop_def
    proof (rule_tac split_used_let_extR)
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_let assign_app_constr.simps ct_sem_conjE by metis
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                   then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_let by meson
    qed (fastforce)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G1 \<bar> fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' \<alpha>"
      using cg_let
    proof (intro cg_let.hyps(3))
      fix i :: nat
      assume i_size: "i < length G1"
      show "if i \<in> fv e1 
        then assign_app_ctx S S' (G1 \<bar> fv e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
        else assign_app_ctx S S' (G1 \<bar> fv e1) ! i = None \<or>
             assign_app_ctx S S' (G1 \<bar> fv e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i))) \<and> 
             A \<turnstile> assign_app_constr S S' (CtDrop (fst (G1 ! i)))"
        using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by auto
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    moreover have "A \<ddagger> Some (S n1) # assign_app_ctx S S' (G2 \<bar> ?dec_fv_e2 \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<tau>"
      using cg_let
    proof (intro cg_let.hyps(5))
      fix i :: nat
      assume i_size: "i < length ((\<alpha>, 0) # G2)"
      show "if i \<in> fv e2
        then (Some (S n1) # assign_app_ctx S S' (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i =
              Some (assign_app_ty S S' (fst (((\<alpha>, 0) # G2) ! i)))
        else (Some (S n1) # assign_app_ctx S S' (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i = None \<or>
             (Some (S n1) # assign_app_ctx S S' (G2 \<bar> ?dec_fv_e2 \<union> ?idxs)) ! i =
              Some (assign_app_ty S S' (fst (((\<alpha>, 0) # G2) ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (((\<alpha>, 0) # G2) ! i)))"
      proof (cases "i = 0")
        case True
        then show ?thesis
          using cg_let cg_gen_output_type_unused_same 
          by (auto split: if_splits; metis ct_sem_conj_iff i_size less_not_refl2 nth_Cons_0 snd_conv)
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
            then have "A \<turnstile> assign_app_constr S S' (CtDrop (fst (G1 ! (i - 1))))"
              by (meson atLeastLessThan_iff cg_let.prems dec_i_in_idxs member_filter)
            then have "A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! (i - 1))))"
              using cg_ctx_type_same1 cg_let.hyps dec_i_in_idxs by auto
          }
          ultimately show ?thesis
            using assign_app_ctx_restrict_some i_nonzero i_size 
            by (simp only: nth_Cons' i_nonzero; case_tac "i - 1 \<notin> ?idxs"; fastforce)
        qed
      qed
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
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
    moreover have "assign_app_ty S S' \<tau> = TPrim Bool"
      using cg_blit ct_sem_eq_iff by auto
    ultimately show ?thesis
      using typing_sig_refl typing_blit by force 
  qed
next
  case (cg_ilit C m \<tau> G n)  
  then show ?case
  proof -
    obtain n where n_def: "(assign_app_ty S S' \<tau>) = TPrim (Num n)"
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
    moreover have "assign_app_ty S S' \<tau> = TPrim (Num n)"
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
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs)"
      using cg_if
    proof (rule_tac split_used_if_extR)
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_if assign_app_constr.simps ct_sem_conjE by metis
      show "A \<turnstile> assign_app_constr S S' C3"
        using cg_if assign_app_constr.simps ct_sem_conjE by metis
      show "\<forall>i. known_ty (S i)"
        using cg_if assign_prop_def by meson
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                  then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                  else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_if.prems by meson
    qed (blast)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G1\<bar>fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' (TPrim Bool)"
      using cg_if
    proof (intro cg_if.hyps(2))
      {
        fix i :: nat
        assume i_size : "i < length G1"
        show "if i \<in> fv e1 
          then assign_app_ctx S S' (G1 \<bar> fv e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
          else assign_app_ctx S S' (G1 \<bar> fv e1) ! i = None \<or>
               assign_app_ctx S S' (G1 \<bar> fv e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i))) \<and> 
               A \<turnstile> assign_app_constr S S' (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_nth i_size ctx_restrict_def by simp
      }
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<tau>"
      using cg_if
    proof (intro cg_if.hyps(4))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        show "if i \<in> fv e2
         then assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i)))
         else assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
        proof (cases "i \<in> fv e2")
          case False
          consider (i_in_e3) "i \<in> fv e3" | (i_in_idxs) "i \<in> ?idxs" | (i_in_neither) "i \<notin> fv e3 \<union> ?idxs"
            by blast
          then show ?thesis
          proof cases
            case i_in_e3
            have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G4 ! i)))"
              using cg_if ct_sem_conj_iff i_size cg_ctx_idx_size
            proof (rule_tac alg_ctx_jn_type_used_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
              show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
                using cg_gen_output_type_used_diff cg_if False i_in_e3 i_size 
                  cg_gen_output_type_unused_same by metis
            qed (force)+
            then show ?thesis
              using cg_if.hyps assign_app_ctx_restrict_some i_in_e3 alg_ctx_jn_type_same1 
                cg_ctx_length cg_ctx_type_same1 i_size by (auto simp add: False)
          next
            case i_in_idxs
            have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
              using cg_if assign_app_constr.simps cg_ctx_length cg_ctx_type_same1 i_in_idxs i_size 
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
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G2\<bar>(fv e2 \<union> fv e3) \<union> ?idxs) \<turnstile> assign_app_expr S S' e3' : assign_app_ty S S' \<tau>"
      using cg_if
    proof (intro cg_if.hyps(6))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        show "if i \<in> fv e3
         then assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i)))
         else assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S S' (G2 \<bar> ?fve2e3 \<union> ?idxs) ! i = Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
        proof (cases "i \<in> fv e3")
          case False
          consider (i_in_e2) "i \<in> fv e2" | (i_in_idxs) "i \<in> ?idxs" | (i_in_neither) "i \<notin> fv e2 \<union> ?idxs"
            by blast
          then show ?thesis
          proof cases
            case i_in_e2
            have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G4 ! i)))"
              using cg_if ct_sem_conj_iff i_size cg_ctx_idx_size
            proof (rule_tac alg_ctx_jn_type_used_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
              show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
                using cg_gen_output_type_used_diff cg_if False i_in_e2 i_size 
                  cg_gen_output_type_unused_same by metis
            qed (force)+
            then show ?thesis
              using cg_if.hyps assign_app_ctx_restrict_some i_in_e2 alg_ctx_jn_type_same1 
                cg_ctx_length cg_ctx_type_same1 i_size by (auto simp add: False)
          next
            case i_in_idxs
            have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
              using cg_if assign_app_constr.simps cg_ctx_length cg_ctx_type_same1 i_in_idxs i_size 
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
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    ultimately show ?thesis
      using typing_sig_refl typing_if by simp
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  then show ?case
  proof -
    let ?e="Prim x [e1, e2]"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_iop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_iop assign_app_constr.simps ct_sem_conjE by metis
      show "\<forall>i. known_ty (S i)"
        using cg_iop assign_prop_def by metis
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                   then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_iop by meson
    qed (fastforce)+
    moreover have "assign_app_ty S S' \<tau> \<noteq> TPrim Bool"
      using ct_sem_int_not_bool cg_iop ct_sem_conj_iff assign_app_constr.simps by metis
    moreover have "x \<in> {Plus nt, Minus nt, Times nt, Divide nt}"
      using cg_iop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S S' (G1\<bar>fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' \<tau>"
      using cg_iop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len 
        assign_app_ctx_restrict_some ctx_restrict_nth_none by (intro cg_iop.hyps(3); simp)
    moreover have "A \<ddagger> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<tau>"
      using cg_iop
    proof (intro cg_iop.hyps(5))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        have "i \<notin> fv e2 \<and> assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some y \<Longrightarrow> i \<in> ?idxs"
          using assign_app_ctx_restrict_some_ex i_size by fastforce
        then show "if i \<in> fv e2
         then assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S S' (fst (G2 ! i)))
         else assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              None \<or>
              assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
        proof -
          {
            assume i_not_in_e2: "i \<notin> fv e2"
            assume not_none: "\<exists>y. assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some y"
            have "i \<in> ?idxs"
              using i_not_in_e2 not_none i_size assign_app_ctx_restrict_some_ex by blast
            then have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
              using cg_iop cg_ctx_type_same1 by fastforce
          }
          then show ?thesis
            using assign_app_ctx_restrict_some assign_app_ctx_restrict_some_val i_size
            by (auto split: if_splits; simp)
        qed
      }
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
    ultimately show ?thesis
      using typing_sig_refl typing_iop by force
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  then show ?case
  proof -
    let ?e="Prim x [e1, e2]"
    let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_cop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_cop assign_app_constr.simps ct_sem_conjE by metis
      show "\<forall>i. known_ty (S i)"
        using cg_cop assign_prop_def by meson
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (Prim x [e1, e2]) 
                                   then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_cop by meson
    qed (fastforce)+
    moreover have "S n1 \<noteq> TPrim Bool" 
      using ct_sem_int_not_bool cg_cop ct_sem_conj_iff assign_app_constr.simps by auto
    moreover have "x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}"
      using cg_cop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S S' (G1\<bar>fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' \<alpha>"
      using cg_cop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len
      by (intro cg_cop(4); force simp add: ctx_restrict_def)
    moreover have "A \<ddagger> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<alpha>"
      using cg_cop
    proof (intro cg_cop(6))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume "\<exists>y. assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) ! i = Some y"
          then have "i \<in> ?idxs"
            using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by fastforce
          then have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
            using cg_cop cg_ctx_type_same1 by fastforce
        }
        then show "if i \<in> fv e2
         then assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S S' (fst (G2 ! i)))
         else assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) ! i = None \<or>
              assign_app_ctx S S' (G2 \<bar>fv e2 \<union> ?idxs) ! i =
              Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
          using assign_app_ctx_restrict_some assign_app_ctx_restrict_some_val i_size by auto
      }
    qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "assign_app_ty S S' \<tau> = TPrim Bool"
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
    have "A \<turnstile> \<Gamma> \<leadsto> assign_app_ctx S S' (G1\<bar>fv e1) \<box> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs)"
      using cg_bop
    proof (rule_tac split_used_extR[where ?e="?e"])
      show "A \<turnstile> assign_app_constr S S' C2"
        using cg_bop assign_app_constr.simps ct_sem_conjE by metis
      show "\<forall>i. known_ty (S i)"
        using cg_bop assign_prop_def by metis
      show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (Prim x [e1, e2]) 
                                   then \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S S' (fst (G1 ! i)))"
        using cg_bop by meson
    qed (fastforce)+
    moreover have "x \<in> {BitAnd nt, BitOr nt}"
      using cg_bop.hyps by simp
    moreover have "A \<ddagger> assign_app_ctx S S' (G1\<bar>fv e1) \<turnstile> assign_app_expr S S' e1' : assign_app_ty S S' \<tau>"
      using cg_bop
    proof (intro cg_bop.hyps(3))
      {
        fix i :: nat
        assume i_size: "i < length G1"
        show "if i \<in> fv' 0 e1
         then assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i)))
         else assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = None \<or>
              assign_app_ctx S S' (G1 \<bar> fv' 0 e1) ! i = Some (assign_app_ty S S' (fst (G1 ! i))) \<and> 
              A \<turnstile> assign_app_constr S S' (CtDrop (fst (G1 ! i)))"
          using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by simp
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "A \<ddagger> assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) \<turnstile> assign_app_expr S S' e2' : assign_app_ty S S' \<tau>"
      using cg_bop
    proof (intro cg_bop.hyps(5))
      {
        fix i :: nat
        assume i_size: "i < length G2"
        {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume "\<exists>y. assign_app_ctx S S' (G2\<bar>fv e2 \<union> ?idxs) ! i = Some y"
          then have "i \<in> ?idxs"
            using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by fastforce
          then have "A \<turnstile> CtDrop (assign_app_ty S S' (fst (G2 ! i)))"
            using cg_bop cg_ctx_type_same1 by fastforce
        }
        then show "if i \<in> fv e2
          then assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i =
               Some (assign_app_ty S S' (fst (G2 ! i)))
          else assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i = None \<or>
               assign_app_ctx S S' (G2 \<bar> fv e2 \<union> ?idxs) ! i =
               Some (assign_app_ty S S' (fst (G2 ! i))) \<and>
               A \<turnstile> assign_app_constr S S' (CtDrop (fst (G2 ! i)))"
          using i_size assign_app_ctx_restrict_some_val assign_app_ctx_restrict_some by auto
      }
    qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
    moreover have "assign_app_ty S S' \<tau> = TPrim Bool"
      using cg_bop ct_sem_conj_iff ct_sem_eq_iff by auto
    ultimately show ?thesis
      using typing_sig_refl typing_bop by force
  qed
next
  case (cg_tapp name C \<rho> m ts \<beta>s n1 \<rho>' C' C2 \<tau> n' n G)
  then show ?case
      proof -
    have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S S' (TypeApp name (ts @ \<beta>s)) : (assign_app_ty S S' \<rho>')"
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
      moreover have "A \<turnstile> assign_app_constr S S' (subst_ct (ts @ \<beta>s) C)"
        using cg_tapp.hyps cg_tapp.prems ct_sem_conjE by auto
      moreover have "assign_app_ty S S' \<rho>' = assign_app_ty S S' (subst_ty (ts @ \<beta>s) \<rho>)"
        using cg_tapp.hyps by blast
      ultimately show ?thesis
        using assign_app_constr_subst_ct_commute assign_app_ty_subst_ty_commute type_of_known
          typing_tapp by auto
    qed
    moreover have "A \<turnstile> CtSub (assign_app_ty S S' \<rho>') (assign_app_ty S S' \<tau>)"
      using cg_tapp.hyps cg_tapp.prems ct_sem_conj_iff by auto
    ultimately show ?thesis
      using typing_sig by simp
  qed
next
  case (cg_vcon \<alpha> n2 \<beta> n1 G1 e G2 C e' C' nm \<tau>)
  then show ?case
  proof -
    obtain Ks where ks_def: "TVariant Ks None = assign_app_ty S S' (TVariant [(nm, \<beta>, Unused)] (Some \<alpha>))"
      by simp
    obtain Ks' where ks'_def: "Ks' = (map variant_elem_used Ks)[0 := Ks ! 0]" by blast
    have ks'_hd_type: "(fst \<circ> snd) (Ks' ! 0) = S n1"
      using ks'_def ks_def cg_vcon.hyps by force
    have ks'_ks_prop: "length Ks' = length Ks \<and> (\<forall>i < length Ks'. fst (Ks' ! i) = fst (Ks ! i)
                                          \<and> A \<turnstile> CtSub ((fst \<circ> snd) (Ks' ! i)) ((fst \<circ> snd) (Ks ! i))
                                          \<and> (snd \<circ> snd) (Ks' ! i) \<le> (snd \<circ> snd) (Ks ! i))"
    proof - 
      {
        fix i :: nat
        assume i_size: "i < length Ks'"
        then have "fst (Ks' ! i) = fst (Ks ! i) \<and> 
                   A \<turnstile> CtSub ((fst \<circ> snd) (Ks' ! i)) ((fst \<circ> snd) (Ks ! i)) \<and> 
                   (snd \<circ> snd) (Ks' ! i) \<le> (snd \<circ> snd) (Ks ! i)"
        proof (cases "i = 0")
          case True
          then show ?thesis 
            using i_size ks'_def ct_sem_equal ct_sem_refl by force
        next
          case False
          then show ?thesis
            using ks'_def map_conv_all_nth ct_sem_equal ct_sem_refl i_size variant_elem_used_nm_eq 
              variant_elem_used_type_eq variant_elem_used_usage_nondec by auto
        qed
      } then show ?thesis using ks'_def by fastforce
    qed
    have "distinct (map fst Ks')"
      using ks'_ks_prop cg_vcon.prems ks'_def ks_def assign_prop_def
      by (metis (no_types, lifting)  map_eq_iff_nth_eq)
    moreover have "\<forall>i<length Ks'. if i = 0 then (snd \<circ> snd) (Ks' ! i) = Unused 
                                           else (snd \<circ> snd) (Ks' ! i) = Used"
    proof -
      {
        fix i :: nat
        assume i_size: "i < length Ks'"
        then have "if i = 0 then (snd \<circ> snd) (Ks' ! i) = Unused else (snd \<circ> snd) (Ks' ! i) = Used"
          using ks'_def ks_def
        proof (cases "i = 0")
          case False
          then show ?thesis
            using variant_elem_used_usage_used i_size ks'_def by auto
        qed (simp)
      } then show ?thesis by blast
    qed
    moreover have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S S' e' : assign_app_ty S S' \<beta>"
      using cg_vcon ct_sem_conj_iff by auto
    moreover have "A \<turnstile> CtSub (TVariant Ks' None) (assign_app_ty S S' \<tau>)"
      using cg_vcon
    proof -
      have "A \<turnstile> CtSub (TVariant Ks None) (assign_app_ty S S' \<tau>)"
        using cg_vcon ct_sem_conj_iff ks_def by simp
      then show ?thesis
        using ks'_ks_prop ct_sem_varsub_conv_all_nth ct_sem_sub_trans by blast
    qed
    ultimately show ?thesis
      using typing_sig typing_vcon[where Ks="Ks'" and i="0"] ks'_hd_type cg_vcon.hyps 
        ks'_def ks_def by fastforce
  qed
next
  case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case sorry
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case sorry
qed

lemma cg_sound:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "G = []"
    and "A \<turnstile> assign_app_constr S S' C"      
    and "assign_prop S S'"  
  shows "A \<ddagger> [] \<turnstile> (assign_app_expr S S' e') : (assign_app_ty S S' \<tau>)"
  using assms cg_sound_induction by force

end
end