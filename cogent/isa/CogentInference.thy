theory CogentInference
  imports Util
begin

lemma nondec_fun_prop:
  assumes "\<forall>i < n. P i \<le> P (Suc i)"
    and "\<And>a b. P a = P b \<Longrightarrow> P a \<le> P b"
    and "\<And>a b c. P a \<le> P b \<Longrightarrow> P b \<le> P c \<Longrightarrow> P a \<le> P c"
  shows "j \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> P j \<le> P k"
proof (induct "k - j" arbitrary: k)
  case 0
  then show ?case using assms by force
next
  case (Suc x)
  consider (equal) "Suc j = k" | (larger) "j < k - 1"
    using Suc by linarith
  then show ?case
  proof cases
    case equal
    then show ?thesis using assms Suc by force
  next
    case larger
    have "P j \<le> P (k - 1)" 
      using larger Suc by simp
    moreover have "P (k - 1) \<le> P k"
      using assms larger diff_Suc_1 less_diff_conv less_imp_Suc_add not_less not_less_eq
      by (metis local.Suc(4))
    ultimately show ?thesis using assms by blast
  qed 
qed 

lemma constant_fun_prop':
  assumes "\<forall>i < n. P i = P (Suc i)"
  shows "j \<le> k \<Longrightarrow> k \<le> n \<Longrightarrow> P j = P k"
proof (induct "k - j" arbitrary: k)
  case 0
  then show ?case by force
next
  case (Suc x)
  consider (equal) "Suc j = k" | (larger) "j < k - 1"
    using Suc by linarith
  then show ?case
  proof cases
    case equal
    then show ?thesis using assms Suc by force
  next
    case larger
    have "P j = P (k - 1)" 
      using larger Suc by simp
    moreover have "P (k - 1) = P k"
      using assms larger diff_Suc_1 less_diff_conv less_imp_Suc_add not_less not_less_eq
      by (metis local.Suc(4))
    ultimately show ?thesis by argo
  qed
qed

lemma constant_fun_prop:
  assumes "\<forall>i < n. P i = P (Suc i)"
    and "j \<le> n \<and> k \<le> n"
  shows "P j = P k"
proof -
  consider (smaller) "j \<le> k" | (larger) "j \<ge> k"
    by fastforce
  then show ?thesis
  proof cases
    case smaller
    then show ?thesis using constant_fun_prop' assms by blast
  next
    case larger
    then show ?thesis using constant_fun_prop'[where ?j=k and ?k=j] assms by metis
  qed
qed


datatype num_type = U8 | U16 | U32 | U64

datatype prim_type = Num num_type | Bool

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


datatype variant_usage_tag = Checked | Unchecked
datatype record_usage_tag = Taken | Present

instantiation variant_usage_tag :: "{boolean_algebra, linorder}"
begin

fun uminus_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag" where
  "uminus_variant_usage_tag Checked   = Unchecked"
| "uminus_variant_usage_tag Unchecked = Checked"

definition top_variant_usage_tag :: variant_usage_tag where
  "top_variant_usage_tag \<equiv> Unchecked"
declare top_variant_usage_tag_def[simp]

definition bot_variant_usage_tag :: variant_usage_tag where
  "bot_variant_usage_tag \<equiv> Checked"
declare bot_variant_usage_tag_def[simp]

fun inf_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag \<Rightarrow> variant_usage_tag" where
  "inf_variant_usage_tag Checked   _      = Checked"
| "inf_variant_usage_tag Unchecked Checked   = Checked"
| "inf_variant_usage_tag Unchecked Unchecked = Unchecked"

fun sup_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag \<Rightarrow> variant_usage_tag" where
  "sup_variant_usage_tag Unchecked _      = Unchecked"
| "sup_variant_usage_tag Checked   Unchecked = Unchecked"
| "sup_variant_usage_tag Checked   Checked   = Checked"

fun less_eq_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag \<Rightarrow> bool" where
  "less_eq_variant_usage_tag _      Unchecked = True"
| "less_eq_variant_usage_tag Checked   Checked   = True"
| "less_eq_variant_usage_tag Unchecked Checked   = False"

fun less_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag \<Rightarrow> bool" where
  "less_variant_usage_tag _      Checked   = False"
| "less_variant_usage_tag Unchecked Unchecked = False"
| "less_variant_usage_tag Checked   Unchecked = True"

definition minus_variant_usage_tag :: "variant_usage_tag \<Rightarrow> variant_usage_tag \<Rightarrow> variant_usage_tag" 
  where "minus_variant_usage_tag x y \<equiv> inf x (- y)"
declare minus_variant_usage_tag_def[simp]

instance proof
  fix x y z :: variant_usage_tag

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

instantiation record_usage_tag :: "{boolean_algebra, linorder}"
begin

fun uminus_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag" where
  "uminus_record_usage_tag Taken   = Present"
| "uminus_record_usage_tag Present = Taken"

definition top_record_usage_tag :: record_usage_tag where
  "top_record_usage_tag \<equiv> Taken"
declare top_record_usage_tag_def[simp]

definition bot_record_usage_tag :: record_usage_tag where
  "bot_record_usage_tag \<equiv> Present"
declare bot_record_usage_tag_def[simp]

fun inf_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag \<Rightarrow> record_usage_tag" where
  "inf_record_usage_tag Present _       = Present"
| "inf_record_usage_tag Taken   Present = Present"
| "inf_record_usage_tag Taken   Taken   = Taken"

fun sup_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag \<Rightarrow> record_usage_tag" where
  "sup_record_usage_tag Taken   _       = Taken"
| "sup_record_usage_tag Present Taken   = Taken"
| "sup_record_usage_tag Present Present = Present"

fun less_eq_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag \<Rightarrow> bool" where
  "less_eq_record_usage_tag _       Taken   = True"
| "less_eq_record_usage_tag Present Present = True"
| "less_eq_record_usage_tag Taken   Present = False"

fun less_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag \<Rightarrow> bool" where
  "less_record_usage_tag _       Present = False"
| "less_record_usage_tag Taken   Taken   = False"
| "less_record_usage_tag Present Taken   = True"

definition minus_record_usage_tag :: "record_usage_tag \<Rightarrow> record_usage_tag \<Rightarrow> record_usage_tag" where
  "minus_record_usage_tag x y \<equiv> inf x (- y)"
declare minus_record_usage_tag_def[simp]

instance proof
  fix x y z :: record_usage_tag

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
type_synonym unif_var = nat

datatype sigil = Writable 
               | ReadOnly
               | Unboxed
               | SUnknown index

datatype type = TVar index
              | TFun type type
              | TPrim prim_type
              | TUnknown index
              | TVariant "(name \<times> type \<times> variant_usage_tag) list" "unif_var option"
              | TAbstract name "type list" sigil
              | TRecord "(name \<times> type \<times> record_usage_tag) list" "unif_var option" sigil
              | TObserve index
              | TBang type

datatype lit = LBool bool
             | LNat nat


fun abs :: "num_type \<Rightarrow> nat" where
"abs U8 = 256"
| "abs U16 = 512"
| "abs U32 = 1024"
| "abs U64 = 2048"

fun subst_ty :: "type \<Rightarrow> type \<Rightarrow> type \<Rightarrow> type" where
  "subst_ty \<mu> \<mu>' (TVar i)             = (if \<mu> = (TVar i) then \<mu>' else (TVar i))"
| "subst_ty \<mu> \<mu>' (TFun \<tau> \<rho>)           = (if \<mu> = (TFun \<tau> \<rho>) then \<mu>' 
                                         else (TFun (subst_ty \<mu> \<mu>' \<tau>) (subst_ty \<mu> \<mu>' \<rho>)))"
| "subst_ty \<mu> \<mu>' (TPrim pt)           = (if \<mu> = (TPrim pt) then \<mu>' else TPrim pt)"
| "subst_ty \<mu> \<mu>' (TUnknown i)         = (if \<mu> = (TUnknown i) then \<mu>' else (TUnknown i))"
| "subst_ty \<mu> \<mu>' (TVariant Ks \<alpha>)      = (if \<mu> = (TVariant Ks \<alpha>) then \<mu>' 
                                         else (TVariant (map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks) \<alpha>))"
| "subst_ty \<mu> \<mu>' (TAbstract nm ts s)  = (if \<mu> = (TAbstract nm ts s) then \<mu>' 
                                         else (TAbstract nm (map (subst_ty \<mu> \<mu>') ts) s))"
| "subst_ty \<mu> \<mu>' (TRecord fs \<alpha> s)     = (if \<mu> = (TRecord fs \<alpha> s) then \<mu>'
                                         else (TRecord (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs) \<alpha> s))"
| "subst_ty \<mu> \<mu>' (TObserve i)         = (if \<mu> = (TObserve i) then \<mu>' 
                                         else (TObserve i))"
| "subst_ty \<mu> \<mu>' (TBang t)            = (if \<mu> = (TBang t) then \<mu>' else (TBang (subst_ty \<mu> \<mu>' t)))"

fun subst_tyvar :: "type list \<Rightarrow> type \<Rightarrow> type" where
  "subst_tyvar \<delta> (TVar i)            = (if i < length \<delta> then \<delta> ! i else TVar i)"
| "subst_tyvar \<delta> (TFun a b)          = TFun (subst_tyvar \<delta> a) (subst_tyvar \<delta> b)"
| "subst_tyvar \<delta> (TPrim p)           = TPrim p"
| "subst_tyvar \<delta> (TUnknown i)        = TUnknown i"
| "subst_tyvar \<delta> (TVariant Ks \<alpha>)     = TVariant (map (\<lambda>(nm, t, u). (nm, subst_tyvar \<delta> t, u)) Ks) \<alpha>"
| "subst_tyvar \<delta> (TAbstract nm ts s) = TAbstract nm (map (subst_tyvar \<delta>) ts) s"
| "subst_tyvar \<delta> (TRecord fs \<alpha> s)    = TRecord (map (\<lambda>(f, t, u). (f, subst_tyvar \<delta> t, u)) fs) \<alpha> s"
| "subst_tyvar \<delta> (TObserve i)        = (if i < length \<delta> then (TBang (\<delta> ! i)) else TObserve i)"
| "subst_tyvar \<delta> (TBang t)           = TBang (subst_tyvar \<delta> t)"


fun max_type_var :: "type \<Rightarrow> nat" where
  "max_type_var (TVar i)            = i"
| "max_type_var (TFun a b)          = max (max_type_var a) (max_type_var b)"
| "max_type_var (TPrim p)           = 0"
| "max_type_var (TUnknown i)        = 0"
| "max_type_var (TVariant Ks \<alpha>)     = Max (set (map (max_type_var \<circ> fst \<circ> snd) Ks))"
| "max_type_var (TAbstract nm ts s) = Max (set (map max_type_var ts))"
| "max_type_var (TRecord fs \<alpha> s)    = Max (set (map (max_type_var \<circ> fst \<circ> snd) fs))"
| "max_type_var (TObserve i)        = i"
| "max_type_var (TBang t)           = max_type_var t"


fun variant_elem_checked :: "(name \<times> type \<times> variant_usage_tag) \<Rightarrow> 
                             (name \<times> type \<times> variant_usage_tag)" where
  "variant_elem_checked (nm, t, _) = (nm, t, Checked)"

lemma variant_elem_checked_nm_eq: "y = variant_elem_checked x \<Longrightarrow> fst y = fst x"
  by (metis fst_conv variant_elem_checked.elims)

lemma variant_elem_checked_type_eq: "y = variant_elem_checked x \<Longrightarrow> (fst \<circ> snd) y = (fst \<circ> snd) x"
  by (metis comp_apply fst_conv snd_conv surjective_pairing variant_elem_checked.simps)

lemma variant_elem_checked_usage_checked: "y = variant_elem_checked x \<Longrightarrow> (snd \<circ> snd) y = Checked"
  by (metis comp_apply snd_conv variant_elem_checked.elims)

lemma variant_elem_checked_usage_nondec: 
  assumes "y = variant_elem_checked x"
  shows "(snd \<circ> snd) y \<le> (snd \<circ> snd) x"
  using assms
proof (cases "(snd \<circ> snd) x = Checked")
  case True
  then show ?thesis using assms variant_elem_checked_usage_checked by auto 
next
  case False
  then show ?thesis using less_eq_variant_usage_tag.elims by blast
qed


fun variant_nth_checked :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "variant_nth_checked n (TVar i)            = undefined"  
| "variant_nth_checked n (TFun a b)          = undefined"
| "variant_nth_checked n (TPrim p)           = undefined"
| "variant_nth_checked n (TUnknown i)        = undefined"
| "variant_nth_checked n (TVariant Ks \<alpha>)     = TVariant (Ks[n := variant_elem_checked (Ks ! n)]) \<alpha>"
| "variant_nth_checked n (TAbstract nm ts s) = undefined"
| "variant_nth_checked n (TRecord fs \<alpha> s)    = undefined"
| "variant_nth_checked n (TObserve i)        = undefined"
| "variant_nth_checked n (TBang t)           = undefined"

fun variant_elem_unchecked :: "(name \<times> type \<times> variant_usage_tag) \<Rightarrow> 
                               (name \<times> type \<times> variant_usage_tag)" where
  "variant_elem_unchecked (nm, t, _) = (nm, t, Unchecked)"

lemma variant_elem_unchecked_nm_eq: "y = variant_elem_unchecked x \<Longrightarrow> fst y = fst x"
  by (metis fst_conv variant_elem_unchecked.elims)

lemma variant_elem_unchecked_type_eq: 
  "y = variant_elem_unchecked x \<Longrightarrow> (fst \<circ> snd) y = (fst \<circ> snd) x"
  by (metis comp_apply fst_conv snd_conv surjective_pairing variant_elem_unchecked.simps)

lemma variant_elem_unchecked_usage_unchecked: 
  "y = variant_elem_unchecked x \<Longrightarrow> (snd \<circ> snd) y = Unchecked"
  by (metis comp_apply snd_conv variant_elem_unchecked.elims)

lemma variant_elem_unchecked_usage_noninc: 
  assumes "y = variant_elem_unchecked x"
  shows "(snd \<circ> snd) y \<ge> (snd \<circ> snd) x"
  using assms
proof (cases "(snd \<circ> snd) x = Checked")
  case True
  then show ?thesis using assms using less_eq_variant_usage_tag.elims by auto
next
  case False
  then show ?thesis using assms variant_elem_unchecked_usage_unchecked by auto
qed

fun variant_nth_unchecked :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "variant_nth_unchecked n (TVar i)            = undefined"  
| "variant_nth_unchecked n (TFun a b)          = undefined"
| "variant_nth_unchecked n (TPrim p)           = undefined"
| "variant_nth_unchecked n (TUnknown i)        = undefined"
| "variant_nth_unchecked n (TVariant Ks \<alpha>)     = TVariant (Ks[n := variant_elem_unchecked (Ks ! n)]) \<alpha>"
| "variant_nth_unchecked n (TAbstract nm ts s) = undefined"
| "variant_nth_unchecked n (TRecord fs \<alpha> s)    = undefined"
| "variant_nth_unchecked n (TObserve i)        = undefined"
| "variant_nth_unchecked n (TBang t)           = undefined"


fun record_elem_taken :: "(name \<times> type \<times> record_usage_tag) \<Rightarrow> (name \<times> type \<times> record_usage_tag)" 
  where "record_elem_taken (nm, t, _) = (nm, t, Taken)"

fun record_nth_taken :: "nat \<Rightarrow> type \<Rightarrow> type" where
  "record_nth_taken n (TVar i)            = undefined"  
| "record_nth_taken n (TFun a b)          = undefined"
| "record_nth_taken n (TPrim p)           = undefined"
| "record_nth_taken n (TUnknown i)        = undefined"
| "record_nth_taken n (TVariant Ks \<alpha>)     = undefined"
| "record_nth_taken n (TAbstract nm ts s) = undefined"
| "record_nth_taken n (TRecord fs \<alpha> s)    = TRecord (fs[n := record_elem_taken (fs ! n)]) \<alpha> s"
| "record_nth_taken n (TObserve i)        = undefined"
| "record_nth_taken n (TBang t)           = undefined"


inductive normalise :: "type \<Rightarrow> type \<Rightarrow> bool" ("_ \<hookrightarrow> _" [40, 40] 60) where
norm_tvar:
  "TBang (TVar i)                    \<hookrightarrow> TObserve i"
| norm_tfun:
  "TBang (TFun t u)                  \<hookrightarrow> TFun t u"
| norm_tprim:
  "TBang (TPrim pt)                  \<hookrightarrow> TPrim pt"
| norm_tvariant:
  "TBang (TVariant Ks None)          \<hookrightarrow> TVariant (map (\<lambda>(nm, t, u). (nm, TBang t, u)) Ks) None"
| norm_tabstract_w:
  "TBang (TAbstract nm ts Writable)  \<hookrightarrow> TAbstract nm (map TBang ts) ReadOnly"
| norm_tabstract_r:
  "TBang (TAbstract nm ts ReadOnly)  \<hookrightarrow> TAbstract nm (map TBang ts) ReadOnly"
| norm_tabstract_u:
  "TBang (TAbstract nm ts Unboxed)   \<hookrightarrow> TAbstract nm (map TBang ts) Unboxed"
| norm_tobserve:
  "TBang (TObserve i)                \<hookrightarrow> TObserve i"
| norm_trecord_w:
  "TBang (TRecord fs None Writable)  \<hookrightarrow> TRecord (map (\<lambda>(f, t, u). (f, TBang t, u)) fs) 
                                                None ReadOnly"
| norm_trecord_r:
  "TBang (TRecord fs None ReadOnly)  \<hookrightarrow> TRecord (map (\<lambda>(f, t, u). (f, TBang t, u)) fs) 
                                                None ReadOnly"
| norm_trecord_u:
  "TBang (TRecord fs None Unboxed)   \<hookrightarrow> TRecord (map (\<lambda>(f, t, u). (f, TBang t, u)) fs) 
                                                None Unboxed"

lemma normalise_domain:
  assumes "\<mu> \<hookrightarrow> \<mu>'"
  shows "\<exists>\<tau>. \<mu> = TBang \<tau>"
  using assms by (auto elim: normalise.cases)


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
  | CtEscape type
  | CtNotRead sigil

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
| "map_types_ct f (CtEscape t)    = CtEscape (f t)"
| "map_types_ct f (CtNotRead s)   = CtNotRead s"

definition subst_ty_ct :: "type \<Rightarrow> type \<Rightarrow> constraint \<Rightarrow> constraint" where
  "subst_ty_ct \<tau> \<rho> \<equiv> map_types_ct (subst_ty \<tau> \<rho>)"

definition subst_tyvar_ct :: "type list \<Rightarrow> constraint \<Rightarrow> constraint" where
  "subst_tyvar_ct \<delta> \<equiv> map_types_ct (subst_tyvar \<delta>)"

inductive known_sigil :: "sigil \<Rightarrow> bool" where
"known_sigil ReadOnly"
| "known_sigil Writable"
| "known_sigil Unboxed"

inductive known_ty :: "type \<Rightarrow> bool" where
known_tvar:
  "known_ty (TVar n)"
| known_tfun:
  "\<lbrakk> known_ty t1
   ; known_ty t2
   \<rbrakk> \<Longrightarrow> known_ty (TFun t1 t2)"
| known_tprim:
  "known_ty (TPrim pt)"
| known_tvariant:
  "\<forall>i < length Ks. known_ty ((fst \<circ> snd) (Ks ! i)) \<Longrightarrow> known_ty (TVariant Ks None)"
| known_tabstract:
  "\<lbrakk> \<forall>i < length ts. known_ty (ts ! i)
   ; known_sigil s
   \<rbrakk> \<Longrightarrow>  known_ty (TAbstract nm ts s)"
| known_trecord:
  "\<lbrakk> \<forall>i < length fs. known_ty ((fst \<circ> snd) (fs ! i)) 
   ; known_sigil s
   \<rbrakk> \<Longrightarrow> known_ty (TRecord fs None s)"
| known_tobserve:
  "known_ty (TObserve i)"
| known_tbang:
  "known_ty t \<Longrightarrow> known_ty (TBang t)"

inductive_cases known_tfunE: "known_ty (TFun t1 t2)"
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
| known_ctnotread:
  "known_sigil s \<Longrightarrow> known_ct (CtNotRead s)"

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
                 | LetBang "bool list" "'f expr" "'f expr"
                 | If "'f expr" "'f expr" "'f expr"
                 | Sig "'f expr" type
                 | Case "'f expr" name "'f expr" "'f expr"
                 | Esac "'f expr" name "'f expr"
                 | Struct "name list" "'f expr list"
                 | Take "'f expr" name "'f expr"
                 | Put "'f expr" name "'f expr"
                 | Member "'f expr" name
                 

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


definition minus_ctx :: "bool list \<Rightarrow> ctx \<Rightarrow> ctx" where
  "minus_ctx ys \<Gamma> \<equiv> List.map2 (\<lambda>m \<tau>. if (ys ! m) then None else \<tau>) [0..<length \<Gamma>] \<Gamma>"

definition set0_cg_ctx :: "bool list \<Rightarrow> cg_ctx \<Rightarrow> cg_ctx" where
  "set0_cg_ctx ys G \<equiv> List.map2 (\<lambda>m (\<tau>, n). if (ys ! m) then (\<tau>, 0) else (\<tau>, n)) [0..<length G] G"

definition bang_cg_ctx :: "bool list \<Rightarrow> cg_ctx \<Rightarrow> cg_ctx" where
  "bang_cg_ctx ys G \<equiv> List.map2 (\<lambda>m (\<tau>, n). if (ys ! m) then (TBang \<tau>, n) 
                                                        else (\<tau>, n)) [0..<length G] G"

lemma minus_ctx_length:
  shows "length G = length (minus_ctx ys G)"
  using map2_length minus_ctx_def by force

lemma set0_cg_ctx_length:
  shows "length G = length (set0_cg_ctx ys G)"
  using map2_length set0_cg_ctx_def by force

lemma bang_cg_ctx_length:
  shows "length G = length (bang_cg_ctx ys G)"
  using map2_length bang_cg_ctx_def by force

lemma minus_ctx_prop:
  assumes "i < length G"
  shows "((minus_ctx ys G) ! i) = (if (ys ! i) then None else (G ! i))"
  using assms by (simp add: minus_ctx_def)

lemma minus_ctx_prop_none:
  assumes "i < length G"
    and "ys ! i"
  shows "(minus_ctx ys G) ! i = None"
  using assms minus_ctx_prop by presburger

lemma minus_ctx_prop_some:
  assumes "i < length G"
    and "\<not>(ys ! i)"
  shows "(minus_ctx ys G) ! i = G ! i"
  using assms minus_ctx_prop by presburger

lemma set0_cg_ctx_type_same:
  assumes "i < length G"
  shows "fst (G ! i) = fst ((set0_cg_ctx ys G) ! i)"
  using assms by (simp add: set0_cg_ctx_def case_prod_beta)

lemma bang_cg_ctx_type_prop:
  assumes "i < length G \<or> i < length (bang_cg_ctx ys G)"
  shows "fst ((bang_cg_ctx ys G) ! i) = (if (ys ! i) then TBang (fst (G ! i)) else fst (G ! i))"
  using assms by (simp add: bang_cg_ctx_def case_prod_beta)

lemma set0_cg_ctx_type_checked_prop:
  assumes "i < length G"
  shows "snd ((set0_cg_ctx ys G) ! i) = (if (ys ! i) then 0 else snd (G ! i))"
  using assms by (simp add: set0_cg_ctx_def case_prod_beta)

lemma bang_cg_ctx_type_checked_same:
  assumes "i < length G \<or> i < length (bang_cg_ctx ys G)"
  shows "snd ((bang_cg_ctx ys G) ! i) = snd (G ! i)"
  using assms by (simp add: bang_cg_ctx_def case_prod_beta)


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

lemma alg_ctx_jn_type_checked_nondec1:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1" 
  shows "snd (G1 ! i) \<le> snd (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_checked_nondec2:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
  shows "snd (G1' ! i) \<le> snd (G2 ! i)"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_checked_max:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
  shows "snd (G2 ! i) = max (snd (G1 ! i)) (snd (G1' ! i))"
  using assms by (clarsimp simp add: alg_ctx_jn.simps list_all3_conv_all_nth)

lemma alg_ctx_jn_type_checked_same:
  assumes "G1 \<Join> G1' \<leadsto> G2 | C"
    and "i < length G1'"
    and "snd (G1 ! i) = snd (G1' ! i)"
  shows "snd (G2 ! i) = snd (G1 ! i)"
  using assms alg_ctx_jn_type_checked_max by auto


section {* Constraint Semantics (Fig 3.6 3.9 3.12) *}
inductive constraint_sem :: "axm_set \<Rightarrow> constraint \<Rightarrow> bool" ("_ \<turnstile> _" [40, 40] 60) where
ct_sem_share:
  "\<lbrakk> CtShare \<rho> \<in> A
   ; \<exists>i. \<rho> = TVar i
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtShare \<rho>"
| ct_sem_drop:
  "\<lbrakk> CtDrop \<rho> \<in> A 
   ; \<exists>i. \<rho> = TVar i
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtDrop \<rho>"
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
  "\<lbrakk> \<forall>i < length Ks. ((snd \<circ> snd) (Ks ! i) = Checked) \<rbrakk> \<Longrightarrow> A \<turnstile> CtExhausted (TVariant Ks None)"
| ct_sem_varsub:
  "\<lbrakk> map fst Ks1 = map fst Ks2
   ; list_all2 (\<lambda>k1 k2. (A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2))) Ks1 Ks2
   ; list_all2 (\<lambda>k1 k2. ((snd \<circ> snd) k1) \<le> ((snd \<circ> snd) k2)) Ks1 Ks2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2 None)"
| ct_sem_varshare:
  "\<lbrakk> \<forall>i < length Ks. (snd \<circ> snd) (Ks ! i) = Unchecked \<longrightarrow> A \<turnstile> CtShare ((fst \<circ> snd) (Ks ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtShare (TVariant Ks None)"
| ct_sem_vardrop:
  "\<lbrakk> \<forall>i < length Ks. (snd \<circ> snd) (Ks ! i) = Unchecked \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (Ks ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtDrop (TVariant Ks None)" 
| ct_sem_absdrop:
  "\<lbrakk> s \<noteq> Writable
   ; \<forall>i < length ts. A \<turnstile> CtDrop (ts ! i)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtDrop (TAbstract nm ts s)"
| ct_sem_absshare:
  "\<lbrakk> s \<noteq> Writable
   ; \<forall>i < length ts. A \<turnstile> CtShare (ts ! i)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtShare (TAbstract nm ts s)"
| ct_sem_absesc:
  "\<lbrakk> s \<noteq> ReadOnly
   ; \<forall>i < length ts. A \<turnstile> CtEscape (ts ! i)
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtEscape (TAbstract nm ts s)"
| ct_sem_funesc:
  "A \<turnstile> CtEscape (TFun t u)"
| ct_sem_primesc:
  "A \<turnstile> CtEscape (TPrim pt)"
| ct_sem_sumesc:
  "\<lbrakk> \<forall>i < length Ks. A \<turnstile> CtEscape ((fst \<circ> snd) (Ks ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtEscape (TVariant Ks None)"
| ct_sem_obsdrop:
  "A \<turnstile> CtDrop (TObserve i)"
| ct_sem_obsshare:
  "A \<turnstile> CtShare (TObserve i)"
| ct_sem_sigil:
  "s \<noteq> ReadOnly \<Longrightarrow> A \<turnstile> CtNotRead s"
| ct_sem_recsub:
  "\<lbrakk> list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs1 fs2
   ; map fst fs1 = map fst fs2  
   ; list_all2 (\<lambda>f1 f2. (A \<turnstile> CtSub ((fst \<circ> snd) f1) ((fst \<circ> snd) f2))) fs1 fs2
   ; list_all2 (\<lambda>f1 f2. ((snd \<circ> snd) f1) \<le> ((snd \<circ> snd) f2)) fs1 fs2
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtSub (TRecord fs1 None s) (TRecord fs2 None s)"
| ct_sem_recshare:
  "\<lbrakk> s \<noteq> Writable
   ; \<forall>i < length fs. (snd \<circ> snd) (fs ! i) = Present \<longrightarrow> A \<turnstile> CtShare ((fst \<circ> snd) (fs ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtShare (TRecord fs None s)"
| ct_sem_recdrop:
  "\<lbrakk> s \<noteq> Writable
   ; \<forall>i < length fs. (snd \<circ> snd) (fs ! i) = Present \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (fs ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtDrop (TRecord fs None s)"
| ct_sem_recescape:
  "\<lbrakk> s \<noteq> ReadOnly
   ; \<forall>i < length fs. (snd \<circ> snd) (fs ! i) = Present \<longrightarrow> A \<turnstile> CtEscape ((fst \<circ> snd) (fs ! i))
   \<rbrakk> \<Longrightarrow> A \<turnstile> CtEscape (TRecord fs None s)"

inductive_cases ct_sem_conjE: "A \<turnstile> CtConj C1 C2"
inductive_cases ct_sem_intE: "A \<turnstile> CtIBound (LNat m) \<tau>"
inductive_cases ct_sem_reflE: "A \<turnstile> CtEq \<tau> \<rho>" 
inductive_cases ct_sem_funE1: "A \<turnstile> CtSub (TFun \<tau>1 \<tau>2) \<rho>"
inductive_cases ct_sem_funE2: "A \<turnstile> CtSub \<rho> (TFun \<tau>1 \<tau>2)"
inductive_cases ct_sem_exhaust: "A \<turnstile> CtExhausted (TVariant Ks None)"
inductive_cases ct_sem_varsubE1: "A \<turnstile> CtSub (TVariant Ks \<alpha>) \<tau>"
inductive_cases ct_sem_varsubE2: "A \<turnstile> CtSub \<tau> (TVariant Ks \<alpha>)"
inductive_cases ct_sem_recsubE1: "A \<turnstile> CtSub (TRecord fs \<alpha> s) \<tau>"
inductive_cases ct_sem_recsubE2: "A \<turnstile> CtSub \<tau> (TRecord fs \<alpha> s)"
inductive_cases ct_sem_vardropE: "A \<turnstile> CtDrop (TVariant Ks None)"
inductive_cases ct_sem_recdropE: "A \<turnstile> CtDrop (TRecord fs None s)"
inductive_cases ct_sem_sigilE: "A \<turnstile> CtNotRead s"

lemma ct_sem_sigil_equiv_def:
  "s = Writable \<or> s = Unboxed \<Longrightarrow> A \<turnstile> CtNotRead s"
  using ct_sem_sigil by blast

lemma ct_sem_sigil_iff:
  "s \<noteq> ReadOnly \<longleftrightarrow> A \<turnstile> CtNotRead s"
  using ct_sem_sigil ct_sem_sigilE by metis

lemma ct_sem_conj_iff: "A \<turnstile> CtConj C1 C2 \<longleftrightarrow> A \<turnstile> C1 \<and> A \<turnstile> C2"
  using ct_sem_conj ct_sem_conjE by meson

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

lemma ct_sem_exhaust_all_checked: 
  assumes "A \<turnstile> CtExhausted (TVariant Ks None)"
  shows "\<forall>i < length Ks. (snd \<circ> snd) (Ks ! i) = Checked"
  using assms ct_sem_exhaust by auto

lemma ct_sem_varsub_length:
  assumes "A \<turnstile> CtSub (TVariant Ks1 None) (TVariant Ks2 None)"
  shows "length Ks1 = length Ks2"
  using assms ct_sem_varsubE2 ct_sem_reflE type.inject by (metis map_eq_imp_length_eq)

lemma ct_sem_recsub_length:
  assumes "A \<turnstile> CtSub (TRecord fs1 None s) (TRecord fs2 None s)"
  shows "length fs1 = length fs2"
  using assms ct_sem_eq_iff ct_sem_recsubE2 map_eq_imp_length_eq type.inject
  by (metis (no_types, lifting))

lemma ct_sem_sub_drop_imp_drop:
  assumes "A \<turnstile> CtSub \<tau> \<rho>" and "A \<turnstile> CtDrop \<rho>"
  shows "A \<turnstile> CtDrop \<tau>"
  using assms 
proof (induct "CtSub \<tau> \<rho>" arbitrary: \<tau> \<rho>)
  case (ct_sem_equal A \<tau> \<rho>)
  then show ?case using ct_sem_eq_iff by simp
next
  case (ct_sem_fun A \<rho>1 \<tau>1 \<tau>2 \<rho>2)
  then show ?case using constraint_sem.ct_sem_funD by blast 
next
  case (ct_sem_varsub Ks1 Ks2 A)
  {
    fix i :: nat
    assume i_size:      "i < length Ks1"
    assume i_unchecked: "(snd \<circ> snd) (Ks1 ! i) = Unchecked"
    have "(snd \<circ> snd) (Ks1 ! i) \<le> (snd \<circ> snd) (Ks2 ! i)"
      using list_all2_conv_all_nth[where ?P="(\<lambda>k1 k2. (snd \<circ> snd) k1 \<le> (snd \<circ> snd) k2)"]
        ct_sem_varsub.hyps i_size by blast
    then have "(snd \<circ> snd) (Ks2 ! i) = Unchecked"
      using i_unchecked less_eq_variant_usage_tag.elims by auto
    moreover have "A \<turnstile> CtDrop (TVariant Ks2 None)" "map fst Ks1 = map fst Ks2"
      using ct_sem_varsub by blast+
    ultimately have "A \<turnstile> CtDrop ((fst \<circ> snd) (Ks2 ! i))"
      using  ct_sem_vardropE comp_apply i_size length_map by metis
    then have "A \<turnstile> CtDrop ((fst \<circ> snd) (Ks1 ! i))"
      using i_size ct_sem_varsub by (metis (mono_tags, lifting) list_all2_conv_all_nth)
  }
  then show ?case using ct_sem_vardrop ct_sem_varsub by blast
next
  case (ct_sem_recsub A fs1 fs2 s)
  have "s \<noteq> Writable"
    using ct_sem_recsub ct_sem_recdropE by blast
  moreover {
    fix i :: nat
    assume i_size:    "i < length fs1"
    assume i_present: "(snd \<circ> snd) (fs1 ! i) = Present"
    have i_size2: "i < length fs2" using ct_sem_recsub.hyps i_size length_map by metis
    have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs1 ! i))"
    proof (cases "(snd \<circ> snd) (fs2 ! i) = Present")
      case True
      have "list_all2 (\<lambda>f1 f2. (\<forall>x xa. (fst \<circ> snd) f1 = x \<and> (fst \<circ> snd) f2 = xa 
                                       \<longrightarrow> A \<turnstile> CtDrop xa \<longrightarrow> A \<turnstile> CtDrop x)) fs1 fs2"
        using ct_sem_recsub.hyps by (simp add: list_all2_mono)
      then have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs2 ! i)) \<Longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (fs1 ! i))"
        by (metis (mono_tags, lifting) i_size list_all2_conv_all_nth)
      moreover have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs2 ! i))"
        using ct_sem_recdropE i_size2 True ct_sem_recsub.prems by (metis comp_apply)
      ultimately show ?thesis by argo
    next
      case False
      have "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                               \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs1 fs2"
        using ct_sem_recsub.hyps by (simp add: list_all2_mono)
      then have "(snd \<circ> snd) (fs1 ! i) = Present \<and> (snd \<circ> snd) (fs2 ! i) = Taken 
                 \<Longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (fs1 ! i))"
        by (metis (mono_tags, lifting) i_size list_all2_conv_all_nth)
      then show ?thesis using False i_present record_usage_tag.exhaust by blast
    qed
  }
  ultimately show ?case using ct_sem_recdrop by blast
qed

lemma ct_sem_sub_trans:
  assumes "A \<turnstile> CtSub \<tau>1 \<tau>2"
    and "A \<turnstile> CtSub \<tau>2 \<tau>3"
  shows "A \<turnstile> CtSub \<tau>1 \<tau>3"
  using assms
proof (induct \<tau>2 arbitrary: \<tau>1 \<tau>3)
  case (TFun \<rho> \<rho>')
  obtain \<tau> \<tau>' where \<tau>_\<tau>'_def: "\<tau>1 = TFun \<tau> \<tau>'"
    using TFun.prems ct_sem_fun_exI2 by blast
  obtain \<mu> \<mu>' where \<mu>_\<mu>'_def: "\<tau>3 = TFun \<mu> \<mu>'"
    using TFun.prems ct_sem_fun_exI1 by blast
  consider (equal) "A \<turnstile> CtEq (TFun \<tau> \<tau>') (TFun \<rho> \<rho>')" | (sub) "A \<turnstile> CtSub \<rho> \<tau>" "A \<turnstile> CtSub \<tau>' \<rho>'"
    using \<tau>_\<tau>'_def TFun.prems ct_sem_funE1 by blast
  then show ?case
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
next
  case (TVariant Ks2 \<alpha>)
  consider (equal1) "A \<turnstile> CtEq \<tau>1 (TVariant Ks2 \<alpha>)" | (not_equal1) "\<not>(A \<turnstile> CtEq \<tau>1 (TVariant Ks2 \<alpha>))"
    by blast
  then show ?case
  proof cases
    case equal1
    then show ?thesis
      using ct_sem_eq_iff TVariant.prems by force
  next
    case not_equal1
    consider (equal3) "A \<turnstile> CtEq (TVariant Ks2 \<alpha>) \<tau>3" | (not_equal3) "\<not>(A \<turnstile> CtEq (TVariant Ks2 \<alpha>) \<tau>3)"
      by blast
    then show ?thesis
    proof cases
      case equal3
      then show ?thesis
        using ct_sem_eq_iff TVariant.prems by force
    next
      case not_equal3
      obtain Ks1 where Ks1_def: 
        "\<tau>1 = TVariant Ks1 None"
        "map fst Ks1 = map fst Ks2"
        "list_all2 (\<lambda>k1 k2. (A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2))) Ks1 Ks2"
        "list_all2 (\<lambda>k1 k2. ((snd \<circ> snd) k1) \<le> ((snd \<circ> snd) k2)) Ks1 Ks2"
        using not_equal1 TVariant.prems by (auto elim: ct_sem_varsubE2)
      obtain Ks3 where Ks3_def: 
        "\<tau>3 = TVariant Ks3 None"
        "map fst Ks2 = map fst Ks3"
        "list_all2 (\<lambda>k1 k2. (A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2))) Ks2 Ks3"
        "list_all2 (\<lambda>k1 k2. ((snd \<circ> snd) k1) \<le> ((snd \<circ> snd) k2)) Ks2 Ks3"
        using not_equal3 TVariant.prems by (auto elim: ct_sem_varsubE1)
      moreover have "list_all2 (\<lambda>k1 k2. A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2)) Ks1 Ks3"
      proof - 
        {
          fix i :: nat
          assume i_size: "i < length Ks2"
          have "A \<turnstile> CtSub ((fst \<circ> snd) (Ks1 ! i)) ((fst \<circ> snd) (Ks2 ! i)) \<Longrightarrow> 
                A \<turnstile> CtSub ((fst \<circ> snd) (Ks2 ! i)) ((fst \<circ> snd) (Ks3 ! i)) \<Longrightarrow> 
                A \<turnstile> CtSub ((fst \<circ> snd) (Ks1 ! i)) ((fst \<circ> snd) (Ks3 ! i))"
            using i_size fsts.intros snds.intros by (rule_tac TVariant.hyps; fastforce+)
        }
        then show ?thesis
          using ct_sem_varsub_length TVariant.prems Ks1_def Ks3_def
          by (simp add: list_all2_conv_all_nth)
      qed
      moreover have "list_all2 (\<lambda>k1 k2. ((snd \<circ> snd) k1) \<le> ((snd \<circ> snd) k2)) Ks1 Ks3"
        using Ks1_def Ks3_def by (simp add: list_all2_conv_all_nth; fastforce)
      ultimately show ?thesis
        using ct_sem_varsub Ks1_def Ks3_def by presburger
    qed
  qed
next
  case (TRecord fs2 \<alpha> s)
  consider (equal1) "A \<turnstile> CtEq \<tau>1 (TRecord fs2 \<alpha> s)" 
         | (not_equal1) "\<not>(A \<turnstile> CtEq \<tau>1 (TRecord fs2 \<alpha> s))" by blast
  then show ?case
  proof cases
    case equal1
    then show ?thesis using ct_sem_eq_iff TRecord.prems by force
  next
    case not_equal1
    consider (equal3) "A \<turnstile> CtEq (TRecord fs2 \<alpha> s) \<tau>3" 
           | (not_equal3) "\<not>(A \<turnstile> CtEq (TRecord fs2 \<alpha> s) \<tau>3)" by blast
    then show ?thesis
    proof cases
      case equal3
      then show ?thesis using ct_sem_eq_iff TRecord.prems by force
    next
      case not_equal3
      obtain fs1 where fs1_def: 
        "\<tau>1 = TRecord fs1 None s"
        "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                            \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs1 fs2"
        "map fst fs1 = map fst fs2"
        "list_all2 (\<lambda>f1 f2. (A \<turnstile> CtSub ((fst \<circ> snd) f1) ((fst \<circ> snd) f2))) fs1 fs2"
        "list_all2 (\<lambda>f1 f2. ((snd \<circ> snd) f1) \<le> ((snd \<circ> snd) f2)) fs1 fs2"
        using not_equal1 TRecord.prems by (auto elim: ct_sem_recsubE2)
      obtain fs3 where fs3_def: 
        "\<tau>3 = TRecord fs3 None s"
        "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                            \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs2 fs3"
        "map fst fs2 = map fst fs3"
        "list_all2 (\<lambda>f1 f2. (A \<turnstile> CtSub ((fst \<circ> snd) f1) ((fst \<circ> snd) f2))) fs2 fs3"
        "list_all2 (\<lambda>f1 f2. ((snd \<circ> snd) f1) \<le> ((snd \<circ> snd) f2)) fs2 fs3"
        using not_equal3 TRecord.prems by (auto elim: ct_sem_recsubE1)
      moreover have "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                            \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs1 fs3"
      proof -
        {
          fix i :: nat
          assume i_size:     "i < length fs2"
          assume f1_present: "(snd \<circ> snd) (fs1 ! i) = Present"
          assume f3_taken:   "(snd \<circ> snd) (fs3 ! i) = Taken"
          have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs1 ! i))"
          proof (cases "(snd \<circ> snd) (fs2 ! i) = Present")
            case True
            have "(snd \<circ> snd) (fs2 ! i) = Present \<and> (snd \<circ> snd) (fs3 ! i) = Taken 
                  \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (fs2 ! i))"
              using fs3_def i_size by (metis (mono_tags, lifting) list_all2_conv_all_nth)
            then have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs2 ! i))" using f3_taken True by blast
            moreover have "A \<turnstile> CtSub ((fst \<circ> snd) (fs1 ! i)) ((fst \<circ> snd) (fs2 ! i))"
              using fs1_def i_size by (metis (mono_tags, lifting) list_all2_conv_all_nth)
            ultimately show ?thesis using ct_sem_sub_drop_imp_drop by fast
          next
            case False
            have "(snd \<circ> snd) (fs1 ! i) = Present \<and> (snd \<circ> snd) (fs2 ! i) = Taken 
                  \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (fs1 ! i))"
            using fs1_def by (simp add: i_size list_all2_conv_all_nth)
            then show ?thesis using f1_present False record_usage_tag.exhaust by meson
          qed
        }
        then show ?thesis using fs1_def fs3_def by (simp add: list_all2_conv_all_nth)
      qed
      moreover have "list_all2 (\<lambda>f1 f2. A \<turnstile> CtSub ((fst \<circ> snd) f1) ((fst \<circ> snd) f2)) fs1 fs3"
      proof - 
        {
          fix i :: nat
          assume i_size: "i < length fs2"
          have "A \<turnstile> CtSub ((fst \<circ> snd) (fs1 ! i)) ((fst \<circ> snd) (fs2 ! i)) \<Longrightarrow> 
                A \<turnstile> CtSub ((fst \<circ> snd) (fs2 ! i)) ((fst \<circ> snd) (fs3 ! i)) \<Longrightarrow> 
                A \<turnstile> CtSub ((fst \<circ> snd) (fs1 ! i)) ((fst \<circ> snd) (fs3 ! i))"
            using i_size fsts.intros snds.intros by (rule_tac TRecord.hyps; fastforce+)
        }
        then show ?thesis
          using ct_sem_recsub_length TRecord.prems fs1_def fs3_def
          by (simp add: list_all2_conv_all_nth)
      qed
      moreover have "list_all2 (\<lambda>f1 f2. ((snd \<circ> snd) f1) \<le> ((snd \<circ> snd) f2)) fs1 fs3"
        using fs1_def fs3_def by (simp add: list_all2_conv_all_nth; fastforce)
      ultimately show ?thesis
        using ct_sem_recsub fs1_def fs3_def by presburger
    qed
  qed
qed (auto intro: ct_sem_eq_iff elim: constraint_sem.cases)

lemma ct_sem_norm:
  assumes "A \<turnstile> C"
    and "\<mu> \<hookrightarrow> \<mu>'"
  shows "A \<turnstile> subst_ty_ct \<mu> \<mu>' C"
  using assms
proof (induct rule: constraint_sem.induct)
case (ct_sem_share \<rho> A)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_share by fastforce
next
  case (ct_sem_drop \<rho> A)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_drop by fastforce
next
  case (ct_sem_conj A C1 C2)
  then show ?case
    using subst_ty_ct_def constraint_sem.ct_sem_conj by force
next
  case (ct_sem_int m n A)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_int by auto
next
case (ct_sem_top A)
  then show ?case
    using subst_ty_ct_def constraint_sem.ct_sem_top by force
next
  case (ct_sem_refl A \<tau>)
  then show ?case
    using subst_ty_ct_def ct_sem_eq_iff by force
next
  case (ct_sem_equal A \<tau> \<rho>)
  then show ?case
    using subst_ty_ct_def ct_sem_eq_iff constraint_sem.ct_sem_equal by simp
next
  case (ct_sem_fun A \<rho>1 \<tau>1 \<tau>2 \<rho>2)
  then show ?case
    using constraint_sem.ct_sem_fun normalise_domain subst_ty_ct_def by fastforce
next
  case (ct_sem_funS A \<tau>1 \<tau>2)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_funS by auto
next
  case (ct_sem_funD A \<tau>1 \<tau>2)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_funD by auto
next
  case (ct_sem_primS A pt)
  then show ?case 
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_primS by auto
next
case (ct_sem_primD A pt)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_primD by auto
next
  case (ct_sem_exhaust Ks A)
  have "\<forall>i<length Ks. (snd \<circ> snd) (map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks ! i) = Checked"
    using ct_sem_exhaust.hyps by (simp add: case_prod_unfold)
  then show ?case 
    using constraint_sem.ct_sem_exhaust ct_sem_exhaust.prems normalise_domain subst_ty_ct_def
    by fastforce
next
  case (ct_sem_varsub Ks1 Ks2 A)
  obtain Ks1' where Ks1'_def: "Ks1' = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks1"
    by fast
  obtain Ks2' where Ks2'_def: "Ks2' = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks2"
    by fast
  have "map fst Ks1' = map fst Ks2'"
    using ct_sem_varsub.hyps Ks1'_def Ks2'_def by simp
  moreover have "list_all2 (\<lambda>k1 k2. A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2)) Ks1' Ks2'"
    using ct_sem_varsub Ks1'_def Ks2'_def subst_ty_ct_def
    by (simp add: list_all2_conv_all_nth prod.case_eq_if)
  moreover have "list_all2 (\<lambda>k1 k2. (snd \<circ> snd) k1 \<le> (snd \<circ> snd) k2) Ks1' Ks2'"
    using ct_sem_varsub.hyps Ks1'_def Ks2'_def
    by (simp add: case_prod_unfold list_all2_conv_all_nth)
  ultimately show ?case
    using subst_ty_ct_def constraint_sem.ct_sem_varsub Ks1'_def Ks2'_def ct_sem_varsub.prems 
      normalise_domain by fastforce
next
  case (ct_sem_varshare Ks A)
  obtain KS where KS_def: "KS = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks"
    by blast
  have "\<forall>i < length KS. (snd \<circ> snd) (KS ! i) = Unchecked \<longrightarrow> A \<turnstile> CtShare ((fst \<circ> snd) (KS ! i))"
    using subst_ty_ct_def ct_sem_varshare KS_def by (simp add: case_prod_beta')
  then show ?case
    using ct_sem_varshare subst_ty_ct_def normalise_domain constraint_sem.ct_sem_varshare KS_def
    by fastforce
next
  case (ct_sem_vardrop Ks A)
  obtain KS where KS_def: "KS = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks"
    by blast
  have "\<forall>i < length KS. (snd \<circ> snd) (KS ! i) = Unchecked \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) (KS ! i))"
    using subst_ty_ct_def ct_sem_vardrop KS_def by (simp add: case_prod_beta')
  then show ?case
    using ct_sem_vardrop subst_ty_ct_def normalise_domain constraint_sem.ct_sem_vardrop KS_def
    by fastforce
next
  case (ct_sem_absdrop s ts A nm)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_absdrop by fastforce
next
  case (ct_sem_absshare s ts A nm)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_absshare by fastforce
next
  case (ct_sem_absesc s ts A nm)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_absesc by fastforce
next
  case (ct_sem_funesc A t u)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_funesc by auto
next
  case (ct_sem_primesc A pt)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_primesc by auto
next
  case (ct_sem_sumesc Ks A)
  obtain KS where KS_def: "KS = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) Ks"
    by blast
  have "\<forall>i < length KS. A \<turnstile> CtEscape ((fst \<circ> snd) (KS ! i))"
    using subst_ty_ct_def ct_sem_sumesc KS_def by (simp add: case_prod_beta')
  then show ?case
    using ct_sem_sumesc subst_ty_ct_def normalise_domain constraint_sem.ct_sem_sumesc KS_def
    by fastforce
next
  case (ct_sem_obsdrop A t)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_obsdrop by auto
next
  case (ct_sem_obsshare A t)
  then show ?case
    using subst_ty_ct_def normalise_domain constraint_sem.ct_sem_obsshare by auto
next
  case (ct_sem_sigil s A)
  then show ?case using subst_ty_ct_def constraint_sem.ct_sem_sigil by force
next
  case (ct_sem_recsub A fs1 fs2 s)
  obtain fs1' where fs1'_def: "fs1' = map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs1"
    by fast
  obtain fs2' where fs2'_def: "fs2' = map (\<lambda>(nm, t, u). (nm, subst_ty \<mu> \<mu>' t, u)) fs2"
    by fast
  have "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 = Present \<and> (snd \<circ> snd) f2 = Taken 
                            \<longrightarrow> A \<turnstile> CtDrop ((fst \<circ> snd) f1)) fs1' fs2'"
  proof -
    have "length fs1' = length fs2'"
    proof -
      have "length fs1 = length fs1'" "length fs2 = length fs2'" 
        using fs1'_def fs2'_def length_map by force+
      moreover have "length fs1 = length fs2" using ct_sem_recsub.hyps length_map by metis
      ultimately show ?thesis by argo
    qed
    moreover {
      fix i :: nat
      assume i_size: "i < length fs2'" 
      assume f1'_present: "(snd \<circ> snd) (fs1' ! i) = Present"
      assume f2'_taken:   "(snd \<circ> snd) (fs2' ! i) = Taken"
      have i_size2: "i < length fs2" "i < length fs1" "i < length fs1'" 
        using fs2'_def fs1'_def i_size ct_sem_recsub.hyps map_eq_imp_length_eq by force+
      have "(snd \<circ> snd) (fs1 ! i) = (snd \<circ> snd) (fs1' ! i)"
        using fs1'_def i_size2 by (simp add: case_prod_unfold)
      moreover have "(snd \<circ> snd) (fs2 ! i) = (snd \<circ> snd) (fs2' ! i)"
        using fs2'_def i_size2 by (simp add: case_prod_unfold)
      moreover have "(snd \<circ> snd) (fs1 ! i) = Present \<and> (snd \<circ> snd) (fs2 ! i) = Taken 
                      \<longrightarrow> A \<turnstile> subst_ty_ct \<mu> \<mu>' (CtDrop ((fst \<circ> snd) (fs1 ! i)))"
        using ct_sem_recsub i_size2 by (metis (mono_tags, lifting) list_all2_conv_all_nth)
      ultimately have "A \<turnstile> subst_ty_ct \<mu> \<mu>' (CtDrop ((fst \<circ> snd) (fs1 ! i)))"
        using f1'_present f2'_taken by argo
      then have "A \<turnstile> CtDrop ((fst \<circ> snd) (fs1' ! i))"
        by (simp add: fs1'_def i_size2 prod.case_eq_if subst_ty_ct_def)
    }
    ultimately show ?thesis by (clarsimp simp add: list_all2_conv_all_nth)
  qed
  moreover have "map fst fs1' = map fst fs2'"
    using ct_sem_recsub.hyps fs1'_def fs2'_def by simp
  moreover have "list_all2 (\<lambda>f1 f2. A \<turnstile> CtSub ((fst \<circ> snd) f1) ((fst \<circ> snd) f2)) fs1' fs2'"
    using ct_sem_recsub fs1'_def fs2'_def subst_ty_ct_def
    by (simp add: list_all2_conv_all_nth prod.case_eq_if)
  moreover have "list_all2 (\<lambda>f1 f2. (snd \<circ> snd) f1 \<le> (snd \<circ> snd) f2) fs1' fs2'"
    using ct_sem_recsub.hyps fs1'_def fs2'_def 
    by (simp add: case_prod_unfold list_all2_conv_all_nth)
  ultimately show ?case
    using subst_ty_ct_def constraint_sem.ct_sem_recsub fs1'_def fs2'_def ct_sem_recsub.prems 
      normalise_domain by fastforce
next
  case (ct_sem_recshare s fs A)
  then have "\<forall>i<length (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs).
                       (snd \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i) = Present \<longrightarrow>
                       A \<turnstile> CtShare ((fst \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i))"
    by (simp add: prod.case_eq_if subst_ty_ct_def)
  then show ?case
    using ct_sem_recshare subst_ty_ct_def normalise_domain constraint_sem.ct_sem_recshare 
    by fastforce
next
  case (ct_sem_recdrop s fs A)
  then have "\<forall>i<length (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs).
                       (snd \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i) = Present \<longrightarrow>
                       A \<turnstile> CtDrop ((fst \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i))"
    by (simp add: case_prod_beta' subst_ty_ct_def)
  then show ?case 
    using ct_sem_recdrop subst_ty_ct_def normalise_domain constraint_sem.ct_sem_recdrop 
    by fastforce
next
  case (ct_sem_recescape s fs A)
  then have "\<forall>i<length (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs).
                       (snd \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i) = Present \<longrightarrow>
                      A \<turnstile> CtEscape ((fst \<circ> snd) (map (\<lambda>(f, t, u). (f, subst_ty \<mu> \<mu>' t, u)) fs ! i))"
    by (simp add: case_prod_beta' subst_ty_ct_def)
  then show ?case
    using ct_sem_recescape subst_ty_ct_def normalise_domain constraint_sem.ct_sem_recescape 
    by fastforce
qed


section {* Context relations (Fig 3.2) *}
inductive ctx_split_comp :: "axm_set \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  ctx_split_none  : "ctx_split_comp K None None None"
| ctx_split_left  : "ctx_split_comp K (Some \<tau>) (Some \<tau>) None"
| ctx_split_right : "ctx_split_comp K (Some \<tau>) None (Some \<tau>)"
| ctx_split_share : "\<lbrakk> A \<turnstile> CtShare \<tau> \<rbrakk> \<Longrightarrow> ctx_split_comp K (Some \<tau>) (Some \<tau>) (Some \<tau>)"

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
  weak_none : "weakening_comp K None None"
| weak_keep : "weakening_comp K (Some \<tau>) (Some \<tau>)"
| weak_drop : "\<lbrakk> A \<turnstile> CtDrop \<tau> \<rbrakk> \<Longrightarrow> weakening_comp K (Some \<tau>) None"

definition weakening :: "axm_set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" 
           ("_ \<turnstile> _ \<leadsto>w _" [40,0,40] 60) where
  "weakening K \<equiv> list_all2 (weakening_comp K)"

lemma weak_keep_refl: "weakening_comp K (Some \<tau>) (Some \<rho>) \<Longrightarrow> \<tau> = \<rho>"
  using weakening_comp.cases by auto


section {* Typing Rules (Fig 3.3 3.8 3.13) *}
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
   ; A \<turnstile> subst_tyvar_ct ts C
   ; \<tau>' = subst_tyvar ts \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> TypeApp name ts : \<tau>'"
| typing_let:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : \<tau>1
   ; A \<ddagger> ((Some \<tau>1) # \<Gamma>2) \<turnstile> e2 : \<tau>2
  \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Let e1 e2 : \<tau>2"
| typing_letb:                                                 
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> (minus_ctx ys \<Gamma>1) \<box> \<Gamma>2
   ; \<forall>i < length \<Gamma>1. (((\<Gamma>1 ! i) \<noteq> None) \<and> (ys ! i)) \<longrightarrow> 
      (if (\<Gamma>2 ! i = None) then (\<exists>t. \<Gamma>1 ! i = Some (TBang t)) 
                          else (\<Gamma>1 ! i = Some (TBang (the (\<Gamma>2 ! i)))))
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : \<tau>'
   ; A \<turnstile> CtEscape \<tau>'
   ; A \<ddagger> ((Some \<tau>') # \<Gamma>2) \<turnstile> e2 : \<tau>                                      
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> LetBang ys e1 e2 : \<tau>"
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
   ; \<forall>j < length Ks. if j = i then (snd \<circ> snd) (Ks ! j) = Unchecked else (snd \<circ> snd) (Ks ! j) = Checked
   ; A \<ddagger> \<Gamma> \<turnstile> e : (fst \<circ> snd) (Ks ! i)
   ; \<tau> = TVariant Ks None
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Con nm e: \<tau>"
| typing_case:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; distinct (map fst Ks)
   ; i < length Ks
   ; fst (Ks ! i) = nm
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : variant_nth_unchecked i (TVariant Ks None)
   ; A \<ddagger> (Some ((fst \<circ> snd) (Ks ! i))) # \<Gamma>2 \<turnstile> e2 : \<tau>
   ; A \<ddagger> (Some (variant_nth_checked i (TVariant Ks None))) # \<Gamma>2 \<turnstile> e3 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Case e1 nm e2 e3 : \<tau>" 
| typing_irref:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; distinct (map fst Ks)
   ; i < length Ks
   ; fst (Ks ! i) = nm
   ; \<forall>j < length Ks. if j = i then (snd \<circ> snd) (Ks ! j) = Unchecked else (snd \<circ> snd) (Ks ! j) = Checked
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : (TVariant Ks None)
   ; A \<ddagger> (Some ((fst \<circ> snd) (Ks ! i))) # \<Gamma>2 \<turnstile> e2 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Esac e1 nm e2 : \<tau>"
| typing_member:
  "\<lbrakk> distinct (map fst fs)
   ; i < length fs
   ; fst (fs ! i) = nm
   ; \<forall>j < length fs. if j = i then (snd \<circ> snd) (fs ! i) = Present else (snd \<circ> snd) (fs ! i) = Taken
   ; A \<ddagger> \<Gamma> \<turnstile> e : TRecord fs None s
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Member e nm : \<tau>"
| typing_struct:
  "\<lbrakk> distinct (map fst fs)
   ; nms = map fst fs
   ; \<forall>i < length fs. (snd \<circ> snd) (fs ! i) = Present
   ; length \<Gamma>1s = length nms
   ; \<forall>i < length \<Gamma>1s. A \<ddagger> (\<Gamma>s ! i) \<turnstile> (es ! i) : (fst \<circ> snd) (fs ! i)
   ; length \<Gamma>2s = Suc (length nms)
   ; \<forall>i < length \<Gamma>2s - 1. A \<turnstile> (\<Gamma>2s ! i) \<leadsto> (\<Gamma>1s ! i) \<box> (\<Gamma>2s ! (Suc i))
   ; hd \<Gamma>2s = \<Gamma> \<and> A \<turnstile> (last \<Gamma>2s) \<leadsto>w (empty (length (last \<Gamma>2s)))
   ; \<tau> = TRecord fs None Unboxed
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Struct nms es : \<tau>"
| typing_put:
  "\<lbrakk> distinct (map fst fs)
   ; i < length fs
   ; fst (fs ! i) = nm
   ; (snd \<circ> snd) (fs ! i) = Present
   ; A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : record_nth_taken i (TRecord fs None s)
   ; s \<noteq> ReadOnly
   ; A \<ddagger> \<Gamma>2 \<turnstile> e2 : (fst \<circ> snd) (fs ! i) 
   ; \<tau> = TRecord fs None s 
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Put e1 nm e2 : \<tau>"
| typing_take:
  "\<lbrakk> distinct (map fst fs)
   ; i < length fs
   ; fst (fs ! i) = nm
   ; (snd \<circ> snd) (fs ! i) = Present
   ; A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e1 : TRecord fs None s
   ; s \<noteq> ReadOnly
   ; A \<ddagger> (Some (record_nth_taken i (TRecord fs None s))) # (Some ((fst \<circ> snd) (fs ! i))) 
                                                         # \<Gamma>2 \<turnstile> e2 : \<tau>
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Take e1 nm e2 : \<tau>"

inductive typing_all :: "axm_set \<Rightarrow> ctx \<Rightarrow> 'fnname expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_ \<ddagger> _ \<turnstile>* _ : _" [40,0,0,40] 60) where
typing_all_empty:
  "A \<turnstile> \<Gamma> \<leadsto>w (empty (length \<Gamma>)) \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile>* [] : []"
| typing_all_cons:
  "\<lbrakk> A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2
   ; A \<ddagger> \<Gamma>1 \<turnstile> e : \<tau>
   ; A \<ddagger> \<Gamma>2 \<turnstile>* es : \<tau>s 
   \<rbrakk> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile>* e # es : \<tau> # \<tau>s" 

lemma typing_all_len:
  "A \<ddagger> \<Gamma> \<turnstile>* es : \<tau>s \<Longrightarrow> length es = length \<tau>s"
  by (induct rule: typing_all.induct; simp)

lemma typing_struct_equiv_def:
  assumes "distinct (map fst fs)"
    and "nms = map fst fs"
    and "\<forall>i < length fs. (snd \<circ> snd) (fs ! i) = Present"
    and "A \<ddagger> \<Gamma> \<turnstile>* es : map (fst \<circ> snd) fs"
    and "\<tau> = TRecord fs None Unboxed"
  shows "A \<ddagger> \<Gamma> \<turnstile> Struct nms es : \<tau>"
proof -
  have nms_es_length: "length nms = length es"
    using assms typing_all_len by auto
  {
    fix A \<Gamma> es \<tau>s
    assume typing: "A \<ddagger> \<Gamma> \<turnstile>* es : \<tau>s"
    have "\<exists>\<Gamma>1s \<Gamma>2s. length \<Gamma>1s = length es \<and> 
                    (\<forall>i < length \<Gamma>1s. A \<ddagger> (\<Gamma>1s ! i) \<turnstile> (es ! i) : (\<tau>s ! i)) \<and>
                    length \<Gamma>2s = Suc (length es) \<and> 
                    (\<forall>i < length \<Gamma>2s - 1. A \<turnstile> (\<Gamma>2s ! i) \<leadsto> (\<Gamma>1s ! i) \<box> (\<Gamma>2s ! (Suc i))) \<and>
                    hd \<Gamma>2s = \<Gamma> \<and> A \<turnstile> (last \<Gamma>2s) \<leadsto>w empty (length (last \<Gamma>2s))"
      using typing
    proof (induct rule: typing_all.induct)
      case (typing_all_empty A \<Gamma>)
      then show ?case
        using diff_Suc_1 last_conv_nth length_Cons list.distinct(1) list.sel(1) list.size(3) 
          not_less_zero nth_Cons_0 by metis
    next
      case (typing_all_cons A \<Gamma> \<Gamma>1 \<Gamma>2 e \<tau> es \<tau>s)
      obtain \<Gamma>1s \<Gamma>2s where props: "length \<Gamma>1s = length es"
                                  "\<forall>i < length \<Gamma>1s. A \<ddagger> (\<Gamma>1s ! i) \<turnstile> (es ! i) : (\<tau>s ! i)"
                                  "length \<Gamma>2s = Suc (length es)"
                                  "\<forall>i < length \<Gamma>2s - 1. A \<turnstile> (\<Gamma>2s ! i) \<leadsto> (\<Gamma>1s ! i) \<box> \<Gamma>2s ! Suc i" 
                                  "hd \<Gamma>2s = \<Gamma>2" "A \<turnstile> last \<Gamma>2s \<leadsto>w local.empty (length (last \<Gamma>2s))"
        using typing_all_cons by blast
      obtain \<Gamma>1s' where \<Gamma>1s'_def: "\<Gamma>1s' = \<Gamma>1 # \<Gamma>1s" by blast
      obtain \<Gamma>2s' where \<Gamma>2s'_def: "\<Gamma>2s' = \<Gamma> # \<Gamma>2s" by blast
      have "length \<Gamma>1s' = length (e # es)"
        using \<Gamma>1s'_def props by force
      moreover have "\<forall>i < length \<Gamma>1s'. A \<ddagger> (\<Gamma>1s' ! i) \<turnstile> (e # es) ! i : (\<tau> # \<tau>s) ! i"
        by (rule allI; case_tac "i = 0"; auto simp add: \<Gamma>1s'_def typing_all_cons props)
      moreover have "length \<Gamma>2s' = Suc (length (e # es))"
        using \<Gamma>2s'_def props by force
      moreover have "\<forall>i < length \<Gamma>2s' - 1. A \<turnstile> (\<Gamma>2s' ! i) \<leadsto> (\<Gamma>1s' ! i) \<box> (\<Gamma>2s' ! (Suc i))"
      proof -
        have \<Gamma>2s_hd: "\<Gamma>2s ! 0 = \<Gamma>2"
          using \<Gamma>2s'_def props by (metis list.sel(1) list_exhaust_size_gt0 nth_Cons_0 zero_less_Suc)
        show ?thesis
          by (rule allI; case_tac "i = 0"; auto simp add: \<Gamma>2s_hd \<Gamma>2s'_def \<Gamma>1s'_def props 
                                                          typing_all_cons less_Suc_eq_0_disj) 
      qed
      moreover have "hd \<Gamma>2s' = \<Gamma>" "A \<turnstile> last \<Gamma>2s' \<leadsto>w local.empty (length (last \<Gamma>2s'))"
        using \<Gamma>2s'_def props by force+
      ultimately show ?case by blast
    qed
  }
  then obtain \<Gamma>1s \<Gamma>2s where "length \<Gamma>1s = length nms"
                            "\<forall>i < length \<Gamma>1s. A \<ddagger> (\<Gamma>1s ! i) \<turnstile> (es ! i) : ((map (fst \<circ> snd) fs) ! i)"
                            "length \<Gamma>2s = Suc (length nms)"
                            "\<forall>i < length \<Gamma>2s - 1. A \<turnstile> (\<Gamma>2s ! i) \<leadsto> (\<Gamma>1s ! i) \<box> (\<Gamma>2s ! (Suc i))"
                            "hd \<Gamma>2s = \<Gamma> \<and> A \<turnstile> last \<Gamma>2s \<leadsto>w local.empty (length (last \<Gamma>2s))"
    using assms nms_es_length by metis
  then show ?thesis
    using assms typing_struct by force
qed

lemma typing_sig_refl:
  "A \<ddagger> \<Gamma> \<turnstile> e : \<tau> \<Longrightarrow> A \<ddagger> \<Gamma> \<turnstile> Sig e \<tau> : \<tau>"
  using ct_sem_equal ct_sem_refl type_infer_axioms typing_sig by blast


section {* Elementary Constraint Generation Rules (Fig 3.4 3.10 3.13) *}
inductive constraint_gen_elab :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'fnname expr \<Rightarrow> type \<Rightarrow> 
                                  cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> 'fnname expr \<Rightarrow> bool"
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
| cg_letb:
  "\<lbrakk> \<alpha> = TUnknown n1
   ; \<forall>i < length G1. ys ! i \<longrightarrow> snd (G1 ! i) = 0
   ; (bang_cg_ctx ys G1),(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> (bang_cg_ctx ys G2),n2 | C1 | e1'
   ; ((\<alpha>, 0) # (set0_cg_ctx ys G2)),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 | e2'
   ; C3 = fold CtConj (List.map2 (\<lambda>b (\<rho>, m). if b \<and> m = 0 then CtDrop (TBang \<rho>) else CtTop) ys G2) CtTop
   ; C4 = fold CtConj (List.map2 (\<lambda>b (\<rho>, m). if b \<and> m = 0 then CtDrop \<rho> else CtTop) ys G3) CtTop
   ; C5 = (if m = 0 then CtDrop \<alpha> else CtTop)
   ; C6 = CtEscape \<alpha>
   ; C7 = CtConj ( CtConj ( CtConj (CtConj (CtConj C1 C2) C3) C4) C5) C6
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> LetBang ys e1 e2 : \<tau> \<leadsto> G3,n3 | C7 | Sig (LetBang ys e1' e2') \<tau>"
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
   ; \<beta>s = map (TUnknown \<circ> (+) n) [0..<m]
   ; \<rho>' = subst_tyvar (ts @ \<beta>s) \<rho>
   ; C' = subst_tyvar_ct (ts @ \<beta>s) C
   ; C2 = CtConj (CtSub \<rho>' \<tau>) C'
   ; n' = n + m
   \<rbrakk> \<Longrightarrow> G,n \<turnstile> TypeApp name ts : \<tau> \<leadsto> G,n' | C2 | Sig (TypeApp name (ts @ \<beta>s)) \<tau>"
| cg_vcon:
  "\<lbrakk> \<alpha> = Suc n1
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e : \<beta> \<leadsto> G2,n2 | C | e'
   ; C' = CtConj C (CtSub (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>)) \<tau>)
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Con nm e : \<tau> \<leadsto> G2,n2 | C' | Sig (Con nm e') \<tau>"
| cg_case:
  "\<lbrakk> \<alpha> = Suc n1
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e1 : TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>) \<leadsto> G2,n2 | C1 | e1'
   ; ((\<beta>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<beta>, m) # G3),n3 | C2 |e2'
   ; (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>)), 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> 
     (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>)), l) # G3'),n4 | C3 | e3'
   ; G3 \<Join> G3' \<leadsto> G4 | C4
   ; if m = 0 then C5 = CtDrop \<beta> else C5 = CtTop
   ; if l = 0 then C6 = CtDrop (TVariant [(nm, \<beta>, Checked)] (Some \<alpha>)) else C6 = CtTop
   ; C7 = CtConj (CtConj (CtConj (CtConj (CtConj C1 C2) C3) C4) C5) C6
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Case e1 nm e2 e3 : \<tau> \<leadsto> G4,n4 | C7 | Sig (Case e1' nm e2' e3') \<tau>"
| cg_irref:
  "\<lbrakk> \<alpha> = Suc n1
   ; \<beta> = TUnknown n1
   ; G1,Suc(Suc n1) \<turnstile> e1 : (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>)) \<leadsto> G2,n2 | C1 | e1'
   ; ((\<beta>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<beta>, m) # G3),n3 | C2 | e2'
   ; C3 = CtExhausted (TVariant [(nm, \<beta>, Checked)] (Some \<alpha>))
   ; if m = 0 then C4 = CtDrop \<beta> else C4 = CtTop
   ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Esac e1 nm e2 : \<tau> \<leadsto> G3,n3 | C5 | Sig (Esac e1' nm e2') \<tau>"
| cg_member:
  "\<lbrakk> \<alpha> = Some n1
   ; \<beta> = SUnknown (Suc n1)
   ; G1,Suc(Suc n1) \<turnstile> e : TRecord [(nm, \<tau>, Present)] \<alpha> \<beta> \<leadsto> G2,n2 | C | e'
   ; C' = CtConj C (CtDrop (TRecord [(nm, \<tau>, Taken)] \<alpha> \<beta>))
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Member e nm : \<tau> \<leadsto> G2,n2 | C' | Sig (Member e' nm) \<tau>"
| cg_take:
  "\<lbrakk> \<beta> = TUnknown n1
   ; \<alpha> = Some (Suc n1)
   ; \<gamma> = SUnknown (Suc (Suc n1))
   ; G1,Suc(Suc(Suc n1)) \<turnstile> e1 : TRecord [(nm, \<beta>, Present)] \<alpha> \<gamma> \<leadsto> G2,n2 | C1 | e1'
   ; ((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2),n2 \<turnstile> e2 : \<tau> \<leadsto> 
     ((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, m) # (\<beta>, l) # G3),n3 | C2 | e2'
   ; C3 = (if m = 0 then CtDrop (TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>) else CtTop)
   ; C4 = (if l = 0 then CtDrop \<beta> else CtTop)
   ; C5 = CtNotRead \<gamma>
   ; C6 = CtConj (CtConj (CtConj (CtConj C1 C2) C3) C4) C5
   \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Take e1 nm e2 : \<tau> \<leadsto> G3,n3 | C6 | Sig (Take e1' nm e2') \<tau>"
| cg_put:
  "\<lbrakk> \<beta> = TUnknown n1
    ; \<alpha> = Some (Suc n1)
    ; \<gamma> = SUnknown (Suc (Suc n1))
    ; G1,Suc(Suc(Suc n1)) \<turnstile> e1 : TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma> \<leadsto> G2,n2 | C1 | e1'
    ; G2,n2 \<turnstile> e2 : \<beta> \<leadsto> G3,n3 | C2 | e2'
    ; C3 = CtSub (TRecord [(nm, \<beta>, Present)] \<alpha> \<gamma>) \<tau>
    ; C4 = CtNotRead \<gamma>
    ; C5 = CtConj (CtConj (CtConj C1 C2) C3) C4
    \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Put e1 nm e2 : \<tau> \<leadsto> G3,n3 | C5 | Sig (Put e1' nm e2') \<tau>" 
| cg_struct:
  "\<lbrakk> \<alpha>s = map (TUnknown \<circ> (+) n1) [0..<length nms]
    ; length nms = length es
    ; length Gs = Suc (length nms)
    ; hd Gs = G1 \<and> last Gs = G2 
    ; length ns = Suc (length nms)
    ; hd ns = (n1 + length nms) \<and> last ns = n2
    ; length Cs = length nms
    ; \<forall>i < length nms. (Gs ! i),(ns ! i) \<turnstile> (es ! i) : (\<alpha>s ! i) \<leadsto> 
                       (Gs ! (Suc i)),(ns ! (Suc i)) | (Cs ! i) | (es' ! i)
    ; C' = CtConj (foldr CtConj Cs CtTop)
                  (CtSub (TRecord (List.map2 (\<lambda>nm \<alpha>. (nm, \<alpha>, Present)) nms \<alpha>s) None Unboxed) \<tau>) 
    \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile> Struct nms es : \<tau> \<leadsto> G2,n2 | C' | Sig (Struct nms es') \<tau>"

inductive constraint_gen_elab_all :: "cg_ctx \<Rightarrow> nat \<Rightarrow> 'fnname expr list \<Rightarrow> type list \<Rightarrow> 
                                      cg_ctx \<Rightarrow> nat \<Rightarrow> constraint \<Rightarrow> 'fnname expr list \<Rightarrow> bool"
          ("_,_ \<turnstile>* _ : _ \<leadsto> _,_ | _ | _" [30,0,0,0,0,0,0,30] 60) where
cg_all_empty:
   "G,n \<turnstile>* [] : [] \<leadsto> G,n | CtTop | []"
| cg_all_cons:
   "\<lbrakk> G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e'
    ; G2,n2 \<turnstile>* es : \<tau>s \<leadsto> G3,n3 | C2 | es'
    ; C3 = CtConj C1 C2
    \<rbrakk> \<Longrightarrow> G1,n1 \<turnstile>* (e # es) : (\<tau> # \<tau>s) \<leadsto> G3,n3 | C3 | e' # es'"

lemma cg_gen_elab_all_len:
  "G,n \<turnstile>* es : \<tau>s \<leadsto> G',n' | C | es' \<Longrightarrow> length es = length \<tau>s \<and> length es = length es'"
  by (induct rule: constraint_gen_elab_all.induct; simp) 

lemma cg_struct_equiv_def:
  assumes "\<alpha>s = map (TUnknown \<circ> (+) n1) [0..<length nms]"
    and "G1,(n1 + length nms) \<turnstile>* es : \<alpha>s \<leadsto> G2,n2 | C | es'"
    and "C' = CtConj C (CtSub (TRecord (List.map2 (\<lambda>nm \<alpha>. (nm, \<alpha>, Present)) nms \<alpha>s) None Unboxed) \<tau>)"
  shows "G1,n1 \<turnstile> Struct nms es : \<tau> \<leadsto> G2,n2 | C' | Sig (Struct nms es') \<tau>"
proof (cases "length nms = 0")
  case True
  then have "nms = []" "es = []" "es' = []"
    using assms cg_gen_elab_all_len by force+
  then moreover have "C = CtTop" "G1 = G2" "n1 = n2"
    using assms constraint_gen_elab_all.cases by fastforce+
  ultimately show ?thesis 
    using assms cg_struct[where ?Gs="[G1]" and ?ns="[n1]"] by force
next
  case False
  have nms_es_length: "length nms = length es"
    using assms cg_gen_elab_all_len by simp
  {
    fix G n es \<tau>s G' n' C es'
    assume cg_gen: "G,n \<turnstile>* es : \<tau>s \<leadsto> G',n' | C | es'" 
    have "\<exists>Gs ns Cs. length Gs = Suc (length es) \<and> hd Gs = G \<and> last Gs = G' \<and>
                     length ns = Suc (length es) \<and> hd ns = n \<and> last ns = n' \<and>
                     length Cs = length es \<and> (\<forall>i < length es. 
          (Gs ! i),(ns ! i) \<turnstile> es ! i : \<tau>s ! i \<leadsto> (Gs ! (Suc i)),(ns ! (Suc i)) | Cs ! i | es' ! i) \<and>
                     C = foldr CtConj Cs CtTop"
      using cg_gen
    proof (induct rule: constraint_gen_elab_all.induct)
      case (cg_all_empty G n)
      then show ?case using exI[where x="[G]"] exI[where x="[n]"] exI[where x="[]"] by force
    next
      case (cg_all_cons G1 n1 e \<tau> G2 n2 C1 e' es \<tau>s G3 n3 C2 es' C3)
      obtain Gs ns Cs where props: "length Gs = Suc (length es)" "hd Gs = G2" "last Gs = G3"
                                   "length ns = Suc (length es)" "hd ns = n2" "last ns = n3"
                                   "length Cs = length es" 
                                   "(\<forall>i<length es. (Gs ! i),(ns ! i) \<turnstile> (es ! i) : (\<tau>s ! i) \<leadsto> 
                                    (Gs ! (Suc i)),(ns ! (Suc i)) | (Cs ! i) | (es' ! i))"
                                   "C2 = foldr CtConj Cs CtTop"
        using cg_all_cons by blast
      obtain Gs' where Gs'_def: "Gs' = G1 # Gs" by force
      obtain ns' where ns'_def: "ns' = n1 # ns" by force
      obtain Cs' where Cs'_def: "Cs' = C1 # Cs" by force
      have "length Gs' = Suc (length (e # es))" "hd Gs' = G1" "last Gs' = G3"
        using props Gs'_def by force+
      moreover have "length ns' = Suc (length (e # es))" "hd ns' = n1" "last ns' = n3"
        using props ns'_def by force+
      moreover have "length Cs' = length (e # es)"
        using props Cs'_def by force
      moreover have "\<forall>i < length (e # es). (Gs' ! i),(ns' ! i) \<turnstile> ((e # es) ! i) : ((\<tau> # \<tau>s) ! i) \<leadsto> 
                                   (Gs' ! (Suc i)),(ns' ! (Suc i)) | (Cs' ! i) | ((e' # es') ! i)"
      proof -
        {
          fix i :: nat
          assume i_size: "i < length (e # es)"
          have "(Gs' ! i),(ns' ! i) \<turnstile> ((e # es) ! i) : ((\<tau> # \<tau>s) ! i) \<leadsto> 
              (Gs' ! (Suc i)),(ns' ! (Suc i)) | (Cs' ! i) | ((e' # es') ! i)"
          proof (cases "i = 0")
            case True
            show ?thesis
              using True cg_all_cons Gs'_def ns'_def Cs'_def props 
              by (metis Suc_length_conv list.sel(1) nth_Cons_0 nth_Cons_Suc)
          next
            case False
            then show ?thesis
              using Cs'_def Gs'_def i_size less_Suc_eq_0_disj ns'_def props by auto
          qed
        } then show ?thesis by blast
      qed
      moreover have "C3 = foldr CtConj Cs' CtTop"
        using Cs'_def props cg_all_cons by simp
      ultimately show ?case by blast
    qed
  }
  then obtain Gs ns Cs where "length Gs = Suc (length nms)" "hd Gs = G1" "last Gs = G2"
                             "length ns = Suc (length nms)" "hd ns = n1 + length nms" 
                             "last ns = n2" "length Cs = length nms" 
                             "(\<forall>i < length nms. (Gs ! i),(ns ! i) \<turnstile> (es ! i) : (\<alpha>s ! i) \<leadsto> 
                              (Gs ! (Suc i)),(ns ! (Suc i)) | (Cs ! i) | (es' ! i))"
                             "C = foldr CtConj Cs CtTop"
    using nms_es_length assms by metis
  then show ?thesis 
    using assms False cg_struct nms_es_length by blast
qed

lemma cg_num_fresh_nondec:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "n \<le> n'"
  using assms 
proof (induct rule: constraint_gen_elab.induct)
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  then have "ns ! 0 \<le> ns ! (length nms)"
    by (rule_tac nondec_fun_prop[where ?P="\<lambda>i. ns ! i" and ?n="length nms"]; fastforce)
  then have "hd ns \<le> last ns"
    using cg_struct.hyps Zero_not_Suc diff_Suc_1 hd_conv_nth last_conv_nth length_0_conv lessI 
      less_Suc_eq_0_disj by metis
  then show ?case
    using cg_struct.hyps by linarith
qed force+

lemma cg_ctx_length:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "length G = length G'"
  using assms
proof (induct rule: constraint_gen_elab.inducts)
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case using alg_ctx_jn_length by metis
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case using alg_ctx_jn_length by simp
next
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  then show ?case
    using set0_cg_ctx_length bang_cg_ctx_length by fastforce
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  then have "length (Gs ! 0) = length (Gs ! (length nms))"
    by (rule_tac constant_fun_prop[where ?P="(\<lambda>i. length (Gs ! i))" and ?n="length nms"]; fastforce)
  then show ?case
    using cg_struct.hyps diff_Suc_1 hd_conv_nth last_conv_nth lessI less_Suc_eq_0_disj
    by (metis (no_types, lifting) list.size(3) nat.simps(3))
qed auto

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
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  then show ?case
    using cg_ctx_length bang_cg_ctx_type_prop set0_cg_ctx_type_same bang_cg_ctx_length 
      set0_cg_ctx_length type.inject
    by (metis (no_types, hide_lams) Suc_mono length_Cons nth_Cons_Suc)
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
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  have "length G1 = length G2"
    using cg_take cg_ctx_length by fast
  then show ?case
    using cg_take by fastforce
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  have "\<forall>j < length nms. length (Gs ! 0) = length (Gs ! j)"
    using constant_fun_prop[where ?P="\<lambda>i. length (Gs ! i)" and ?n="length nms"]
      cg_struct cg_ctx_length by (metis Suc_leI zero_order(1))
  then have "\<forall>j < length nms. i < length (Gs ! j)"
    using cg_struct hd_conv_nth Zero_not_Suc by (metis list.size(3))
  then have "fst ((Gs ! 0) ! i) = fst ((Gs ! (length nms)) ! i)"
    using cg_struct constant_fun_prop[where ?P="\<lambda>j. fst ((Gs ! j) ! i)" and ?n="length nms"] 
      by blast
  then show ?case
    using cg_struct.hyps diff_Suc_1 hd_conv_nth last_conv_nth length_greater_0_conv 
      less_Suc_eq_0_disj by metis
qed (auto simp add: cg_ctx_length)+

lemma cg_ctx_type_same2:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
  shows "\<And>i. i < length G' \<Longrightarrow> fst (G ! i) = fst (G' ! i)"
  using assms cg_ctx_type_same1 cg_ctx_idx_size cg_ctx_length by metis

lemma cg_ctx_type_checked_nondec:
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
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  then show ?case
  proof (cases "ys ! i")
    case False
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using bang_cg_ctx_length bang_cg_ctx_type_checked_same cg_ctx_length cg_letb by metis
    moreover have "snd (G2 ! i) \<le> snd (G3 ! i)"
      using False cg_letb set0_cg_ctx_length set0_cg_ctx_type_checked_prop cg_ctx_length
        bang_cg_ctx_length by (metis (no_types, lifting) Suc_mono length_Cons nth_Cons_Suc)
    ultimately show ?thesis
      by linarith
  qed (fastforce intro: cg_letb)
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case
    using cg_ctx_length alg_ctx_jn_type_checked_nondec1 le_trans by fastforce
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
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    have "snd (G1 ! i) \<le> snd (G3 ! i)"
      using cg_case cg_ctx_length type_infer_axioms
      by (metis (no_types, lifting) Suc_less_eq le_trans length_Cons nth_Cons_Suc)
    then show ?thesis
      using alg_ctx_jn_type_checked_nondec1 cg_case cg_ctx_length
      by (metis (no_types, lifting) Suc_less_eq le_trans length_Cons)
  qed
next
  case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
    using Suc_mono cg_ctx_length le_trans length_Cons nth_Cons_Suc by fastforce 
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  have "length G1 = length G2"
    using cg_take cg_ctx_length by fast
  then show ?case
    using cg_take by fastforce
next
  case (cg_put \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau> C4 C5)
  then show ?case
    using cg_take cg_ctx_length by fastforce
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  have "\<forall>j < length nms. length (Gs ! 0) = length (Gs ! j)"
    using constant_fun_prop[where ?P="\<lambda>i. length (Gs ! i)" and ?n="length nms"]
      cg_struct cg_ctx_length by (metis Suc_leI zero_order(1))
  then have "\<forall>j < length nms. i < length (Gs ! j)"
    using cg_struct hd_conv_nth Zero_not_Suc by (metis list.size(3))
  then have "snd ((Gs ! 0) ! i) \<le> snd ((Gs ! (length nms)) ! i)"
    using cg_struct nondec_fun_prop[where ?P="\<lambda>j. snd ((Gs ! j) ! i)" and ?n="length nms"] 
    by fastforce
  then show ?case 
    using cg_struct.hyps diff_Suc_1 hd_conv_nth last_conv_nth lessI less_Suc_eq_0_disj  
       by (metis (no_types, lifting) list.size(3) nat.simps(3))
qed blast+ 


section {* Assignment Definition *}
(* when we are assigning an unknown type a type, the assigned type should not contain any
   unknown types itself *)
type_synonym assignment = "(nat \<Rightarrow> type) \<times> (nat \<Rightarrow> (string \<times> type \<times> variant_usage_tag) list)
                                         \<times> (nat \<Rightarrow> (string \<times> type \<times> record_usage_tag) list)
                                         \<times> (nat \<Rightarrow> sigil)"

fun assign_app_sigil :: "assignment \<Rightarrow> sigil \<Rightarrow> sigil" where
  "assign_app_sigil S ReadOnly = ReadOnly"
| "assign_app_sigil S Writable = Writable"
| "assign_app_sigil S Unboxed  = Unboxed"
| "assign_app_sigil S (SUnknown i) = (snd \<circ> snd \<circ> snd) S i"

fun assign_app_ty :: "assignment \<Rightarrow> type \<Rightarrow> type" where
  "assign_app_ty S (TVar n)                = TVar n"
| "assign_app_ty S (TFun t1 t2)            = TFun (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_ty S (TPrim pt)              = TPrim pt"
| "assign_app_ty S (TUnknown n)            = fst S n"
| "assign_app_ty S (TVariant Ks None)      = TVariant (map (\<lambda>(nm, t, u). (nm, assign_app_ty S t, u)) Ks) None"
| "assign_app_ty S (TVariant Ks (Some n))  = TVariant ((map (\<lambda>(nm, t, u). (nm, assign_app_ty S t, u)) Ks) @ 
                                                      (((fst \<circ> snd) S) n)) None"
| "assign_app_ty S (TRecord fs None s)     = TRecord (map (\<lambda>(f, t, u). (f, assign_app_ty S t, u)) fs) None s"
| "assign_app_ty S (TRecord fs (Some n) s) = TRecord ((map (\<lambda>(f, t, u). (f, assign_app_ty S t, u)) fs) @ 
                                                     (((fst \<circ> snd \<circ> snd) S) n)) None (assign_app_sigil S s)"
| "assign_app_ty S (TAbstract nm ts s)     = TAbstract nm (map (assign_app_ty S) ts) s"
| "assign_app_ty S (TObserve i)            = TObserve i"
| "assign_app_ty S (TBang t)               = TBang (assign_app_ty S t)"

fun assign_app_expr :: "assignment \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where
  "assign_app_expr S (Var n)            = Var n" 
| "assign_app_expr S (TypeApp e ts)     = TypeApp e (map (assign_app_ty S) ts)"
| "assign_app_expr S (Prim prim_op ts)  = Prim prim_op (map (assign_app_expr S) ts)"
| "assign_app_expr S (App e1 e2)        = App (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S Unit               = Unit"
| "assign_app_expr S (Lit l)            = Lit l"
| "assign_app_expr S (Cast nt e)        = Cast nt (assign_app_expr S e)"
| "assign_app_expr S (Let e1 e2)        = Let (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S (LetBang ys e1 e2) = LetBang ys (assign_app_expr S e1) (assign_app_expr S e2)"
| "assign_app_expr S (If e1 e2 e3)      = If (assign_app_expr S e1) (assign_app_expr S e2) (assign_app_expr S e3)"
| "assign_app_expr S (Sig e t)          = Sig (assign_app_expr S e) (assign_app_ty S t)"
| "assign_app_expr S (Con nm e)         = Con nm (assign_app_expr S e)"
| "assign_app_expr S (Case e1 nm e2 e3) = Case (assign_app_expr S e1) nm (assign_app_expr S e2) (assign_app_expr S e3)"
| "assign_app_expr S (Esac e1 nm e2)    = Esac (assign_app_expr S e1) nm (assign_app_expr S e2)"
| "assign_app_expr S (Struct fs es)     = Struct fs (map (assign_app_expr S) es)" 
| "assign_app_expr S (Take e1 f e2)     = Take (assign_app_expr S e1) f (assign_app_expr S e2)"
| "assign_app_expr S (Put e1 f e2)      = Put (assign_app_expr S e1) f (assign_app_expr S e2)"
| "assign_app_expr S (Member e f)       = Member (assign_app_expr S e) f"

fun "assign_app_constr" :: "assignment \<Rightarrow> constraint \<Rightarrow> constraint" where
  "assign_app_constr S (CtConj c1 c2)   = CtConj (assign_app_constr S c1) (assign_app_constr S c2)"
| "assign_app_constr S (CtIBound l t)   = CtIBound l (assign_app_ty S t)"
| "assign_app_constr S (CtEq t1 t2)     = CtEq (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S (CtSub t1 t2)    = CtSub (assign_app_ty S t1) (assign_app_ty S t2)"
| "assign_app_constr S CtTop            = CtTop"
| "assign_app_constr S CtBot            = CtBot"
| "assign_app_constr S (CtShare t)      = CtShare (assign_app_ty S t)"
| "assign_app_constr S (CtDrop t)       = CtDrop (assign_app_ty S t)"
| "assign_app_constr S (CtExhausted v)  = CtExhausted (assign_app_ty S v)"
| "assign_app_constr S (CtEscape t)     = CtEscape (assign_app_ty S t)"
| "assign_app_constr S (CtNotRead s)    = CtNotRead s"

definition assign_app_ctx :: "assignment \<Rightarrow> ctx \<Rightarrow> ctx" where
  "assign_app_ctx S G = map (map_option (assign_app_ty S)) G"

definition known_assignment :: "assignment \<Rightarrow> bool" where
  "known_assignment S \<equiv> \<forall>i. known_ty ((fst S) i) &
                        (\<forall>Ks Ks' n. assign_app_ty S (TVariant Ks (Some n)) = TVariant Ks' None 
                                   \<longrightarrow> distinct (map fst Ks') \<and> (known_ty (TVariant Ks' None))) &
                        (\<forall>fs fs' n s s'. assign_app_ty S (TRecord fs (Some n) s) = TRecord fs' None s'
                                   \<longrightarrow> distinct (map fst fs') \<and> (known_ty (TRecord fs' None s))
                                                              \<and> known_sigil s')"

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

lemma assign_app_ty_subst_tyvar_commute: 
  assumes "known_ty \<tau>"
  shows "assign_app_ty S (subst_tyvar xs \<tau>) = subst_tyvar (map (assign_app_ty S) xs) \<tau>"
  using assms 
proof (induct \<tau>)
  case (known_tfun t1 t2)
  then show ?case
    using known_tfunE by auto
next
  case (known_tvariant Ks)
  then have "map (\<lambda>k. assign_app_ty S (subst_tyvar xs ((fst \<circ> snd) k))) Ks = 
             map (\<lambda>k. subst_tyvar (map (assign_app_ty S) xs) ((fst \<circ> snd) k)) Ks"
    using map_eq_iff_nth_eq by blast
  then have "map (\<lambda>(nm, t, s). (nm, assign_app_ty S (subst_tyvar xs t), s)) Ks = 
             map (\<lambda>(nm, t, s). (nm, subst_tyvar (map (assign_app_ty S) xs) t, s)) Ks"
    using case_prod_beta comp_apply by auto
  then show ?case
    using subst_tyvar.simps assign_app_ty.simps by auto
next
  case (known_tabstract ts nm s)
  then have "map (\<lambda>t. assign_app_ty S (subst_tyvar xs t)) ts = 
             map (\<lambda>t. subst_tyvar (map (assign_app_ty S) xs) t) ts"
    using map_eq_iff_nth_eq by blast
  then show ?case
    using subst_tyvar.simps assign_app_ty.simps by auto
next
  case (known_trecord fs s)
  then have "map (\<lambda>f. assign_app_ty S (subst_tyvar xs ((fst \<circ> snd) f))) fs = 
             map (\<lambda>f. subst_tyvar (map (assign_app_ty S) xs) ((fst \<circ> snd) f)) fs"
    using map_eq_iff_nth_eq by blast
  then have "map (\<lambda>(nm, t, s). (nm, assign_app_ty S (subst_tyvar xs t), s)) fs = 
             map (\<lambda>(nm, t, s). (nm, subst_tyvar (map (assign_app_ty S) xs) t, s)) fs"
    using case_prod_beta comp_apply by auto
  then show ?case
    using subst_tyvar.simps assign_app_ty.simps by auto
qed (force intro: subst_tyvar.simps assign_app_ty.simps)+ 

lemma assign_app_constr_subst_tyvar_ct_commute: 
  assumes "known_ct C"
  shows "assign_app_constr S (subst_tyvar_ct xs C) = subst_tyvar_ct (map (assign_app_ty S) xs) C"
  using assms
proof (induct C)
qed (auto simp add: subst_tyvar_ct_def assign_app_ty_subst_tyvar_commute)+

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

lemma alg_ctx_jn_type_checked_diff:
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
    using alg_ctx_jn_type_same1 assms by auto
qed

section {* split_checked (Lemma 3.1) *}
(* Free Variables *)
fun fv' :: "nat \<Rightarrow> 'f expr \<Rightarrow> index set" where
  fv'_var:      "fv' n (Var i)              = (if i \<ge> n then {i - n} else {})"
| fv'_typeapp:  "fv' n (TypeApp f ts)       = {}"
| fv'_prim:     "fv' n (Prim prim_op es)    = (\<Union>e \<in> set es. fv' n e)"
| fv'_app:      "fv' n (App e1 e2)          = (fv' n e1) \<union> (fv' n e2)"
| fv'_unit:     "fv' n Unit                 = {}"
| fv'_lit:      "fv' n (Lit l)              = {}"
| fv'_cast:     "fv' n (Cast nt e)          = fv' n e"
| fv'_let:      "fv' n (Let e1 e2)          = (fv' n e1) \<union> (fv' (Suc n) e2)"
| fv'_letb:     "fv' n (LetBang ys e1 e2)   = (fv' n e1 - {y. ys ! (y + n)}) \<union> (fv' (Suc n) e2)"
| fv'_if:       "fv' n (If e1 e2 e3)        = (fv' n e1) \<union> (fv' n e2) \<union> (fv' n e3)"
| fv'_sig:      "fv' n (Sig e t)            = fv' n e"
| fv'_con:      "fv' n (Con nm e)           = fv' n e"
| fv'_case:     "fv' n (Case e1 nm e2 e3)   = (fv' n e1) \<union> (fv' (Suc n) e2) \<union> (fv' (Suc n) e3)"
| fv'_esac:     "fv' n (Esac e1 nm e2)      = (fv' n e1) \<union> (fv' (Suc n) e2)"
| fv'_struct:   "fv' n (Struct fs es)       = (\<Union>e \<in> set es. fv' n e)"
| fv'_take:     "fv' n (Take e1 f e2)       = (fv' n e1) \<union> (fv' (Suc (Suc n)) e2)"
| fv'_put:      "fv' n (Put e1 f e2)        = (fv' n e1) \<union> (fv' n e2)"
| fv'_member:   "fv' n (Member e f)         = fv' n e"

lemmas fv'_induct = fv'.induct[case_names fv'_var fv'_typeapp fv'_prim fv'_app fv'_unit fv'_lit 
                                          fv'_cast fv'_let fv'_letb fv'_if fv'_sig]

abbreviation fv :: "'s expr \<Rightarrow> index set" where
  "fv t \<equiv> fv' 0 t" 

lemma i_fv'_suc_iff_suc_i_fv':
  "i \<in> fv' (Suc m) e \<longleftrightarrow> Suc i \<in> fv' m e"
  by (induct m e arbitrary: i rule: fv'_induct; auto)

lemma fv'_suc_eq_dec_fv':
  "fv' (Suc m) e = image (\<lambda>x. x - 1) (fv' m e - {0})"
proof -
  have "\<forall>i \<in> fv' (Suc m) e.  i \<in> image (\<lambda>x. x - 1) (fv' m e - {0})"
    using i_fv'_suc_iff_suc_i_fv'
    by (metis Diff_empty Diff_insert0 diff_Suc_1 image_iff insertE insert_Diff nat.simps(3))
  moreover have "\<forall>i \<in> image (\<lambda>x. x - 1) (fv' m e - {0}). i \<in> fv' (Suc m) e"
    by (simp add: i_fv'_suc_iff_suc_i_fv')
  ultimately show ?thesis
    by blast
qed

lemma fv'_suc_eq_dec_fv'_minus:
  "(fv' (Suc m) e) - is = (\<lambda>x. x - 1) ` (fv' m e - ({0} \<union> (Suc ` is)))"
proof -
  have "\<forall>i \<in> (fv' (Suc m) e) - is. i \<in> (\<lambda>x. x - 1) ` (fv' m e - ({0} \<union> (Suc ` is)))"
    using i_fv'_suc_iff_suc_i_fv' DiffE DiffI Suc_eq_plus1 UnE diff_Suc_1
    by (metis (no_types, lifting) empty_iff image_iff insert_iff nat.simps(3))
  moreover have "\<forall>i \<in> (\<lambda>x. x - 1) ` (fv' m e - ({0} \<union> (Suc ` is))). i \<in> (fv' (Suc m) e) - is"
    using i_fv'_suc_iff_suc_i_fv' by force
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
  assumes "i \<notin> nS"
    and "i < length G"
  shows "(G\<bar>ns) ! i = (G\<bar>ns \<union> nS) ! i"
  by (metis Un_iff assms ctx_restrict_nth_none ctx_restrict_nth_some)

lemma assign_app_ctx_restrict_none:
  assumes "i \<notin> ns"
    and "i < length G"
  shows "assign_app_ctx S (G\<bar>ns) ! i = None"
  by (simp add: assign_app_ctx_def assms ctx_restrict_len ctx_restrict_nth_none)

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
  using assms assign_app_ctx_restrict_none by (metis option.simps(3))

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
    case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
    have "i \<in> fv' m e1 \<or> (Suc i) \<in> fv' m e2"
      using cg_letb.prems i_fv'_suc_iff_suc_i_fv' by auto
    then show ?case
      using bang_cg_ctx_length set0_cg_ctx_length bang_cg_ctx_length cg_ctx_length cg_letb.hyps 
      by (metis Suc_less_eq length_Cons)
  next
    case (cg_case \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
    then show ?case
      by (force simp add: i_fv'_suc_iff_suc_i_fv' cg_ctx_length)
  next
    case (cg_irref \<alpha> n1 \<beta> n2 G1 e1 nm G2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
    then show ?case 
      by (force simp add: i_fv'_suc_iff_suc_i_fv' cg_ctx_length)
  next
    case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
    have "i \<in> fv' m e1 \<or> (Suc (Suc i)) \<in> fv' m e2"
      using cg_take.prems by (simp add: i_fv'_suc_iff_suc_i_fv')
    then show ?case
      using cg_ctx_length cg_take by fastforce
  next
    case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
    obtain j where j_def: "i \<in> fv' m (es ! j)" "j < length es"
      using cg_struct fv'_struct by (metis UN_E in_set_conv_nth)
    have "j < length nms \<Longrightarrow> length (Gs ! 0) = length (Gs ! j)"
      using constant_fun_prop[where ?P="\<lambda>j. length (Gs ! j)" and ?n="length nms"]
        cg_struct cg_ctx_length by (metis Suc_leI zero_order(1))
    then show ?case
      using cg_struct.hyps j_def by (metis hd_conv_nth list.size(3) nat.simps(3))
  qed (auto simp add: cg_ctx_length split: if_splits)
qed

lemma cg_gen_output_type_checked_inc:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
    shows "snd (G2 ! i) > snd (G1 ! i)"
  using assms
proof (induct arbitrary: i rule: constraint_gen_elab.induct)
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_app.prems by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using cg_app.hyps cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
        constraint_gen_elab.cg_app 
      by (metis (no_types, lifting) dual_order.strict_iff_order leD)
  next
    case i_in_e2
    then show ?thesis 
      using cg_app.hyps cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
        constraint_gen_elab.cg_app
      by (metis dual_order.strict_iff_order leD)
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  have i_in_e1e2: "i \<in> fv' 0 e1 \<or> i \<in> fv' (Suc 0) e2"
    using fv'_let cg_let.prems by blast
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using i_in_e1e2 by blast
  then show ?case
  proof cases
    case i_in_e1
    then have "snd (G1 ! i) < snd (G2 ! i)"
      using cg_let.hyps by blast
    moreover  have "snd (G2 ! i) \<le> snd (G3 ! i)"
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_let
        i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    ultimately show ?thesis
      by simp
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"          
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_let.hyps
      by (metis i_fv'_suc_iff_suc_i_fv' length_Cons not_less_eq)
    moreover have "snd (G2 ! i) < snd (G3 ! i)"
      using cg_let.hyps i_fv'_suc_iff_suc_i_fv' i_in_e2 by fastforce
    ultimately show ?thesis
      using le_less_trans by blast
  qed
next
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  consider (i_in_e1) "i \<in> fv e1" "\<not>(ys ! i)" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using cg_letb.prems fv'_letb by fastforce
  then show ?case
  proof cases
    case i_in_e1
    have i_size: "i < length G1"
      using cg_gen_fv_elem_size i_in_e1 cg_letb.hyps bang_cg_ctx_length by metis
    have "snd (G1 ! i) < snd (G2 ! i)"
      using cg_letb.hyps bang_cg_ctx_length bang_cg_ctx_type_checked_same cg_ctx_length 
        i_in_e1 i_size by metis
    moreover have "snd (G2 ! i) \<le> snd (G3 ! i)"
    proof -
      have "snd ((set0_cg_ctx ys G2) ! i) \<le> snd (G3 ! i)"
        using cg_letb.hyps set0_cg_ctx_length cg_ctx_length i_size cg_ctx_type_checked_nondec
          bang_cg_ctx_length by (metis (no_types, lifting) Suc_mono length_Cons nth_Cons_Suc)
      then show ?thesis
        using bang_cg_ctx_length cg_letb.hyps i_in_e1 i_size set0_cg_ctx_type_checked_prop
          cg_ctx_length by metis
    qed
    ultimately show ?thesis
      by linarith
  next
    case i_in_e2
    have "Suc i < length ((\<alpha>, 0) # (set0_cg_ctx ys G2))"
      using cg_gen_fv_elem_size cg_letb i_in_e2 Suc_mono length_Cons i_fv'_suc_iff_suc_i_fv' 
      by metis
    then have i_size: "i < length G2"
      using set0_cg_ctx_length by fastforce
    show ?thesis
    proof (cases "ys ! i")
      case True
      have "snd (G1 ! i) = 0"
        using cg_letb.hyps True bang_cg_ctx_length cg_ctx_length i_size by metis
      then show ?thesis
        using cg_letb.hyps i_fv'_suc_iff_suc_i_fv' i_in_e2 by fastforce
    next
      case False
      have "snd (G1 ! i) \<le> snd (G2 ! i)"
      proof -
        have "snd ((bang_cg_ctx ys G1) ! i) \<le> snd ((bang_cg_ctx ys G2) ! i)"
          using cg_ctx_type_checked_nondec i_size bang_cg_ctx_length cg_letb.hyps cg_ctx_length by auto
        then show ?thesis
          using bang_cg_ctx_type_checked_same i_size cg_ctx_length bang_cg_ctx_length cg_letb.hyps
          by metis
      qed
      moreover have "snd (G2 ! i) < snd (G3 !i)"
        using cg_letb i_fv'_suc_iff_suc_i_fv' i_in_e2 set0_cg_ctx_type_checked_prop[OF i_size] False
           nth_Cons_Suc by metis
      ultimately show ?thesis
        by linarith
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  have i_in_e1e2e3: "i \<in> fv e1 \<or> i \<in> fv e2 \<or> i \<in> fv e3"
    using cg_if.prems by auto
  have snd_G1_le_G2: "snd (G1 ! i) \<le> snd (G2 ! i)"
    using i_in_e1e2e3 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_if.hyps
    by metis
  have snd_G2_le_G3: "snd (G2 ! i) \<le> snd (G3 ! i)"
    using i_in_e1e2e3 cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_if.hyps
      cg_ctx_length by metis
  have snd_G3_le_G4: "snd (G3 ! i) \<le> snd (G4 ! i)"
    using i_in_e1e2e3 alg_ctx_jn_type_checked_nondec1 cg_gen_fv_elem_size cg_if.hyps 
      cg_ctx_length by metis
  have snd_G3'_le_G4: "snd (G3' ! i) \<le> snd (G4 ! i)"
    using i_in_e1e2e3 alg_ctx_jn_type_checked_nondec2 cg_gen_fv_elem_size cg_if.hyps 
      cg_ctx_length by metis
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"
    using i_in_e1e2e3 by blast
  then show ?case
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
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
    using cg_iop.prems by auto
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using i_in_e1e2 by blast
  then show ?case
  proof cases
    case i_in_e1
    have "snd (G2 ! i) \<le> snd (G3 ! i)"      
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_iop.hyps
      by metis
    then show ?thesis
      using cg_iop.hyps i_in_e1 by fastforce
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_iop.hyps
      by metis
    then show ?thesis
      using cg_iop.hyps i_in_e2 by fastforce
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
    using cg_cop.prems by auto
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using i_in_e1e2 by blast
  then show ?case
  proof cases
    case i_in_e1
    have "snd (G2 ! i) \<le> snd (G3 ! i)" 
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_cop.hyps
      by metis
    then show ?thesis
      using i_in_e1 cg_cop.hyps by force
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"      
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_cop.hyps
      by metis
    then show ?thesis
      using i_in_e2 cg_cop.hyps by force    
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  have i_in_e1e2: "i \<in> fv e1 \<or> i \<in> fv e2"
    using cg_bop.prems by auto
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using i_in_e1e2 by blast
  then show ?case
  proof cases
    case i_in_e1
    have "snd (G2 ! i) \<le> snd (G3 ! i)"      
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_bop.hyps
      by metis
    then show ?thesis
      using i_in_e1 cg_bop.hyps by force
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"      
      using i_in_e1e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_bop.hyps
      by metis
    then show ?thesis
      using i_in_e2 cg_bop.hyps by force
  qed
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  have i_in_e1e2e3: "i \<in> fv e1 \<or> i \<in> fv' (Suc 0) e2 \<or> i \<in> fv' (Suc 0) e3"
    using cg_case.prems by fastforce
  have snd_G1_le_G2: "snd (G1 ! i) \<le> snd (G2 ! i)"
    using i_in_e1e2e3 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_case.hyps
    by (metis i_fv'_suc_iff_suc_i_fv' length_Cons not_less_eq)
  have snd_G2_le_G3: "snd (G2 ! i) \<le> snd (G3 ! i)"
    using i_in_e1e2e3 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_case
      i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq length_Cons nth_Cons_Suc)
  have snd_G3_le_G4: "snd (G3 ! i) \<le> snd (G4 ! i)"
    using i_in_e1e2e3 cg_gen_fv_elem_size cg_case.hyps cg_ctx_length alg_ctx_jn_type_checked_nondec1 
      cg_case.hyps i_fv'_suc_iff_suc_i_fv'
    by (metis Suc_le_lessD length_Cons less_Suc_eq_le old.nat.inject)
  have snd_G3'_le_G4: "snd (G3' ! i) \<le> snd (G4 ! i)"
    using i_in_e1e2e3 cg_gen_fv_elem_size cg_case.hyps cg_ctx_length alg_ctx_jn_type_checked_nondec2 
      cg_case.hyps i_fv'_suc_iff_suc_i_fv'
    by (metis Suc_le_lessD length_Cons less_Suc_eq_le old.nat.inject)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
    using i_in_e1e2e3 by blast
  then show ?case
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
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using cg_irref.prems by fastforce
  then show ?case
  proof cases
    case i_in_e1
    then have "snd (G2 ! i) \<le> snd (G3 ! i)"
      using cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_irref.hyps
      by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    then show ?thesis
      using cg_irref.hyps i_in_e1 by force
  next
    case i_in_e2
    then have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_irref 
        i_fv'_suc_iff_suc_i_fv' by (metis length_Cons not_less_eq)
    then show ?thesis
      using cg_irref.hyps i_fv'_suc_iff_suc_i_fv' i_in_e2 by fastforce
  qed
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "Suc (Suc i) \<in> fv e2"
    using cg_take.prems i_fv'_suc_iff_suc_i_fv' fv'_take by blast
  then show ?case
  proof cases
    case i_in_e1
    have "i < length G2"
      using cg_gen_fv_elem_size cg_take i_in_e1 cg_ctx_length by force
    then have "snd (((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2) ! (Suc (Suc i))) \<le> 
               snd (((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, m) # (\<beta>, l) # G3) ! (Suc (Suc i)))"
      using cg_ctx_type_checked_nondec cg_take.hyps by fastforce
    then show ?thesis
      using i_in_e1 cg_take by force
  next
    case i_in_e2
    have "Suc (Suc i) < length ((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2)"
      using cg_gen_fv_elem_size cg_take i_in_e2 cg_ctx_length by meson
    then have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using cg_ctx_length cg_take cg_take cg_ctx_type_checked_nondec by force
    then show ?thesis
      using i_in_e2 cg_take by force
  qed
next
  case (cg_put \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau> C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_put.prems by fastforce
  then show ?case 
  proof cases
    case i_in_e1
    have "snd (G2 ! i) \<le> snd (G3 ! i)"
      using cg_put cg_ctx_type_checked_nondec i_in_e1 cg_gen_fv_elem_size cg_ctx_length by metis
    then show ?thesis
      using i_in_e1 cg_put by fastforce
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using cg_put cg_ctx_type_checked_nondec i_in_e2 cg_gen_fv_elem_size cg_ctx_length by metis
    then show ?thesis
      using i_in_e2 cg_put by force
  qed
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  obtain j where j_def: "i \<in> fv (es ! j)" "j < length nms"
    using cg_struct fv'_struct by (metis UN_E in_set_conv_nth)
  have "\<forall>k < length nms. i < length (Gs ! k)"
    using constant_fun_prop[where ?P="\<lambda>i. length (Gs ! i)" and ?n="length nms"]
      cg_struct cg_ctx_length j_def cg_gen_fv_elem_size by (metis Suc_leI)
  then have "\<forall>k < length nms. snd ((Gs ! k) ! i) \<le> snd ((Gs ! (Suc k)) ! i)"
    using cg_struct cg_ctx_type_checked_nondec by meson
  then have "snd ((Gs ! 0) ! i) \<le> snd ((Gs ! j) ! i)" 
            "snd ((Gs ! (Suc j)) ! i) \<le> snd ((Gs ! (length nms)) ! i)"
    using nondec_fun_prop[where ?P="\<lambda>a. snd ((Gs ! a) ! i)" and ?n="length nms"] j_def
    by fastforce+
  moreover have "snd ((Gs ! j) ! i) < snd ((Gs ! (Suc j)) ! i)"
    using cg_struct j_def by presburger
  ultimately have "snd ((Gs ! 0) ! i) < snd ((Gs ! (length nms)) ! i)"
    by linarith
  then show ?case
    using hd_conv_nth last_conv_nth cg_struct.hyps by (metis Zero_not_Suc diff_Suc_1 list.size(3))
qed simp+

lemma cg_gen_output_type_checked_nonzero:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
  shows "snd (G2 ! i) > 0"
  using assms cg_gen_output_type_checked_inc by fastforce

lemma cg_gen_output_type_checked_diff:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "i \<in> fv(e)"
  shows "snd (G2 ! i) \<noteq> snd (G1 ! i)"
  using assms cg_gen_output_type_checked_inc by fastforce

lemma cg_gen_type_checked_nonzero_imp_share:
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
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_app.prems fv'_app by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_app ct_sem_conjE by blast
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_ctx_length cg_gen_fv_elem_size
        cg_app by (metis neq0_conv not_le ct_sem_conjE)
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using cg_let.prems fv'_let by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis using 
        cg_let ct_sem_conj_iff by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        ct_sem_conjE i_fv'_suc_iff_suc_i_fv' cg_let
      by (metis Suc_less_eq gt_or_eq_0 leD length_Cons nth_Cons_Suc)
  qed
next
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  consider (i_in_e1) "i \<in> fv e1" "\<not>(ys ! i)" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using fv'_letb cg_letb.prems by force
  then show ?case
  proof cases
    case i_in_e1
    have i_size: "i < length G1"
      using cg_gen_fv_elem_size i_in_e1 cg_letb.hyps bang_cg_ctx_length by metis
    then show ?thesis
      using i_in_e1 cg_letb bang_cg_ctx_type_checked_same bang_cg_ctx_type_prop i_size
        ct_sem_conjE by metis
  next
    case i_in_e2
    have i_size: "i < length G2"
      using cg_letb.hyps cg_gen_fv_elem_size i_in_e2 i_fv'_suc_iff_suc_i_fv' set0_cg_ctx_length 
      by (metis Suc_less_eq length_Cons)
    show ?thesis
    proof (cases "ys ! i")
      case True
      have "i < length G1"
        using i_size cg_letb.hyps cg_ctx_length bang_cg_ctx_length by metis
      then show ?thesis
        using cg_letb True by force
    next
      case False
      have i_size2: "i < length (bang_cg_ctx ys G1)"
        using i_size cg_ctx_length cg_letb.hyps bang_cg_ctx_length by metis
      have "0 < snd (((\<alpha>, 0) # set0_cg_ctx ys G2) ! Suc i)"
      proof -
        have "0 < snd ((bang_cg_ctx ys G1) ! i)"
          using cg_letb.prems False bang_cg_ctx_type_checked_same i_size2 by simp
        then have "0 < snd ((bang_cg_ctx ys G2) ! i)"
          using cg_ctx_type_checked_nondec[where G="bang_cg_ctx ys G1"] cg_letb.hyps i_size2 by force
        then show ?thesis
          using False bang_cg_ctx_type_checked_same i_size set0_cg_ctx_type_checked_prop by simp
      qed
      moreover have "\<rho> = fst (((\<alpha>, 0) # set0_cg_ctx ys G2) ! Suc i)"
      proof -
        have "\<rho> = fst ((bang_cg_ctx ys G1) ! i)"
          using bang_cg_ctx_type_prop False i_size2 cg_letb.prems by presburger
        then show ?thesis
          using cg_letb bang_cg_ctx_type_prop False set0_cg_ctx_type_same i_size cg_ctx_type_same1 
            i_size2  by simp
      qed
      ultimately show ?thesis
        using i_in_e2 i_fv'_suc_iff_suc_i_fv' ct_sem_conjE cg_letb by metis
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"
    using cg_if.prems fv'_if by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE by (metis (no_types, lifting) gt_or_eq_0 leD)
  next
    case i_in_e3
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE by (metis (no_types, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_iop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_iop ct_sem_conjE by metis
  next
    case i_in_e2
    then show ?thesis
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_iop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_cop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_cop ct_sem_conjE by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_cop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_bop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_bop ct_sem_conjE by metis
  next
    case i_in_e2
    then show ?thesis
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_bop ct_sem_conjE by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_vcon \<alpha> n1 \<beta> n2 G1 e G2 C e' C' nm \<tau>)
  then show ?case
    using ct_sem_conjE fv'_con by blast
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
    using cg_case.prems by fastforce
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using ct_sem_conj_iff cg_case by presburger
  next
    case i_in_e2
    have "0 < snd (((\<beta>, 0) # G2) ! Suc i)"
      using cg_case i_in_e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
        i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
    moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
      using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e2 
        cg_ctx_type_same1
      by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
    ultimately show ?thesis
      using i_fv'_suc_iff_suc_i_fv' i_in_e2 cg_case ct_sem_conj_iff by metis
  next
    case i_in_e3
    have "0 < snd (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>), 0) # G2) ! Suc i)"
      using cg_case i_in_e3 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
        i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
    moreover have "\<rho> = fst (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>), 0) # G2) ! Suc i)"
      using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e3
        cg_ctx_type_same1
      by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
    ultimately show ?thesis
      using i_fv'_suc_iff_suc_i_fv' i_in_e3 cg_case ct_sem_conj_iff by metis
  qed
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using cg_irref.prems by fastforce
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using cg_irref ct_sem_conj_iff by metis
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_checked_nondec 
        cg_gen_fv_elem_size by (metis Suc_less_SucD length_Cons)
    moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
      using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_same1 
        cg_gen_fv_elem_size 
      by (metis Suc_eq_plus1 length_Cons less_SucE not_add_less1 nth_Cons_Suc)
    ultimately show ?thesis
      using gr_zeroI leD ct_sem_conj_iff cg_irref i_fv'_suc_iff_suc_i_fv' by fastforce
  qed
next
  case (cg_member \<alpha> n1 \<beta> G1 e nm \<tau> G2 n2 C e' C')
  then show ?case using ct_sem_conj_iff by force
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "Suc (Suc i) \<in> fv e2"
    using i_fv'_suc_iff_suc_i_fv' fv'_take cg_take.prems by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis using cg_take i_in_e1 ct_sem_conj_iff by metis
  next
    case i_in_e2
    have "0 < snd (((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2) ! (Suc (Suc i)))"
      using cg_take cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size i_in_e2
      by (metis Suc_less_SucD gr_zeroI leD length_Cons nth_Cons_Suc)
    moreover have "\<rho> = fst (((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2) ! (Suc (Suc i)))"
      using cg_ctx_type_same2 cg_gen_fv_elem_size cg_take i_in_e2
      by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    ultimately show ?thesis
      using cg_take i_in_e2 ct_sem_conj_iff by metis
  qed  
next
  case (cg_put \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau> C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_put.prems fv'_put by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis using cg_put ct_sem_conj_iff by metis
  next
    case i_in_e2
    have "0 < snd (G2 ! i)" 
      using cg_put cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size i_in_e2 
      by (metis gr_zeroI leD)
    moreover have "\<rho> = fst (G2 ! i)"
      using cg_ctx_type_same2 cg_gen_fv_elem_size cg_put i_in_e2 by meson
    ultimately show ?thesis
      using i_in_e2 cg_put ct_sem_conj_iff by metis
  qed
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  obtain j where j_def: "i \<in> fv (es ! j)" "j < length nms"
    using cg_struct fv'_struct by (metis UN_E in_set_conv_nth)
  have Gs_elem_length: "\<forall>k < length nms. i < length (Gs ! k)"
    using constant_fun_prop[where ?P="\<lambda>i. length (Gs ! i)" and ?n="length nms"]
      cg_struct cg_ctx_length j_def cg_gen_fv_elem_size by (metis Suc_leI)
  have "snd ((Gs ! 0) ! i) \<le> snd ((Gs ! j) ! i)"
    using cg_struct j_def cg_ctx_type_checked_nondec Gs_elem_length
    by (rule_tac nondec_fun_prop[where ?P="\<lambda>j. snd ((Gs ! j) ! i)" and ?n="length nms"]; auto)
  moreover have "fst ((Gs ! 0) ! i) = fst ((Gs ! j) ! i)"
    using Gs_elem_length cg_ctx_type_same1 cg_struct j_def
    by (rule_tac constant_fun_prop[where ?P="\<lambda>j. fst ((Gs ! j) ! i)" and ?n="length nms"]; auto)
  moreover have "A \<turnstile> (Cs ! j)"
    using j_def ct_sem_conj_fold cg_struct ct_sem_conj_iff by metis
  ultimately show ?case
    using cg_struct j_def dual_order.strict_trans1 hd_conv_nth less_Suc_eq_0_disj
    by (metis (no_types, lifting) less_numeral_extra(3) list.size(3))
qed simp+

lemma cg_gen_output_type_unchecked_same:
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
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  have i_size: "i < length G2"
    using cg_letb cg_ctx_length bang_cg_ctx_length by metis
  consider (i_in_e1) "i \<in> fv e1" "Suc i \<notin> fv e2" "ys ! i" | (i_in_neither) "i \<notin> fv e1" "Suc i \<notin> fv e2"
    using cg_letb.prems fv'_letb i_fv'_suc_iff_suc_i_fv' by fastforce 
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using cg_letb i_size set0_cg_ctx_length set0_cg_ctx_type_checked_prop by fastforce
  next
    case i_in_neither
    then show ?thesis
      using i_size bang_cg_ctx_length cg_letb i_in_neither set0_cg_ctx_length 
        set0_cg_ctx_type_checked_prop bang_cg_ctx_type_checked_same by fastforce
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  then show ?case     
    using alg_ctx_jn_type_checked_max cg_ctx_idx_size by simp
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  then show ?case
  proof -
    have "i \<notin> fv e1" "(Suc i) \<notin> fv e2" "(Suc i) \<notin> fv e3"
      using i_fv'_suc_iff_suc_i_fv' cg_case by auto
    then moreover have "snd (G1 ! i) = snd (G3 ! i) \<and> snd (G3 ! i) = snd (G3' ! i) \<and> i < length G3"
      using cg_case cg_ctx_length nth_Cons_Suc by (metis (no_types) Suc_less_eq length_Cons)+
    ultimately show ?thesis
      using alg_ctx_jn_length alg_ctx_jn_type_checked_same cg_case.hyps by auto
  qed
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  then show ?case
    using cg_ctx_length i_fv'_suc_iff_suc_i_fv' by fastforce
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  have "i \<notin> fv e1" "Suc (Suc i) \<notin> fv e2"
    using cg_take.prems fv'_take by (simp add: i_fv'_suc_iff_suc_i_fv')+
  then show ?case
    using cg_ctx_length cg_take length_Cons fv'_take by fastforce
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  have "\<forall>j < length nms. length (Gs ! 0) = length (Gs ! j)"
    using constant_fun_prop[where ?P="\<lambda>j. length (Gs ! j)" and ?n="length nms"] cg_ctx_length 
      cg_struct by (metis Nat.add_0_right le_add1 less_imp_add_positive nat_add_left_cancel_le)
  then have "\<forall>j < length nms. i < length (Gs ! j)"
    using cg_struct by (metis Zero_not_Suc hd_conv_nth list.size(3))
  moreover have "\<forall>j < length nms. i \<notin> fv (es ! j)" 
    using cg_struct fv'_struct by auto
  ultimately have "snd ((Gs ! 0) ! i) = snd ((Gs ! (length nms)) ! i)"
    by (rule_tac constant_fun_prop[where ?P="\<lambda>j. snd ((Gs ! j) ! i)" and ?n="length nms"]; 
        simp add: cg_struct)
  then show ?case
    using cg_struct.hyps by (metis Zero_not_Suc diff_Suc_1 hd_conv_nth last_conv_nth list.size(3))
qed (simp add: cg_ctx_idx_size)+ 

lemma cg_assign_type_checked_nonzero_imp_share:
  assumes "G1,n1 \<turnstile> e : \<tau> \<leadsto> G2,n2 | C1 | e1'"
      and "i \<in> fv(e)"
      and "snd (G1 ! i) > 0"
      and "\<rho> = fst (G1 ! i)"
      and "A \<turnstile> assign_app_constr S C1"
      and "known_assignment S"
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
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using fv'_app cg_app.prems by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_app ct_sem_conjE  by (simp, blast)
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_ctx_length cg_gen_fv_elem_size
        cg_app assign_app_constr.simps by (metis (no_types, lifting) gt_or_eq_0 leD ct_sem_conjE)
  qed
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using fv'_let cg_let.prems by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using cg_let ct_sem_conj_iff assign_app_constr.simps by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        ct_sem_conjE i_fv'_suc_iff_suc_i_fv' cg_let assign_app_constr.simps
      by (metis (no_types, lifting) Suc_less_eq gr0I leD length_Cons nth_Cons_Suc)
  qed
next
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  consider (i_in_e1) "i \<in> fv e1" "\<not>(ys ! i)" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using fv'_letb cg_letb.prems by force
  then show ?case
  proof cases
    case i_in_e1
    have i_size: "i < length G1"
      using cg_gen_fv_elem_size i_in_e1 cg_letb.hyps bang_cg_ctx_length by metis
    have "A \<turnstile> assign_app_constr S C1"
      using cg_letb ct_sem_conj_iff assign_app_constr.simps by force
    then show ?thesis
      using i_in_e1 cg_letb bang_cg_ctx_type_checked_same bang_cg_ctx_type_prop i_size by metis
  next
    case i_in_e2
    have i_size: "i < length G2"
      using cg_letb.hyps cg_gen_fv_elem_size i_in_e2 i_fv'_suc_iff_suc_i_fv' set0_cg_ctx_length 
      by (metis Suc_less_eq length_Cons)
    show ?thesis
    proof (cases "ys ! i")
      case True
      have "i < length G1"
        using i_size cg_letb.hyps cg_ctx_length bang_cg_ctx_length by metis
      then show ?thesis
        using cg_letb True by force
    next
      case False
      have i_size2: "i < length (bang_cg_ctx ys G1)"
        using i_size cg_ctx_length cg_letb.hyps bang_cg_ctx_length by metis
      have "0 < snd (((\<alpha>, 0) # set0_cg_ctx ys G2) ! Suc i)"
      proof -
        have "0 < snd ((bang_cg_ctx ys G1) ! i)"
          using cg_letb.prems False bang_cg_ctx_type_checked_same i_size2 by simp
        then have "0 < snd ((bang_cg_ctx ys G2) ! i)"
          using cg_ctx_type_checked_nondec[where G="bang_cg_ctx ys G1"] cg_letb.hyps i_size2 by force
        then show ?thesis
          using False bang_cg_ctx_type_checked_same i_size set0_cg_ctx_type_checked_prop by simp
      qed
      moreover have "\<rho> = fst (((\<alpha>, 0) # set0_cg_ctx ys G2) ! Suc i)"
      proof -
        have "\<rho> = fst ((bang_cg_ctx ys G1) ! i)"
          using bang_cg_ctx_type_prop False i_size2 cg_letb.prems by presburger
        then show ?thesis
          using cg_letb bang_cg_ctx_type_prop False set0_cg_ctx_type_same i_size cg_ctx_type_same1 
            i_size2  by simp
      qed
      moreover have "A \<turnstile> assign_app_constr S C2"
        using cg_letb ct_sem_conj_iff assign_app_constr.simps by auto
      ultimately show ?thesis
        using i_in_e2 i_fv'_suc_iff_suc_i_fv' cg_letb by blast 
    qed
  qed
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2" | (i_in_e3) "i \<in> fv e3"  
    using fv'_if cg_if.prems by blast
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE assign_app_constr.simps by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE assign_app_constr.simps by (metis (no_types, lifting) leD not_gr_zero)
  next
    case i_in_e3
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_if ct_sem_conjE assign_app_constr.simps by (metis (no_types, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
    using cg_iop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_iop ct_sem_conjE assign_app_constr.simps by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_iop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
    using cg_cop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_cop ct_sem_conjE assign_app_constr.simps by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_cop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"  
    using cg_bop.prems fv'_prim by auto
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_bop ct_sem_conjE assign_app_constr.simps by metis
  next
    case i_in_e2
    then show ?thesis 
      using cg_ctx_length cg_ctx_type_same1 cg_ctx_type_checked_nondec cg_gen_fv_elem_size
        cg_bop ct_sem_conjE assign_app_constr.simps by (metis (mono_tags, lifting) gt_or_eq_0 leD)
  qed
next
  case (cg_vcon \<alpha> n1 \<beta> n2 G1 e G2 C e' C' nm \<tau>)
  then show ?case
    using ct_sem_conjE fv'_con assign_app_constr.simps by metis
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2" | (i_in_e3) "i \<in> fv' (Suc 0) e3"
    using cg_case.prems by fastforce
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using ct_sem_conj_iff cg_case assign_app_constr.simps by metis
  next
    case i_in_e2
    have "0 < snd (((\<beta>, 0) # G2) ! Suc i)"
      using cg_case i_in_e2 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
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
    have "0 < snd (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>), 0) # G2) ! Suc i)"
      using cg_case i_in_e3 cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size 
        i_fv'_suc_iff_suc_i_fv' by (metis Suc_less_eq  gr_zeroI leD length_Cons nth_Cons_Suc)
    moreover have "\<rho> = fst (((TVariant [(nm, \<beta>, Checked)] (Some \<alpha>), 0) # G2) ! Suc i)"
      using cg_case cg_ctx_length cg_gen_fv_elem_size i_fv'_suc_iff_suc_i_fv' i_in_e3
        cg_ctx_type_same1
      by (metis length_Cons less_SucE list.size(4) not_add_less1 nth_Cons_Suc)
    moreover have "A \<turnstile> assign_app_constr S C3"
      using cg_case ct_sem_conj_iff assign_app_constr.simps by metis
    ultimately show ?thesis
      using cg_case i_fv'_suc_iff_suc_i_fv' i_in_e3 by blast
  qed
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv' (Suc 0) e2"
    using cg_irref.prems by fastforce
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis
      using cg_irref ct_sem_conj_iff assign_app_constr.simps by metis
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_checked_nondec 
        cg_gen_fv_elem_size by (metis Suc_less_SucD length_Cons)
    moreover have "\<rho> = fst (((\<beta>, 0) # G2) ! Suc i)"
      using i_in_e2 cg_ctx_length cg_irref i_fv'_suc_iff_suc_i_fv' cg_ctx_type_same1 
        cg_gen_fv_elem_size 
      by (metis Suc_eq_plus1 length_Cons less_SucE not_add_less1 nth_Cons_Suc)
    ultimately show ?thesis
      using gr_zeroI leD ct_sem_conj_iff cg_irref i_fv'_suc_iff_suc_i_fv' by fastforce
  qed
next
  case (cg_member \<alpha> n1 \<beta> G1 e nm \<tau> G2 n2 C e' C')
  then show ?case using ct_sem_conj_iff by simp
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "Suc (Suc i) \<in> fv e2"
    using cg_take.prems i_fv'_suc_iff_suc_i_fv' fv'_take by blast 
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis using ct_sem_conj_iff cg_take by force
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_take i_in_e2
      by (metis Suc_less_SucD length_Cons)
    moreover have "\<rho> = fst (((TRecord [(nm, \<beta>, Taken)] \<alpha> \<gamma>, 0) # (\<beta>, 0) # G2) ! (Suc (Suc i)))"
      using cg_ctx_type_same2 cg_gen_fv_elem_size cg_take i_in_e2
      by (metis Suc_less_eq length_Cons nth_Cons_Suc)
    ultimately show ?thesis
      using ct_sem_conj_iff cg_take i_in_e2 by fastforce
  qed
next
  case (cg_put \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau> C4 C5)
  consider (i_in_e1) "i \<in> fv e1" | (i_in_e2) "i \<in> fv e2"
    using cg_put.prems i_fv'_suc_iff_suc_i_fv' fv'_put by blast 
  then show ?case
  proof cases
    case i_in_e1
    then show ?thesis using ct_sem_conj_iff cg_put by force
  next
    case i_in_e2
    have "snd (G1 ! i) \<le> snd (G2 ! i)"
      using cg_ctx_length cg_ctx_type_checked_nondec cg_gen_fv_elem_size cg_put i_in_e2 by metis
    then show ?thesis
      using ct_sem_conj_iff cg_put i_in_e2 cg_ctx_type_same2 cg_gen_fv_elem_size by force
  qed
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  obtain j where j_def: "i \<in> fv (es ! j)" "j < length nms"
    using cg_struct fv'_struct by (metis UN_E in_set_conv_nth)
  have Gs_elem_length: "\<forall>k < length nms. i < length (Gs ! k)"
    using constant_fun_prop[where ?P="\<lambda>i. length (Gs ! i)" and ?n="length nms"]
      cg_struct cg_ctx_length j_def cg_gen_fv_elem_size by (metis Suc_leI)
  have "snd ((Gs ! 0) ! i) \<le> snd ((Gs ! j) ! i)"
    using cg_struct j_def cg_ctx_type_checked_nondec Gs_elem_length
    by (rule_tac nondec_fun_prop[where ?P="\<lambda>j. snd ((Gs ! j) ! i)" and ?n="length nms"]; auto)
  moreover have "fst ((Gs ! 0) ! i) = fst ((Gs ! j) ! i)"
    using Gs_elem_length cg_ctx_type_same1 cg_struct j_def
    by (rule_tac constant_fun_prop[where ?P="\<lambda>j. fst ((Gs ! j) ! i)" and ?n="length nms"]; auto)
  moreover have "A \<turnstile> assign_app_constr S (Cs ! j)"
    using j_def ct_sem_assign_conj_foldr cg_struct ct_sem_conj_iff by simp
  ultimately show ?case
    using j_def cg_struct hd_conv_nth less_Suc_eq_0_disj less_le_trans 
    by (metis (no_types, lifting) less_numeral_extra(3) list.size(3))
qed simp+

lemma split_unionR':
  assumes "ns = ns1 \<union> ns2"
    and "\<And>i. i < length G1 \<Longrightarrow> fst (G1 ! i) = fst (G2 ! i)"
    and "A \<turnstile> assign_app_ctx S (G1\<bar>ns) \<leadsto> assign_app_ctx S (G1\<bar>ns1) \<box> assign_app_ctx S (G2\<bar>ns2)"
    and "\<forall>i\<in>I. i < length G1 \<and> i \<notin> ns"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(ns \<union> I)) \<leadsto> assign_app_ctx S (G1\<bar>ns1) \<box> assign_app_ctx S (G2\<bar>ns2 \<union> I)"
  using assms
proof -
  let ?SG1ns = "assign_app_ctx S (G1\<bar>ns)"
  let ?SG1nS = "assign_app_ctx S (G1\<bar>(ns \<union> I))"
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
    moreover have "(?SG1ns ! j) = (?SG1nS ! j)"
      using j_size j_not_in_I assign_app_ctx_len assign_app_ctx_nth assms context_splitting_def 
        ctx_restrict_len ctx_restrict_un_elem_same by (metis (full_types))
    ultimately have "ctx_split_comp A (?SG1nS ! j) (?SG1ns1 ! j) (?SG2ns2' ! j)"
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
    then have "?SG1nS ! i =  ?SG2ns2' ! i"
      using i_in_I assign_app_ctx_len assign_app_ctx_nth assms context_splitting_def 
        ctx_restrict_len by (metis list_all3_conv_all_nth)
    then have "ctx_split_comp A (?SG1nS ! i) (?SG1ns1 ! i) (?SG2ns2' ! i)"
      using SG1ns1_none ctx_split_comp.simps by auto
  }
  ultimately show ?thesis
    using assign_app_ctx_len assms context_splitting_def ctx_restrict_len 
    by (metis (full_types) list_all3_conv_all_nth)
qed

lemma split_unionR:
  assumes "ns = ns1 \<union> ns2"
    and "\<And>i. i < length G1 \<Longrightarrow> fst (G1 ! i) = fst (G2 ! i)"
    and "A \<turnstile> assign_app_ctx S (G1\<bar>ns) \<leadsto> assign_app_ctx S (G1\<bar>ns1) \<box> assign_app_ctx S (G2\<bar>ns2)"
    and "\<forall>i\<in>I. i < length G1 \<and> i \<notin> ns"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>ns1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>ns2 \<union> I)"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(ns \<union> I)) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms split_unionR' by simp

section {* Lemma 3.1 *}
lemma split_checked:
  assumes "fv e = (fv e1) \<union> (fv e2)"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<rho> \<leadsto> G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>(fv e2))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2 = "assign_app_ctx S (G2\<bar>(fv e2))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  moreover {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e2_SG2e2_none: "i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e2_SG2e2_some: "i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    consider (i_in_e) "i \<in> fv e" | (i_not_in_e) "i \<notin> fv e"
      by blast
    then have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof cases
      case i_in_e
      consider (case_1) "i \<in> fv e1" "i \<notin> fv e2" | (case_2) "i \<notin> fv e1" "i \<in> fv e2"
        |   (case_3) "i \<in> fv e1" "i \<in> fv e2"
        using assms i_in_e by blast
      then show ?thesis
      proof cases
        case case_1
        then show ?thesis
          using ctx_split_left i_in_e i_size no_i_in_e2_SG2e2_none ctx_restrict_len 
            ctx_restrict_nth_some assign_app_ctx_def by auto
      next
        case case_2
        then show ?thesis
          using assms cg_ctx_type_same1 i_in_e i_in_e2_SG2e2_some i_in_e_SG1e_some i_size
            no_i_in_e1_SG1e1_none ctx_split_right by auto
      next
        case case_3
        have i_type_checked: "snd (G2!i) > 0"
          using cg_gen_output_type_checked_nonzero assms case_3 by auto
        then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2!i)))"
          using assms case_3 cg_assign_type_checked_nonzero_imp_share by simp
        moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
          using i_in_e case_3 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
        moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
          using assms assign_app_ctx_def case_3 i_size G1_G2_length cg_ctx_type_same1 
            ctx_restrict_len ctx_restrict_nth_some by simp
        ultimately show ?thesis 
          using G1_G2_length case_3 i_size ctx_restrict_len ctx_restrict_nth_some ctx_split_share 
            assign_app_ctx_def by auto
      qed
    next
      case i_not_in_e
      have "(i \<notin> (fv e1)) \<and> (i \<notin> (fv e2))"
        using assms i_not_in_e by simp
      then show ?thesis
        using ctx_split_none i_not_in_e i_size no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2_none 
          no_i_in_e_SG1e_none by auto
    qed
  }
  ultimately show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed

lemma split_checked_let:
  assumes "e = Let e1 e2"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "((\<tau>,m) # G2),n2 \<turnstile> e2 : \<rho> \<leadsto> ((\<tau>,m') # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>image (\<lambda>x. x-1) (fv e2 - {0}))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?SG2e2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2)"
  have fv_e: "fv e = fv e1 \<union> (image (\<lambda>x. x-1) (fv e2 - {0}))"
    using assms fv'_suc_eq_dec_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  moreover {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e2_SG2e2_none: "Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
    proof -
      have "Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
        using fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' by blast
      then show "Suc i \<notin> fv e2 \<Longrightarrow> ?SG2e2 ! i = None"
        using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    qed
    have i_in_e2_SG2e2_some: "Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
    proof -
      have "Suc i \<notin> fv e2 \<Longrightarrow> i \<notin> (image (\<lambda>x. x-1) (fv e2 - {0}))"
        using fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' by blast
      then show "Suc i \<in> fv e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G2!i)))"
        by (metis G1_G2_length assign_app_ctx_restrict_some fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_size)
    qed
    consider (i_in_e) "i \<in> fv e" | (i_not_in_e) "i \<notin> fv e"
      by blast
    then have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof cases
      case i_in_e
      consider (case_1) "i \<in> fv e1" "i \<notin> ?dec_fv_e2" | (case_2) "i \<notin> fv e1" "i \<in> ?dec_fv_e2" 
             | (case_3) "i \<in> fv e1" "i \<in> ?dec_fv_e2"
        using assms i_in_e fv_e by blast
      then show ?thesis
      proof cases
        case case_1
        then show ?thesis
          using ctx_split_left fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_in_e i_size 
            no_i_in_e2_SG2e2_none i_in_e1_SG1e1_some i_in_e_SG1e_some by metis
      next
        case case_2
        then show ?thesis
          using assms G1_G2_length assign_app_ctx_restrict_some cg_ctx_type_same1 i_in_e i_size 
            no_i_in_e1_SG1e1_none ctx_split_right by metis
      next
        case case_3
        have i_type_checked: "snd (G2 ! i) > 0"
          using cg_gen_output_type_checked_nonzero assms case_3 by auto
        then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2!i)))"
          using assms case_3 cg_assign_type_checked_nonzero_imp_share
          by (metis fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' nth_Cons_Suc)
        moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
          using i_in_e case_3 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def by auto
        moreover have "(?SG1e1 ! i) = (?SG2e2 ! i)"
          using assms assign_app_ctx_def case_3 i_size G1_G2_length cg_ctx_type_same1 
            ctx_restrict_len ctx_restrict_nth_some by simp
        ultimately show ?thesis 
          using G1_G2_length case_3 i_in_e i_size ctx_restrict_len ctx_restrict_nth_some 
            ctx_split_share assign_app_ctx_def by auto
      qed
    next
      case i_not_in_e
      have "(i \<notin> (fv e1)) \<and> (i \<notin> ?dec_fv_e2)"
        using fv_e i_not_in_e by auto
      then show ?thesis
        using ctx_split_none fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_not_in_e i_size 
          no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2_none no_i_in_e_SG1e_none by metis
    qed
  }
  ultimately show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed

lemma split_checked_letb:
  assumes "e = LetBang ys e1 e2"
    and "(bang_cg_ctx ys G1),(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> (bang_cg_ctx ys G2),n2 | C1 | e1'"
    and "((\<alpha>, 0) # (set0_cg_ctx ys G2)),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> assign_app_ctx S (G1\<bar>fv e1 - {y. ys ! y}) \<box> assign_app_ctx S (G2\<bar>image (\<lambda>x. x-1) (fv e2 - {0}))"
  using assms
proof -
  let ?\<Gamma> = "assign_app_ctx S (G1\<bar>fv e)"
  let ?fv_e1_no_y = "fv e1 - {y. ys ! y}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>?fv_e1_no_y)"
  let ?dec_fv_e2 = "(\<lambda>x. x-1) ` (fv e2 - {0})"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2)"
  have fv_e: "fv e = (fv e1 - {y. ys ! y}) \<union> ((\<lambda>x. x-1) ` (fv e2 - {0}))"
    using assms fv'_suc_eq_dec_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length set0_cg_ctx_length bang_cg_ctx_length by metis
  moreover {
    fix i :: nat
    assume i_size: "i < length G1"
    have \<Gamma>_none: "i \<notin> fv e \<Longrightarrow> ?\<Gamma> ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>_some: "i \<in> fv e \<Longrightarrow> ?\<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have \<Gamma>1_none: "i \<notin> ?fv_e1_no_y \<Longrightarrow> ?\<Gamma>1 ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>1_some: "i \<in> ?fv_e1_no_y \<Longrightarrow> ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have \<Gamma>2_none: "i \<notin> ?dec_fv_e2 \<Longrightarrow> ?\<Gamma>2 ! i = None"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>2_some: "i \<in> ?dec_fv_e2 \<Longrightarrow> ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i)))"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have "ctx_split_comp A (?\<Gamma> ! i) (?\<Gamma>1 ! i) (?\<Gamma>2 ! i)"
    proof (cases "i \<in> fv e")
      case True
      consider (case_1) "i \<in> ?fv_e1_no_y" "i \<notin> ?dec_fv_e2" 
             | (case_2) "i \<notin> ?fv_e1_no_y" "i \<in> ?dec_fv_e2" 
             | (case_3) "i \<in> ?fv_e1_no_y" "i \<in> ?dec_fv_e2" 
        using assms True fv_e by blast
      then show ?thesis
      proof cases
        case case_1
        then show ?thesis
          using \<Gamma>_some \<Gamma>1_some \<Gamma>2_none ctx_split_left True by presburger
      next
        case case_2
        have "fst (bang_cg_ctx ys G1 ! i) = fst (bang_cg_ctx ys G2 ! i)"
          using assms cg_ctx_type_same1 i_size bang_cg_ctx_length by simp
        then show ?thesis
          using \<Gamma>_some \<Gamma>1_none \<Gamma>2_some ctx_split_right True assms case_2 bang_cg_ctx_type_prop 
            G1_G2_length i_size type.inject by metis
      next
        case case_3
        have "snd (G2 ! i) > 0"
          using cg_gen_output_type_checked_nonzero assms case_3 bang_cg_ctx_type_checked_same i_size 
            bang_cg_ctx_length cg_ctx_length by (metis DiffE)
        then moreover have "A \<turnstile> CtShare (assign_app_ty S (fst (G2!i)))"
          using G1_G2_length assms case_3 fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_size
            set0_cg_ctx_type_same set0_cg_ctx_type_checked_prop cg_assign_type_checked_nonzero_imp_share
          by (metis DiffE mem_Collect_eq nth_Cons_Suc)
        moreover have "fst (G1 ! i) = fst (G2 ! i)"
          using assms bang_cg_ctx_length bang_cg_ctx_type_prop case_3 i_size cg_ctx_length 
            cg_ctx_type_same2 by (metis (no_types, lifting) DiffE mem_Collect_eq)
        ultimately show ?thesis
          using True \<Gamma>1_some \<Gamma>2_some \<Gamma>_some case_3 ctx_split_share by auto
      qed
    next
      case False
      then show ?thesis
        using fv_e \<Gamma>_none \<Gamma>1_none \<Gamma>2_none ctx_split_none by force
    qed
  }
  ultimately show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (clarsimp simp add: list_all3_conv_all_nth) 
qed

lemma split_checked_if:
  assumes "e = If e1 e2 e3"
    and "G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'"
    and "G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "known_assignment S"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
  using assms   
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2e3 = "assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  moreover {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1!i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have no_i_in_e2_SG2e2e3_none: "i \<notin> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = None"
      using G1_G2_length assign_app_ctx_nth ctx_restrict_len ctx_restrict_nth_none i_size
        assign_app_ctx_none_iff by metis
    have i_in_e2_SG2e2_some: "i \<in> fv e2 \<union> fv e3 \<Longrightarrow> ?SG2e2e3 ! i = Some (assign_app_ty S (fst (G2!i)))"
      using i_size G1_G2_length assign_app_ctx_restrict_some by metis
    consider (i_in_e) "i \<in> fv e" | (i_not_in_e) "i \<notin> fv e"
      by blast
    then have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof cases
      case i_in_e
      consider (case_1) "i \<in> fv e1" "i \<notin> fv e2 \<union> fv e3" 
        | (case_2) "i \<notin> fv e1" "i \<in> fv e2 \<union> fv e3"
        | (case_3) "i \<in> fv e1" "i \<in> fv e2 \<union> fv e3"
        using assms i_in_e by fastforce
      then show ?thesis
      proof cases
        case case_1
        then show ?thesis
          using ctx_split_left i_in_e i_size no_i_in_e2_SG2e2e3_none ctx_restrict_len 
            ctx_restrict_nth_some assign_app_ctx_def by auto
      next
        case case_2
        then show ?thesis
          using assign_app_ctx_restrict_some assms i_in_e i_in_e2_SG2e2_some i_size
            no_i_in_e1_SG1e1_none cg_ctx_type_same1 ctx_split_right by auto
      next
        case case_3
        have i_type_checked: "snd (G2 ! i) > 0"
          using cg_gen_output_type_checked_nonzero assms case_3 by auto
        then have i_type_share: "A \<turnstile> CtShare (assign_app_ty S (fst (G2 ! i)))"
          using assms case_3 cg_assign_type_checked_nonzero_imp_share by blast
        moreover have "(?SG1e ! i) = (?SG1e1 ! i)"
          using i_in_e case_3 i_size ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def
          by auto
        moreover have "(?SG1e1 ! i) = (?SG2e2e3 ! i)"
          using assms assign_app_ctx_def case_3 i_size G1_G2_length cg_ctx_type_same1 
            ctx_restrict_len ctx_restrict_nth_some by simp
        ultimately show ?thesis
          using G1_G2_length case_3 i_size ctx_restrict_len ctx_restrict_nth_some ctx_split_share 
            i_in_e2_SG2e2_some by auto
      qed
    next
      case i_not_in_e
      have "(i \<notin> fv e1) \<and> (i \<notin> fv e2 \<union> fv e3)"
        using assms i_not_in_e by simp
      then show ?thesis 
        using ctx_split_none i_not_in_e i_size no_i_in_e1_SG1e1_none no_i_in_e2_SG2e2e3_none 
          no_i_in_e_SG1e_none by auto
    qed
  }
  ultimately show ?thesis
    using G1_G2_length context_splitting_def assign_app_ctx_len ctx_restrict_len
    by (metis (full_types) list_all3_conv_all_nth)
qed 

lemma split_checked_case:
  assumes "e = Case e1 nm e2 e3"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "((\<gamma>, 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> ((\<gamma>, l) # G3'),n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "known_assignment S"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "dec_fv_e3 = image (\<lambda>x. x-1) (fv e3 - {0})"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> dec_fv_e3)"
  using assms 
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2e3 = "assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> dec_fv_e3)"
  have fv_e: "fv e = fv e1 \<union> dec_fv_e2 \<union> dec_fv_e3"
    using assms fv'_suc_eq_dec_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms by (rule_tac cg_ctx_length; simp)
  {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by blast
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by blast 
    have no_i_in_e2e3_SG2e2e3_none: "i \<notin> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?SG2e2e3 ! i = None"
      using G1_G2_length assign_app_ctx_restrict_none i_size by auto
    have i_in_e2e3_SG2e2e3_some: "i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?SG2e2e3 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using G1_G2_length assign_app_ctx_restrict_some i_size cg_ctx_type_same1 assms by auto
    have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2e3 ! i)"
    proof (cases "i \<in> fv e")
      case True
      have "i \<in> fv e1 \<or> i \<in> dec_fv_e2 \<union> dec_fv_e3"
        using True fv_e by auto
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<notin> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
        using ctx_split_left True i_in_e_SG1e_some i_in_e1_SG1e1_some no_i_in_e2e3_SG2e2e3_none 
          by auto
      moreover have "i \<notin> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
        using ctx_split_right True i_in_e_SG1e_some no_i_in_e1_SG1e1_none i_in_e2e3_SG2e2e3_some 
          by presburger
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<union> dec_fv_e3 \<Longrightarrow> ?thesis"
      proof -
        assume i_in_e1: "i \<in> fv e1"
        assume i_in_e2e3: "i \<in> dec_fv_e2 \<union> dec_fv_e3"
        have "A \<turnstile> CtShare (assign_app_ty S (fst (G1 ! i)))"
        proof -
          have i_type_checked: "snd (G2 ! i) > 0"
            using cg_gen_output_type_checked_nonzero assms i_in_e1 by auto
          consider (suc_i_in_e2) "Suc i \<in> fv e2" | (suc_i_in_e3) "Suc i \<in> fv e3"
            using i_in_e2e3 fv'_suc_eq_dec_fv'  assms by fastforce
          then show ?thesis
          proof cases
            case suc_i_in_e2
            have "A \<turnstile> CtShare (assign_app_ty S (fst (((\<beta>, 0) # G2) ! Suc i)))"
              using assms suc_i_in_e2 cg_assign_type_checked_nonzero_imp_share i_type_checked 
                nth_Cons_Suc by metis
            then show ?thesis
              using G1_G2_length cg_ctx_type_same1 i_size assms by force
          next
            case suc_i_in_e3
            have "A \<turnstile> CtShare (assign_app_ty S (fst (((\<gamma>, 0) # G2) ! Suc i)))"
              using assms suc_i_in_e3 cg_assign_type_checked_nonzero_imp_share i_type_checked 
                nth_Cons_Suc by metis
            then show ?thesis
              using G1_G2_length cg_ctx_type_same1 i_size assms by force
          qed
        qed
        then show "?thesis"
          using ctx_split_share True i_in_e1 i_in_e2e3 i_in_e_SG1e_some i_in_e1_SG1e1_some 
            i_in_e2e3_SG2e2e3_some by presburger
      qed
      ultimately show ?thesis
        using True by argo
    next
      case False
      have "i \<notin> fv e1" "i \<notin> dec_fv_e2 \<union> dec_fv_e3"
        using fv_e False by blast+
      then show ?thesis
        using ctx_split_none False no_i_in_e2e3_SG2e2e3_none no_i_in_e1_SG1e1_none 
          no_i_in_e_SG1e_none by presburger
    qed
  }
  then show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len G1_G2_length assms
    by (simp add: list_all3_conv_all_nth)
      qed

lemma split_checked_irref:
  assumes "e = Esac e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>dec_fv_e2)"
  using assms 
proof -
  let ?SG1e = "assign_app_ctx S (G1\<bar>(fv e))"
  let ?SG1e1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?SG2e2 = "assign_app_ctx S (G2\<bar>dec_fv_e2)"
  have fv_e: "fv e = fv e1 \<union> dec_fv_e2"
    using assms fv'_suc_eq_dec_fv' by auto
  have G1_G2_length: "length G1 = length G2"
    using assms by (rule_tac cg_ctx_length; simp)
  {
    fix i :: nat
    assume i_size: "i < length G1"
    have no_i_in_e_SG1e_none: "i \<notin> fv e \<Longrightarrow> ?SG1e ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e_SG1e_some: "i \<in> fv e \<Longrightarrow> ?SG1e ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by blast
    have no_i_in_e1_SG1e1_none: "i \<notin> fv e1 \<Longrightarrow> ?SG1e1 ! i = None"
      using assign_app_ctx_restrict_none i_size by blast
    have i_in_e1_SG1e1_some: "i \<in> fv e1 \<Longrightarrow> ?SG1e1 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using assign_app_ctx_restrict_some i_size by blast
    have no_i_in_e2_SG2e2_none: "i \<notin> dec_fv_e2 \<Longrightarrow> ?SG2e2 ! i = None"
      using G1_G2_length assign_app_ctx_restrict_none i_size cg_ctx_type_same1 assms by metis
    have i_in_e2_SG2e2_some: "i \<in> dec_fv_e2 \<Longrightarrow> ?SG2e2 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using G1_G2_length assign_app_ctx_restrict_some i_size cg_ctx_type_same1 assms by metis
    have "ctx_split_comp A (?SG1e ! i) (?SG1e1 ! i) (?SG2e2 ! i)"
    proof (cases "i \<in> fv e")
      case True
      then have "i \<in> fv e1 \<or> i \<in> dec_fv_e2"
        using fv_e by simp
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<notin> dec_fv_e2 \<Longrightarrow> ?thesis"
        using ctx_split_left True i_in_e_SG1e_some i_in_e1_SG1e1_some no_i_in_e2_SG2e2_none 
          by presburger
      moreover have "i \<notin> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<Longrightarrow> ?thesis"
        using ctx_split_right True i_in_e_SG1e_some no_i_in_e1_SG1e1_none i_in_e2_SG2e2_some 
          by presburger
      moreover have "i \<in> fv e1 \<Longrightarrow> i \<in> dec_fv_e2 \<Longrightarrow> ?thesis"
      proof -
        assume i_in_e1: "i \<in> fv e1"
        assume i_in_e2: "i \<in> dec_fv_e2"
        have "A \<turnstile> CtShare (assign_app_ty S (fst (G1 ! i)))"
        proof -
          have i_type_checked: "snd (G2 ! i) > 0"
            using cg_gen_output_type_checked_nonzero assms i_in_e1 by auto
          then have "A \<turnstile> CtShare (assign_app_ty S (fst (((\<beta>, 0) # G2) ! Suc i)))"
            using assms fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_in_e2 
            cg_assign_type_checked_nonzero_imp_share nth_Cons_Suc by (metis nth_Cons_Suc)
          then show ?thesis
            using G1_G2_length cg_ctx_type_same1 i_size assms by force
        qed
        then show ?thesis
          using ctx_split_share True i_in_e1 i_in_e2 i_in_e_SG1e_some i_in_e1_SG1e1_some 
            i_in_e2_SG2e2_some by presburger
      qed
      ultimately show ?thesis
        by fast
    next
      case False
      then show ?thesis
        using ctx_split_none fv_e no_i_in_e2_SG2e2_none no_i_in_e1_SG1e1_none no_i_in_e_SG1e_none 
        by auto
    qed
  }
  then show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len G1_G2_length assms
    by (simp add: list_all3_conv_all_nth)
qed

lemma split_checked_take:
  assumes "e = Take e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # (\<gamma>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # (\<gamma>, l) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "dec2_fv_e2 = (\<lambda>x. x-1) ` (\<lambda>x. x-1) ` (fv e2 - {0, 1})"
  shows "A \<turnstile> assign_app_ctx S (G1\<bar>(fv e)) \<leadsto> assign_app_ctx S (G1\<bar>(fv e1)) \<box> assign_app_ctx S (G2\<bar>dec2_fv_e2)"
  using assms 
proof -
  let ?\<Gamma> = "assign_app_ctx S (G1\<bar>fv e)"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>(fv e1))"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>dec2_fv_e2)" 
  have fv_e: "fv e = (fv e1) \<union> ((\<lambda>x. x-1) ` (\<lambda>x. x-1) ` (fv e2 - {0,1}))"
    using assms fv'_suc_eq_dec_fv' fv'_suc_eq_dec_fv'_minus fv'_take
    by (metis One_nat_def image_empty image_insert insert_is_Un)
  have G1_G2_length: "length G1 = length G2"
    using assms cg_ctx_length by blast
  moreover {
    fix i :: nat
    assume i_size: "i < length G1"
    have \<Gamma>_none: "i \<notin> fv e \<Longrightarrow> ?\<Gamma> ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>_some: "i \<in> fv e \<Longrightarrow> ?\<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have \<Gamma>1_none: "i \<notin> fv e1 \<Longrightarrow> ?\<Gamma>1 ! i = None"
      using ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>1_some: "i \<in> fv e1 \<Longrightarrow> ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have \<Gamma>2_none: "i \<notin> dec2_fv_e2 \<Longrightarrow> ?\<Gamma>2 ! i = None"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_none assign_app_ctx_def i_size by auto
    have \<Gamma>2_some: "i \<in> dec2_fv_e2 \<Longrightarrow> ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i)))"
      using G1_G2_length ctx_restrict_len ctx_restrict_nth_some assign_app_ctx_def i_size by auto
    have "ctx_split_comp A (?\<Gamma> ! i) (?\<Gamma>1 ! i) (?\<Gamma>2 ! i)"
    proof (cases "i \<in> fv e")
      case True
      consider (i_in_e1) "i \<in> fv e1" "i \<notin> dec2_fv_e2" 
             | (i_in_e2) "i \<notin> fv e1" "i \<in> dec2_fv_e2" 
             | (i_in_both) "i \<in> fv e1" "i \<in> dec2_fv_e2"
        using assms True fv_e by blast
      then show ?thesis
      proof cases
        case i_in_e1
        then show ?thesis
          using \<Gamma>_some \<Gamma>1_some \<Gamma>2_none ctx_split_left True by presburger
      next
        case i_in_e2
        then show ?thesis
          using \<Gamma>_some \<Gamma>1_none \<Gamma>2_some ctx_split_right True assms cg_ctx_type_same1 i_size by auto
      next
        case i_in_both
        have "A \<turnstile> CtShare (assign_app_ty S (fst (G2 ! i)))"
        proof - 
          have "Suc (Suc i) \<in> fv e2"
            using i_in_both fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' fv'_suc_eq_dec_fv'_minus
              assms by (metis (no_types, lifting) One_nat_def image_empty image_insert insert_is_Un)
          moreover have "snd (((\<beta>, 0) # (\<gamma>, l) # G2) ! (Suc (Suc i))) > 0"
            using cg_gen_output_type_checked_nonzero assms i_in_both by auto
          ultimately show ?thesis
            using cg_assign_type_checked_nonzero_imp_share assms by (metis nth_Cons_Suc)
        qed
        then show ?thesis
          using \<Gamma>_some \<Gamma>1_some \<Gamma>2_some ctx_split_share True G1_G2_length assms i_in_both 
            cg_ctx_type_same2 i_size by auto
      qed
    next
      case False
      then show ?thesis
        using \<Gamma>_none \<Gamma>1_none \<Gamma>2_none ctx_split_none fv_e assms by auto
    qed
  }
  ultimately show ?thesis
    using context_splitting_def assign_app_ctx_len ctx_restrict_len assms
    by (clarsimp simp add: list_all3_conv_all_nth) 
qed

lemma split_checked_extR:
  assumes "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<rho> \<leadsto> G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>(fv e1))"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>(fv e2 \<union> idxs))""fv e = (fv e1) \<union> (fv e2)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>fv e2)"
    using split_checked assms by blast
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using assms by (rule_tac split_unionR; force intro: cg_ctx_type_same1)
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

lemma split_checked_let_extR:
  assumes "e = Let e1 e2"
    and "G1,n1 \<turnstile> e1 : \<tau> \<leadsto> G2,n2 | C1 | e1'"
    and "((\<tau>,m) # G2),n2 \<turnstile> e2 : \<rho> \<leadsto> ((\<tau>,m') # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>dec_fv_e2)"
    using split_checked_let assms by simp
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using assms fv'_suc_eq_dec_fv' by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
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

lemma split_checked_letb_extR:
  assumes "e = LetBang ys e1 e2"
    and "(bang_cg_ctx ys G1),(Suc n1) \<turnstile> e1 : \<alpha> \<leadsto> (bang_cg_ctx ys G2),n2 | C1 | e1'"
    and "((\<alpha>, 0) # (set0_cg_ctx ys G2)),n2 \<turnstile> e2 : \<tau> \<leadsto> ((\<alpha>, m) # G3),n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "dec_fv_e2 = (\<lambda>x. x-1) ` (fv e2 - {0})"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1 - {y. ys ! y})"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
proof - 
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  proof -
    have "\<forall>i < length G1. fst (G1 ! i) = fst (G2 ! i)"
      using assms cg_ctx_type_same1[where G="bang_cg_ctx ys G1" and G'="bang_cg_ctx ys G2"] 
        bang_cg_ctx_type_prop bang_cg_ctx_length cg_ctx_length type.inject
      by (metis (no_types, lifting))
    moreover have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>dec_fv_e2)"
      using split_checked_letb assms by simp
    moreover have "fv e1 - {y. ys ! y} \<union> fv' (Suc 0) e2 = fv e1 - {y. ys ! y} \<union> dec_fv_e2"
      using assms fv'_suc_eq_dec_fv' by metis
    ultimately show ?thesis
      using assms split_unionR by simp
  qed
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assms ctx_restrict_len assign_app_ctx_len by presburger
    moreover { 
      fix i :: nat
      assume i_size: "i < length G1"
      have "\<Gamma> ! i = assign_app_ctx S (G1\<bar>fv e \<union> idxs) ! i"
      proof (cases "i \<in> fv e")
        case True
        then show ?thesis
          using Un_iff assign_app_ctx_restrict_some assms i_size by (metis (no_types, lifting))
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
            using False assign_app_ctx_restrict_some assms i_size by (metis (no_types, lifting))
        qed
      qed
    }
    ultimately show ?thesis
      using assms by (rule_tac nth_equalityI; presburger)
  qed
  ultimately show ?thesis
    using assms by argo
qed

lemma split_checked_if_extR:
  assumes "e = If e1 e2 e3"
    and "G1,n1 \<turnstile> e1 : (TPrim Bool) \<leadsto> G2,n2 | C1 | e1'"
    and "G2,n2 \<turnstile> e2 : \<tau> \<leadsto> G3,n3 | C2 | e2'"
    and "G2,n3 \<turnstile> e3 : \<tau> \<leadsto> G3',n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3) \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>(fv e2 \<union> fv e3))"
    using split_checked_if assms by meson
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
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

lemma split_checked_case_extR:
  assumes "e = Case e1 nm e2 e3"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "((\<gamma>, 0) # G2),n3 \<turnstile> e3 : \<tau> \<leadsto> ((\<gamma>, l) # G3'),n4 | C3 | e3'"
    and "A \<turnstile> assign_app_constr S C2"
    and "A \<turnstile> assign_app_constr S C3"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "dec_fv_e3 = image (\<lambda>x. x-1) (fv e3 - {0})"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>(dec_fv_e2 \<union> dec_fv_e3) \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>(dec_fv_e2 \<union> dec_fv_e3))"
    using split_checked_case assms by meson
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using fv'_suc_eq_dec_fv' assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    moreover { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      consider (case_1) "i \<in> fv e" | (case_2) "i \<notin> fv e" "\<Gamma> ! i = None" 
             | (case_3) "i \<notin> fv e" "\<Gamma> ! i \<noteq> None"
        by fast
      then have "\<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
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

lemma split_checked_irref_extR:
  assumes "e = Esac e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec_fv_e2 = image (\<lambda>x. x-1) (fv e2 - {0})"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>dec_fv_e2 \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>dec_fv_e2)"
    using split_checked_irref assms by meson
  then have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using fv'_suc_eq_dec_fv' assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    moreover { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      consider (case_1) "i \<in> fv e" | (case_2) "i \<notin> fv e" "\<Gamma> ! i = None" 
             | (case_3) "i \<notin> fv e" "\<Gamma> ! i \<noteq> None"
        by fast
      then have "\<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
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

lemma split_checked_take_extR:
  assumes "e = Take e1 nm e2"
    and "G1,n1 \<turnstile> e1 : \<alpha> \<leadsto> G2,n2 | C1 | e1'"
    and "(\<beta>, 0) # (\<gamma>, 0) # G2,n2 \<turnstile> e2 : \<tau> \<leadsto> (\<beta>, m) # (\<gamma>, l) # G3,n3 | C2 | e2'"
    and "A \<turnstile> assign_app_constr S C2"
    and "known_assignment S"
    and "\<And>i. i < length G1 \<Longrightarrow>
            if i \<in> fv e
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
    and "length G1 = length \<Gamma>"
    and "idxs = Set.filter (\<lambda>x. x \<notin> fv e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
    and "dec2_fv_e2 = (\<lambda>x. x-1) ` (\<lambda>x. x-1) ` (fv e2 - {0, 1})"
    and "\<Gamma>1 = assign_app_ctx S (G1\<bar>fv e1)"
    and "\<Gamma>2 = assign_app_ctx S (G2\<bar>dec2_fv_e2 \<union> idxs)"
  shows "A \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
  using assms 
proof -
  have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e) \<leadsto> \<Gamma>1 \<box> assign_app_ctx S (G2\<bar>dec2_fv_e2)"
    using split_checked_take assms by meson
  moreover have "(\<lambda>x. x-1) ` (\<lambda>x. x-1) ` (fv e2 - {0, 1}) = fv' (Suc (Suc 0)) e2"
    using fv'_suc_eq_dec_fv' fv'_suc_eq_dec_fv'_minus 
    by (metis One_nat_def image_empty image_insert insert_is_Un)
  ultimately have "A \<turnstile> assign_app_ctx S (G1\<bar>fv e \<union> idxs) \<leadsto> \<Gamma>1 \<box> \<Gamma>2"
    using assms by (rule_tac split_unionR; auto intro: cg_ctx_type_same1)
  moreover have "\<Gamma> = assign_app_ctx S (G1\<bar>fv e \<union> idxs)"
  proof -
    have "length \<Gamma> = length (assign_app_ctx S (G1\<bar>fv e \<union> idxs))"
      using assign_app_ctx_len assms ctx_restrict_def by auto
    moreover { 
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      consider (case_1) "i \<in> fv e" | (case_2) "i \<notin> fv e" "\<Gamma> ! i = None" 
             | (case_3) "i \<notin> fv e" "\<Gamma> ! i \<noteq> None"
        by fast
      then have "\<Gamma> ! i = assign_app_ctx S (G1 \<bar> fv e \<union> idxs) ! i"
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
lemma cg_sound_induction:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "A \<turnstile> assign_app_constr S C" 
    and "known_assignment S"
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
  have "A \<ddagger> \<Gamma> \<turnstile> Var i : (assign_app_ty S \<rho>)"
  proof -
    have "A \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i (assign_app_ty S \<rho>)"
    proof -
      have "length \<Gamma> = length (singleton (length \<Gamma>) i (assign_app_ty S \<rho>))"
        by (simp add: singleton_len)
      moreover have "(\<And>ia. ia < length \<Gamma> \<Longrightarrow>
                   weakening_comp A (\<Gamma> ! ia) (singleton (length \<Gamma>) i (assign_app_ty S \<rho>) ! ia))"
      proof -
        {
          fix ia :: nat
          assume ia_size: "ia < length \<Gamma>"
          show "?thesis ia"
          proof (cases "ia = i")
            case True
            have "\<Gamma> ! i = Some (assign_app_ty S (fst (G ! i)))"
              using cg_var1.hyps cg_var1.prems by fastforce
            then show ?thesis
              using True cg_var1.hyps ia_size weak_keep singleton_some by auto
          next
            case False
            then show ?thesis 
              using ia_size cg_var1 singleton_none weakening_comp.simps by fastforce
          qed
        }
      qed
      ultimately show ?thesis
        using cg_var1.hyps cg_var1.prems weakening_def by (metis list_all2_all_nthI)
    qed
    then show ?thesis
      using cg_var1.prems cg_var1.hyps typing_var by auto
  qed
  moreover have "A \<turnstile> CtSub (assign_app_ty S \<rho>) (assign_app_ty S \<tau>)"
    using cg_var1.prems cg_var1.hyps ct_sem_conjE assign_app_constr.simps by metis
  ultimately show ?case
    using typing_sig by simp
next
  case (cg_var2 G i \<rho> n G' C \<tau>)
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
          using assign_app_constr.simps(8) calculation cg_var2.hyps cg_var2.prems diff_zero 
            weak_drop weak_none fv'_var by (metis leI less_nat_zero_code singletonD)
        ultimately show "\<And>ia. ia < length \<Gamma> \<Longrightarrow> ?thesis ia"
          using cg_var2.hyps weak_keep singleton_some by fastforce
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
  ultimately show ?case
    using typing_sig by simp
next
  case (cg_sig G1 n1 e \<tau>' G2 n2 C e' C' \<tau>)
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
  ultimately show ?case
    using typing_sig by simp
next
  case (cg_app \<alpha> n1 G1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  let ?e="App e1 e2"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_app 
  proof (rule_tac split_checked_extR)
    show "A \<turnstile> assign_app_constr S C2"
      using cg_app assign_app_constr.simps ct_sem_conjE by metis
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (App e1 e2) 
                                   then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_app by meson
  qed (blast intro!: fv'_app)+
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S (TFun \<alpha> \<tau>)"
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
  qed (force simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_def)+
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<alpha>"
    using cg_app
  proof (intro cg_app.hyps(5))
    fix i
    assume i_size: "i < length G2"
    show "if i \<in> fv e2
         then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) else ?\<Gamma>2 ! i = None \<or>
              ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
      using cg_app cg_ctx_type_same1 i_size ctx_restrict_def
      by (auto split: if_splits; clarsimp simp add: assign_app_ctx_nth; metis option.distinct(1) option.sel)
  qed (force simp add: ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len)+
  ultimately show ?case
    using typing_sig_refl typing_app by simp
next
  case (cg_let \<alpha> n1 G1 e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4)
  let ?e = "Let e1 e2"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_let 
  proof (rule_tac split_checked_let_extR)
    show "A \<turnstile> assign_app_constr S C2"
      using cg_let assign_app_constr.simps ct_sem_conjE by metis
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                   then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_let by meson
  qed blast+
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S \<alpha>"
    using cg_let
  proof (intro cg_let.hyps(3))
    fix i :: nat
    assume i_size: "i < length G1"
    show "if i \<in> fv e1 
        then ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) else ?\<Gamma>1 ! i = None \<or>
             ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
             A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
      using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by auto
  qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
  moreover have "A \<ddagger> Some ((fst S) n1) # ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_let
  proof (intro cg_let.hyps(5))
    fix i :: nat
    assume i_size: "i < length ((\<alpha>, 0) # G2)"
    show "if i \<in> fv e2
        then (Some ((fst S) n1) # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((\<alpha>, 0) # G2) ! i)))
        else (Some ((fst S) n1) # ?\<Gamma>2) ! i = None \<or>
             (Some ((fst S) n1) # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((\<alpha>, 0) # G2) ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (((\<alpha>, 0) # G2) ! i)))"
    proof (cases "i = 0")
      case True
      then show ?thesis
        using cg_let cg_gen_output_type_unchecked_same 
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
          then have "A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! (i - 1))))"
            by (meson atLeastLessThan_iff cg_let.prems dec_i_in_idxs member_filter)
          then have "A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! (i - 1))))"
            using cg_ctx_type_same1 cg_let.hyps dec_i_in_idxs by auto
        }
        ultimately show ?thesis
        using assign_app_ctx_restrict_some i_nonzero i_size 
        by (simp only: nth_Cons' i_nonzero; case_tac "i - 1 \<notin> ?idxs"; simp)
      qed
    qed
  qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
  ultimately show ?case
    using typing_sig_refl typing_let cg_let.hyps by simp
next
  case (cg_letb \<alpha> n1 G1 ys e1 G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5 C6 C7)
  let ?e = "LetBang ys e1 e2"
  let ?dec_fv_e2 = "(\<lambda>x. x-1) ` (fv e2 - {0})"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (bang_cg_ctx ys G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> minus_ctx ys ?\<Gamma>1 \<box> ?\<Gamma>2"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length (minus_ctx ys (assign_app_ctx S (bang_cg_ctx ys G1 \<bar> fv e1)))"
      have "minus_ctx ys (assign_app_ctx S (bang_cg_ctx ys G1 \<bar> fv e1)) ! i = 
            assign_app_ctx S (G1 \<bar> fv e1 - {y. ys ! y}) ! i"
      proof (cases "ys ! i")
        case True
        then show ?thesis
          using assign_app_ctx_len assign_app_ctx_restrict_none bang_cg_ctx_length ctx_restrict_len 
            i_size minus_ctx_length minus_ctx_prop_none by auto
      next
        case False
        then show ?thesis
          using assign_app_ctx_len assign_app_ctx_restrict_none assign_app_ctx_restrict_some 
            bang_cg_ctx_length bang_cg_ctx_type_prop ctx_restrict_len i_size minus_ctx_length
            minus_ctx_prop_some by (metis Diff_iff mem_Collect_eq minus_ctx_prop_some)
      qed
    }
    then have "minus_ctx ys (assign_app_ctx S (bang_cg_ctx ys G1 \<bar> fv e1)) = 
               assign_app_ctx S (G1 \<bar> fv e1 - {y. ys ! y})"
      using assign_app_ctx_len bang_cg_ctx_length ctx_restrict_len minus_ctx_length nth_equalityI 
      by metis
    moreover have "A \<turnstile> assign_app_constr S C2"
      using cg_letb ct_sem_conj_iff by fastforce
    moreover have "\<forall>i < length G1. if i \<in> fv' 0 (LetBang ys e1 e2) 
                    then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                    else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_letb by meson
    ultimately show ?thesis 
      by (rule_tac split_checked_letb_extR[where ?G1.0=G1]; blast intro: cg_letb)
  qed
  moreover have "\<forall>i<length ?\<Gamma>1. ?\<Gamma>1 ! i \<noteq> None \<and> ys ! i \<longrightarrow> (if ?\<Gamma>2 ! i = None 
                 then \<exists>t. ?\<Gamma>1 ! i = Some (TBang t) else ?\<Gamma>1 ! i = Some (TBang (the (?\<Gamma>2 ! i))))"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length ?\<Gamma>1"
      assume i_in_\<Gamma>1: "?\<Gamma>1 ! i \<noteq> None"
      assume i_in_ys: "ys ! i"
      have i_in_e1: "i \<in> fv e1"
        using i_in_\<Gamma>1 assign_app_ctx_len assign_app_ctx_restrict_none ctx_restrict_len i_size 
        by metis
      then have "?\<Gamma>1 ! i = Some (assign_app_ty S (fst (bang_cg_ctx ys G1 ! i)))"
        using assign_app_ctx_len assign_app_ctx_restrict_some ctx_restrict_len i_size by auto
      then have \<Gamma>1_i: "?\<Gamma>1 ! i = Some (TBang (assign_app_ty S (fst (G1 ! i))))"
        using assign_app_ctx_len bang_cg_ctx_type_prop ctx_restrict_len i_in_ys i_size by auto
      have "if ?\<Gamma>2 ! i = None then \<exists>t. ?\<Gamma>1 ! i = Some (TBang t) 
                              else ?\<Gamma>1 ! i = Some (TBang (the (?\<Gamma>2 ! i)))"
      proof (cases "?\<Gamma>2 ! i = None")
        case True
        then show ?thesis
          using \<Gamma>1_i by meson
      next
        case False
        have "?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i)))"
          using False assign_app_ctx_len assign_app_ctx_restrict_none assign_app_ctx_restrict_some 
            bang_cg_ctx_length cg_ctx_length cg_letb.hyps ctx_restrict_len i_size
          by (metis (no_types, lifting))
        moreover have "fst (bang_cg_ctx ys G1 ! i) = fst (bang_cg_ctx ys G2 ! i)"
          using i_in_e1 cg_ctx_type_same1 cg_letb.hyps cg_gen_fv_elem_size by meson
        ultimately show ?thesis
          using \<Gamma>1_i assign_app_ctx_len bang_cg_ctx_type_prop cg_ctx_length cg_letb ctx_restrict_len 
            i_in_ys i_size by auto
      qed
    }
    then show ?thesis by auto
  qed
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S \<alpha>"
    using cg_letb ctx_restrict_len assign_app_ctx_restrict_none assign_app_ctx_restrict_some 
    by (rule_tac cg_letb.hyps(4); auto simp add: ct_sem_conj_iff assign_app_ctx_len)
  moreover have "A \<turnstile> CtEscape ((fst S) n1)"
    using cg_letb assign_app_constr.simps ct_sem_conj_iff by simp
  moreover have "A \<ddagger> Some ((fst S) n1) # ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length ((\<alpha>, 0) # set0_cg_ctx ys G2)"
      consider (i_zero) "i = 0" | (i_nonzero) "i > 0" by fast
      then have "if i \<in> fv e2 then (Some ((fst S) n1) # ?\<Gamma>2) ! i =
                    Some (assign_app_ty S (fst (((\<alpha>, 0) # set0_cg_ctx ys G2) ! i)))
                 else (Some ((fst S) n1) # ?\<Gamma>2) !  i = None \<or> (Some ((fst S) n1) # ?\<Gamma>2) ! i =
                    Some (assign_app_ty S (fst (((\<alpha>, 0) # set0_cg_ctx ys G2) ! i))) \<and>
                 A \<turnstile> assign_app_constr S (CtDrop (fst (((\<alpha>, 0) # set0_cg_ctx ys G2) ! i)))"
      proof (cases)
        case i_zero
        {
          assume not_in_e2: "0 \<notin> fv e2"
          have "m = 0"
            using cg_gen_output_type_unchecked_same cg_letb.hyps not_in_e2 i_zero 
            by (metis i_size i_zero nth_Cons_0 snd_conv)
          then have "A \<turnstile> CtDrop (assign_app_ty S \<alpha>)"
            using cg_letb ct_sem_conj_iff assign_app_constr.simps by force
        }
        then show ?thesis
          using cg_letb.hyps i_zero by auto
      next
        case i_nonzero
        have "i \<in> fv e2 \<Longrightarrow> ?\<Gamma>2 ! (i - 1) = 
                            Some (assign_app_ty S (fst (set0_cg_ctx ys G2 ! (i - 1))))"
          using i_nonzero assign_app_ctx_restrict_some i_size set0_cg_ctx_length
            set0_cg_ctx_type_same by auto
        moreover have "i \<notin> fv e2 \<Longrightarrow> ?\<Gamma>2 ! (i - Suc 0) = None \<or> ?\<Gamma>2 ! (i - Suc 0) = 
                        Some (assign_app_ty S (fst (set0_cg_ctx ys G2 ! (i - Suc 0))))"
        proof (cases "i - Suc 0 \<in> ?dec_fv_e2 \<union> ?idxs")
          case True
          then show ?thesis
            using assign_app_ctx_restrict_some i_nonzero i_size set0_cg_ctx_length 
              set0_cg_ctx_type_same by auto
        next
          case False
          then show ?thesis
            using i_size i_nonzero set0_cg_ctx_length assign_app_ctx_restrict_none by auto
        qed
        moreover {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume \<Gamma>2_dec_i_not_none: "?\<Gamma>2 ! (i-1) \<noteq> None"
          have "(i - 1) \<in> ?dec_fv_e2 \<union> ?idxs"
            using \<Gamma>2_dec_i_not_none assign_app_ctx_restrict_none i_nonzero i_size length_Cons 
              set0_cg_ctx_length by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred)
          then have "i - 1 \<in> ?idxs"
            using fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_nonzero i_not_in_e2
            by (metis (no_types, lifting) One_nat_def Suc_pred UnE)
          then have "i - 1 \<notin> fv ?e" "\<Gamma> ! (i - Suc 0) \<noteq> None"
            by simp+
          then have "A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! (i - 1))))"
            using cg_letb bang_cg_ctx_length cg_ctx_length i_nonzero i_size length_Cons 
              set0_cg_ctx_length by (metis One_nat_def Suc_less_eq Suc_pred)
          moreover have "fst (bang_cg_ctx ys G1 ! (i - 1)) = fst (bang_cg_ctx ys G2 ! (i - 1))"
            using cg_ctx_type_same2 cg_letb.hyps i_size bang_cg_ctx_length set0_cg_ctx_length 
              i_nonzero by simp
          ultimately have "A \<turnstile> CtDrop (assign_app_ty S (fst (set0_cg_ctx ys G2 ! (i - 1))))"
            using assign_app_constr.simps bang_cg_ctx_length bang_cg_ctx_type_prop i_nonzero i_size
              cg_ctx_length cg_letb.hyps length_Cons set0_cg_ctx_length set0_cg_ctx_type_same
              type.inject by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred)
        }
        ultimately show ?thesis
          using i_nonzero nth_Cons' by force
      qed
    }
    moreover have "A \<turnstile> assign_app_constr S C2"
      using cg_letb ct_sem_conj_iff by force
    ultimately show ?thesis
      using assign_app_ctx_len ctx_restrict_len set0_cg_ctx_length cg_letb.prems
      by (rule_tac cg_letb.hyps(6); force simp add: assign_app_ctx_len)
  qed
  ultimately show ?case
    using typing_sig_refl typing_letb cg_letb.hyps by auto
next
  case (cg_blit C \<tau> G n l)
  have "A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
        using empty_def weak_none i_size cg_blit.prems weak_drop empty_none
        by (case_tac "\<Gamma> ! i = None"; fastforce)
    }
    then show ?thesis
      by (simp add: list_all2_all_nthI empty_def weakening_def)
  qed
  moreover have "assign_app_ty S \<tau> = TPrim Bool"
    using cg_blit ct_sem_eq_iff by auto
  ultimately show ?case
    using typing_sig_refl typing_blit by force 
next
  case (cg_ilit C m \<tau> G n)  
  obtain n where n_def: "(assign_app_ty S \<tau>) = TPrim (Num n)"
    using cg_ilit ct_sem_int_imp by fastforce 
  have "A \<turnstile> \<Gamma> \<leadsto>w local.empty (length \<Gamma>)"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length \<Gamma>"
      have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
        using empty_def weak_none i_size cg_ilit.prems weak_drop empty_none
        by (case_tac "\<Gamma> ! i = None"; fastforce)
    }
    then show ?thesis
      by (simp add: list_all2_all_nthI empty_def weakening_def)
  qed
  moreover have "m < abs n"
    using cg_ilit ct_sem_int_imp n_def by force
  moreover have "assign_app_ty S \<tau> = TPrim (Num n)"
    using cg_ilit ct_sem_int_imp n_def by fast
  ultimately show ?case
    using typing_sig_refl typing_ilit by simp
next
  case (cg_if G1 n1 e1 G2 n2 C1 e1' e2 \<tau> G3 n3 C2 e2' e3 G3' n4 C3 e3' G4 C4 C5)
  let ?e = "If e1 e2 e3"
  let ?fve2e3 = "fv e2 \<union> fv e3"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?fve2e3 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_if
  proof (rule_tac split_checked_if_extR)
    show "A \<turnstile> assign_app_constr S C2"
      using cg_if assign_app_constr.simps ct_sem_conjE by metis
    show "A \<turnstile> assign_app_constr S C3"
      using cg_if assign_app_constr.simps ct_sem_conjE by metis
    show "known_assignment S"
      using cg_if  by meson
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                  then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                  else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_if.prems by meson
  qed (blast)+
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S (TPrim Bool)"
    using cg_if
  proof (intro cg_if.hyps(2))
    {
      fix i :: nat
      assume i_size : "i < length G1"
      show "if i \<in> fv e1 
          then ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) else ?\<Gamma>1 ! i = None \<or>
               ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
               A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
        using assign_app_ctx_nth i_size ctx_restrict_def by simp
    }
  qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_if
  proof (intro cg_if.hyps(4))
    {
      fix i :: nat
      assume i_size: "i < length G2"
      show "if i \<in> fv e2
         then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) else ?\<Gamma>2 ! i = None \<or> 
              ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
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
          proof (rule_tac alg_ctx_jn_type_checked_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
            show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
              using cg_gen_output_type_checked_diff cg_if False i_in_e3 i_size 
                cg_gen_output_type_unchecked_same by metis
          qed (force)+
          then show ?thesis
            using cg_if.hyps assign_app_ctx_restrict_some i_in_e3 alg_ctx_jn_type_same1 
              cg_ctx_length cg_ctx_type_same1 i_size by (auto simp add: False)
        next
          case i_in_idxs
          have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
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
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e3' : assign_app_ty S \<tau>"
    using cg_if
  proof (intro cg_if.hyps(6))
    {
      fix i :: nat
      assume i_size: "i < length G2"
      show "if i \<in> fv e3
         then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) else ?\<Gamma>2! i = None \<or>
              ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
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
          proof (rule_tac alg_ctx_jn_type_checked_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
            show "snd (G3 ! i) \<noteq> snd (G3' ! i)"
              using cg_gen_output_type_checked_diff cg_if False i_in_e2 i_size 
                cg_gen_output_type_unchecked_same by metis
          qed (force)+
          then show ?thesis
            using cg_if.hyps assign_app_ctx_restrict_some i_in_e2 alg_ctx_jn_type_same1 
              cg_ctx_length cg_ctx_type_same1 i_size by (auto simp add: False)
        next
          case i_in_idxs
          have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
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
  ultimately show ?case
    using typing_sig_refl typing_if by simp
next
  case (cg_iop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C5)
  let ?e = "Prim x [e1, e2]"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_iop
  proof (rule_tac split_checked_extR[where ?e.0="?e"])
    show "A \<turnstile> assign_app_constr S C2"
      using cg_iop assign_app_constr.simps ct_sem_conjE by metis
    show "known_assignment S"
      using cg_iop  by metis
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv ?e 
                                   then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_iop by meson
  qed auto+
  moreover have "assign_app_ty S \<tau> \<noteq> TPrim Bool"
    using ct_sem_int_not_bool cg_iop ct_sem_conj_iff assign_app_constr.simps by metis
  moreover have "x \<in> {Plus nt, Minus nt, Times nt, Divide nt}"
    using cg_iop.hyps by simp
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S \<tau>"
    using cg_iop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len 
      assign_app_ctx_restrict_some ctx_restrict_nth_none by (intro cg_iop.hyps(3); simp)
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_iop
  proof (intro cg_iop.hyps(5))
    {
      fix i :: nat
      assume i_size: "i < length G2"
      have "i \<notin> fv e2 \<and> ?\<Gamma>2 ! i = Some y \<Longrightarrow> i \<in> ?idxs"
        using assign_app_ctx_restrict_some_ex i_size by blast
      then show "if i \<in> fv e2 then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i)))
                 else ?\<Gamma>2 ! i = None \<or> ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
                                        A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
      proof -
        {
          assume i_not_in_e2: "i \<notin> fv e2"
          assume not_none: "\<exists>y. assign_app_ctx S (G2 \<bar> fv e2 \<union> ?idxs) ! i = Some y"
          have "i \<in> ?idxs"
            using i_not_in_e2 not_none i_size assign_app_ctx_restrict_some_ex by blast
          then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
            using cg_iop cg_ctx_type_same1 by fastforce
        }
        then show ?thesis
          using assign_app_ctx_restrict_some assign_app_ctx_restrict_some_val i_size
          by (auto split: if_splits; simp)
      qed
    }
  qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_def)+
  ultimately show ?case
    using typing_sig_refl typing_iop by force
next
  case (cg_cop \<alpha> n1 x nt G1 e1 G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau>)
  let ?e = "Prim x [e1, e2]"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_cop
  proof (rule_tac split_checked_extR[where ?e="?e"])
    show "A \<turnstile> assign_app_constr S C2"
      using cg_cop assign_app_constr.simps ct_sem_conjE by metis
    show "known_assignment S"
      using cg_cop  by meson
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (Prim x [e1, e2]) 
                                   then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_cop by meson
  qed auto+
  moreover have "(fst S) n1 \<noteq> TPrim Bool" 
    using ct_sem_int_not_bool cg_cop ct_sem_conj_iff assign_app_constr.simps by auto
  moreover have "x \<in> {Eq (Num nt), NEq (Num nt), Lt nt, Gt nt, Le nt, Ge nt}"
    using cg_cop.hyps by simp
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S \<alpha>"
    using cg_cop assign_app_ctx_nth ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len
      assign_app_ctx_restrict_none assign_app_ctx_restrict_some by (intro cg_cop(4); simp)
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<alpha>"
    using cg_cop
  proof (intro cg_cop(6))
    {
      fix i :: nat
      assume i_size: "i < length G2"
      {
        assume i_not_in_e2: "i \<notin> fv e2"
        assume "\<exists>y. ?\<Gamma>2 ! i = Some y"
        then have "i \<in> ?idxs"
          using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by blast
        then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
          using cg_cop cg_ctx_type_same1 by fastforce
      }
      then show "if i \<in> fv e2 then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i)))
                 else ?\<Gamma>2 ! i = None \<or> ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
                                        A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
        using assign_app_constr.simps assign_app_ctx_restrict_none assign_app_ctx_restrict_some 
          i_size by (metis (no_types, lifting) Un_iff)
    }
  qed (force simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
  moreover have "assign_app_ty S \<tau> = TPrim Bool"
    using cg_cop ct_sem_conj_iff ct_sem_eq_iff by simp
  ultimately show ?case
    using typing_sig_refl typing_cop cg_cop.hyps by force
next
  case (cg_bop x nt G1 n1 e1 \<tau> G2 n2 C1 e1' e2 G3 n3 C2 e2' C3)
  let ?e="Prim x [e1, e2]"
  let ?idxs="Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>fv e2 \<union> ?idxs)"
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_bop
  proof (rule_tac split_checked_extR[where ?e="?e"])
    show "A \<turnstile> assign_app_constr S C2"
      using cg_bop assign_app_constr.simps ct_sem_conjE by metis
    show "known_assignment S"
      using cg_bop  by metis
    show "\<And>i. i < length G1 \<Longrightarrow> if i \<in> fv' 0 (Prim x [e1, e2]) 
                                   then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                                   else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_bop by meson
  qed auto+
  moreover have "x \<in> {BitAnd nt, BitOr nt}"
    using cg_bop.hyps by simp
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S \<tau>"
    using cg_bop
  proof (intro cg_bop.hyps(3))
    {
      fix i :: nat
      assume i_size: "i < length G1"
      show "if i \<in> fv' 0 e1
         then ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) else ?\<Gamma>1 ! i = None \<or>
              ?\<Gamma>1 ! i = Some (assign_app_ty S (fst (G1 ! i))) \<and> 
              A \<turnstile> assign_app_constr S (CtDrop (fst (G1 ! i)))"
        using assign_app_ctx_none_iff assign_app_ctx_restrict_some i_size ctx_restrict_def by simp
    }
  qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
  moreover have "A \<ddagger> ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_bop
  proof (intro cg_bop.hyps(5))
    {
      fix i :: nat
      assume i_size: "i < length G2"
      {
        assume i_not_in_e2: "i \<notin> fv e2"
        assume "\<exists>y. ?\<Gamma>2 ! i = Some y"
        then have "i \<in> ?idxs"
          using assign_app_ctx_restrict_some_ex i_size i_not_in_e2 by blast
        then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! i)))"
          using cg_bop cg_ctx_type_same1 by fastforce
      }
      then show "if i \<in> fv e2
          then ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) else ?\<Gamma>2 ! i = None \<or>
               ?\<Gamma>2 ! i = Some (assign_app_ty S (fst (G2 ! i))) \<and>
               A \<turnstile> assign_app_constr S (CtDrop (fst (G2 ! i)))"
        using assign_app_constr.simps assign_app_ctx_restrict_none assign_app_ctx_restrict_some 
          i_size by (metis (no_types, lifting) Un_iff)
    }
  qed (simp add: ct_sem_conj_iff assign_app_ctx_len ctx_restrict_len)+
  moreover have "assign_app_ty S \<tau> = TPrim Bool"
    using cg_bop ct_sem_conj_iff ct_sem_eq_iff by auto
  ultimately show ?case
    using typing_sig_refl typing_bop by force
next
  case (cg_tapp name C \<rho> m ts \<beta>s n \<rho>' C' C2 \<tau> n' G)
  have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S (TypeApp name (ts @ \<beta>s)) : (assign_app_ty S \<rho>')"
  proof -
    have "A \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)"
    proof -
      {
        fix i :: nat
        assume i_size: "i < length \<Gamma>"
        have "weakening_comp A (\<Gamma> ! i) (empty (length \<Gamma>) ! i)"
          using local.empty_def weak_none i_size cg_tapp.prems weak_drop empty_none i_size
          by (case_tac "\<Gamma> ! i = None"; fastforce)
      }
      then show ?thesis
        by (simp add: list_all2_all_nthI empty_def weakening_def)
    qed
    moreover have "type_of name = (C, \<rho>)"
      using cg_tapp.hyps by simp
    moreover have "A \<turnstile> assign_app_constr S (subst_tyvar_ct (ts @ \<beta>s) C)"
      using cg_tapp.hyps cg_tapp.prems ct_sem_conjE by auto
    moreover have "assign_app_ty S \<rho>' = assign_app_ty S (subst_tyvar (ts @ \<beta>s) \<rho>)"
      using cg_tapp.hyps by blast
    ultimately show ?thesis
      using assign_app_constr_subst_tyvar_ct_commute assign_app_ty_subst_tyvar_commute type_of_known
        typing_tapp by auto
  qed
  moreover have "A \<turnstile> CtSub (assign_app_ty S \<rho>') (assign_app_ty S \<tau>)"
    using cg_tapp.hyps cg_tapp.prems ct_sem_conj_iff by auto
  ultimately show ?case
    using typing_sig by simp
next
  case (cg_vcon \<alpha> n1 \<beta> G1 e G2 n2 C e' C' nm \<tau>)
  obtain Ks where ks_def: "TVariant Ks None = assign_app_ty S (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>))"
    by simp
  obtain KS where kS_def: "KS = (map variant_elem_checked Ks)[0 := Ks ! 0]" by blast
  have kS_hd_type: "(fst \<circ> snd) (KS ! 0) = (fst S) n1"
    using kS_def ks_def cg_vcon.hyps by force
  have kS_ks_prop: "map fst KS = map fst Ks \<and> 
                       list_all2 (\<lambda>k1 k2. (A \<turnstile> CtSub ((fst \<circ> snd) k1) ((fst \<circ> snd) k2))) KS Ks \<and> 
                       list_all2 (\<lambda>k1 k2. ((snd \<circ> snd) k1) \<le> ((snd \<circ> snd) k2)) KS Ks"
  proof - 
    {
      fix i :: nat
      assume i_size: "i < length KS"
      then have "fst (KS ! i) = fst (Ks ! i) \<and> 
                   A \<turnstile> CtSub ((fst \<circ> snd) (KS ! i)) ((fst \<circ> snd) (Ks ! i)) \<and> 
                   (snd \<circ> snd) (KS ! i) \<le> (snd \<circ> snd) (Ks ! i)"
      proof (cases "i = 0")
        case True
        then show ?thesis 
          using i_size kS_def ct_sem_equal ct_sem_refl by force
      next
        case False
        then show ?thesis
          using kS_def map_conv_all_nth ct_sem_equal ct_sem_refl i_size variant_elem_checked_nm_eq 
            variant_elem_checked_type_eq variant_elem_checked_usage_nondec by auto
      qed
    } then show ?thesis using kS_def by (simp add: map_eq_iff_nth_eq list_all2_conv_all_nth)
  qed
  have "distinct (map fst KS)"
    using kS_ks_prop cg_vcon.prems ks_def known_assignment_def by metis
  moreover have "\<forall>i<length KS. if i = 0 then (snd \<circ> snd) (KS ! i) = Unchecked 
                                           else (snd \<circ> snd) (KS ! i) = Checked"
  proof -
    {
      fix i :: nat
      assume i_size: "i < length KS"
      then have "if i = 0 then (snd \<circ> snd) (KS ! i) = Unchecked else (snd \<circ> snd) (KS ! i) = Checked"
        using kS_def ks_def
      proof (cases "i = 0")
        case False
        then show ?thesis
          using variant_elem_checked_usage_checked i_size kS_def by auto
      qed (simp)
    } then show ?thesis by blast
  qed
  moreover have "A \<ddagger> \<Gamma> \<turnstile> assign_app_expr S e' : assign_app_ty S \<beta>"
    using cg_vcon ct_sem_conj_iff by auto
  moreover have "A \<turnstile> CtSub (TVariant KS None) (assign_app_ty S \<tau>)"
    using cg_vcon
  proof -
    have "A \<turnstile> CtSub (TVariant Ks None) (assign_app_ty S \<tau>)"
      using cg_vcon ct_sem_conj_iff ks_def by simp
    then show ?thesis
      using kS_ks_prop ct_sem_sub_trans ct_sem_varsub by blast
  qed
  ultimately show ?case
    using typing_sig typing_vcon[where Ks="KS" and i="0"] kS_hd_type cg_vcon.hyps 
      kS_def ks_def by fastforce
next
  case (cg_case \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' e3 l G3' n4 C3 e3' G4 C4 C5 C6 C7)
  let ?e="Case e1 nm e2 e3"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?dec_fv_e3 = "image (\<lambda>x. x-1) (fv e3 - {0})"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2  \<union> ?dec_fv_e3 \<union> ?idxs)"
  obtain Ks where ks_def: "TVariant Ks None = assign_app_ty S (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>))"
    by simp
  have ks_hd_type: "(fst \<circ> snd) (Ks ! 0) = (fst S) n1"
    using ks_def cg_case.hyps by auto
  have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_case ct_sem_conj_iff 
  proof (rule_tac split_checked_case_extR) 
    show "\<And>i. i < length G1 \<Longrightarrow>  
          if i \<in> fv' 0 ?e then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
                          else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
      using cg_case by metis
  qed auto+
  moreover have "distinct (map fst Ks)" 
    using cg_case.prems ks_def known_assignment_def by metis
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>))"
    using cg_case ctx_restrict_len assign_app_ctx_len 
  proof (rule_tac cg_case.hyps(4))
    show "A \<turnstile> assign_app_constr S C1"
      using cg_case ct_sem_conj_iff by force
  qed (auto simp add: assign_app_ctx_restrict_none assign_app_ctx_restrict_some)
  moreover have "A \<ddagger> Some ((fst S) n1) # ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_case ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len
  proof (rule_tac cg_case.hyps(6))
    {
      fix i :: nat
      assume i_size: "i < length ((\<beta>, 0) # G2)"
      show "if i \<in> fv e2
         then (Some ((fst S) n1) # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((\<beta>, 0) # G2) ! i)))
         else (Some ((fst S) n1) # ?\<Gamma>2) ! i = None \<or>
              (Some ((fst S) n1) # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((\<beta>, 0) # G2) ! i))) \<and>
              A \<turnstile> assign_app_constr S (CtDrop (fst (((\<beta>, 0) # G2) ! i)))"
      proof -
        consider (i_zero) "i = 0" | (i_nonzero) "i \<noteq> 0"
          by blast
        then show ?thesis
        proof cases
          case i_zero
          have "i \<notin> fv e2 \<Longrightarrow> m = 0"
            using cg_gen_output_type_unchecked_same cg_case.hyps i_zero 
            by (metis i_size nth_Cons_0 snd_conv)
          moreover have "m = 0 \<Longrightarrow> A \<turnstile> assign_app_constr S (CtDrop \<beta>)"
            using cg_case ct_sem_conj_iff i_zero by auto
          ultimately show ?thesis
            using i_zero cg_case.hyps by force
        next
          case i_nonzero
          have G1_G2_type_same: "fst (G1 ! (i - 1)) = fst (G2 ! (i - 1))"
            using cg_ctx_type_same2 cg_case.hyps i_size i_nonzero by auto
          have G2_G3_type_same: "(fst (G2 ! (i - 1))) = (fst (G3 ! (i - 1)))"
            using cg_case.hyps cg_ctx_type_same1[where G="(\<beta>, 0) # G2" and G'="(\<beta>, m) # G3"]  
              i_nonzero i_size by fastforce
          have G3_G4_type_same: "(fst (G3 ! (i - 1))) = (fst (G4 ! (i - 1)))"
            using cg_case.hyps cg_ctx_length[where G="(\<beta>, 0) # G2" and G'="(\<beta>, m) # G3"] i_size
              i_nonzero alg_ctx_jn_type_same1 by simp
          consider (i_in_e2) "i \<in> fv e2" | (i_not_in_e2) "i \<notin> fv e2" by blast
          then show ?thesis
          proof cases
            case i_in_e2
            then show ?thesis
              using i_nonzero i_size by (simp; rule_tac assign_app_ctx_restrict_some; force)
          next
            case i_not_in_e2
            consider (i_in_e3) "i \<in> fv e3" | (i_in_idxs) "i - 1 \<in> ?idxs" 
                   | (i_in_neither) "i \<notin> fv e3 \<and> i - 1 \<notin> ?idxs" by blast
            then show ?thesis
            proof cases
              case i_in_e3
              have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! (i - Suc 0))))"
              proof -
                have "A \<turnstile> CtDrop (assign_app_ty S (fst (G4 ! (i - Suc 0))))"
                  using cg_case ct_sem_conj_iff
                proof (rule_tac alg_ctx_jn_type_checked_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
                  show "i - Suc 0 < length G3'"
                    using cg_ctx_length i_nonzero i_size cg_case.hyps(7) by fastforce
                  have "snd (G3 ! (i - 1)) = snd (G2 ! (i - 1))"
                    using cg_gen_output_type_unchecked_same cg_case.hyps i_not_in_e2 i_size i_nonzero
                    by (metis (mono_tags, hide_lams) nth_Cons')
                  moreover have "snd (G3' ! (i - 1)) \<noteq> snd (G2 ! (i - 1))"
                    using cg_gen_output_type_checked_diff cg_case.hyps i_in_e3 i_size i_nonzero
                    by (metis (mono_tags, hide_lams) nth_Cons')
                  ultimately show "snd (G3 ! (i - Suc 0)) \<noteq> snd (G3' ! (i - Suc 0))"
                    by fastforce
                qed (force)+
                then show ?thesis
                  using G2_G3_type_same G3_G4_type_same by fastforce
              qed
              then show ?thesis 
                using i_not_in_e2 i_in_e3 i_size apply auto
                using i_nonzero assign_app_ctx_restrict_some_val by auto
            next
              case i_in_idxs
              have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! (i - 1))))"
                using i_in_idxs cg_case.prems G1_G2_type_same by force
              then show ?thesis
                using i_not_in_e2 i_size apply auto
                using assign_app_ctx_restrict_some_val i_nonzero by auto
            next
              case i_in_neither
              then show ?thesis
                using assign_app_ctx_restrict_none fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' 
                  i_nonzero i_not_in_e2 i_size One_nat_def Suc_less_eq Suc_pred UnE length_Cons
                  neq0_conv nth_Cons' by (metis (no_types, lifting))
            qed
          qed 
        qed
      qed
    }
  qed simp+
  moreover have "A \<ddagger> Some (variant_nth_checked 0 (TVariant Ks None)) # ?\<Gamma>2 \<turnstile> assign_app_expr S e3' : assign_app_ty S \<tau>"
    using cg_case ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len
  proof (rule_tac cg_case.hyps(8))
    {
      let ?TVar\<beta>\<alpha>="TVariant [(nm, \<beta>, Checked)] (Some \<alpha>)"
      let ?TVarKs="Some (variant_nth_checked 0 (TVariant Ks None))"
      fix i :: nat
      assume i_size: "i < length ((?TVar\<beta>\<alpha>, 0) # G2)"
      show "if i \<in> fv e3
          then (?TVarKs # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((?TVar\<beta>\<alpha>, 0) # G2) ! i)))
          else (?TVarKs # ?\<Gamma>2) ! i = None \<or>
               (?TVarKs # ?\<Gamma>2) ! i = Some (assign_app_ty S (fst (((?TVar\<beta>\<alpha>, 0) # G2) ! i))) \<and>
               A \<turnstile> assign_app_constr S (CtDrop (fst (((?TVar\<beta>\<alpha>, 0) # G2) ! i)))"
      proof -
        consider (i_zero) "i = 0" | (i_nonzero) "i \<noteq> 0"
          by blast
        then show ?thesis
        proof cases
          case i_zero
          have "i \<notin> fv e3 \<Longrightarrow> l = 0"
            using cg_gen_output_type_unchecked_same cg_case.hyps i_zero 
            by (metis i_size nth_Cons_0 snd_conv)
          moreover have "l = 0 \<Longrightarrow> A \<turnstile> CtDrop (assign_app_ty S (fst (((?TVar\<beta>\<alpha>, 0) # G2) ! i)))"
            using cg_case ct_sem_conj_iff i_zero by auto
          ultimately show ?thesis
            using i_zero ks_def by force
        next
          case i_nonzero
          have G1_G2_type_same: "fst (G1 ! (i - 1)) = fst (G2 ! (i - 1))"
            using cg_ctx_type_same2 cg_case.hyps i_size i_nonzero by auto
          have G2_G3'_type_same: "(fst (G2 ! (i - 1))) = (fst (G3' ! (i - 1)))"
            using cg_ctx_type_same1[where G="(?TVar\<beta>\<alpha>, 0) # G2" and G'="(?TVar\<beta>\<alpha>, l) # G3'"]  
              cg_case.hyps i_nonzero i_size by fastforce
          have G3'_G4_type_same: "(fst (G3' ! (i - 1))) = (fst (G4 ! (i - 1)))"
            using cg_ctx_length[where G="(?TVar\<beta>\<alpha>, 0) # G2" and G'="(?TVar\<beta>\<alpha>, l) # G3'"]
              i_size cg_case.hyps i_nonzero alg_ctx_jn_type_same2 by force
          consider (i_in_e3) "i \<in> fv e3" | (i_not_in_e3) "i \<notin> fv e3" by blast
          then show ?thesis
          proof cases
            case i_in_e3
            then show ?thesis
              using i_nonzero i_size by (simp; rule_tac assign_app_ctx_restrict_some; force)
          next
            case i_not_in_e3
            consider (i_in_e2) "i \<in> fv e2" | (i_in_idxs) "i - 1 \<in> ?idxs" 
                   | (i_in_neither) "i \<notin> fv e2 \<and> i - 1 \<notin> ?idxs" by blast
            then show ?thesis
            proof cases
              case i_in_e2
              have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! (i - Suc 0))))"
              proof -
                have "A \<turnstile> CtDrop (assign_app_ty S (fst (G4 ! (i - Suc 0))))"
                  using cg_case ct_sem_conj_iff
                proof (rule_tac alg_ctx_jn_type_checked_diff[where ?G1.0=G3 and ?G1'=G3' and ?C=C4])
                  show "i - Suc 0 < length G3'"
                    using cg_ctx_length i_nonzero i_size cg_case.hyps(7) by fastforce
                  have "snd (G3' ! (i - 1)) = snd (G2 ! (i - 1))"
                    using cg_gen_output_type_unchecked_same cg_case.hyps i_not_in_e3 i_size i_nonzero
                    by (metis (mono_tags, hide_lams) nth_Cons')
                  moreover have "snd (G3 ! (i - 1)) \<noteq> snd (G2 ! (i - 1))"
                    using cg_gen_output_type_checked_diff cg_case.hyps i_in_e2 i_size i_nonzero
                    by (metis (mono_tags, hide_lams) nth_Cons')
                  ultimately show "snd (G3 ! (i - Suc 0)) \<noteq> snd (G3' ! (i - Suc 0))"
                    by fastforce
                qed (force)+
                then show ?thesis
                  using G2_G3'_type_same G3'_G4_type_same by fastforce
              qed
              then show ?thesis 
                using i_not_in_e3 i_in_e2 i_size apply auto
                using i_nonzero assign_app_ctx_restrict_some_val by auto
            next
              case i_in_idxs
              have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! (i - 1))))"
                using i_in_idxs cg_case.prems G1_G2_type_same by force
              then show ?thesis
                using i_not_in_e3 i_size apply auto
                using assign_app_ctx_restrict_some_val i_nonzero by auto
            next
              case i_in_neither
              then show ?thesis
                using assign_app_ctx_restrict_none fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' 
                  i_nonzero i_not_in_e3 i_size One_nat_def Suc_less_eq Suc_pred UnE length_Cons
                  neq0_conv nth_Cons' by (metis (no_types, lifting))
            qed
          qed 
        qed
      qed
    }
  qed simp+
  ultimately show ?case
    using ks_def ks_hd_type typing_sig_refl typing_case[where Ks="Ks" and i="0"] by simp
next
  case (cg_irref \<alpha> n1 \<beta> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m G3 n3 C2 e2' C3 C4 C5)
  let ?e = "Esac e1 nm e2"
  let ?dec_fv_e2 = "image (\<lambda>x. x-1) (fv e2 - {0})"
  let ?idxs = "Set.filter (\<lambda>x. x \<notin> fv ?e \<and> \<Gamma> ! x \<noteq> None) {0..<length G1}"
  let ?\<Gamma>1 = "assign_app_ctx S (G1\<bar>fv e1)"
  let ?\<Gamma>2 = "assign_app_ctx S (G2\<bar>?dec_fv_e2 \<union> ?idxs)"
  obtain Ks where ks_def: "TVariant Ks None = assign_app_ty S (TVariant [(nm, \<beta>, Checked)] (Some \<alpha>))"
    by simp
  obtain KS where kS_def: "KS = Ks[0 := variant_elem_unchecked (Ks ! 0)]" by blast 
  have "TVariant KS None = assign_app_ty S (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>))"
    using kS_def ks_def by auto
  moreover have "A \<turnstile> \<Gamma> \<leadsto> ?\<Gamma>1 \<box> ?\<Gamma>2"
    using cg_irref ct_sem_conj_iff  
  proof (rule_tac split_checked_irref_extR) 
    {
      fix i :: nat
      assume i_size: "i < length G1"
      show "if i \<in> fv ?e 
              then \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))
              else \<Gamma> ! i = None \<or> \<Gamma> ! i = Some (assign_app_ty S (fst (G1 ! i)))"
        using cg_irref.prems i_size by meson
    }
  qed auto+
  moreover have "distinct (map fst KS)"
  proof -
    have "distinct (map fst Ks)"
      using cg_irref.prems ks_def known_assignment_def by metis
    then show ?thesis
      using kS_def variant_elem_unchecked_nm_eq by (metis list_update_id map_update)
  qed
  moreover have "\<forall>i<length KS. if i = 0 then (snd \<circ> snd) (KS ! i) = Unchecked 
                                           else (snd \<circ> snd) (KS ! i) = Checked"
  proof -
    have ks_all_checked: "\<forall>i < length Ks. (snd \<circ> snd) (Ks ! i) = Checked"
      using ks_def ct_sem_exhaust_all_checked cg_irref ct_sem_conj_iff assign_app_constr.simps by force
    then show ?thesis
      using kS_def ks_all_checked variant_elem_unchecked_usage_unchecked by auto
  qed
  moreover have "A \<ddagger> ?\<Gamma>1 \<turnstile> assign_app_expr S e1' : assign_app_ty S (TVariant [(nm, \<beta>, Unchecked)] (Some \<alpha>))"
    using  assign_app_ctx_len assign_app_ctx_restrict_none assign_app_ctx_restrict_some cg_irref 
      ct_sem_conjE ctx_restrict_len by (metis assign_app_constr.simps(1))
  moreover have "A \<ddagger> Some ((fst \<circ> snd) (KS ! 0)) # ?\<Gamma>2 \<turnstile> assign_app_expr S e2' : assign_app_ty S \<tau>"
    using cg_irref ct_sem_conj_iff ctx_restrict_len assign_app_ctx_len nth_Cons_0
  proof (rule_tac cg_irref.hyps(6))
    {
      fix i :: nat
      assume i_size: "i < length ((\<beta>, 0) # G2)"
      consider (i_zero) "i = 0" | (i_nonzero) "i > 0" by fast
      then show "if i \<in> fv e2 then (Some ((fst \<circ> snd) (KS ! 0)) # ?\<Gamma>2) ! i =
                    Some (assign_app_ty S (fst (((\<beta>, 0) # G2) ! i)))
                 else (Some ((fst \<circ> snd) (KS ! 0)) # ?\<Gamma>2) ! i = None \<or>
                      (Some ((fst \<circ> snd) (KS ! 0)) # ?\<Gamma>2) ! i =
                      Some (assign_app_ty S (fst (((\<beta>, 0) # G2) ! i))) \<and>
                      A \<turnstile> assign_app_constr S (CtDrop (fst (((\<beta>, 0) # G2) ! i)))"
      proof cases
        case i_zero
        have "i \<notin> fv e2 \<Longrightarrow> m = 0"
          using cg_gen_output_type_unchecked_same[where ?G1.0="(\<beta>, 0) # G2" and ?G2.0="(\<beta>, m) # G3"] 
            cg_irref.hyps i_zero by fastforce
        moreover have "m = 0 \<Longrightarrow> A \<turnstile> assign_app_constr S (CtDrop \<beta>)"
          using cg_irref ct_sem_conj_iff i_zero by force
        ultimately show ?thesis
          using i_zero ks_def kS_def by force
      next
        case i_nonzero
        consider (i_in_e2) "i \<in> fv e2" | (i_in_idxs) "i \<notin> fv e2" "i - 1 \<in> ?idxs" | 
                 (i_in_neither) "i \<notin> fv e2" "i - 1 \<notin> ?idxs" by blast
        then show ?thesis
        proof cases
          case i_in_e2
          then show ?thesis
            using i_nonzero assign_app_ctx_restrict_some i_size by simp
        next
          case i_in_idxs
          then have "A \<turnstile> CtDrop (assign_app_ty S (fst (G2 ! (i - 1))))"
            using cg_ctx_type_same1[where G="G1" and G'="G2"] cg_irref i_nonzero by fastforce
          then show ?thesis
            using assign_app_ctx_restrict_some cg_ctx_length i_in_idxs i_nonzero cg_irref i_size 
              i_nonzero by simp
        next
          case i_in_neither
          then have "i - 1 \<notin> ?dec_fv_e2 \<union> ?idxs"
            using fv'_suc_eq_dec_fv' i_fv'_suc_iff_suc_i_fv' i_nonzero
            by (metis (no_types, lifting) UnE Suc_pred')
          then show ?thesis
            using i_nonzero i_size assign_app_ctx_restrict_none by auto
        qed
      qed
    }
  qed simp+
  ultimately show ?case
    using typing_sig_refl typing_irref[where Ks="KS" and i="0"] kS_def ks_def by auto
next
  case (cg_member \<alpha> n1 \<beta> G1 e nm \<tau> G2 n2 C e' C')
  then show ?case sorry
next
  case (cg_take \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 \<tau> m l G3 n3 C2 e2' C3 C4 C5 C6)
  then show ?case sorry
next
  case (cg_put \<beta> n1 \<alpha> \<gamma> G1 e1 nm G2 n2 C1 e1' e2 G3 n3 C2 e2' C3 \<tau> C4 C5)
  then show ?case sorry
next
  case (cg_struct \<alpha>s n1 nms es Gs G1 G2 ns n2 Cs es' C' \<tau>)
  then show ?case sorry
qed

lemma cg_sound:
  assumes "G,n \<turnstile> e : \<tau> \<leadsto> G',n' | C | e'"
    and "G = []"
    and "A \<turnstile> assign_app_constr S C"      
    and "known_assignment S"  
  shows "A \<ddagger> [] \<turnstile> (assign_app_expr S e') : (assign_app_ty S \<tau>)"
  using assms cg_sound_induction by fastforce

end
end