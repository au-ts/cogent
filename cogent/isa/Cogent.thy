(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Cogent 
  imports Util
begin

type_synonym name = string

type_synonym index = nat

type_synonym field = nat

section {* Prim Ops  *}

datatype num_type = U8 | U16 | U32 | U64

datatype prim_type = Num num_type | Bool | String

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


section {* Types *}


(* Actually, Datalayout information is not needed for the proof
of correspondence (see commit which removes 
all of the datalayout indications)
*)

type_synonym BitRange = "nat * nat" (* size and offset *)

(* size of a pointer, in bits *)
definition size_ptr :: nat where "size_ptr = 32"

fun size_prim_layout :: "prim_type \<Rightarrow> nat" where
  "size_prim_layout Bool = 1"
| "size_prim_layout (Num U8) = 8"
| "size_prim_layout (Num U16) = 16"
| "size_prim_layout (Num U32) = 32"
| "size_prim_layout (Num U64) = 64"
| "size_prim_layout String = undefined"

datatype ptr_layout = LayBitRange BitRange 
  | LayVar index nat (* offset *)
  | LayProduct ptr_layout ptr_layout
  | LayVariant BitRange (* size and offset of the tag  *) "(name \<times> nat \<times> ptr_layout) list"
  | LayRecord "(name \<times> ptr_layout) list"

fun bitrange_offset :: "nat \<Rightarrow> BitRange \<Rightarrow> BitRange" where
 "bitrange_offset n (s, off) = (s, off + n)"

fun layout_offset :: "nat \<Rightarrow> ptr_layout \<Rightarrow> ptr_layout" where
    "layout_offset n (LayVar v off) = LayVar v (off + n)"
  | "layout_offset n (LayProduct p1 p2) = LayProduct (layout_offset n p1) (layout_offset n p2)"
  | "layout_offset n (LayBitRange b) = LayBitRange (bitrange_offset n b)"
  | "layout_offset n (LayVariant b l) = LayVariant (bitrange_offset n b) 
                        (map (\<lambda>(name, i, p). (name, i, layout_offset n p)) l)"
  | "layout_offset n (LayRecord l) = LayRecord  
                        (map (\<lambda>(name, p). (name, layout_offset n p)) l)"

fun bitrange_taken_bit_list :: "BitRange \<Rightarrow> nat list" where
 "bitrange_taken_bit_list (s, off) = [off..<off+s]"

fun bitrange_taken_bits :: "BitRange \<Rightarrow> nat \<Rightarrow> bool" where
  "bitrange_taken_bits (s, off) n = (n \<ge> off \<and> n < off + s)"


fun layout_taken_bits :: "ptr_layout \<Rightarrow> nat \<Rightarrow> bool" where
  "layout_taken_bits (LayVar _ _) _ = False"
| "layout_taken_bits (LayVariant b ls) n = 
       (bitrange_taken_bits b n \<or> 
         list_ex (\<lambda> (_, _, l) \<Rightarrow>
                   layout_taken_bits l n) ls)"
| "layout_taken_bits (LayRecord ls) n =
   list_ex (\<lambda> (_, l) \<Rightarrow> layout_taken_bits l n) ls"
| "layout_taken_bits (LayProduct p1 p2) n =
   (layout_taken_bits p1 n \<or>
   layout_taken_bits p2 n )"
| "layout_taken_bits (LayBitRange v) n = bitrange_taken_bits v n "

fun layout_taken_bit_list :: "ptr_layout \<Rightarrow> nat list" where
  "layout_taken_bit_list (LayVar _ _) = []"
| "layout_taken_bit_list (LayVariant b ls) = 
      (bitrange_taken_bit_list b @ 
        concat (map (\<lambda> (_, _, l) .
                   layout_taken_bit_list l) ls)) "
| "layout_taken_bit_list (LayRecord ls) =
      concat (map (\<lambda> (_, l) \<Rightarrow> layout_taken_bit_list l) ls)"
| "layout_taken_bit_list (LayProduct p1 p2) =
      (layout_taken_bit_list p1 @
         layout_taken_bit_list p2 )"
| "layout_taken_bit_list (LayBitRange b) =
            bitrange_taken_bit_list b "


definition at_most_one :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  where "at_most_one f l =
  (length (filter f l) \<le> 1)"


fun layout_wellformed :: "nat \<Rightarrow> ptr_layout \<Rightarrow> bool" where
  "layout_wellformed n (LayVar i _) = (i < n)"
| "layout_wellformed _ (LayBitRange _) = True"
| "layout_wellformed m (LayVariant b ls) = 
    (list_all (\<lambda> (_, _, l) . layout_wellformed m l) ls
  \<and> (list_all   
       (\<lambda> n. list_all (\<lambda> (_, idx, l) . n \<notin> set (layout_taken_bit_list l) ) ls)
       (bitrange_taken_bit_list b)
    )
  \<and> list_all (\<lambda> (_, idx, l) . idx < 2 ^ fst b) ls
  \<and> distinct (map (\<lambda>(_, idx, _). idx) ls))"
| "layout_wellformed m (LayRecord ls) =
    (list_all (\<lambda> (_, l) . layout_wellformed m l) ls
  \<and> (list_all
       (\<lambda>n . length (filter (\<lambda> (_, l). n \<in> set (layout_taken_bit_list l)) ls) = 1))
       (concat (map (layout_taken_bit_list o snd) ls)))"

| "layout_wellformed m (LayProduct p1 p2) = 
     (layout_wellformed m p1 \<and> layout_wellformed m p2
   \<and> (set (layout_taken_bit_list p1) \<inter> set (layout_taken_bit_list p2)) = {})
"  


datatype access_perm = ReadOnly | Writable

(* Sigils represent where the memory that makes up the datatype is, and its access permissions.
 *
 * Data is either boxed (on the heap), or unboxed (on the stack). If data is on the heap, we keep
 * track of how it is represented, and what access permissions it requires.
 *)

datatype sigil = Boxed access_perm "ptr_layout option"
               | Unboxed

lemma sigil_cases:
  obtains (SBoxRo) "\<exists> ptrl. x = Boxed ReadOnly ptrl"
  | (SBoxWr) "\<exists> ptrl. x = Boxed Writable ptrl"
  | (SUnbox) "x = Unboxed"
proof (cases x)
  case (Boxed p ptrl)
  moreover assume "(\<exists> ptrl. x = Boxed ReadOnly ptrl \<Longrightarrow> thesis)"
    and "(\<exists> ptrl. x = Boxed Writable ptrl \<Longrightarrow> thesis)"
  ultimately show ?thesis
    by (cases p, simp+)
qed simp

primrec sigil_perm :: "sigil \<Rightarrow> access_perm option" where
  "sigil_perm (Boxed p _) = Some p"
| "sigil_perm Unboxed     = None"


subsection {* Types *}

(* the states of elements in variants/records *)
datatype variant_state = Checked | Unchecked
datatype record_state = Taken | Present

(* variant and record states are boolean algebras.
   This should match up with the subtyping lattice ops. *)

instantiation variant_state :: "{boolean_algebra, linorder}"
begin

fun uminus_variant_state :: "variant_state \<Rightarrow> variant_state" where
  "uminus_variant_state Checked   = Unchecked"
| "uminus_variant_state Unchecked = Checked"

definition top_variant_state :: variant_state where
  "top_variant_state \<equiv> Unchecked"
declare top_variant_state_def[simp]

definition bot_variant_state :: variant_state where
  "bot_variant_state \<equiv> Checked"
declare bot_variant_state_def[simp]

fun inf_variant_state :: "variant_state \<Rightarrow> variant_state \<Rightarrow> variant_state" where
  "inf_variant_state Checked   _         = Checked"
| "inf_variant_state Unchecked Checked   = Checked"
| "inf_variant_state Unchecked Unchecked = Unchecked"

fun sup_variant_state :: "variant_state \<Rightarrow> variant_state \<Rightarrow> variant_state" where
  "sup_variant_state Unchecked _         = Unchecked"
| "sup_variant_state Checked   Unchecked = Unchecked"
| "sup_variant_state Checked   Checked   = Checked"

fun less_eq_variant_state :: "variant_state \<Rightarrow> variant_state \<Rightarrow> bool" where
  "less_eq_variant_state _         Unchecked = True"
| "less_eq_variant_state Checked   Checked   = True"
| "less_eq_variant_state Unchecked Checked   = False"

fun less_variant_state :: "variant_state \<Rightarrow> variant_state \<Rightarrow> bool" where
  "less_variant_state _         Checked   = False"
| "less_variant_state Unchecked Unchecked = False"
| "less_variant_state Checked   Unchecked = True"

definition minus_variant_state :: "variant_state \<Rightarrow> variant_state \<Rightarrow> variant_state" where
  "minus_variant_state x y \<equiv> inf x (- y)"
declare minus_variant_state_def[simp]

instance proof
  fix x y z :: variant_state

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

instantiation record_state :: "{boolean_algebra, linorder}"
begin

fun uminus_record_state :: "record_state \<Rightarrow> record_state" where
  "uminus_record_state Taken   = Present"
| "uminus_record_state Present = Taken"

definition top_record_state :: record_state where
  "top_record_state \<equiv> Taken"
declare top_record_state_def[simp]

definition bot_record_state :: record_state where
  "bot_record_state \<equiv> Present"
declare bot_record_state_def[simp]

fun inf_record_state :: "record_state \<Rightarrow> record_state \<Rightarrow> record_state" where
  "inf_record_state Present _       = Present"
| "inf_record_state Taken   Present = Present"
| "inf_record_state Taken   Taken   = Taken"

fun sup_record_state :: "record_state \<Rightarrow> record_state \<Rightarrow> record_state" where
  "sup_record_state Taken   _       = Taken"
| "sup_record_state Present Taken   = Taken"
| "sup_record_state Present Present = Present"

fun less_eq_record_state :: "record_state \<Rightarrow> record_state \<Rightarrow> bool" where
  "less_eq_record_state _       Taken   = True"
| "less_eq_record_state Present Present = True"
| "less_eq_record_state Taken   Present = False"

fun less_record_state :: "record_state \<Rightarrow> record_state \<Rightarrow> bool" where
  "less_record_state _       Present = False"
| "less_record_state Taken   Taken   = False"
| "less_record_state Present Taken   = True"

definition minus_record_state :: "record_state \<Rightarrow> record_state \<Rightarrow> record_state" where
  "minus_record_state x y \<equiv> inf x (- y)"
declare minus_record_state_def[simp]

instance proof
  fix x y z :: record_state

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


subsection {* variants *}

fun variant_un_step :: "(['t, 't] \<Rightarrow> 't) \<Rightarrow> ([bool, bool] \<Rightarrow> bool) \<Rightarrow> ('a \<times> 't \<times> bool) \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) option" where
  "variant_un_step f g (tag, t, b) ys = (case find (\<lambda>p. fst p = tag) ys of
                                          Some (tag', t', b') \<Rightarrow> Some (tag, f t t', g b b')
                                        | None \<Rightarrow> None)"

(* precondition: \<open>fst ` set xs = fst ` set ys\<close> *)
definition variant_un :: "(['t, 't] \<Rightarrow> 't) \<Rightarrow> ([bool, bool] \<Rightarrow> bool) \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) list" where
  "variant_un f g xs ys = fold (\<lambda>x acc. case variant_un_step f g x ys of
                                          Some xy \<Rightarrow> xy # acc
                                        | None \<Rightarrow> acc) xs []"


fun variant_un_tailrec :: "(['t, 't] \<Rightarrow> 't) \<Rightarrow> ([bool, bool] \<Rightarrow> bool) \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) list \<Rightarrow> ('a \<times> 't \<times> bool) list" where
  "variant_un_tailrec f g [] ys acc = acc"
| "variant_un_tailrec f g (x # xs) ys acc = (case find (\<lambda>p. fst p = fst x) ys of
                                          Some p \<Rightarrow> (fst x, f (fst (snd x)) (fst (snd p)), g (snd (snd x)) (snd (snd p))) # acc
                                        | None \<Rightarrow> acc)"

lemma variant_un_bound_generalised:
  shows "length (fold (\<lambda>x acc. case variant_un_step f g x ys of
                                 Some xy \<Rightarrow> xy # acc
                               | None \<Rightarrow> acc) xs init) \<le> length init + length xs + length ys"
proof (induct xs arbitrary: init)
  case (Cons x xs)
  then show ?case
  proof (cases "variant_un_step f g x ys")
    case (Some a)
    then show ?thesis
      using Cons
      by (simp, metis (no_types, lifting) add_Suc length_Cons)
  qed (simp add: le_Suc_eq)
qed simp

lemma variant_un_bound: "length (variant_un f g xs ys) \<le> length xs + length ys"
  using variant_un_bound_generalised[where init="[]"]
  by (simp add: variant_un_def)


subsection {* types *}

datatype type = TVar index
              | TVarBang index
              | TCon name "type list" sigil
              | TFun type type
              | TPrim prim_type
              | TSum "(name \<times> type \<times> variant_state) list"
              | TProduct type type
              | TRecord "(name \<times> type \<times> record_state) list" sigil
              | TUnit

datatype lit = LBool bool
             | LU8 "8 word"
             | LU16 "16 word"
             | LU32 "32 word"
             | LU64 "64 word"
             (* etc *)

fun cast_to :: "num_type \<Rightarrow> lit \<Rightarrow> lit option" where
  "cast_to U8  (LU8  x) = Some (LU8 x)"
| "cast_to U16 (LU8  x) = Some (LU16 (ucast x))"
| "cast_to U16 (LU16 x) = Some (LU16 x)"
| "cast_to U32 (LU8  x) = Some (LU32 (ucast x))"
| "cast_to U32 (LU16 x) = Some (LU32 (ucast x))"
| "cast_to U32 (LU32 x) = Some (LU32 x)"
| "cast_to U64 (LU8  x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU16 x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU32 x) = Some (LU64 (ucast x))"
| "cast_to U64 (LU64 x) = Some (LU64 x)"

section {* Expressions *}

datatype 'f expr = Var index
                 (* TODO: polymorphic layouts for abstract functions *)
                 | AFun 'f  "type list" "ptr_layout list"
                 | Fun "'f expr" "type list" "ptr_layout list"
                 | Prim prim_op "'f expr list"
                 | App "'f expr" "'f expr"
                 | Con "(name \<times> type \<times> variant_state) list" name "'f expr"
                 | Struct "type list" "'f expr list"
                 | Member "'f expr" field
                 | Unit
                 | Lit lit
                 | SLit string
                 | Cast num_type "'f expr"
                 | Tuple "'f expr" "'f expr"
                 | Put "'f expr" field "'f expr"
                 | Let "'f expr" "'f expr"
                 | LetBang "index set" "'f expr" "'f expr"
                 | Case "'f expr" name "'f expr" "'f expr"
                 | Esac "'f expr" name
                 | If "'f expr" "'f expr" "'f expr"
                 | Take "'f expr" field "'f expr"
                 | Split "'f expr" "'f expr"
                 | Promote type "'f expr"

section {* Bang *}

fun bang_sigil :: "sigil \<Rightarrow> sigil" where
  "bang_sigil (Boxed ReadOnly r) = Boxed ReadOnly r"
| "bang_sigil (Boxed Writable r) = Boxed ReadOnly r"
| "bang_sigil Unboxed            = Unboxed"

fun bang :: "type \<Rightarrow> type" where
  "bang (TVar i)       = TVarBang i"
| "bang (TVarBang i)   = TVarBang i"
| "bang (TCon n ts s)  = TCon n (map bang ts) (bang_sigil s)"
| "bang (TFun a b)     = TFun a b"
| "bang (TPrim p)      = TPrim p"
| "bang (TSum ps)      = TSum (map (\<lambda> (c, (t, b)). (c, (bang t, b))) ps)"
| "bang (TProduct t u) = TProduct (bang t) (bang u)"
| "bang (TRecord ts s) = TRecord (map (\<lambda>(n, t, b). (n, bang t, b)) ts) (bang_sigil s)"
| "bang (TUnit)        = TUnit"

section {* Representation Types (for use in C-refinement) *}

(* TODO: update to contain mininimal layout information *)
(*  [repr] is a cleared version of [type].
minimal representation of types for C-refinement.
Equal [repr] should match the same C-type, contrary to 
[type]
 *)
datatype repr = RPtr repr
              | RCon name "repr list"
              | RFun
              | RPrim prim_type
              | RSum "(name \<times> repr) list"
              | RProduct "repr" "repr"
              | RRecord "repr list" "ptr_layout option"
              | RUnit

fun type_repr :: "type \<Rightarrow> repr" where
  "type_repr (TFun t t')          = RFun"
| "type_repr (TPrim t)            = RPrim t"
| "type_repr (TSum ts)            = RSum (map (\<lambda>(a,b,_).(a, type_repr b)) ts)"
| "type_repr (TProduct a b)       = RProduct (type_repr a) (type_repr b)"
| "type_repr (TCon n ts Unboxed)  = RCon n (map type_repr ts)"
| "type_repr (TCon n ts _)        = RPtr (RCon n (map type_repr ts))"
| "type_repr (TRecord ts Unboxed) = RRecord (map (\<lambda>(_,b,_). type_repr b) ts) None"
| "type_repr (TRecord ts (Boxed _ ptrl))       = RPtr (RRecord (map (\<lambda>(_,b,_). type_repr b) ts) ptrl)"
| "type_repr (TUnit)              = RUnit"

section {* Representation Types (for use in layout) *}


datatype lrepr = LRPtr
              | LRCon name "lrepr list"
              | LRFun
              | LRPrim prim_type
              | LRSum "(name \<times> lrepr) list"
              | LRProduct "lrepr" "lrepr"
              | LRRecord "(name \<times> lrepr) list"
              | LRUnit
              | LRVar nat

fun type_lrepr :: "type \<Rightarrow> lrepr" where
  "type_lrepr (TFun t t')          = LRFun"
| "type_lrepr (TPrim t)            = LRPrim t"
| "type_lrepr (TSum ts)            = LRSum (map (\<lambda>(a,b,_).(a, type_lrepr b)) ts)"
| "type_lrepr (TProduct a b)       = LRProduct (type_lrepr a) (type_lrepr b)"
| "type_lrepr (TCon n ts Unboxed)  = LRCon n (map type_lrepr ts)"
| "type_lrepr (TCon n ts _)        = LRPtr "
| "type_lrepr (TRecord ts Unboxed) = LRRecord (map (\<lambda>(a,b,_). (a, type_lrepr b)) ts)"
| "type_lrepr (TRecord ts _)       = LRPtr"
| "type_lrepr (TUnit)              = LRUnit"
| "type_lrepr (TVar v) = LRVar v"
| "type_lrepr (TVarBang v) = LRVar v"

fun lrepr_wellformed :: "nat \<Rightarrow> lrepr \<Rightarrow> bool" where
  "lrepr_wellformed n LRFun                = True"
| "lrepr_wellformed n (LRPrim _)           = True"
| "lrepr_wellformed n LRUnit               = True"
| "lrepr_wellformed n LRPtr                = True"
| "lrepr_wellformed n (LRSum ts)           = list_all (\<lambda>(_,b). lrepr_wellformed n b) ts"
| "lrepr_wellformed n (LRProduct a b)      = (lrepr_wellformed n a \<and> lrepr_wellformed n b)"
| "lrepr_wellformed n (LRCon _ ts)         = list_all (lrepr_wellformed n) ts"
| "lrepr_wellformed n (LRRecord ts)        = list_all (\<lambda>(_,b). lrepr_wellformed n b) ts"
| "lrepr_wellformed n (LRVar v) = (v < n)"


section {* Kinds *}

datatype kind_comp
  = D (* Drop *)
  | S (* Share *)
  | E (* Escape *)

type_synonym kind = "kind_comp set"

(* number of layout variables *)
type_synonym lay_env = nat
(* in practice, lrepr is a record *)
type_synonym lay_constraints = "(ptr_layout \<times> lrepr) set"

type_synonym poly_type = "lay_env \<times> kind list \<times> lay_constraints  
                        \<times> type \<times> type"

type_synonym 'v env  = "'v list"

type_synonym 'a substitution = "'a list"

fun sigil_kind :: "sigil \<Rightarrow> kind" where
  "sigil_kind (Boxed ReadOnly _) = {D,S}"
| "sigil_kind (Boxed Writable _) = {E}"
| "sigil_kind Unboxed            = {D,S,E}"


inductive match_repr_layout :: "lrepr \<Rightarrow> ptr_layout \<Rightarrow> bool"
  where
  match_lrtvar :  "match_repr_layout (LRVar i) l"
| match_lrprim : "(s = size_prim_layout t) \<Longrightarrow> match_repr_layout (LRPrim t) (LayBitRange (s, x))"
| match_lrsum : "\<lbrakk> (map fst ts :: name list) = map fst ls
   ; list_all2 match_repr_layout (map snd ts) (map (snd \<circ> snd) ls)
   \<rbrakk> \<Longrightarrow> match_repr_layout (LRSum ts) (LayVariant x ls)"
| match_lrproduct : "\<lbrakk> match_repr_layout t1 p1
   ; match_repr_layout t2 p2
   \<rbrakk> \<Longrightarrow> match_repr_layout (LRProduct t1 t2) (LayProduct p1 p2)"
| match_lrptr : "(s = size_ptr) \<Longrightarrow> match_repr_layout LRPtr (LayBitRange (s, n))"
| match_lrrecord : "\<lbrakk> (map fst ts :: name list) = map fst ls
   \<comment> \<open>; match_repr_layout_all (map snd ts) (map snd ls)\<close>
; list_all2 match_repr_layout (map snd ts) (map snd ls)
   \<rbrakk> \<Longrightarrow> match_repr_layout (LRRecord ts) (LayRecord ls)"
| match_lrunit : "s = 0 \<Longrightarrow> match_repr_layout LRUnit (LayBitRange (s, n))"
| match_lrlvar : "match_repr_layout t (LayVar i off)"


lemma match_repr_layout_simps:
  "\<And> l i. match_repr_layout (LRVar i) l"
  
  "\<And>t p. match_repr_layout (LRPrim t) (LayBitRange p) \<longleftrightarrow> fst p = size_prim_layout t"
  "\<And>ts ls x. match_repr_layout (LRSum ts) (LayVariant x ls) \<longleftrightarrow>
      map fst ts = map fst ls \<and> list_all2 match_repr_layout (map snd ts) (map (snd \<circ> snd) ls)"
  "\<And>t1 t2 p1 p2. match_repr_layout (LRProduct t1 t2) (LayProduct p1 p2) \<longleftrightarrow>
      match_repr_layout t1 p1 \<and> match_repr_layout t2 p2"
  "\<And>ts p. match_repr_layout LRPtr (LayBitRange p) \<longleftrightarrow> fst p = size_ptr"
  "\<And>ts ls. match_repr_layout (LRRecord ts ) (LayRecord ls) \<longleftrightarrow>
      map fst ts = map fst ls \<and> list_all2 match_repr_layout (map snd ts) (map snd ls)"
  "\<And>p. match_repr_layout LRUnit (LayBitRange p) \<longleftrightarrow> fst p = 0"
  "\<And>t i off. match_repr_layout t (LayVar i off)"
  by (force intro: match_repr_layout.intros
      elim: match_repr_layout.cases)+


type_synonym field_types = "(char list \<times> Cogent.type \<times> record_state) list"
(*  (fst t, f (fst (snd t)), snd (snd t) *)
abbreviation map_field_type where
  "map_field_type f \<equiv> map (\<lambda> (n, t, b).(n, f t, b))"



definition match_constraint :: "lay_constraints \<Rightarrow> ptr_layout \<Rightarrow> lrepr \<Rightarrow> bool"

where "match_constraint C ptr_layout rep \<equiv> 
\<comment> \<open>TODO: No need to keep track of the constraint: if the type and the layout do not contain
any variable, then we know that any substitution of them will remain valid\<close>
(layout_wellformed 0 ptr_layout \<and> lrepr_wellformed 0 rep) 
   \<or> (ptr_layout, rep) \<in> C"



definition matches_fields_layout where
 "matches_fields_layout nl C rep ptr_layout \<equiv>
   match_repr_layout rep ptr_layout \<and>
   layout_wellformed nl ptr_layout \<and>
match_constraint C ptr_layout rep
"    

fun matches_type_sigil :: "lay_env \<Rightarrow> lay_constraints \<Rightarrow> lrepr
              \<Rightarrow> sigil \<Rightarrow> bool"
  where
  "matches_type_sigil nl C t Unboxed = True"
| "matches_type_sigil nl C t (Boxed _ (Some ptr_layout)) =
     matches_fields_layout nl C t ptr_layout"
| "matches_type_sigil nl C t (Boxed _ None) = True"

lemma matches_type_sigil_boxed : 
  "matches_type_sigil L C \<tau> (Boxed Writable s) =
matches_type_sigil L C \<tau> (Boxed ReadOnly s)"  
  by(cases s) simp+

lemma sigil_lay_cases[case_names BoxedLay BoxedNoLay Unboxed]:
  assumes "\<And> p ptrl. P (Boxed p (Some ptrl))"
          "\<And> p. P (Boxed p None)"
          "P Unboxed" 
  shows "P s"
  apply (cases s)
   apply(rename_tac p ptrl)
   apply (case_tac ptrl)  
  using assms 
  by simp_all



fun type_wellformed :: "lay_env \<Rightarrow> nat \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> bool" where
  "type_wellformed nl n C (TVar i) = (i < n)"
| "type_wellformed nl n C (TVarBang i) = (i < n)"
| "type_wellformed nl n C (TCon _ ts _) = list_all (\<lambda>x. type_wellformed nl n C x) ts"
| "type_wellformed nl n C (TFun t1 t2) = (type_wellformed nl n C t1 \<and> type_wellformed nl n C t2)"
| "type_wellformed nl n C (TPrim _) = True"
| "type_wellformed nl n C (TSum ts) = (distinct (map fst ts) \<and> (list_all (\<lambda>x. type_wellformed nl n C (fst (snd x))) ts))"
| "type_wellformed nl n C (TProduct t1 t2) = (type_wellformed nl n C t1 \<and> type_wellformed nl n C t2)"
| "type_wellformed nl n C (TRecord ts perm) = 
  ( distinct (map fst ts) \<and> (list_all (\<lambda>x. type_wellformed nl n C (fst (snd x))) ts)
   \<and> matches_type_sigil nl C 
   (LRRecord (map (\<lambda>(n,t,_). (n, type_lrepr t)) ts)) perm )"
| "type_wellformed nl n C TUnit = True"


definition type_wellformed_pretty :: " lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> bool" ("_, _, _ \<turnstile> _ wellformed" [30,30,20] 60) where
  "L, K, C \<turnstile> t wellformed \<equiv> type_wellformed L (length K) C t"
declare type_wellformed_pretty_def[simp]

lemma type_wellformed_intros:
  "\<And>nl n C i. i < n \<Longrightarrow> type_wellformed nl n C (TVar i)"
  "\<And>nl n C i. i < n \<Longrightarrow> type_wellformed nl n C (TVarBang i)"
  "\<And>nl n C name ts s. list_all (\<lambda>x. type_wellformed nl n C x) ts \<Longrightarrow> type_wellformed nl n C (TCon name ts s)"
  "\<And>nl n C t1 t2. \<lbrakk> type_wellformed nl n C t1 ; type_wellformed nl n C t2 \<rbrakk> \<Longrightarrow> type_wellformed nl n C (TFun t1 t2)"
  "\<And>nl n C p. type_wellformed nl n C (TPrim p)"
  "\<And>nl n C ts. \<lbrakk> distinct (map fst ts) ; list_all (\<lambda>x. type_wellformed nl n C (fst (snd x))) ts \<rbrakk> \<Longrightarrow> type_wellformed nl n C (TSum ts)"
  "\<And>nl n C t1 t2. \<lbrakk> type_wellformed nl n C t1 ; type_wellformed nl n C t2 \<rbrakk> \<Longrightarrow> type_wellformed nl n C (TProduct t1 t2)"
  "\<And>nl n C ts s. \<lbrakk> distinct (map fst ts) ; list_all (\<lambda>x. type_wellformed nl n C (fst (snd x))) ts ;
     matches_type_sigil nl C (LRRecord (map (\<lambda>(n,t,_). (n, type_lrepr t)) ts)) s \<rbrakk> \<Longrightarrow> type_wellformed nl n C (TRecord ts s)"
  "\<And>nl n C. type_wellformed nl n C TUnit"
  by (simp add: list_all_iff)+

lemma type_wellformed_pretty_intros:
  "\<And>nl K C i. i < length K \<Longrightarrow> type_wellformed_pretty nl K C (TVar i)"
  "\<And>nl K C i. i < length K \<Longrightarrow> type_wellformed_pretty nl K C (TVarBang i)"
  "\<And>nl K C name ts s. list_all (\<lambda>x. type_wellformed_pretty nl K C x) ts \<Longrightarrow> type_wellformed_pretty nl K C (TCon name ts s)"
  "\<And>nl K C t1 t2. \<lbrakk> type_wellformed_pretty nl K C t1 ; type_wellformed_pretty nl K C t2 \<rbrakk> \<Longrightarrow> type_wellformed_pretty nl K C (TFun t1 t2)"
  "\<And>nl K C p. type_wellformed_pretty nl K C (TPrim p)"
  "\<And>nl K C ts. \<lbrakk> distinct (map fst ts) ; list_all (\<lambda>x. type_wellformed_pretty nl K C (fst (snd x))) ts \<rbrakk> \<Longrightarrow> type_wellformed_pretty nl K C (TSum ts)"
  "\<And>nl K C t1 t2. \<lbrakk> type_wellformed_pretty nl K C t1 ; type_wellformed_pretty nl K C t2 \<rbrakk> \<Longrightarrow> type_wellformed_pretty nl K C (TProduct t1 t2)"
  "\<And>nl K C ts s. \<lbrakk> distinct (map fst ts) ; list_all (\<lambda>x. type_wellformed_pretty nl K C (fst (snd x))) ts
    ; matches_type_sigil nl C (LRRecord (map (\<lambda>(n,t,_). (n, type_lrepr t)) ts)) s \<rbrakk> \<Longrightarrow> type_wellformed_pretty nl K C (TRecord ts s)"
  "\<And>nl K C. type_wellformed_pretty nl K C TUnit"
  by (simp add: list_all_iff)+

definition type_wellformed_all_pretty :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type list \<Rightarrow> bool" ("_, _, _ \<turnstile>* _ wellformed" [30, 0, 0,20] 60) where
  "L, K, C \<turnstile>* ts wellformed \<equiv> (\<forall>t\<in>set ts. type_wellformed L (length K) C t)"
declare type_wellformed_all_pretty_def[simp]

definition proc_ctx_wellformed :: "('f \<Rightarrow> poly_type) \<Rightarrow> bool" where
  "proc_ctx_wellformed \<Xi> = (\<forall> f. let (L, K, C, \<tau>i, \<tau>o) = \<Xi> f in L, K, C \<turnstile> TFun \<tau>i \<tau>o wellformed)"


fun kinding_fn :: "kind env \<Rightarrow> type \<Rightarrow> kind" where
  "kinding_fn K (TVar i)         = (if i < length K then K ! i else undefined)"
| "kinding_fn K (TVarBang i)     = {D,S}"
| "kinding_fn K (TCon n ts s)    = Inter (set (map (kinding_fn K) ts)) \<inter> (sigil_kind s)"
| "kinding_fn K (TFun ta tb)     = UNIV"
| "kinding_fn K (TPrim p)        = UNIV"
| "kinding_fn K (TSum ts)        = Inter (set (map (\<lambda>(_,t,b). case b of Unchecked \<Rightarrow> kinding_fn K t | Checked \<Rightarrow> UNIV) ts))"
| "kinding_fn K (TProduct ta tb) = kinding_fn K ta \<inter> kinding_fn K tb"
| "kinding_fn K (TRecord ts s)   = Inter (set (map (\<lambda>(_,t,b). case b of Present \<Rightarrow> kinding_fn K t | Taken \<Rightarrow> UNIV) ts)) \<inter> (sigil_kind s)"
| "kinding_fn K TUnit            = UNIV"

lemmas kinding_fn_induct = kinding_fn.induct[case_names kind_tvar kind_tvarb kind_tcon kind_tfun kind_tprim kind_tsum kind_tprod kind_trec kind_tunit]


definition kinding :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> kind \<Rightarrow> bool" ("_, _, _ \<turnstile> _ :\<kappa> _" [30,0,0,0,30] 60) where
  "L, K, C \<turnstile> t :\<kappa> k \<equiv> L, K, C \<turnstile> t wellformed \<and> k \<subseteq> kinding_fn K t"

lemma kindingI:
  "L, K, C \<turnstile> t wellformed \<Longrightarrow> k \<subseteq> kinding_fn K t \<Longrightarrow> L, K, C \<turnstile> t :\<kappa> k"
  by (simp add: kinding_def)

definition kinding_all :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type list \<Rightarrow> kind \<Rightarrow> bool" ("_, _, _ \<turnstile>* _ :\<kappa> _" [30,0,0,0,30] 60) where
  "L, K, C \<turnstile>* ts :\<kappa> k \<equiv> (\<forall>t\<in>set ts. L, K, C \<turnstile> t wellformed) \<and> k \<subseteq> (\<Inter>t\<in>set ts. kinding_fn K t)"

definition kinding_variant :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> (name \<times> type \<times> variant_state) list \<Rightarrow> kind \<Rightarrow> bool" ("_, _, _ \<turnstile>* _ :\<kappa>v _" [30,0,0,0,60] 60) where
  "L, K, C \<turnstile>* ts :\<kappa>v k \<equiv> (\<forall>(_,t,_)\<in>set ts. L, K, C \<turnstile> t wellformed) \<and> k \<subseteq> (\<Inter>(_,t,b)\<in>set ts. (case b of Checked \<Rightarrow> UNIV | Unchecked \<Rightarrow> kinding_fn K t))"

definition kinding_record  :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> (name \<times> type \<times> record_state) list \<Rightarrow> kind \<Rightarrow> bool" ("_, _, _ \<turnstile>* _ :\<kappa>r _" [30,0,0,0,30] 60) where
  "L, K, C \<turnstile>* ts :\<kappa>r k \<equiv> (\<forall>(_,t,_)\<in>set ts. L, K, C \<turnstile> t wellformed) \<and> k \<subseteq> (\<Inter>(_,t,b)\<in>set ts. (case b of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K t))"

lemmas kinding_defs = kinding_def kinding_all_def kinding_variant_def kinding_record_def


section {* Observation and type instantiation *}

fun instantiate_lrepr :: "lrepr substitution \<Rightarrow> lrepr \<Rightarrow> lrepr" where
  "instantiate_lrepr \<delta> (LRVar i) = (if i < length \<delta> then \<delta> ! i else LRVar i)"
| "instantiate_lrepr _ LRPtr = LRPtr"
| "instantiate_lrepr \<delta> (LRCon n ts) = LRCon n (map (instantiate_lrepr \<delta>) ts)"
| "instantiate_lrepr _ LRFun = LRFun"
| "instantiate_lrepr _ LRUnit = LRUnit"
| "instantiate_lrepr _ (LRPrim t) = LRPrim t "
| "instantiate_lrepr \<delta> (LRSum ts) = LRSum (map (\<lambda>(n, t). (n, instantiate_lrepr \<delta> t)) ts) "
| "instantiate_lrepr \<delta> (LRProduct t1 t2) = LRProduct (instantiate_lrepr \<delta> t1)  (instantiate_lrepr \<delta> t2)"
| "instantiate_lrepr \<delta> (LRRecord ts) = LRRecord (map (\<lambda>(n, t). (n, instantiate_lrepr \<delta> t)) ts) "

(* layout instantiation *)
fun instantiate_lay :: "ptr_layout substitution \<Rightarrow> ptr_layout \<Rightarrow> ptr_layout"
  where
(* TODO: use an environment to keep track of the constraints of the layout variables, as
in the dargent write-up *)
  "instantiate_lay \<delta> (LayVar i offset) = (if i < length \<delta> then layout_offset offset (\<delta> ! i) else LayVar i offset)"
| "instantiate_lay \<delta> (LayProduct l1 l2) = LayProduct (instantiate_lay \<delta> l1) (instantiate_lay \<delta> l2)"
| "instantiate_lay \<delta> (LayVariant b ls) = LayVariant b (map (\<lambda>(n, tag, l). (n, tag, instantiate_lay \<delta> l)) ls)"
| "instantiate_lay \<delta> (LayRecord ls) = LayRecord (map (\<lambda>(n, l). (n, instantiate_lay \<delta> l)) ls)"
| "instantiate_lay _ (LayBitRange v) = LayBitRange v"

fun instantiate_sigil :: "ptr_layout substitution \<Rightarrow> sigil \<Rightarrow> sigil"
  where
  "instantiate_sigil \<delta> (Boxed perm ptrl) = Boxed perm (map_option (instantiate_lay \<delta>) ptrl)"
| "instantiate_sigil \<delta> s = s"

lemma sigil_perm_instantiate_sigil[simp] : "sigil_perm (instantiate_sigil \<epsilon> s) = sigil_perm s"
proof(induct s rule:sigil_lay_cases)
case (BoxedLay p ptrl)
  then show ?case 
    by (cases p) (simp)+
next
  case (BoxedNoLay p)
  then show ?case 
     by (cases p) (simp)+
qed simp

fun instantiate :: "ptr_layout substitution \<Rightarrow> type substitution \<Rightarrow> type \<Rightarrow> type" where
  "instantiate \<epsilon> \<delta> (TVar i)       = (if i < length \<delta> then \<delta> ! i else TVar i)"
| "instantiate \<epsilon> \<delta> (TVarBang i)   = (if i < length \<delta> then bang (\<delta> ! i) else TVarBang i)"
| "instantiate \<epsilon> \<delta> (TCon n ts s)  = TCon n (map (instantiate \<epsilon> \<delta>) ts) s"
| "instantiate \<epsilon> \<delta> (TFun a b)     = TFun (instantiate \<epsilon> \<delta> a) (instantiate \<epsilon> \<delta> b)"
| "instantiate \<epsilon> \<delta> (TPrim p)      = TPrim p"
| "instantiate \<epsilon> \<delta> (TSum ps)      = TSum (map (\<lambda> (c, t, b). (c, instantiate \<epsilon> \<delta> t, b)) ps)"
| "instantiate \<epsilon> \<delta> (TProduct t u) = TProduct (instantiate \<epsilon> \<delta> t) (instantiate \<epsilon> \<delta> u)"
| "instantiate \<epsilon> \<delta> (TRecord ts s) = TRecord (map (\<lambda> (n, t, b). (n, instantiate \<epsilon> \<delta> t, b)) ts) 
             (instantiate_sigil \<epsilon> s)"
| "instantiate \<epsilon> \<delta> (TUnit)        = TUnit"

fun specialise :: "ptr_layout substitution \<Rightarrow> type substitution \<Rightarrow> 'f expr \<Rightarrow> 'f expr" where
  "specialise \<epsilon> \<delta> (Var i)           = Var i"
| "specialise \<epsilon> \<delta> (Fun f ts ls)     = Fun f (map (instantiate \<epsilon> \<delta>) ts) (map (instantiate_lay \<epsilon>) ls)"
| "specialise \<epsilon> \<delta> (AFun f ts ls)    = AFun f (map (instantiate \<epsilon> \<delta>) ts) (map (instantiate_lay \<epsilon>) ls)"
| "specialise \<epsilon> \<delta> (Prim p es)       = Prim p (map (specialise \<epsilon> \<delta>) es)"
| "specialise \<epsilon> \<delta> (App a b)         = App (specialise \<epsilon> \<delta> a) (specialise \<epsilon> \<delta> b)"
| "specialise \<epsilon> \<delta> (Con as t e)      = Con (map (\<lambda> (c,t,b). (c, instantiate \<epsilon> \<delta> t, b)) as) t (specialise \<epsilon> \<delta> e)"
| "specialise \<epsilon> \<delta> (Struct ts vs)    = Struct (map (instantiate \<epsilon> \<delta>) ts) (map (specialise \<epsilon> \<delta>) vs)"
| "specialise \<epsilon> \<delta> (Member v f)      = Member (specialise \<epsilon> \<delta> v) f"
| "specialise \<epsilon> \<delta> (Unit)            = Unit"
| "specialise \<epsilon> \<delta> (Cast t e)        = Cast t (specialise \<epsilon> \<delta> e)"
| "specialise \<epsilon> \<delta> (Lit v)           = Lit v"
| "specialise \<epsilon> \<delta> (SLit s)          = SLit s"
| "specialise \<epsilon> \<delta> (Tuple a b)       = Tuple (specialise \<epsilon> \<delta> a) (specialise \<epsilon> \<delta> b)"
| "specialise \<epsilon> \<delta> (Put e f e')      = Put (specialise \<epsilon> \<delta> e) f (specialise \<epsilon> \<delta> e')"
| "specialise \<epsilon> \<delta> (Let e e')        = Let (specialise \<epsilon> \<delta> e) (specialise \<epsilon> \<delta> e')"
| "specialise \<epsilon> \<delta> (LetBang vs e e') = LetBang vs (specialise \<epsilon> \<delta> e) (specialise \<epsilon> \<delta> e')"
| "specialise \<epsilon> \<delta> (Case e t a b)    = Case (specialise \<epsilon> \<delta> e) t (specialise \<epsilon> \<delta> a) (specialise \<epsilon> \<delta> b)"
| "specialise \<epsilon> \<delta> (Esac e t)        = Esac (specialise \<epsilon> \<delta> e) t"
| "specialise \<epsilon> \<delta> (If c t e)        = If (specialise \<epsilon> \<delta> c) (specialise \<epsilon> \<delta> t) (specialise \<epsilon> \<delta> e)"
| "specialise \<epsilon> \<delta> (Take e f e')     = Take (specialise \<epsilon> \<delta> e) f (specialise \<epsilon> \<delta> e')"
| "specialise \<epsilon> \<delta> (Split v va)      = Split (specialise \<epsilon> \<delta> v) (specialise \<epsilon> \<delta> va)"
| "specialise \<epsilon> \<delta> (Promote t x)     = Promote (instantiate \<epsilon> \<delta> t) (specialise \<epsilon> \<delta> x)"

section {* Subtyping *}

abbreviation record_kind_subty :: "lay_env \<Rightarrow> kind_comp set list \<Rightarrow> lay_constraints \<Rightarrow> name \<times> Cogent.type \<times> record_state \<Rightarrow> name \<times> Cogent.type \<times> record_state \<Rightarrow> bool" where
  "record_kind_subty L K C p1 p2 \<equiv> snd (snd p1) = snd (snd p2) \<or> ((L, K, C \<turnstile> (fst (snd p1)) :\<kappa> {D}) \<and> snd (snd p1) < snd (snd p2))"

abbreviation variant_kind_subty :: "name \<times> Cogent.type \<times> variant_state \<Rightarrow> name \<times> Cogent.type \<times> variant_state \<Rightarrow> bool" where
  "variant_kind_subty p1 p2 \<equiv> snd (snd p1) \<le> snd (snd p2)"

inductive subtyping :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool" ("_, _, _ \<turnstile> _ \<sqsubseteq> _" [40,0,0,0,40] 60) where
  subty_tvar   : "n1 = n2 \<Longrightarrow> L, K, C \<turnstile> TVar n1 \<sqsubseteq> TVar n2"
| subty_tvarb  : "n1 = n2 \<Longrightarrow> L, K, C \<turnstile> TVarBang n1 \<sqsubseteq> TVarBang n2"
| subty_tcon   : "\<lbrakk> n1 = n2 ; s1 = s2 ; ts1 = ts2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TCon n1 ts1 s1 \<sqsubseteq> TCon n2 ts2 s2"
| subty_tfun   : "\<lbrakk> L, K, C \<turnstile> t2 \<sqsubseteq> t1
                  ; L, K, C \<turnstile> u1 \<sqsubseteq> u2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TFun t1 u1 \<sqsubseteq> TFun t2 u2"
| subty_tprim  : "\<lbrakk> p1 = p2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TPrim p1 \<sqsubseteq> TPrim p2"
(* TODO: adapt with dargent *)
| subty_trecord: "\<lbrakk> list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) ts1 ts2
                  ; map fst ts1 = map fst ts2
                  ; list_all2 (record_kind_subty L K C) ts1 ts2
                  ; s1 = s2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TRecord ts1 s1 \<sqsubseteq> TRecord ts2 s2"
| subty_tprod  : "\<lbrakk> L, K, C \<turnstile> t1 \<sqsubseteq> t2
                  ; L, K, C \<turnstile> u1 \<sqsubseteq> u2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TProduct t1 u1 \<sqsubseteq> TProduct t2 u2"
| subty_tsum   : "\<lbrakk> list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) ts1 ts2
                  ; map fst ts1 = map fst ts2
                  ; list_all2 variant_kind_subty ts1 ts2
                  \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> TSum ts1 \<sqsubseteq> TSum ts2"
| subty_tunit  : "L, K, C \<turnstile> TUnit \<sqsubseteq> TUnit"

section {* Contexts *}

type_synonym ctx = "type option env"

definition empty :: "nat \<Rightarrow> ctx" where
  "empty \<equiv> (\<lambda> x. replicate x None)"

definition singleton :: "nat \<Rightarrow> index \<Rightarrow> type \<Rightarrow> ctx" where
  "singleton n i t \<equiv> (empty n)[i := Some t]"

declare singleton_def [simp]

definition instantiate_ctx :: "ptr_layout substitution \<Rightarrow> type substitution \<Rightarrow> ctx \<Rightarrow> ctx" where
  "instantiate_ctx \<epsilon> \<delta> \<Gamma> \<equiv> map (map_option (instantiate \<epsilon> \<delta>)) \<Gamma>"

inductive split_comp :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool"
          ("_, _, _ \<turnstile> _ \<leadsto> _ \<parallel> _" [30,0,0,0,0,20] 60) where
  none  : "L, K, C \<turnstile> None \<leadsto> None \<parallel> None"
| left  : "\<lbrakk> L, K, C \<turnstile> t wellformed \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> Some t \<leadsto> Some t \<parallel> None"
| right : "\<lbrakk> L, K, C \<turnstile> t wellformed \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> Some t \<leadsto> None   \<parallel> Some t"
| share : "\<lbrakk> L, K, C \<turnstile> t :\<kappa> k; S \<in> k \<rbrakk> \<Longrightarrow> L, K, C \<turnstile> Some t \<leadsto> Some t \<parallel> Some t"

definition split :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_, _, _ \<turnstile> _ \<leadsto> _ | _" [30,0,0,0,0,20] 60) where
  "split L K C \<equiv> list_all3 (split_comp L K C)"

lemmas split_induct[consumes 1, case_names split_empty split_cons, induct set: list_all3]
 = list_all3_induct[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]

lemmas split_empty = all3Nil[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]
lemmas split_cons = all3Cons[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]

lemmas split_Cons = list_all3_Cons[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]
lemmas split_Cons1 = list_all3_Cons1[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]
lemmas split_Cons2 = list_all3_Cons2[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]
lemmas split_Cons3 = list_all3_Cons3[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]

lemmas split_conv_all_nth = list_all3_conv_all_nth[where P="split_comp L K C" for L K C, simplified split_def[symmetric]]

definition pred :: "nat \<Rightarrow> nat" where
  "pred n \<equiv> (case n of Suc n' \<Rightarrow> n')"

inductive split_bang_comp :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> bool \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" ("_, _ , _ , _ \<turnstile> _ \<leadsto>b _ \<parallel> _" [55,0,0,0,0,0,55] 60) where
  none   : "L, K, C \<turnstile> x \<leadsto> a \<parallel> b \<Longrightarrow> L, K, C , False \<turnstile> x \<leadsto>b a \<parallel> b"
| dobang : "L, K, C \<turnstile> x wellformed \<Longrightarrow> L, K, C , True \<turnstile> Some x \<leadsto>b Some (bang x) \<parallel> Some x"

inductive split_bang :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> index set \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool"  ("_, _ , _ , _ \<turnstile> _ \<leadsto>b _ | _" [55,0,0,0,0,0,55] 60) where
  split_bang_empty : "L, K, C , is \<turnstile> [] \<leadsto>b [] | []"
| split_bang_cons  : "\<lbrakk> L, K, C , (pred ` Set.remove (0 :: index) is) \<turnstile> xs \<leadsto>b as | bs
                      ; L, K, C, (0 \<in> is) \<turnstile> x \<leadsto>b a \<parallel> b
                      \<rbrakk> \<Longrightarrow> L, K, C , is \<turnstile> x # xs \<leadsto>b a # as | b # bs"

lemma split_bang_Cons:
  "L, K, C , is \<turnstile> x # xs \<leadsto>b a # as | b # bs \<longleftrightarrow> (L, K, C, (0 \<in> is) \<turnstile> x \<leadsto>b a \<parallel> b \<and> L, K, C , (pred ` Set.remove (0 :: index) is) \<turnstile> xs \<leadsto>b as | bs)"
  by (auto elim: split_bang.cases intro: split_bang.intros)

inductive weakening_comp :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> type option \<Rightarrow> type option \<Rightarrow> bool" where
  none : "weakening_comp L K C None None"
| keep : "\<lbrakk> L, K, C \<turnstile> t wellformed \<rbrakk> \<Longrightarrow> weakening_comp L K C (Some t) (Some t)"
| drop : "\<lbrakk> L, K, C \<turnstile> t :\<kappa> k; D \<in> k \<rbrakk> \<Longrightarrow> weakening_comp L K C (Some t) None"

definition weakening :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_, _, _ \<turnstile> _ \<leadsto>w _" [30,0,0,0,20] 60) where
  "weakening L K C \<equiv> list_all2 (weakening_comp L K C)"

lemmas weakening_induct[consumes 1, case_names weakening_empty weakening_cons, induct set: list_all2]
 = list_all2_induct[where P="weakening_comp L K C" for L K C, simplified weakening_def[symmetric]]

lemmas weakening_nil = List.list.rel_intros(1)[where R="weakening_comp L K C" for L K C, simplified weakening_def[symmetric]]
lemmas weakening_cons =  List.list.rel_intros(2)[where R="weakening_comp L K C" for L K C, simplified weakening_def[symmetric]]

lemmas weakening_Cons = list_all2_Cons[where P="weakening_comp L K C" for L K C, simplified weakening_def[symmetric]]

lemmas weakening_conv_all_nth = list_all2_conv_all_nth[where P="weakening_comp L K C" for L K C, simplified weakening_def[symmetric]]


definition is_consumed :: "lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> ctx \<Rightarrow> bool" ("_, _, _ \<turnstile> _ consumed" [30,0,0,20] 60 ) where
  "L, K, C \<turnstile> \<Gamma> consumed \<equiv> L, K, C \<turnstile> \<Gamma> \<leadsto>w empty (length \<Gamma>)"

declare is_consumed_def [simp]

section {* Built-in types *}

primrec prim_op_type :: "prim_op \<Rightarrow> prim_type list \<times> prim_type" where
  "prim_op_type (Plus t)   = ([Num t, Num t], Num t)"
| "prim_op_type (Times t)  = ([Num t, Num t], Num t)"
| "prim_op_type (Minus t)  = ([Num t, Num t], Num t)"
| "prim_op_type (Divide t) = ([Num t, Num t], Num t)"
| "prim_op_type (Mod t)    = ([Num t, Num t], Num t)"
| "prim_op_type (BitAnd t) = ([Num t, Num t], Num t)"
| "prim_op_type (BitOr t)  = ([Num t, Num t], Num t)"
| "prim_op_type (BitXor t) = ([Num t, Num t], Num t)"
| "prim_op_type (LShift t) = ([Num t, Num t], Num t)"
| "prim_op_type (RShift t) = ([Num t, Num t], Num t)"
| "prim_op_type (Complement t) = ([Num t], Num t)"
| "prim_op_type (Gt t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Lt t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Le t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Ge t)     = ([Num t, Num t], Bool )"
| "prim_op_type (Eq t)     = ([t    , t    ], Bool )"
| "prim_op_type (NEq t)    = ([t    , t    ], Bool )"
| "prim_op_type (And)      = ([Bool , Bool ], Bool )"
| "prim_op_type (Or)       = ([Bool , Bool ], Bool )"
| "prim_op_type (Not)      = ([Bool],         Bool )"

primrec lit_type :: "lit \<Rightarrow> prim_type" where
  "lit_type (LBool _) = Bool"
| "lit_type (LU8  _)  = Num U8"
| "lit_type (LU16 _)  = Num U16"
| "lit_type (LU32 _)  = Num U32"
| "lit_type (LU64 _)  = Num U64"

fun upcast_valid :: "num_type \<Rightarrow> num_type \<Rightarrow> bool" where
  "upcast_valid U8  U8  = True"
| "upcast_valid U8  U16 = True"
| "upcast_valid U8  U32 = True"
| "upcast_valid U8  U64 = True"
| "upcast_valid U16 U16 = True"
| "upcast_valid U16 U32 = True"
| "upcast_valid U16 U64 = True"
| "upcast_valid U32 U32 = True"
| "upcast_valid U32 U64 = True"
| "upcast_valid U64 U64 = True"
| "upcast_valid _   _   = False"

primrec prim_lbool where
  "prim_lbool (LBool b) = b"
| "prim_lbool (LU8 w) = False"
| "prim_lbool (LU16 w) = False"
| "prim_lbool (LU32 w) = False"
| "prim_lbool (LU64 w) = False"

definition prim_word_op
  where prim_word_op_def[simp]:
  "prim_word_op f8 f16 f32 f64 xs = (case (take 2 xs) of
      [LU8 x, LU8 y] \<Rightarrow> LU8 (f8 x y)
    | [LU16 x, LU16 y] \<Rightarrow> LU16 (f16 x y)
    | [LU32 x, LU32 y] \<Rightarrow> LU32 (f32 x y)
    | [LU64 x, LU64 y] \<Rightarrow> LU64 (f64 x y)
    | _ \<Rightarrow> LBool False)"

definition prim_word_comp
  where prim_word_comp_def[simp]:
  "prim_word_comp f8 f16 f32 f64 xs = (case (take 2 xs) of
      [LU8 x, LU8 y] \<Rightarrow> LBool (f8 x y)
    | [LU16 x, LU16 y] \<Rightarrow> LBool (f16 x y)
    | [LU32 x, LU32 y] \<Rightarrow> LBool (f32 x y)
    | [LU64 x, LU64 y] \<Rightarrow> LBool (f64 x y)
    | _ \<Rightarrow> LBool False)"

primrec eval_prim_op :: "prim_op \<Rightarrow> lit list \<Rightarrow> lit"
where
    "eval_prim_op Not xs = LBool (\<not> prim_lbool (hd xs))"
  | "eval_prim_op And xs = LBool (prim_lbool (hd xs) \<and> prim_lbool (xs ! 1))"
  | "eval_prim_op Or xs = LBool (prim_lbool (hd xs) \<or> prim_lbool (xs ! 1))"
  | "eval_prim_op (Eq _) xs = LBool (hd xs = xs ! 1)"
  | "eval_prim_op (NEq _) xs = LBool (hd xs \<noteq> xs ! 1)"
  | "eval_prim_op (Plus _) xs = prim_word_op (+) (+) (+) (+) xs"
  | "eval_prim_op (Minus _) xs = prim_word_op (-) (-) (-) (-) xs"
  | "eval_prim_op (Times _) xs = prim_word_op (*) (*) (*) (*) xs"
  | "eval_prim_op (Divide _) xs = prim_word_op checked_div checked_div checked_div checked_div  xs"
  | "eval_prim_op (Mod _) xs = prim_word_op checked_mod checked_mod checked_mod checked_mod xs"
  | "eval_prim_op (Gt _) xs = prim_word_comp greater greater greater greater xs"
  | "eval_prim_op (Lt _) xs = prim_word_comp less less less less xs"
  | "eval_prim_op (Le _) xs = prim_word_comp less_eq less_eq less_eq less_eq xs"
  | "eval_prim_op (Ge _) xs = prim_word_comp greater_eq greater_eq greater_eq greater_eq xs"
  | "eval_prim_op (BitAnd _) xs = prim_word_op bitAND bitAND bitAND bitAND xs"
  | "eval_prim_op (BitOr _) xs = prim_word_op bitOR bitOR bitOR bitOR xs"
  | "eval_prim_op (BitXor _) xs = prim_word_op bitXOR bitXOR bitXOR bitXOR xs"
  | "eval_prim_op (LShift _) xs = prim_word_op (checked_shift shiftl) (checked_shift shiftl)
        (checked_shift shiftl) (checked_shift shiftl) xs"
  | "eval_prim_op (RShift _) xs = prim_word_op (checked_shift shiftr) (checked_shift shiftr)
        (checked_shift shiftr) (checked_shift shiftr) xs"
  | "eval_prim_op (Complement _) xs = prim_word_op (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x)
        (\<lambda>x y. bitNOT x) (\<lambda>x y. bitNOT x) [hd xs, hd xs]"

lemma eval_prim_op_lit_type:
  "prim_op_type pop = (\<tau>s, \<tau>) \<Longrightarrow> map lit_type xs = \<tau>s
    \<Longrightarrow> lit_type (eval_prim_op pop xs) = \<tau>"
  by (cases pop, auto split: lit.split)


definition subst_wellformed :: 
 "
 lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints
 \<Rightarrow> ptr_layout substitution \<Rightarrow>
 type substitution \<Rightarrow> 
 lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow>
 bool" ("_, _, _ \<turnstile> _, _ :s _, _, _" [30,0,0,0,0,0,0,20] 60) where
"L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C \<equiv> list_all2 (kinding L' K' C') \<delta> K \<and>
 (
length \<epsilon> = L \<and>
  (\<forall>(l,t) \<in> C. 
\<comment> \<open>I need theses hypotheses to prove that
the composite of two wellformed substitutions
is wellformed. With this hypothesis, I can then use
associativity of instantiate_lrepr and instantiate_lay\<close>
layout_wellformed L l \<longrightarrow>
lrepr_wellformed (length K) t \<longrightarrow>
matches_fields_layout L' C' 
 (instantiate_lrepr (map type_lrepr \<delta>) t) (instantiate_lay \<epsilon> l)
)
)"

section {* Typing rules *}

inductive typing :: "('f \<Rightarrow> poly_type) \<Rightarrow> lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> ctx \<Rightarrow> 'f expr \<Rightarrow> type \<Rightarrow> bool"
          ("_, _, _, _, _ \<turnstile> _ : _" [30,0,0,0,0,0,20] 60)
      and typing_all :: "('f \<Rightarrow> poly_type) \<Rightarrow> lay_env \<Rightarrow> kind env \<Rightarrow> lay_constraints \<Rightarrow> ctx \<Rightarrow> 'f expr list \<Rightarrow> type list \<Rightarrow> bool"
          ("_, _, _, _, _ \<turnstile>* _ : _" [30,0,0,0,0,0,20] 60) where

typing_var    : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto>w singleton (length \<Gamma>) i t
                   ; i < length \<Gamma>
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Var i : t"

| typing_afun   : "\<lbrakk> \<Xi> f = (L', K', C', t, u)
                   ; t' = instantiate ls ts t
                   ; u' = instantiate ls ts u
                   ; L, K, C \<turnstile> \<Gamma> consumed
                   ; L', K', C' \<turnstile> TFun t u wellformed
                   ; L, K, C \<turnstile> ls, ts :s L', K', C'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> AFun f ts ls : TFun t' u'"

| typing_fun    : "\<lbrakk> \<Xi>, L', K', C', [Some t] \<turnstile> f : u                 
                   ; t' = instantiate \<epsilon> \<delta> t
                   ; u' = instantiate \<epsilon> \<delta> u
                   ; L, K, C \<turnstile> \<Gamma> consumed
\<comment> \<open>why don't we ask for TFun t u to be well formed as
for abstract functions? Because we know that typing implies
wellformedness\<close>
                   ; L', K', C' \<turnstile> t wellformed
                   ; L, K, C \<turnstile> \<epsilon>, \<delta> :s L', K', C'
                   \<comment> \<open>These two additional requirements ensure that the layouts are good\<close>
                   \<comment> \<open>but then, do we still need K' \<turnstile> t wellformed ?\<close>
                 \<comment> \<open>  ; L, K, C \<turnstile> t' wellformed
                   ; L, K, C \<turnstile> u' wellformed\<close>
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Fun f \<delta> \<epsilon> : TFun t' u'"
(* The original one *)
(*
| typing_fun_orig    : "\<lbrakk> \<Xi>, L, K, C', [Some t] \<turnstile> f : u                 
                   ; t' = instantiate ts t
                   ; u' = instantiate ts u
                   ; L, K, C \<turnstile> \<Gamma> consumed
                   ; K' \<turnstile> t wellformed
                   ; list_all2 (kinding L K C) ts K'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Fun f ts ls : TFun t' u'"
*)
(* | typing_fun_alt : "\<lbrakk> \<Xi>, L, K, C, [Some t] \<turnstile> f : u                 
                    ; L, K, C \<turnstile> \<Gamma> consumed                  
                    \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Fun f ts : TFun t u"
*)

| typing_app    : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> a : TFun x y
                   ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile> b : x
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> App a b : y"

| typing_cast   : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile> e : TPrim (Num \<tau>)
                   ; upcast_valid \<tau> \<tau>'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Cast \<tau>' e : TPrim (Num \<tau>')"

| typing_tuple  : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> t : T
                   ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile> u : U
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Tuple t u : TProduct T U"

| typing_split  : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> x : TProduct t u
                   ; \<Xi>, L, K, C, (Some t)#(Some u)#\<Gamma>2 \<turnstile> y : t'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Split x y : t'"

| typing_let    : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> x : t
                   ; \<Xi>, L, K, C, (Some t # \<Gamma>2) \<turnstile> y : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Let x y : u"

| typing_letb   : "\<lbrakk> L, K, C, is \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> x : t
                   ; \<Xi>, L, K, C, (Some t # \<Gamma>2) \<turnstile> y : u
                   ; L, K, C \<turnstile> t :\<kappa> k
                   ; E \<in> k
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> LetBang is x y : u"

| typing_con    : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile> x : t
                   ; (tag, t, Unchecked) \<in> set ts
                   ; L, K, C \<turnstile> TSum ts wellformed
                   ; ts = ts'
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Con ts tag x : TSum ts'"

| typing_case   : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> x : TSum ts
                   ; (tag, t, Unchecked) \<in> set ts
                   ; \<Xi>, L, K, C, (Some t # \<Gamma>2) \<turnstile> a : u
                   ; \<Xi>, L, K, C, (Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2) \<turnstile> b : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Case x tag a b : u"

| typing_esac   : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile> x : TSum ts
                   ; [(n, t, Unchecked)] = filter ((=) Unchecked \<circ> snd \<circ> snd) ts
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Esac x n : t"

| typing_if     : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> x : TPrim Bool
                   ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile> a : t
                   ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile> b : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> If x a b : t"

| typing_prim   : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile>* args : map TPrim ts
                   ; prim_op_type oper = (ts,t)
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Prim oper args : TPrim t"

| typing_lit    : "\<lbrakk> L, K, C \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Lit l : TPrim (lit_type l)"

| typing_slit   : "\<lbrakk> L, K, C \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> SLit s : TPrim String"

| typing_unit   : "\<lbrakk> L, K, C \<turnstile> \<Gamma> consumed
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Unit : TUnit"

| typing_struct : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile>* es : ts
                   ; distinct ns
                   ; length ns = length ts
                   ; ts' = zip ns (zip ts (replicate (length ts) Present))
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Struct ts es : TRecord ts' Unboxed"

| typing_member : "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile> e : TRecord ts s
                   ; L, K, C \<turnstile> TRecord ts s :\<kappa> k
                   ; S \<in> k
                   ; f < length ts
                   ; ts ! f = (n, t, Present)
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Member e f : t"

| typing_take   : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, Present)
                   ; L, K, C \<turnstile> t :\<kappa> k
                   ; S \<in> k \<or> taken = Taken
                   ; \<Xi>, L, K, C, (Some t # Some (TRecord (ts [f := (n,t,taken)]) s) # \<Gamma>2) \<turnstile> e' : u
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Take e f e' : u"

| typing_put    : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                   ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile> e : TRecord ts s
                   ; sigil_perm s \<noteq> Some ReadOnly
                   ; f < length ts
                   ; ts ! f = (n, t, taken)
                   ; L, K, C \<turnstile> t :\<kappa> k
                   ; D \<in> k \<or> taken = Taken
                   ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile> e' : t
                   \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Put e f e' : TRecord (ts [f := (n,t,Present)]) s"

| typing_promote: "\<lbrakk> \<Xi>, L, K, C, \<Gamma> \<turnstile> x : t' ; L, K, C \<turnstile> t' \<sqsubseteq> t \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile> Promote t x : t"

| typing_all_empty : "\<Gamma> = empty n \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile>* [] : []"

| typing_all_cons  : "\<lbrakk> L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2
                      ; \<Xi>, L, K, C, \<Gamma>1 \<turnstile>  e  : t
                      ; \<Xi>, L, K, C, \<Gamma>2 \<turnstile>* es : ts
                      \<rbrakk> \<Longrightarrow> \<Xi>, L, K, C, \<Gamma> \<turnstile>* (e # es) : (t # ts)"


inductive_cases typing_num     [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> e : TPrim (Num \<tau>)"
inductive_cases typing_bool    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> e : TPrim Bool"
inductive_cases typing_varE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Var i : \<tau>"
inductive_cases typing_appE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> App x y : \<tau>"
inductive_cases typing_litE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Lit l : \<tau>"
inductive_cases typing_slitE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> SLit l : \<tau>"
inductive_cases typing_funE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Fun f ts ls : \<tau>"
inductive_cases typing_afunE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> AFun f ts ls : \<tau>"
inductive_cases typing_ifE     [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> If c t e : \<tau>"
inductive_cases typing_conE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Con ts t e : \<tau>"
inductive_cases typing_unitE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Unit : \<tau>"
inductive_cases typing_primE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Prim p es : \<tau>"
inductive_cases typing_memberE [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Member e f : \<tau>"
inductive_cases typing_tupleE  [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Tuple a b : \<tau>"
inductive_cases typing_caseE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Case x t m n : \<tau>"
inductive_cases typing_esacE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Esac e t : \<tau>"
inductive_cases typing_castE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Cast t e : \<tau>"
inductive_cases typing_letE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Let a b : \<tau>"
inductive_cases typing_structE [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Struct ts es : \<tau>"
inductive_cases typing_letbE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> LetBang vs a b : \<tau>"
inductive_cases typing_takeE   [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Take x f e : \<tau>"
inductive_cases typing_putE    [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Put x f e : \<tau>"
inductive_cases typing_splitE  [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Split x e : \<tau>"
inductive_cases typing_promoteE[elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile> Promote \<tau>' x : \<tau>"
inductive_cases typing_all_emptyE [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile>* []       : \<tau>s"
inductive_cases typing_all_consE  [elim]: "\<Xi>, L, K, C, \<Gamma> \<turnstile>* (x # xs) : \<tau>s"

section {* Syntax structural judgements *}

subsection {* A-normal form *}

inductive atom ::"'f expr \<Rightarrow> bool" where
  "atom (Var x)"
| "atom (Fun f ts ls)"
| "atom (AFun f ts ls)"
| "atom (Prim p (map Var is))"
| "atom (Con ts n (Var x))"
| "atom (Struct ts (map Var is))"
| "atom (Cast t (Var x))"
| "atom (Member (Var x) f)"
| "atom Unit"
| "atom (Lit l)"
| "atom (SLit l)"
| "atom (Tuple (Var x) (Var y))"
| "atom (Esac (Var x) t)"
| "atom (App (Var a) (Var b))"
| "atom (App (Fun f ts ls) (Var b))"
| "atom (App (AFun f ts ls) (Var b))"
| "atom (Put (Var x) f (Var y))"

inductive a_normal :: "'f expr \<Rightarrow> bool" where
  "\<lbrakk> atom x \<rbrakk> \<Longrightarrow> a_normal x"
| "\<lbrakk> atom x ; a_normal y \<rbrakk> \<Longrightarrow> a_normal (Let x y)"
| "\<lbrakk> a_normal x ; a_normal y \<rbrakk> \<Longrightarrow> a_normal (LetBang is x y)"
| "\<lbrakk> a_normal m ; a_normal n \<rbrakk> \<Longrightarrow> a_normal (Case (Var x) t m n)"
| "\<lbrakk> a_normal t ; a_normal e \<rbrakk> \<Longrightarrow> a_normal (If (Var x) t e)"
| "\<lbrakk> a_normal y \<rbrakk> \<Longrightarrow> a_normal (Split (Var x) y)"
| "\<lbrakk> a_normal y \<rbrakk> \<Longrightarrow> a_normal (Take (Var x) f y)"

inductive_cases a_normal_E:  "a_normal x"
inductive_cases a_normal_LetE:  "a_normal (Let x y)"
inductive_cases a_normal_LetBangE: "a_normal (LetBang is x y)"
inductive_cases a_normal_CaseE: "a_normal (Case x t m n)"
inductive_cases a_normal_IfE: "a_normal (If x t e)"
inductive_cases a_normal_Split: "a_normal (Split x y)"
inductive_cases a_normal_TakeE:  "a_normal (Take x f e)"


section {* Wellformed lemmas *}

lemma wellformed_record_wellformed_elem:
  assumes "L, K, C \<turnstile> TRecord ts s wellformed"
    and "(name, t, taken) \<in> set ts"
  shows "L, K, C \<turnstile> t wellformed"
  by (metis assms fst_conv in_set_conv_nth list_all_length snd_conv type_wellformed.simps(8) type_wellformed_pretty_def)

lemma wellformed_sum_wellformed_elem:
  assumes "L, K, C \<turnstile> TSum ts wellformed"
    and "(name, t, taken) \<in> set ts"
  shows "L, K, C \<turnstile> t wellformed"
  by (metis assms fst_conv in_set_conv_nth list_all_length snd_conv type_wellformed.simps(6) type_wellformed_pretty_def)


lemma type_lrepr_wellformed : "type_wellformed L n C t \<Longrightarrow> 
  lrepr_wellformed n (type_lrepr t)"
  by(induct t rule:type_lrepr.induct) (fastforce simp add:list_all_iff)+

 (*
lemma lrepr_wellformed_mono :
  "lrepr_wellformed n t \<Longrightarrow>
 n \<le> n'  \<Longrightarrow>
lrepr_wellformed n'  t"
  by (induct t)(fastforce simp add:list_all_iff)+
*)
lemma layout_wellformed_mono :
  "layout_wellformed n t \<Longrightarrow>
 n \<le> n'  \<Longrightarrow>
layout_wellformed n'  t"
  by (induct t)(fastforce simp add:list_all_iff)+


lemma type_wellformed_mono :
  "type_wellformed L n C t \<Longrightarrow>
L \<le> L' \<Longrightarrow> n \<le> n' \<Longrightarrow> C \<subseteq> C' \<Longrightarrow>
 type_wellformed L' n' C' t"
proof(induct t)
  case (TRecord perm s)
  then show ?case 
  proof(induct s rule:sigil_lay_cases)
    case (BoxedLay p ptrl)
    then show ?case 
      by (fastforce intro:layout_wellformed_mono simp add:list_all_iff matches_fields_layout_def match_constraint_def)                
  qed (fastforce simp add:list_all_iff)+
qed (fastforce simp add:list_all_iff)+


lemma match_type_sigil_empty_constraint:
"matches_type_sigil 0 C t s \<Longrightarrow>
lrepr_wellformed 0 t 
\<Longrightarrow>
matches_type_sigil 0 {} t s"
proof(induct s rule:sigil_lay_cases)
  case (BoxedLay p ptrl)
  then show ?case 
    by(simp add:matches_fields_layout_def match_constraint_def)
qed simp+

lemma wellformed_empty_constraint :
  "0, [], C \<turnstile> t wellformed \<Longrightarrow> 0, [], {} \<turnstile> t wellformed"
proof(induct t)
  case (TRecord perm s)
  then show ?case 

    
    by (fastforce intro: match_type_sigil_empty_constraint simp add:list_all_iff prod.case_distrib type_lrepr_wellformed) 
qed (fastforce simp add:list_all_iff)+



section {* Kinding lemmas *}

(* kinding in terms of the higher level kinding judgements *)
lemma kinding_simps:
  "\<And>L K C i k.      L, K, C \<turnstile> (TVar i) :\<kappa> k         \<longleftrightarrow> i < length K \<and> k \<subseteq> K ! i"
  "\<And>L K C i k.      L, K, C \<turnstile> (TVarBang i) :\<kappa> k     \<longleftrightarrow> i < length K \<and> k \<subseteq> {D,S}"
  "\<And>L K C n ts s k. L, K, C \<turnstile> (TCon n ts s) :\<kappa> k    \<longleftrightarrow> (L, K, C \<turnstile>* ts :\<kappa> k) \<and> k \<subseteq> sigil_kind s"
  "\<And>L K C ta tb k.  L, K, C \<turnstile> (TFun ta tb) :\<kappa> k     \<longleftrightarrow> k \<subseteq> UNIV \<and> (L, K, C \<turnstile> ta wellformed) \<and> (L, K, C \<turnstile> tb wellformed)"
  "\<And>L K C p k.      L, K, C \<turnstile> (TPrim p) :\<kappa> k        \<longleftrightarrow> k \<subseteq> UNIV"
  "\<And>L K C ts k.     L, K, C \<turnstile> (TSum ts) :\<kappa> k        \<longleftrightarrow> (L, K, C \<turnstile>* ts :\<kappa>v k) \<and> distinct (map fst ts)"
  "\<And>L K C ta tb k.  L, K, C \<turnstile> (TProduct ta tb) :\<kappa> k \<longleftrightarrow> (L, K, C \<turnstile> ta :\<kappa> k) \<and> (L, K, C \<turnstile> tb :\<kappa> k)"
  "\<And>L K C ts s k.   L, K, C \<turnstile> (TRecord ts s) :\<kappa> k   \<longleftrightarrow> (L, K, C \<turnstile>* ts :\<kappa>r k) \<and> k \<subseteq> sigil_kind s \<and> distinct (map fst ts)
                                                   \<and> matches_type_sigil L C (LRRecord (map (\<lambda>(n,t,_). (n, type_lrepr t)) ts)) s"
  "\<And>L K C k.        L, K, C \<turnstile> TUnit :\<kappa> k            \<longleftrightarrow> k \<subseteq> UNIV"
  by (auto simp add: kinding_defs list_all_iff)

lemma kinding_all_simps:
  "\<And>L K C k.        L, K, C \<turnstile>* [] :\<kappa> k       \<longleftrightarrow> True"
  "\<And>L K C t ts k.   L, K, C \<turnstile>* (t # ts) :\<kappa> k \<longleftrightarrow> (L, K, C \<turnstile> t :\<kappa> k) \<and> (L, K, C \<turnstile>* ts :\<kappa> k)"
  by (auto simp add: kinding_defs list_all_iff)

lemma kinding_variant_simps:
  "\<And>L K C k.        L, K, C \<turnstile>* [] :\<kappa>v k                     \<longleftrightarrow> True"
  "\<And>L K C n t ts k. L, K, C \<turnstile>* ((n,t,Unchecked) # ts) :\<kappa>v k \<longleftrightarrow> (L, K, C \<turnstile> t :\<kappa> k) \<and> (L, K, C \<turnstile>* ts :\<kappa>v k)"
  "\<And>L K C n t ts k. L, K, C \<turnstile>* ((n,t,Checked) # ts) :\<kappa>v k   \<longleftrightarrow> (L, K, C \<turnstile> t wellformed) \<and> (L, K, C \<turnstile>* ts :\<kappa>v k)"
  by (auto simp add: kinding_defs list_all_iff)

lemma kinding_record_simps:
  "\<And>L K C k.        L, K, C \<turnstile>* [] :\<kappa>r k                   \<longleftrightarrow> True"
  "\<And>L K C n t ts k. L, K, C \<turnstile>* ((n,t,Present) # ts) :\<kappa>r k \<longleftrightarrow> (L, K, C \<turnstile> t :\<kappa> k) \<and> (L, K, C \<turnstile>* ts :\<kappa>r k)"
  "\<And>L K C n t ts k. L, K, C \<turnstile>* ((n,t,Taken) # ts) :\<kappa>r k   \<longleftrightarrow> (L, K, C \<turnstile> t wellformed) \<and> (L, K, C \<turnstile>* ts :\<kappa>r k)"
  by (auto simp add: kinding_defs list_all_iff)

lemma kinding_imp_wellformed:
  "L, K, C \<turnstile> t :\<kappa> k \<Longrightarrow> L, K, C \<turnstile> t wellformed"
  by (simp add: kinding_def)

lemma kinding_iff_wellformed:
  shows
    "(\<exists>k. L, K, C \<turnstile> t :\<kappa> k) \<longleftrightarrow> L, K, C \<turnstile> t wellformed"
    "(\<exists>k. L, K, C \<turnstile>* ts :\<kappa> k) \<longleftrightarrow> L, K, C \<turnstile>* ts wellformed"
    "(\<exists>k. L, K, C \<turnstile>* tvs :\<kappa>v k) \<longleftrightarrow> L, K, C \<turnstile>* map (fst \<circ> snd) tvs wellformed"
    "(\<exists>k. L, K, C \<turnstile>* trs :\<kappa>r k) \<longleftrightarrow> L, K, C \<turnstile>* map (fst \<circ> snd) trs wellformed"
  by (auto simp add: kinding_defs)

lemma kinding_to_wellformedD:
  shows
    "L, K, C \<turnstile> t :\<kappa> k \<Longrightarrow> L, K, C \<turnstile> t wellformed"
    "L, K, C \<turnstile>* ts :\<kappa> k \<Longrightarrow> L, K, C \<turnstile>* ts wellformed"
    "L, K, C \<turnstile>* tvs :\<kappa>v k \<Longrightarrow> L, K, C \<turnstile>* map (fst \<circ> snd) tvs wellformed"
    "L, K, C \<turnstile>* trs :\<kappa>r k \<Longrightarrow> L, K, C \<turnstile>* map (fst \<circ> snd) trs wellformed"
  by (auto simp add: kinding_defs)

lemma subst_wellformed_list_all2_kindingD:
  "L, K, C \<turnstile>  ls, ts :s L', K', C' \<Longrightarrow> list_all2 (kinding L K C) ts K'"
  by (simp add: subst_wellformed_def)


lemma list_all2_kinding_wellformedD:
  "list_all2 (kinding L K C) ts K' \<Longrightarrow> list_all (type_wellformed L (length K) C) ts \<and> length ts = length K'"
  by (simp add: kinding_def list_all2_conv_all_nth list_all_length)

lemma supersumption:
fixes k' :: kind
assumes k_is_superset : "k' \<subseteq> k"
shows "L, K, C \<turnstile>  t  :\<kappa> k  \<Longrightarrow> L, K, C \<turnstile>  t  :\<kappa> k'"
and   "L, K, C \<turnstile>* ts :\<kappa> k  \<Longrightarrow> L, K, C \<turnstile>* ts :\<kappa> k'"
and   "L, K, C \<turnstile>* xs :\<kappa>v k \<Longrightarrow> L, K, C \<turnstile>* xs :\<kappa>v k'"
and   "L, K, C \<turnstile>* fs :\<kappa>r k \<Longrightarrow> L, K, C \<turnstile>* fs :\<kappa>r k'"
  using k_is_superset
  by (fastforce simp add: kinding_defs)+

lemma kind_top:
shows "k \<subseteq> {D, S, E}"
by (force intro: kind_comp.exhaust)

lemma kinding_all_nth:
fixes n :: nat
assumes "L, K, C \<turnstile>* ts :\<kappa> k"
and     "n < length ts"
shows   "L, K, C \<turnstile> (ts ! n) :\<kappa> k"
using assms proof (induct ts arbitrary: n)
     case Nil  then show ?case by auto
next case Cons then show ?case by (case_tac n, auto simp add: kinding_defs)
qed

lemma kinding_all_set:
  shows "(L, K, C \<turnstile>* ts :\<kappa> k) = (\<forall>t\<in>set ts. L, K, C \<turnstile> t :\<kappa> k)"
  by (auto simp add: kinding_defs)

lemma kinding_all_subset:
assumes "L, K, C \<turnstile>* ts :\<kappa> k"
and     "set us \<subseteq> set ts"
shows   "L, K, C \<turnstile>* us :\<kappa> k"
using assms by (auto simp add: kinding_all_set)

lemma kinding_all_list_all:
  shows "(L, K, C \<turnstile>* ts :\<kappa> k) = list_all (\<lambda>t. L, K, C \<turnstile> t :\<kappa> k) ts"
  by (induct ts; fastforce simp add: kinding_defs)

lemma kinding_typelist_wellformed_elem:
  assumes "L, K, C \<turnstile>* ts :\<kappa> k"
    and "t \<in> set ts"
  shows "L, K, C \<turnstile> t wellformed"
  using assms kinding_all_set kinding_def by auto

lemma kinding_in_kind_helper:
  assumes
    "x \<in> k"
    "L, K, C \<turnstile> t :\<kappa> k"
  shows "L, K, C \<turnstile> t :\<kappa> {x}"
  using assms
  unfolding kinding_def
  by blast

lemma kinding_variant_cons:
  shows "(L, K, C \<turnstile>* t # ts :\<kappa>v k) \<longleftrightarrow> (case snd (snd t) of Checked \<Rightarrow> L, K, C \<turnstile> fst (snd t) wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> fst (snd t) :\<kappa> k) \<and> (L, K, C \<turnstile>* ts :\<kappa>v k)"
  by (cases t, case_tac c; force simp add: kinding_defs)

lemma kinding_variant_conv_all_nth:
  shows "(L, K, C \<turnstile>* ts :\<kappa>v k) \<longleftrightarrow> (\<forall>i < length ts. case snd (snd (ts ! i)) of
                                                Checked \<Rightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) wellformed
                                              | Unchecked \<Rightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) :\<kappa> k)"
proof (induct ts)
  case (Cons a ts)
  then show ?case
    by (cases "snd (snd a)";
        clarsimp simp add: kinding_variant_cons All_less_Suc2,
        metis nth_Cons_Suc)
qed (simp add: kinding_defs)

lemma kinding_variant_set:
  shows "(L, K, C \<turnstile>* ts :\<kappa>v k) = (\<forall>(n,t,b)\<in>set ts. case b of Checked \<Rightarrow> L, K, C \<turnstile> t wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> t :\<kappa> k)"
proof (induct ts)
  case (Cons a ts)
  then show ?case
    by (cases a; case_tac c; clarsimp simp add: kinding_variant_cons)
qed (simp add: kinding_defs)

lemma kinding_variant_wellformed_elem:
  assumes "L, K, C \<turnstile>* ts :\<kappa>v k"
    and "(n,t,b) \<in> set ts"
  shows "L, K, C \<turnstile> t wellformed"
  using assms
  by (induct ts; force simp add: kinding_defs)

lemma kinding_variant_all_wellformed:
  assumes
    "L, K, C \<turnstile>* ts :\<kappa>v k"
    "(n,t,b) \<in> set ts"
  shows   "L, K, C \<turnstile> t wellformed"
  using assms
  by (case_tac b; force simp add: kinding_variant_set kinding_defs)

lemma kinding_all_variant':
  assumes "L, K, C \<turnstile>* map (fst \<circ> snd) ts :\<kappa> k"
  shows   "L, K, C \<turnstile>* ts :\<kappa>v k"
  using assms
proof (induct ts)
  case (Cons a ts)
  then show ?case
    by (case_tac a; case_tac c; simp add: kinding_defs)
qed (force simp add: kinding_defs)

lemma variant_tagged_list_update_wellformedI:
  assumes
    "n \<in> fst ` set ts"
    "distinct (map fst ts)"
    "L, K, C \<turnstile> t wellformed"
    "L, K, C \<turnstile>* map (fst \<circ> snd) ts wellformed"
  shows "L, K, C \<turnstile> TSum (tagged_list_update n (t, b) ts) wellformed"
  using assms
  by (induct ts arbitrary: n t b; fastforce simp add: list_all_iff)

lemma variant_tagged_list_update_kinding:
  assumes "n \<in> fst ` set ts"
  shows
    "L, K, C \<turnstile>* (tagged_list_update n (\<tau>, Checked) ts) :\<kappa>v k \<Longrightarrow> L, K, C \<turnstile> \<tau> wellformed"
    "L, K, C \<turnstile>* (tagged_list_update n (\<tau>, Unchecked) ts) :\<kappa>v k \<Longrightarrow> L, K, C \<turnstile> \<tau> :\<kappa> k"
  using assms tagged_list_update_success_contains_updated_elem
  by (fastforce dest: bspec[where x="(n,\<tau>,Checked)"] simp add: kinding_variant_set)+

lemma kinding_variant_downcast:
  assumes
    "L, K, C \<turnstile>* ts :\<kappa>v k"
    "distinct (map fst ts)"
    "(tag, t, Unchecked) \<in> set ts"
  shows
    "L, K, C \<turnstile>* tagged_list_update tag (t, Checked) ts :\<kappa>v k"
proof -
  obtain i
    where tag_elem_at:
      "ts ! i = (tag, t, Unchecked)"
      "i < length ts"
    using assms by (meson in_set_conv_nth)
  then have
    "L, K, C \<turnstile> t :\<kappa> k"
    "\<forall>(n, t, b) \<in> set ts. case b of Checked \<Rightarrow> L, K, C \<turnstile> t wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> t :\<kappa> k"
    using assms kinding_variant_conv_all_nth kinding_variant_set by auto
  then have "\<forall>(n, t, b) \<in> insert (tag, t, Checked) (set ts). case b of Checked \<Rightarrow> L, K, C \<turnstile> t wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> t :\<kappa> k"
    by (clarsimp simp add: Ball_def kinding_def split: variant_state.splits)
  then have "\<forall>(n, t, b) \<in> set (ts[i := (tag, t, Checked)]). case b of Checked \<Rightarrow> L, K, C \<turnstile> t wellformed | Unchecked \<Rightarrow> L, K, C \<turnstile> t :\<kappa> k"
    by (metis (no_types, lifting) set_update_subset_insert subsetCE)
  then show ?thesis
    using tag_elem_at assms
    by (simp add: kinding_variant_set tagged_list_update_distinct)
qed


lemma kinding_record_cons:
  shows "(L, K, C \<turnstile>* t # ts :\<kappa>r k) \<longleftrightarrow> (case snd (snd t) of Taken \<Rightarrow> L, K, C \<turnstile> fst (snd t) wellformed | Present \<Rightarrow> L, K, C \<turnstile> fst (snd t) :\<kappa> k) \<and> (L, K, C \<turnstile>* ts :\<kappa>r k)"
  by (cases t; case_tac c; force simp add: kinding_defs)

lemma kinding_record_conv_all_nth:
  shows "(L, K, C \<turnstile>* ts :\<kappa>r k) \<longleftrightarrow> (\<forall>i < length ts. case snd (snd (ts ! i)) of
                                                Taken \<Rightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) wellformed
                                              | Present \<Rightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) :\<kappa> k)"
proof (induct ts)
  case (Cons a ts)
  then show ?case
    apply (clarsimp simp add: kinding_record_cons All_less_Suc2)
    apply (metis nth_Cons_0 nth_Cons_Suc)
    done
qed (simp add: kinding_defs)

lemma kinding_record_set:
  shows "(L, K, C \<turnstile>* ts :\<kappa>r k) = (\<forall>(n,t,b)\<in>set ts. case b of Taken \<Rightarrow> L, K, C \<turnstile> t wellformed | Present \<Rightarrow> L, K, C \<turnstile> t :\<kappa> k)"
proof (induct ts)
  case (Cons a ts)
  then show ?case
    by (cases a; case_tac c; clarsimp simp add: kinding_record_cons)
qed (simp add: kinding_defs)

lemma kinding_record_wellformed_elem:
  assumes "L, K, C \<turnstile>* ts :\<kappa>r k"
    and "(name,t,taken) \<in> set ts"
  shows "L, K, C \<turnstile> t wellformed"
  using assms
  by (induct ts; force simp add: kinding_defs)

lemma kinding_record_wellformed_nth:
assumes "L, K, C \<turnstile>* ts :\<kappa>r k"
and     "ts ! n = (name,t,taken)"
and     "n < length ts"
shows   "L, K, C \<turnstile> t wellformed"
using assms(1)
  and assms(2) [THEN sym]
  and assms(3) by (force intro: kinding_record_wellformed_elem[simplified]
                         simp:  set_conv_nth)

lemma kinding_all_record:
  assumes
    "L, K, C \<turnstile>* ts :\<kappa> k"
    "length ns = length ts"
  shows
    "L, K, C \<turnstile>* zip ns (zip ts (replicate (length ts) Present)) :\<kappa>r k"
  using assms
proof (induct ts arbitrary: ns)
  case (Cons a ts)
  moreover then obtain n ns' where "ns = n # ns'"
    by (metis Suc_length_conv length_Cons)
  ultimately show ?case
    by (fastforce simp add: length_Cons kinding_defs)
qed (force simp add: kinding_defs)

lemma kinding_all_record':
  assumes "L, K, C \<turnstile>* map (fst \<circ> snd) ts :\<kappa> k"
  shows   "L, K, C \<turnstile>* ts :\<kappa>r k"
  using assms
proof (induct ts)
  case (Cons a ts)
  then show ?case
    by (case_tac a; case_tac c; auto simp add: kinding_defs)
qed (force simp add: kinding_defs)

lemma kinding_record_update:
  assumes "L, K, C \<turnstile>* ts :\<kappa>r k"
    and "ts ! n = (name, a, b)"
    and "L, K, C \<turnstile> a :\<kappa> k'"
  shows "L, K, C \<turnstile>* (ts[ n := (name, a, Present)]) :\<kappa>r (k \<inter> k')"
  using assms
proof (induct ts arbitrary: n)
  case (Cons a ts)
  then show ?case
    by (force intro!: Cons.hyps simp add: nth_Cons kinding_defs split: nat.splits)
qed (force simp add: kinding_defs)

lemma sigil_kind_writable:
  assumes "sigil_perm s = Some Writable"
    and " k \<subseteq> sigil_kind (Boxed Writable p)"
  shows "k \<subseteq> sigil_kind s"
  using assms
  by (case_tac s rule: sigil_cases, auto)


section {* Bang lemmas *}

lemma bang_sigil_idempotent:
shows "bang_sigil (bang_sigil s) = bang_sigil s"
  by (cases s rule: bang_sigil.cases, simp+)

lemma bang_idempotent:
shows "bang (bang \<tau>) = bang \<tau>"
by (force intro: bang.induct [where P = "\<lambda> \<tau> . bang (bang \<tau>) = bang \<tau>"]
          simp:  bang_sigil_idempotent)

lemma bang_sigil_kind:
shows "{D , S} \<subseteq> sigil_kind (bang_sigil s)"
  by (case_tac s rule: bang_sigil.cases, auto)


lemma bang_sigil_boxed : " bang_sigil (Boxed r ptrl) = 
Boxed ReadOnly ptrl"
  by(cases r;simp)


lemma bang_matches_type_sigil:
  "
matches_type_sigil L C t (bang_sigil s) =
matches_type_sigil L C t s 
   "
  by(induct s rule:sigil_lay_cases)  (simp add:bang_sigil_boxed)+
 
  
lemma bang_lrepr : "type_lrepr (bang t) = type_lrepr t"
  by (induct t rule:type_lrepr.induct;clarsimp simp add:bang_sigil_boxed )
(*
lemma bang_lrepr_trecord : "type_lrepr (TRecord (map_field_type bang ts) (bang_sigil s)) = 
   type_lrepr (TRecord ts s)"
  by (rule bang_lrepr[of "TRecord ts s", simplified])
  *)
  

lemma bang_wellformed:
  "type_wellformed L C n t \<Longrightarrow> type_wellformed L C n (bang t)"
  apply(induct t rule: type_wellformed.induct)           
          apply   (clarsimp simp add: list.pred_map list_all_iff  bang_matches_type_sigil)+
   apply(clarsimp simp add:prod.case_distrib comp_def bang_lrepr)+
  done
  

lemma bang_kinding_fn:
  shows "{D,S} \<subseteq> kinding_fn K (bang t)"
proof (induct K t rule: kinding_fn_induct)
  case (kind_tcon K n ts s)
  then show ?case
    using bang_sigil_kind by (simp add: list_all_iff)
next
  case (kind_tsum K ts)
  then show ?case
    by (fastforce simp add: list_all_iff simp del: insert_subset split: variant_state.split)
next
  case (kind_trec K ts s)
  then show ?case
    using bang_sigil_kind
    by (fastforce simp add: list_all_iff simp del: insert_subset split: record_state.split)
qed auto

lemma bang_kind:
shows "L, K, C \<turnstile>  t  wellformed \<Longrightarrow> k \<subseteq> {D, S} \<Longrightarrow> L, K, C \<turnstile> bang t :\<kappa> k"
and   "L, K, C \<turnstile>* ts wellformed \<Longrightarrow> k \<subseteq> {D, S} \<Longrightarrow> L, K, C \<turnstile>* map bang ts :\<kappa> k"
and   "L, K, C \<turnstile>* map (fst \<circ> snd) xs wellformed \<Longrightarrow> k \<subseteq> {D, S} \<Longrightarrow> L, K, C \<turnstile>* map (\<lambda>(n,t,b). (n, bang t, b)) xs :\<kappa>v k"
and   "L, K, C \<turnstile>* map (fst \<circ> snd) fs wellformed \<Longrightarrow> k \<subseteq> {D, S} \<Longrightarrow> L, K, C \<turnstile>* map (\<lambda>(n,t,b). (n, bang t, b)) fs :\<kappa>r k"
  using bang_wellformed bang_kinding_fn
  by (fastforce simp add: kinding_defs INT_subset_iff simp del: insert_subset
      split: variant_state.split record_state.split)+

section {* Subtyping lemmas *}

lemma subtyping_simps:
  shows
  "\<And>n1 n2. L, K, C \<turnstile> TVar n1 \<sqsubseteq> TVar n2 \<longleftrightarrow> n1 = n2"
  "\<And>n1 n2. L, K, C \<turnstile> TVarBang n1 \<sqsubseteq> TVarBang n2 \<longleftrightarrow> n1 = n2"
  "\<And>n1 ts1 s1 n2 ts2 s2. L, K, C \<turnstile> TCon n1 ts1 s1 \<sqsubseteq> TCon n2 ts2 s2 \<longleftrightarrow> n1 = n2 \<and> s1 = s2 \<and> ts1 = ts2"
  "\<And>t1 u1 t2 u2. L, K, C \<turnstile> TFun t1 u1 \<sqsubseteq> TFun t2 u2 \<longleftrightarrow> L, K, C \<turnstile> t2 \<sqsubseteq> t1 \<and> L, K, C \<turnstile> u1 \<sqsubseteq> u2"
  "\<And>p1 p2. L, K, C \<turnstile> TPrim p1 \<sqsubseteq> TPrim p2 \<longleftrightarrow> p1 = p2"
  "\<And>ts1 s1 ts2 s2. L, K, C \<turnstile> TRecord ts1 s1 \<sqsubseteq> TRecord ts2 s2
                    \<longleftrightarrow> list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) ts1 ts2
                    \<and> list_all2 (record_kind_subty L K C) ts1 ts2
                    \<and> map fst ts1 = map fst ts2
                    \<and> s1 = s2"
  "\<And>t1 u1 t2 u2. L, K, C \<turnstile> TProduct t1 u1 \<sqsubseteq> TProduct t2 u2 \<longleftrightarrow> L, K, C \<turnstile> t1 \<sqsubseteq> t2 \<and> L, K, C \<turnstile> u1 \<sqsubseteq> u2"
  "\<And>ts1 ts2. L, K, C \<turnstile> TSum ts1 \<sqsubseteq> TSum ts2
                    \<longleftrightarrow> list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) ts1 ts2
                    \<and> list_all2 (variant_kind_subty) ts1 ts2
                    \<and> map fst ts1 = map fst ts2"
  "L, K, C \<turnstile> TUnit \<sqsubseteq> TUnit"
  by (auto simp: subtyping.intros intro!: subtyping.intros elim!: subtyping.cases)

lemma subtyping_bang_preservation:
  assumes
    "L, K, C \<turnstile> t1 \<sqsubseteq> t2"
    "L, K, C \<turnstile> t1 wellformed"
  shows "L, K, C \<turnstile> bang t1 \<sqsubseteq> bang t2"
  using assms
proof (induct rule: subtyping.induct)
  case subty_tcon then show ?case
    by (force simp add: list_all2_conv_all_nth intro: subtyping.intros)
next
  case (subty_trecord L K C ts1 ts2 s1 s2)
  moreover then have "\<And>i k. i < length ts2 \<Longrightarrow> L, K, C \<turnstile> bang (fst (snd (ts1 ! i))) :\<kappa> {D}"
    by (auto simp add: list_all_length intro!: bang_kind, metis length_map)
  moreover have "\<And>i. i < length ts2 \<Longrightarrow> snd (snd (ts1 ! i)) \<le> snd (snd (ts2 ! i))"
    using subty_trecord.hyps
    by (force simp add: list_all2_conv_all_nth if_bool_eq_conj le_less)
  ultimately show ?case
    by (slowsimp simp add: subtyping_simps list_all2_conv_all_nth list_all_length le_less split: prod.splits)
next
  case subty_tsum then show ?case
    by (slowsimp intro!: subtyping.intros simp add: list_all2_conv_all_nth list_all_length split: prod.splits)
qed (simp add: subtyping_simps)+

lemma subtyping_lrepr : "L, K, C \<turnstile> t1 \<sqsubseteq> t2 \<Longrightarrow> type_lrepr t1 = type_lrepr t2"
proof(induct rule:subtyping.induct)
  case (subty_trecord L K C ts1 ts2 s1 s2)
  then show ?case
    by (cases s2)
     ( simp add: case_prod_beta' map_eq_iff_nth_eq list_all2_conv_all_nth  )+
next
  case (subty_tsum L K C ts1 ts2)
  then show ?case
    by (simp add: case_prod_beta' map_eq_iff_nth_eq list_all2_conv_all_nth  )+
    
qed (simp+)

lemma subtyping_refl: "L, K, C \<turnstile> t \<sqsubseteq> t"
proof (induct t)
  case (TSum ts)
  moreover then have "\<And>i. i < length ts \<Longrightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) \<sqsubseteq> fst (snd (ts ! i))"
    using fsts.intros snds.intros nth_mem by blast
  ultimately show ?case
    by (fastforce intro!: subtyping.intros simp add: list_all2_conv_all_nth list_all_length)
next
  case (TRecord ts s)
  moreover then have "\<And>i. i < length ts \<Longrightarrow> L, K, C \<turnstile> fst (snd (ts ! i)) \<sqsubseteq> fst (snd (ts ! i))"
    using fsts.intros snds.intros nth_mem by blast
  ultimately show ?case
    by (fastforce intro!: subtyping.intros simp add: list_all2_conv_all_nth list_all_length)
qed (auto intro!: subtyping.intros simp add: list.rel_refl_strong list_all_iff)

lemma subtyping_wellformed_preservation:
  assumes
    "L, K, C \<turnstile> t1 \<sqsubseteq> t2"
  shows
    "L, K, C \<turnstile> t1 wellformed \<Longrightarrow> L, K, C \<turnstile> t2 wellformed"
    "L, K, C \<turnstile> t2 wellformed \<Longrightarrow> L, K, C \<turnstile> t1 wellformed"
  using assms
proof (induct rule: subtyping.inducts)
  fix L K C 
  case (subty_tcon n1 n2 s1 s2 ts1 ts2)
  then show
    "L, K, C \<turnstile> TCon n1 ts1 s1 wellformed \<Longrightarrow> L, K, C \<turnstile> TCon n2 ts2 s2 wellformed"
    "L, K, C \<turnstile> TCon n2 ts2 s2 wellformed \<Longrightarrow> L, K, C \<turnstile> TCon n1 ts1 s1 wellformed"
    by (fastforce simp add: list_all2_conv_all_nth Ball_def in_set_conv_nth list_all_iff)+
next
  case (subty_trecord L K C ts1 ts2 s1 s2)
  moreover then have aux :
    "list_all (\<lambda>p1. L, K, C \<turnstile> fst (snd p1) wellformed) ts1 \<longleftrightarrow> list_all (\<lambda>p2. L, K, C \<turnstile> fst (snd p2) wellformed) ts2"
    by (clarsimp simp add: list_all2_mono iff_conv_conj_imp list_all2_conv_all_nth list_all_length)
  moreover then have 
  "map (\<lambda>(n, t, _). (n, type_lrepr t)) ts1 = 
   map (\<lambda>(n, t, _). (n, type_lrepr t)) ts2"   

    using subty_trecord
    
    
    
    by(fastforce dest:subtyping_lrepr split:prod.split simp add:
 list_all2_conv_all_nth map_eq_iff_nth_eq)
    

  ultimately show
    "L, K, C \<turnstile> TRecord ts1 s1 wellformed \<Longrightarrow> L, K, C \<turnstile> TRecord ts2 s2 wellformed"
    "L, K, C \<turnstile> TRecord ts2 s2 wellformed \<Longrightarrow> L, K, C \<turnstile> TRecord ts1 s1 wellformed"   
    by simp+
next
  case (subty_tsum L K C ts1 ts2)
  moreover then have
    "list_all (\<lambda>p1. L, K, C \<turnstile> fst (snd p1) wellformed) ts1 \<longleftrightarrow> list_all (\<lambda>p2. L, K, C \<turnstile> fst (snd p2) wellformed) ts2"
    by (clarsimp simp add: list_all2_mono iff_conv_conj_imp list_all2_conv_all_nth list_all_length)
  ultimately show
    "L, K, C \<turnstile> TSum ts1 wellformed \<Longrightarrow> L, K, C \<turnstile> TSum ts2 wellformed"
    "L, K, C \<turnstile> TSum ts2 wellformed \<Longrightarrow> L, K, C \<turnstile> TSum ts1 wellformed"
    by simp+
qed simp+




lemma subtyping_kinding_fn_drop_super_impl_drop_sub:
  assumes "L, K, C \<turnstile> p \<sqsubseteq> q"
  and "D \<in> kinding_fn K q"
  shows "D \<in> kinding_fn K p"
  using assms
proof (induct rule: subtyping.inducts)
  case (subty_trecord L K C pts qts ps qs)
  moreover have kind_pts:
    "\<And>n pt pb. (n, pt, pb) \<in> set pts \<Longrightarrow> D \<in> (case pb of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K pt)"
  proof -
    fix n tp bp
    assume elem_pts: "(n, tp, bp) \<in> set pts"
    then obtain i tq bq
      where elems_at_i:
        "i < length qts"
        "pts ! i = (n, tp, bp)"
        "qts ! i = (n, tq, bq)"
      using \<open>map fst pts = map fst qts\<close>
      by (simp add: in_set_conv_nth map_eq_iff_nth_eq, metis fst_conv surj_pair)
    moreover have ih_elim:
      "D \<in> kinding_fn K tq \<longrightarrow> D \<in> kinding_fn K tp"
      "bp = bq \<or> ((L, K, C \<turnstile> tp :\<kappa> {D}) \<and> bp < bq)"
      using subty_trecord.hyps elems_at_i
      by (auto simp add: list_all2_conv_all_nth map_eq_iff_nth_eq le_less)
    ultimately show "D \<in> (case bp of Taken \<Rightarrow> UNIV | Present \<Rightarrow> kinding_fn K tp)"
      using subty_trecord.prems
      by (force simp add: kinding_def all_set_conv_all_nth split: record_state.splits)
  qed
  ultimately show ?case
    by clarsimp
next
  case (subty_tsum L K C pts qts)
  moreover have kind_pts: "\<And>n pt pb. (n, pt, pb) \<in> set pts \<Longrightarrow> D \<in> (case pb of Checked \<Rightarrow> UNIV | Unchecked \<Rightarrow> kinding_fn K pt)"
  proof -
    fix n tp bp
    assume elem_pts: "(n, tp, bp) \<in> set pts"
    then obtain i tq bq
      where elems_at_i:
        "i < length qts"
        "pts ! i = (n, tp, bp)"
        "qts ! i = (n, tq, bq)"
      using \<open>map fst pts = map fst qts\<close>
      by (simp add: in_set_conv_nth map_eq_iff_nth_eq, metis fst_conv surj_pair)

    have
      "D \<in> kinding_fn K tq \<longrightarrow> D \<in> kinding_fn K tp"
      "bp \<le> bq"
      using subty_tsum.hyps elems_at_i
      by (auto simp add: list_all2_conv_all_nth map_eq_iff_nth_eq)
    moreover have "bq = Unchecked \<longrightarrow> D \<in> kinding_fn K tq"
      using subty_tsum.prems elems_at_i
      by (fastforce simp add: all_set_conv_all_nth split: prod.splits)
    ultimately show "D \<in> (case bp of Checked \<Rightarrow> UNIV | Unchecked \<Rightarrow> kinding_fn K tp)"
      using less_eq_variant_state.elims
      by (auto split: variant_state.splits)
  qed
  ultimately show ?case by auto
qed auto


lemma subtyping_drop_super_impl_drop_sub:
  assumes "L, K, C \<turnstile> p \<sqsubseteq> q"
  and "L, K, C \<turnstile> q :\<kappa> {D}"
  shows "L, K, C \<turnstile> p :\<kappa> {D}"
  using assms kinding_def subtyping_kinding_fn_drop_super_impl_drop_sub subtyping_wellformed_preservation(2) by auto

lemma subtyping_trans:
  assumes "L, K, C \<turnstile> p \<sqsubseteq> q"
  and     "L, K, C \<turnstile> q \<sqsubseteq> r"
  shows   "L, K, C \<turnstile> p \<sqsubseteq> r"
  using assms
proof (induct q arbitrary: p r rule: type.induct)
next
  case (TFun qt ut)
  show ?case
    using TFun.prems
    apply -
    apply (erule subtyping.cases; clarsimp)
    apply (erule subtyping.cases; clarsimp)
    apply (fast dest: TFun.hyps intro: subtyping.intros)
    done
next
  case (TSum qts)
  moreover obtain pts where p_elims:
    "p = TSum pts"
    "map fst pts = map fst qts"
    "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) pts qts"
    "list_all2 variant_kind_subty pts qts"
    using TSum.prems by (auto elim: subtyping.cases)
  moreover obtain rts where r_elims:
    "r = TSum rts"
    "map fst qts = map fst rts"
    "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) qts rts"
    "list_all2 (\<lambda>p1 p2. snd (snd p1) \<le> snd (snd p2)) qts rts"
    using TSum.prems by (auto elim: subtyping.cases)
  moreover have IH:
    "(\<And>i tp tq tr. i < length qts \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (pts ! i)) \<sqsubseteq> fst (snd (qts ! i)) \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (qts ! i)) \<sqsubseteq> fst (snd (rts ! i)) \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (pts ! i)) \<sqsubseteq> fst (snd (rts ! i)))"
    using TSum.hyps fsts.intros nth_mem snds.intros by blast
  moreover have "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) pts rts"
    using p_elims(3) r_elims(3) IH
    by (clarsimp simp add: list_all2_conv_all_nth)
  moreover have "list_all2 (\<lambda>p1 p2. snd (snd p1) \<le> snd (snd p2)) pts rts"
    using list_all2_trans[OF _ p_elims(4) r_elims(4)]
    by simp
  ultimately show ?case
    using subty_tsum
    by presburger
next
  case (TProduct x1a x2a)
  show ?case
    using TProduct.prems
    apply -
    apply (erule subtyping.cases; clarsimp)
    apply (erule subtyping.cases; clarsimp)
    apply (fast dest: TProduct.hyps intro: subtyping.intros)
    done
next
  case (TRecord qts s)

  obtain pts where p_elims:
    "p = TRecord pts s"
    "map fst pts = map fst qts"
    "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) pts qts"
    "list_all2 (record_kind_subty L K C) pts qts"
    using TRecord.prems by (auto elim: subtyping.cases)
  moreover obtain rts where r_elims:
    "r = TRecord rts s"
    "map fst qts = map fst rts"
    "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) qts rts"
    "list_all2 (record_kind_subty L K C) qts rts"
    using TRecord.prems by (auto elim: subtyping.cases)
  moreover have IH:
    "(\<And>i tp tq tr. i < length qts \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (pts ! i)) \<sqsubseteq> fst (snd (qts ! i)) \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (qts ! i)) \<sqsubseteq> fst (snd (rts ! i)) \<Longrightarrow>
      L, K, C \<turnstile> fst (snd (pts ! i)) \<sqsubseteq> fst (snd (rts ! i)))"
    using TRecord.hyps fsts.intros nth_mem snds.intros by blast
  moreover have "list_all2 (\<lambda>p1 p2. subtyping L K C (fst (snd p1)) (fst (snd p2))) pts rts"
    using p_elims(3) r_elims(3) IH
    by (clarsimp simp add: list_all2_conv_all_nth)
  moreover have sat_p_r: "\<And>i. i < length pts \<Longrightarrow> record_kind_subty L K C (pts ! i) (rts ! i)"
  proof -
    fix i
    assume i_len: "i < length pts"
    moreover have "L, K, C \<turnstile> (fst \<circ> snd) (pts ! i) \<sqsubseteq> (fst \<circ> snd) (qts ! i)"
      using i_len list_all2_lengthD list_all2_nthD2 p_elims by fastforce
    moreover have
      "record_kind_subty L K C (pts ! i) (qts ! i)"
      "record_kind_subty L K C (qts ! i) (rts ! i)"
      using p_elims r_elims i_len
      by (simp add: list_all2_conv_all_nth)+
    ultimately show "record_kind_subty L K C (pts ! i) (rts ! i)"
      by (auto
          simp add: if_bool_eq_conj kinding_defs not_less_iff_gr_or_eq
          dest: subtyping_wellformed_preservation subtyping_kinding_fn_drop_super_impl_drop_sub)
  qed
  ultimately show ?case
    using p_elims r_elims
    by (simp add: sat_p_r list_all2_conv_all_nth subty_trecord)
qed (fast elim: subtyping.cases)+


lemma subtyping_preserves_type_repr:
  "L, K, C \<turnstile> t \<sqsubseteq> t' \<Longrightarrow> type_repr t = type_repr t'"
proof (induct rule: subtyping.induct)
  case (subty_trecord L K C ts1 ts2 s1 s2)
  then show ?case
    by (cases s1; induct rule: list_all2_induct; auto)
next
  case (subty_tsum L K C ts1 ts2)
  then show ?case
    by (induct rule: list_all2_induct; auto)
qed auto

lemma subtyping_preserves_type_repr_map:
  "list_all2 (\<lambda>p1 p2. L, K, C \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) as bs
  \<Longrightarrow> map (type_repr \<circ> fst \<circ> snd) as = map (type_repr \<circ> fst \<circ> snd) bs"
  by (induct rule: list_all2_induct, auto simp add: subtyping_preserves_type_repr)


section {* Typing lemmas *}

lemma typing_all_Cons1I:
  assumes
    "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "\<exists>ta tsa. ts = ta # tsa \<and> \<Xi>, L, K, C, \<Gamma>1 \<turnstile>  e : ta \<and> \<Xi>, L, K, C, \<Gamma>2 \<turnstile>* es : tsa"
  shows "\<Xi>, L, K, C, \<Gamma> \<turnstile>* (e # es) : ts"
  using assms
  by (force intro: typing_all_cons)

lemma variant_elem_preservation:
  assumes tag_in_ts: "(tag, t, b) \<in> set ts"
    and tags_same: "map fst ts = map fst ts'"
    and types_same: "map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'"
    and taken_subcond: "list_all2 (\<lambda>x y. snd (snd x) \<le> snd (snd y)) ts ts'"
  shows "\<exists>b'. (tag, t, b') \<in> set ts' \<and> (b \<le> b')"
proof -
  obtain i
    where ts_at_i:
      "i < length ts"
      "ts ! i = (tag, t, b)"
    by (meson tag_in_ts in_set_conv_nth)
  moreover then obtain b' where ts'_at_i: "ts' ! i = (tag, t, b')"
    by (metis comp_eq_dest_lhs eq_fst_iff length_map nth_map snd_conv tags_same types_same)
  ultimately show ?thesis
    using taken_subcond ts_at_i ts'_at_i nth_mem
    by (fastforce simp add: list_all2_conv_all_nth)
qed

lemma variant_elem_preservation_reverse:
  assumes tag_in_ts': "(tag', t', b') \<in> set ts'"
    and tags_same: "map fst ts = map fst ts'"
    and types_same: "map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'"
    and taken_subcond: "list_all2 (\<lambda>x y. snd (snd x) \<le> snd (snd y)) ts ts'"
  shows "\<exists>b. (tag', t', b) \<in> set ts \<and> (b \<le> b')"
proof -
  obtain i
    where ts'_at_i:
      "i < length ts'"
      "ts' ! i = (tag', t', b')"
    by (meson tag_in_ts' in_set_conv_nth)
  then obtain b where ts_at_i: "ts ! i = (tag', t', b)"
    by (metis comp_eq_dest_lhs eq_fst_iff length_map nth_map snd_conv tags_same types_same)
  moreover have "b \<le> b'"
    using taken_subcond ts_at_i ts'_at_i
    by (fastforce simp add: list_all2_conv_all_nth)
  ultimately show ?thesis
    using taken_subcond ts_at_i ts'_at_i nth_mem
    by (metis length_map tags_same)
qed

section {* Instantiation *}

lemma instantiate_sigil_bang [simp] :
  "instantiate_sigil \<epsilon> (bang_sigil s) = bang_sigil (instantiate_sigil \<epsilon> s)"
proof(cases s)
  case (Boxed perm ptrl)
  then show ?thesis 
    by(cases ptrl) (simp add:bang_sigil_boxed)+    
qed (simp)



lemma instantiate_bang [simp]:
  shows "instantiate \<epsilon> \<delta> (bang \<tau>) = bang (instantiate \<epsilon> \<delta> \<tau>)"
  by (force intro: bang.induct [where P = "\<lambda> \<tau>. instantiate \<epsilon> \<delta> (bang \<tau>) = bang (instantiate \<epsilon> \<delta> \<tau>)"]
          simp:  bang_idempotent bang_lrepr  prod.case_distrib)+


lemma layout_offset_layout_offset[simp] : "layout_offset n1 (layout_offset n2 ptrl) = layout_offset (n1 + n2) ptrl" 
  by(induct ptrl) (fastforce simp add: list_all_iff )+
  


lemma instantiate_lay_layout_offset[simp] : "instantiate_lay \<epsilon> (layout_offset offset ptrl) = layout_offset offset (instantiate_lay \<epsilon> ptrl)"
proof(induct ptrl)
  case (LayBitRange b)
  then show ?case
    by(induct b)simp
  next  case (LayVar x1a x2)
    then show ?case
      
      by (simp add: add.commute)
qed (fastforce simp add: list_all_iff )+


lemma instantiate_lay_instantiate_lay[simp] :
  assumes "layout_wellformed L ptrl"
  "L \<le> length \<epsilon>'"
shows "
instantiate_lay \<epsilon> (instantiate_lay \<epsilon>' ptrl) = instantiate_lay (map (instantiate_lay \<epsilon>) \<epsilon>') ptrl"
  using assms
  by(induct ptrl) (fastforce simp add: list_all_iff)+

lemma instantiate_lrepr_instantiate_lrepr[simp] :
  assumes "lrepr_wellformed n t"
  "n \<le> length \<delta>'"
shows "
instantiate_lrepr \<delta> (instantiate_lrepr \<delta>' t) = instantiate_lrepr (map (instantiate_lrepr \<delta>) \<delta>') t"
  using assms
  by(induct n t rule:lrepr_wellformed.induct) (fastforce simp add: list_all_iff)+
  


lemma instantiate_sigil_instantiate_sigil [simp] :
  assumes "matches_type_sigil L C \<tau> s"
    "L \<le> length \<epsilon>'"
  shows
"instantiate_sigil \<epsilon> (instantiate_sigil \<epsilon>' s) = instantiate_sigil (map (instantiate_lay \<epsilon>) \<epsilon>') s"
  using assms
  by(induct s rule:sigil_lay_cases)  (fastforce simp add:matches_fields_layout_def)+

lemma instantiate_instantiate [simp]:
(*assumes "list_all2 (kinding L K C') \<delta>' K"
and     "length K' = length \<delta>" *)
  assumes "length K \<le> length \<delta>'"
          "L \<le> length \<epsilon>'"
  shows   "L, K, C \<turnstile> x wellformed \<Longrightarrow> 
  instantiate \<epsilon> \<delta> (instantiate \<epsilon>' \<delta>' x) = 
  instantiate (map (instantiate_lay \<epsilon>) \<epsilon>')(map (instantiate \<epsilon> \<delta>) \<delta>') x"
  using assms
proof (induct x arbitrary: \<delta>' rule: instantiate.induct)
next case 3 then show ?case by (force dest: kinding_typelist_wellformed_elem simp add: list_all_iff kinding_simps)
next case 8 then show ?case 
    by(fastforce dest: kinding_record_wellformed_elem simp add: list_all_iff kinding_simps)
 next case 6 then show ?case by (fastforce dest: kinding_variant_wellformed_elem simp add: list_all_iff kinding_simps)
qed (auto simp add: kinding_def kinding_simps dest: list_all2_lengthD)



lemma instantiate_tprim [simp]:
shows "instantiate \<epsilon> \<delta> \<circ> TPrim = TPrim"
  by (rule ext, simp)

lemma instantiate_lay_nothing:
  shows "instantiate_lay [] l = l"
by (induct l) (auto simp: prod_set_defs intro: map_idI)

lemma instantiate_lay_nothing_id[simp]:
shows "instantiate_lay [] = id"
by (rule ext, simp add: instantiate_lay_nothing)

lemma instantiate_sigil_nothing_id[simp]:
  shows "instantiate_sigil [] = id"
  apply(rule ext)
  apply(induct_tac x rule:sigil_lay_cases)
  by simp+

lemma instantiate_nothing:
shows "instantiate [] [] e = e"
by (induct e) (auto simp: prod_set_defs intro: map_idI)

lemma instantiate_nothing_id[simp]:
shows "instantiate [] [] = id"
by (rule ext, simp add: instantiate_nothing)

lemma instantiate_ctx_nothing:
shows "instantiate_ctx [] [] e = e"
unfolding instantiate_ctx_def
by (induct e, auto simp: map_option.id [simplified id_def])

lemma instantiate_ctx_nothing_id[simp]:
shows "instantiate_ctx [] [] = id"
by (rule ext, simp add: instantiate_ctx_nothing)

lemma sigil_kind_instantiate[simp] : "sigil_kind (instantiate_sigil \<epsilon> s) = sigil_kind s"
proof(induct s rule:sigil_lay_cases)
case (BoxedLay p ptrl)
  then show ?case
    by(cases p)(simp)+
qed (simp)+

lemma instantiate_sigil_boxed_invert : "instantiate_sigil \<epsilon> s = Boxed perm ptrl \<longleftrightarrow> ( \<exists> ptrl'. s = Boxed perm ptrl' \<and> ptrl = map_option (instantiate_lay \<epsilon>) ptrl')"
  by (cases s ) (fastforce)+



lemma specialise_nothing:
shows "specialise [] [] e = e"
by (induct e) (auto simp: prod_set_defs intro: map_idI)

lemma specialise_nothing_id[simp]:
shows "specialise [] [] = id"
  by (rule ext, simp add: specialise_nothing)

lemma subst_wellformed_nothing : "L, K, C \<turnstile> [], [] :s 0, [], {}"
  by(simp add: subst_wellformed_def )


lemmas typing_struct_instantiate = typing_struct[where ts = "map (instantiate \<epsilon> \<delta>) ts" for \<epsilon> \<delta> ts, simplified]

lemma wellkinded_imp_kinded: "list_all2 (kinding L' K' C') \<delta> K \<Longrightarrow> list_all2 (\<lambda>t k. k \<subseteq> kinding_fn K' t) \<delta> K"
  by (clarsimp simp add: list_all2_conv_all_nth kinding_def)

lemma wellkinded_imp_wellformed: "list_all2 (kinding L' K' C') \<delta> K \<Longrightarrow> list_all (type_wellformed L' (length K') C') \<delta>"
  by (clarsimp simp add: list_all2_conv_all_nth list_all_length kinding_def)

lemma instantiate_over_variants_subvariants:
  assumes tags_same: "map fst ts = map fst ts'"
    and types_same: "map (fst \<circ> snd) ts = map (fst \<circ> snd) ts'"
  shows "map (\<lambda>(n, t, _). (n, type_repr t)) (map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<tau>s t, b)) ts) =
         map (\<lambda>(c, t, _). (c, type_repr t)) (map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<tau>s t, b)) ts')"
proof -
  have f1: "((\<lambda>(n, t, _). (n, type_repr t)) \<circ> (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<tau>s t, b))) = (\<lambda>(n, t, _). (n, type_repr (instantiate \<epsilon> \<tau>s t)))"
    by fastforce
  have f2: "(\<lambda>(n, t, _). (n, type_repr (instantiate \<epsilon> \<tau>s t))) = (\<lambda>p. (fst p, (type_repr \<circ> (instantiate \<epsilon> \<tau>s) \<circ> (fst \<circ> snd)) p))"
    by fastforce

  have "(map (type_repr \<circ> (instantiate \<epsilon> \<tau>s) \<circ> (fst \<circ> snd)) ts) = (map (type_repr \<circ> (instantiate \<epsilon> \<tau>s) \<circ> (fst \<circ> snd)) ts')"
    using types_same map_map by metis
  then have "map (\<lambda>(n, t, _). (n, type_repr (instantiate \<epsilon> \<tau>s t))) ts =
          map (\<lambda>(n, t, _). (n, type_repr (instantiate \<epsilon> \<tau>s t))) ts'"
    by (fastforce intro: pair_list_eqI simp add: f2 comp_def tags_same)
  then show ?thesis
    by (simp add: f1)
qed

subsection {* substitutivity *}


lemma instantiate_lay_closed[simp] : "layout_wellformed 0 ptrl \<Longrightarrow>
instantiate_lay \<epsilon> ptrl = ptrl"
  by (induct ptrl) (fastforce intro:map_idI simp add:list_all_iff)+


lemma instantiate_lrepr_closed[simp] : "lrepr_wellformed 0 rep \<Longrightarrow>
instantiate_lrepr \<delta> rep = rep"
  by (induct rep) (fastforce intro:map_idI simp add:list_all_iff)+


(* could be stated more generally for substitution of lrepr,
but this would require a specific wellformedness predicate
on substitution *)

lemma instantiate_matches_fields_layout :
  assumes "matches_fields_layout L C \<tau> ptrl"
   "lrepr_wellformed (length K) \<tau>"
    "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"  
  shows "matches_fields_layout L' C' (instantiate_lrepr (map type_lrepr \<delta>) \<tau>) (instantiate_lay \<epsilon> ptrl)"
  using assms
  by(fastforce dest:layout_wellformed_mono simp add:
   matches_fields_layout_def subst_wellformed_def match_constraint_def)

lemma instantiate_match_type_sigil:
  assumes "matches_type_sigil L C \<tau> s"
  "lrepr_wellformed (length K) \<tau>"
   "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
 shows "matches_type_sigil L' C' (instantiate_lrepr (map type_lrepr \<delta>) \<tau>) (instantiate_sigil \<epsilon> s)" 
  using assms
proof(induct s rule:sigil_lay_cases)
  case (BoxedLay p ptrl)
  then show ?case 
    by (simp add:instantiate_matches_fields_layout)
qed simp+ 

(* TODO: move before *)
lemma type_lrepr_instantiate[simp] : "type_lrepr (instantiate \<epsilon> \<delta> t) =
    instantiate_lrepr (map type_lrepr \<delta>) (type_lrepr t)"
proof(induct rule:instantiate.induct)
  (* bang variable *)
  case (2 \<epsilon> \<delta> i)
  then show ?case by (simp add:bang_lrepr)
next
(* TCon *)
  case (3 \<epsilon> \<delta> n ts s)
  then show ?case 
    by(cases s;simp)
next
(* TRecord *)
  case (8 \<epsilon> \<delta> ts s)

  then show ?case
    by(induct_tac s rule:sigil_lay_cases; fastforce)
qed fastforce+



lemma instantiate_match_type_sigil_record:
  assumes "matches_type_sigil L C (LRRecord \<tau>s) s"
   "list_all (\<lambda>(_, y). lrepr_wellformed (length K) y) \<tau>s"
   "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
 shows "matches_type_sigil L' C' (LRRecord (map (\<lambda>(n, t). (n, instantiate_lrepr (map type_lrepr \<delta>) t)) \<tau>s)) (instantiate_sigil \<epsilon> s)"
  using assms
  by(simp add: instantiate_match_type_sigil[where \<tau> = "LRRecord \<tau>s", simplified])
  

            

(* 

This is no longer true with dargent: 
a type variable matches any layout.

*)
lemma instantiate_wellformed:
  assumes
    (* "list_all (type_wellformed n') \<delta>"
    "length \<delta> = n" *)
    "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
    "n  = length K"
    "n' = length K'"
  shows "type_wellformed L n C t \<Longrightarrow> type_wellformed L' n' C' (instantiate \<epsilon> \<delta> t)"
  using assms
proof (induct t)
  case (TVar i)
  then show ?case
    by(fastforce dest:list_all2_kinding_wellformedD 
             simp add:list_all_length subst_wellformed_def)
  
next
  case (TVarBang x)
  then show ?case
    using bang_wellformed
    by(fastforce dest:list_all2_kinding_wellformedD 
             simp add:list_all_length subst_wellformed_def)
next
  case (TRecord ts s)
  show ?case     
    apply (simp) 
    using TRecord instantiate_match_type_sigil_record type_lrepr_wellformed
    by (fastforce simp add: list_all_iff prod.case_distrib comp_def)+
qed (auto simp add: list_all_iff) 

lemma instantiate_lrepr_wellformed:
  assumes
     "list_all (lrepr_wellformed n') \<delta>"
    "length \<delta> = n" 
(*    "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C" *)
    (* "n  = length K" *)
    "n' = length K'"
  shows "lrepr_wellformed n t \<Longrightarrow> lrepr_wellformed n' (instantiate_lrepr 
\<delta> t)"
  using assms
  by (induct t)
   (fastforce dest:list_all2_lengthD simp add: 
list_all2_conv_all_nth  list_all_iff )+

lemma substitutivity_kinding_fn:
  assumes
(*    "list_all (type_wellformed L' (length K') C') \<delta>" *)
    "list_all2 (\<lambda>t k. k \<subseteq> kinding_fn K' t) \<delta> K"
    "type_wellformed L (length K) C t" 
    "k \<subseteq> kinding_fn K t"
  shows "k \<subseteq> kinding_fn K' (instantiate \<epsilon> \<delta> t)"
  using assms
proof (induct t arbitrary: k)
  case (TVarBang i)
  then show ?case
    using bang_kinding_fn
    by (auto simp add: list_all2_conv_all_nth list_all_length)
next
  case (TSum ts)
  then show ?case
    by (fastforce split: variant_state.split simp add: list_all_iff)
next
  case (TRecord ts s)
  then show ?case
  proof(induct s rule:sigil_lay_cases)
    case (BoxedLay perm ptrl) 
    then show ?case
      by (cases perm) (fastforce split: record_state.split simp add:list_all2_conv_all_nth list_all_iff)+
  next
   case (BoxedNoLay p)
   then show ?case
     by (fastforce split: record_state.split simp add:list_all2_conv_all_nth list_all_iff)+
     
  next
    case Unboxed
    then show ?case

      using TRecord
      by (fastforce split: record_state.split simp add: list_all_iff) 
  qed
(*    by (fastforce split: record_state.split simp add: list_all_iff) *)
qed (fastforce simp add: list_all2_conv_all_nth list_all_iff)+

lemma substitutivity_single:
  assumes
(*    "list_all2 (kinding L K C') \<delta> K" *)
"L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
    "L, K, C \<turnstile> t :\<kappa> k"
  shows "L', K', C' \<turnstile> instantiate \<epsilon> \<delta> t :\<kappa> k"
proof -
  have "type_wellformed L' (length K') C' (instantiate \<epsilon> \<delta> t)"
    using assms
    by (auto intro!: instantiate_wellformed simp add: kinding_def list_all2_conv_all_nth list_all_length)
  moreover then have "k \<subseteq> kinding_fn K' (instantiate \<epsilon> \<delta> t)"
    using assms
    by (intro substitutivity_kinding_fn; auto simp add:
subst_wellformed_def kinding_def list_all2_conv_all_nth list_all_length)
  ultimately show "L', K', C' \<turnstile> instantiate \<epsilon> \<delta> t :\<kappa> k"
    by (simp add: kinding_def)
qed

lemma substitutivity_single_kinding_fn:
  assumes
    "list_all2 (kinding L' K' C') \<delta> K"
    "L, K, C \<turnstile> t :\<kappa> k"
  shows "k \<subseteq> kinding_fn K' (instantiate \<epsilon> \<delta> t)"

  using assms  
  by (intro substitutivity_kinding_fn; auto simp add: kinding_def list_all2_conv_all_nth list_all_length) 



lemma substitutivity_rest:
fixes \<delta>    :: "type substitution"
and   K K' :: "kind env"
assumes well_kinded: (* "list_all2 (kinding L' K' C') \<delta> K" *)
"L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows "L, K, C \<turnstile>* ts :\<kappa> k  \<Longrightarrow> L', K', C' \<turnstile>* map (instantiate \<epsilon> \<delta>) ts                :\<kappa> k"
and   "L, K, C \<turnstile>* xs :\<kappa>v k \<Longrightarrow> L', K', C' \<turnstile>* map (\<lambda>(n,a,b). (n,instantiate \<epsilon> \<delta> a, b)) xs :\<kappa>v k"
and   "L, K, C \<turnstile>* fs :\<kappa>r k \<Longrightarrow> L', K', C' \<turnstile>* map (\<lambda>(n,a,b). (n,instantiate \<epsilon> \<delta> a, b)) fs :\<kappa>r k"
  using substitutivity_single well_kinded instantiate_wellformed
    list_all2_kinding_wellformedD list_all2_lengthD
     apply -
    apply (simp add: kinding_all_set kinding_iff_wellformed)+
   apply (fastforce simp add: kinding_variant_set kinding_iff_wellformed split: variant_state.split)
  apply (fastforce simp add: kinding_record_set kinding_iff_wellformed split: record_state.split)
  done

lemmas substitutivity = substitutivity_single substitutivity_rest

(* TODO: improve the proof (Vincent?) *)
lemma list_all2_substitutivity:
fixes \<delta>    :: "type substitution"
and   K K' :: "kind env"
assumes well_kinded: (* "list_all2 (kinding L K C') \<delta> K" *)
"L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows "L, K, C \<turnstile> es, ts :s ls, ks, cs \<Longrightarrow> 
L', K', C' \<turnstile> (map (instantiate_lay \<epsilon>) es), map (instantiate \<epsilon> \<delta>) ts :s ls, ks, cs"
proof -

  assume yop : "L, K, C \<turnstile> es, ts :s ls, ks, cs"
  show "L', K', C' \<turnstile> (map (instantiate_lay \<epsilon>) es), map (instantiate \<epsilon> \<delta>) ts :s ls, ks, cs"
  apply(simp add: subst_wellformed_def)  
  apply(intro conjI)+
    using assms substitutivity
    using yop
      apply (fastforce simp add:list_all2_conv_all_nth subst_wellformed_def)
    using yop
      apply (fastforce simp add:list_all2_conv_all_nth subst_wellformed_def)
  apply(intro ballI)
  apply clarify
  apply(rename_tac l' t')
    using yop
    apply(simp add:subst_wellformed_def)
    apply(erule conjE)+
  apply(erule_tac x = "(l', t')" in  ballE;simp)
     apply(drule instantiate_matches_fields_layout[OF _ _ assms])
     apply (fastforce 
intro:instantiate_lrepr_wellformed
simp add: kinding_def type_lrepr_wellformed list_all2_conv_all_nth list_all_length
comp_def )+  
    done
qed

subsection {* Instantiation of contexts *}

lemma instantiate_ctx_weaken:
assumes "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
  and    (*  "list_all2 (kinding L K C') \<delta> K" *)
   "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows   "L', K', C' \<turnstile> instantiate_ctx \<epsilon> \<delta> \<Gamma> \<leadsto>w instantiate_ctx \<epsilon> \<delta> \<Gamma>'"
using assms(1) [simplified weakening_def] and assms(2) proof (induct rule: list_all2_induct)
     case Nil  then show ?case by (simp add: instantiate_ctx_def weakening_def)
next case Cons then show ?case
    using instantiate_wellformed list_all2_kinding_wellformedD
    by (auto simp add: weakening_comp.simps instantiate_ctx_def weakening_Cons
        dest: substitutivity)
qed


lemma instantiate_ctx_empty [simplified, simp]:
shows "instantiate_ctx \<epsilon> \<delta> (empty l) = empty l"
by (induct l, simp_all add: empty_def
                            instantiate_ctx_def)



lemma instantiate_ctx_singleton [simplified, simp]:
shows "instantiate_ctx \<epsilon> \<delta> (singleton l i \<tau>) = singleton l i (instantiate \<epsilon> \<delta> \<tau>)"
by (induct l arbitrary: i, simp_all add:   instantiate_ctx_def
                                           empty_def
                                    split: nat.split)

lemma instantiate_ctx_length [simp]:
shows "length (instantiate_ctx \<epsilon> \<delta> \<Gamma>) = length \<Gamma>"
by (simp add: instantiate_ctx_def)

lemma instantiate_ctx_consumed [simplified]:
assumes "L, K, C \<turnstile> \<Gamma> consumed"
and     (* "list_all2 (kinding L K C') \<delta> K" *)
   "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows   "L', K', C' \<turnstile> instantiate_ctx \<epsilon> \<delta> \<Gamma> consumed"
using assms by (auto intro: instantiate_ctx_weaken [where \<Gamma>' = "empty (length \<Gamma>)", simplified])

lemma map_option_instantiate_split_comp:
assumes "L, K, C \<turnstile> c \<leadsto> c1 \<parallel> c2"
and     (* "list_all2 (kinding L K C') \<delta> K" *)
 "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows   "L', K', C' \<turnstile> map_option (instantiate \<epsilon> \<delta>) c \<leadsto> map_option (instantiate \<epsilon> \<delta>) c1 \<parallel> map_option (instantiate \<epsilon> \<delta>) c2"
  using assms
  by (auto elim!: split_comp.cases simp add: instantiate_wellformed split_comp.intros
      dest: substitutivity_single list_all2_kinding_wellformedD)

lemma instantiate_ctx_split:
assumes "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
and     (* "list_all2 (kinding L K C') \<delta> K" *)
 "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows   "L', K', C' \<turnstile> instantiate_ctx \<epsilon> \<delta> \<Gamma> \<leadsto> instantiate_ctx \<epsilon> \<delta> \<Gamma>1 | instantiate_ctx \<epsilon> \<delta> \<Gamma>2"
  using assms
  by (auto intro: list_all3_map_over simp: map_option_instantiate_split_comp instantiate_ctx_def split_def)


lemma instantiate_ctx_split_bang:
assumes "split_bang L K C is \<Gamma> \<Gamma>1 \<Gamma>2"
and     (* "list_all2 (kinding L K C') \<delta> K" *)
 "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"
shows   "split_bang L' K' C' is (instantiate_ctx \<epsilon> \<delta> \<Gamma>) (instantiate_ctx \<epsilon> \<delta> \<Gamma>1) (instantiate_ctx \<epsilon> \<delta> \<Gamma>2)"
  using assms
proof (induct rule: split_bang.induct)
  case split_bang_empty
  then show ?case
    by (auto simp: instantiate_ctx_def intro: split_bang.intros)
next
  case split_bang_cons
  then show ?case
    by (auto
        intro!: split_bang.intros substitutivity_single instantiate_wellformed
        elim!: split_bang_comp.cases split_comp.cases
        dest: list_all2_kinding_wellformedD
        simp add: instantiate_ctx_def split_bang_comp.simps split_comp.simps)
qed


lemma instantiate_ctx_cons [simp]:
shows   "instantiate_ctx \<epsilon> \<delta> (Some x # \<Gamma>) = Some (instantiate \<epsilon> \<delta> x) # instantiate_ctx \<epsilon> \<delta> \<Gamma>"
by (simp add: instantiate_ctx_def)


lemma specialisation_subtyping:
  assumes
    "L, K, C \<turnstile> t \<sqsubseteq> t'"
    "L, K, C \<turnstile> t wellformed"
    "L, K, C \<turnstile> t' wellformed"
(*    "list_all2 (kinding L' K' C') \<delta> K" *)
     "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C" 

  shows "L', K', C' \<turnstile> instantiate \<epsilon> \<delta> t \<sqsubseteq> instantiate \<epsilon> \<delta>  t'"
  using assms
proof (induct rule: subtyping.inducts)
  case (subty_tvar i' i K)
  then show ?case
    by (auto intro!: subtyping.intros subtyping_refl simp add: kinding_def list_all2_conv_all_nth)
next
  case (subty_tvarb i' i K)
  moreover then have "type_wellformed L' (length K') C' (bang (\<delta> ! i))"
    by (auto dest: bang_wellformed simp add: kinding_def list_all2_conv_all_nth
subst_wellformed_def
)
  ultimately show ?case
    by (auto intro!: subtyping.intros subtyping_refl simp add: kinding_def list_all2_conv_all_nth)
next
  case (subty_tcon n1 n2 s1 s2 ts1 ts2 K)
  then show ?case
    by (simp add: subtyping_simps(3))
next
  case (subty_trecord L K C ts1 ts2 s1 s2)
  then show ?case
  proof (clarsimp, intro subtyping.intros)
    show "list_all2 (\<lambda>p1 p2. L', K', C' \<turnstile> fst (snd p1) \<sqsubseteq> fst (snd p2)) (map (\<lambda>(n, t, b). (n, instantiate \<epsilon> \<delta> t, b)) ts1) (map (\<lambda>(n, t, b). (n, instantiate \<epsilon> \<delta> t, b)) ts2)"
      using subty_trecord.prems subty_trecord.hyps(1)
      by (fastforce simp add: list_all2_conv_all_nth list_all_length split: prod.splits)
  next
    have "length ts1 = length ts2"
      using list_all2_conv_all_nth subty_trecord.hyps by blast
    then show "list_all2 (record_kind_subty L' K' C') (map (\<lambda>(n, t, b). (n, instantiate \<epsilon> \<delta> t, b)) ts1) (map (\<lambda>(n, t, b). (n, instantiate \<epsilon> \<delta> t, b)) ts2)"
    proof (clarsimp simp add: list_all2_conv_all_nth split: prod.splits)
      fix i n1 t1 b1 n2 t2 b2
      presume localassms:
        "ts1 ! i = (n1, t1, b1)"
        "ts2 ! i = (n2, t2, b2)"
        "i < length ts2"
        "i < length ts1"
        "L', K', C' \<turnstile> instantiate \<epsilon> \<delta> t1 :\<kappa> {D} \<longrightarrow> \<not> b1 < b2"
      moreover then have "b1 = b2 \<or> ((L, K, C \<turnstile> t1 :\<kappa> {D}) \<and> b1 < b2)"
        using subty_trecord.hyps(3)
        by (force simp add: list_all2_conv_all_nth split: prod.splits)
      moreover then have "L, K, C \<turnstile> t1 :\<kappa> {D} \<Longrightarrow> L', K', C' \<turnstile> (instantiate \<epsilon> \<delta> t1) :\<kappa> {D}"
        using subty_trecord.prems substitutivity_single
        by blast
      ultimately show "b1 = b2"
        by clarsimp
    qed force+
  qed force+
next
  case (subty_tsum L K C ts1 ts2)
  moreover then have "\<And>i. i < length ts1 \<Longrightarrow>
    L', K', C' \<turnstile> instantiate \<epsilon> \<delta> (fst (snd (ts1 ! i))) \<sqsubseteq> instantiate \<epsilon> \<delta> (fst (snd (ts2 ! i)))"
    by (auto simp add: list_all2_conv_all_nth list_all_length)
  ultimately show ?case
    by (fastforce intro!: subtyping.intros simp add: list_all2_conv_all_nth split: prod.splits)
qed (auto intro!: subtyping.intros)



section {* Lemmas about contexts, splitting and weakening *}

lemma empty_length:
shows "length (empty n) = n"
by (induct n, simp_all add: empty_def)

subsection {* split *}

lemma split_length:
  assumes "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
  shows "length \<Gamma> = length \<Gamma>1"
    and "length \<Gamma> = length \<Gamma>2"
  using assms
  by (induct rule: split_induct, force+)

lemma split_preservation_some_left:
  assumes splits: "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and idx: "\<Gamma>1 ! i = Some t"
  shows "\<Gamma> ! i  = Some t"
  using assms
  by (induct arbitrary: i rule: split_induct; fastforce simp add: nth_Cons' elim: split_comp.cases)

lemma split_preservation_some_right:
  assumes splits: "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and idx: "\<Gamma>2 ! i = Some t"
  shows "\<Gamma> ! i  = Some t"
  using assms
  by (induct arbitrary: i rule: split_induct; fastforce simp add: nth_Cons' elim: split_comp.cases)

lemma split_preserves_none:
  assumes splits: "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    and idx: "\<Gamma> ! i  = None"
  shows "\<Gamma>1 ! i = None"
    and "\<Gamma>2 ! i = None"
  using assms
  by (induct arbitrary: i rule: split_induct, (fastforce simp add: nth_Cons' elim: split_comp.cases)+)

subsection {* split bang *}

lemma split_bang_length:
  assumes "L, K , C, isa \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | \<Gamma>2"
  shows "length \<Gamma> = length \<Gamma>1"
    and "length \<Gamma> = length \<Gamma>2"
    and "length \<Gamma>1 = length \<Gamma>2"
  using assms
  by (induct rule: split_bang.induct, force+)

lemma split_bang_Cons1:
  shows "(L, K, C, isa \<turnstile> x # \<Gamma>' \<leadsto>b \<Gamma>1 | \<Gamma>2) \<longleftrightarrow>
          (\<exists>a \<Gamma>1' b \<Gamma>2'.
            (L, K, C, (0 \<in> isa) \<turnstile> x \<leadsto>b a \<parallel> b) \<and>
            (L, K, C, (pred ` Set.remove (0 :: index) isa) \<turnstile> \<Gamma>' \<leadsto>b \<Gamma>1' | \<Gamma>2') \<and>
            \<Gamma>1 = a # \<Gamma>1' \<and>
            \<Gamma>2 = b # \<Gamma>2' \<and>
            length \<Gamma>1' = length \<Gamma>' \<and>
            length \<Gamma>2' = length \<Gamma>')"
  by (fastforce dest: split_bang_length elim: split_bang.cases intro!: split_bang.intros)

lemma split_bang_Cons2:
  shows "(L, K, C, isa \<turnstile> \<Gamma> \<leadsto>b a # \<Gamma>1' | \<Gamma>2) \<longleftrightarrow>
          (\<exists>x \<Gamma>' b \<Gamma>2'.
            (L, K, C, (0 \<in> isa) \<turnstile> x \<leadsto>b a \<parallel> b) \<and>
            (L, K, C, (pred ` Set.remove (0 :: index) isa) \<turnstile> \<Gamma>' \<leadsto>b \<Gamma>1' | \<Gamma>2') \<and>
            \<Gamma> = x # \<Gamma>' \<and>
            \<Gamma>2 = b # \<Gamma>2' \<and>
            length \<Gamma>' = length \<Gamma>1' \<and>
            length \<Gamma>2' = length \<Gamma>1')"
  by (fastforce dest: split_bang_length elim: split_bang.cases intro!: split_bang.intros)

lemma split_bang_Cons3:
  shows "(L, K, C, isa \<turnstile> \<Gamma> \<leadsto>b \<Gamma>1 | b # \<Gamma>2') \<longleftrightarrow>
          (\<exists>x \<Gamma>' a \<Gamma>1'.
            (L, K, C, (0 \<in> isa) \<turnstile> x \<leadsto>b a \<parallel> b) \<and>
            (L, K, C, (pred ` Set.remove (0 :: index) isa) \<turnstile> \<Gamma>' \<leadsto>b \<Gamma>1' | \<Gamma>2') \<and>
            \<Gamma> = x # \<Gamma>' \<and>
            \<Gamma>1 = a # \<Gamma>1' \<and>
            length \<Gamma>' = length \<Gamma>2' \<and>
            length \<Gamma>1' = length \<Gamma>2')"
  by (fastforce dest: split_bang_length elim: split_bang.cases intro!: split_bang.intros)

lemma Suc_mem_image_pred:
  "0 \<notin> js \<Longrightarrow> (Suc n \<in> js) = (n \<in> pred ` js)"
  apply (simp add: image_def pred_def)
  apply (auto elim: rev_bexI split: nat.split_asm)
  done

lemma Suc_mem_image_pred_remove:
  "(n \<in> pred ` Set.remove 0 js) = (Suc n \<in> js)"
  by (simp add: Suc_mem_image_pred[symmetric])

lemma split_bang_nth:
  "split_bang L K C is \<Gamma> \<Gamma>1 \<Gamma>2 = (length \<Gamma>1 = length \<Gamma> \<and> length \<Gamma>2 = length \<Gamma>
        \<and> (\<forall>i < length \<Gamma>. L, K, C, i \<in> is \<turnstile> \<Gamma> ! i \<leadsto>b \<Gamma>1 ! i \<parallel> \<Gamma>2 ! i))"
proof (induct \<Gamma> arbitrary: "is" \<Gamma>1 \<Gamma>2)
  case (Cons a \<Gamma>)
  then show ?case
    apply -
    apply (intro iffI)

     apply (clarsimp simp add: split_bang_Cons1)
     apply (case_tac i)
      apply force
     apply (fastforce simp add: Suc_mem_image_pred_remove)

    apply (clarsimp simp add: split_bang_Cons1 Suc_mem_image_pred_remove length_Suc_conv)
    apply (rename_tac a1 \<Gamma>1 a2 \<Gamma>2)
    apply (intro conjI)
     apply (drule_tac x=0 in spec, cases "0 \<in> is"; force simp add: split_bang_comp.simps)
    apply auto

    done
qed (fastforce elim: split_bang.cases intro: split_bang_empty)


lemma weakening_length:
shows "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>' \<Longrightarrow> length \<Gamma> = length \<Gamma>'"
by (auto simp: weakening_def dest:list_all2_lengthD)

lemma weakening_preservation_some:
assumes weak: "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     idx:  "\<Gamma>' ! x = Some t"
shows   "\<Gamma>  ! x = Some t"
using weak[simplified weakening_def]
  and weakening_length[OF weak]
  and idx
  proof (induct arbitrary: x rule: list_all2_induct)
     case Nil                then show ?case by auto
next case (Cons x xs y ys a) then show ?case by (case_tac a, auto elim: weakening_comp.cases)
qed

lemma weakening_preserves_none:
assumes weak: "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and     idx:  "\<Gamma>  ! x = None"
shows   "\<Gamma>' ! x = None"
using weak[simplified weakening_def]
  and weakening_length[OF weak]
  and idx
  proof (induct arbitrary: x rule: list_all2_induct)
     case Nil                then show ?case by auto
next case (Cons x xs y ys a) then show ?case by (case_tac a, auto elim: weakening_comp.cases)
qed

lemma same_type_as_weakened:
  assumes
    "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'[i := Some t]"
    "i < length \<Gamma>"
  shows "\<Gamma> ! i = Some t"
  using assms weakening_length weakening_preservation_some
  by fastforce

lemma same_type_as_split_weakened_left:
  assumes
    "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "L, K, C \<turnstile> \<Gamma>1 \<leadsto>w \<Gamma>1'[x := Some t]"
    "x < length \<Gamma>1"
  shows "\<Gamma> ! x = Some t"
  using assms same_type_as_weakened split_preservation_some_left by blast

lemma same_type_as_split_weakened_right:
  assumes
    "L, K, C \<turnstile> \<Gamma> \<leadsto> \<Gamma>1 | \<Gamma>2"
    "L, K, C \<turnstile> \<Gamma>2 \<leadsto>w \<Gamma>2'[x := Some t]"
    "x < length \<Gamma>2"
  shows "\<Gamma> ! x = Some t"
  using assms same_type_as_weakened split_preservation_some_right by blast


lemma weakening_nth:
assumes weak: "L, K, C \<turnstile> \<Gamma> \<leadsto>w \<Gamma>'"
and           "i < length \<Gamma>"
shows         "weakening_comp L K C (\<Gamma>!i) (\<Gamma>'!i)"
using assms by (auto simp add: weakening_def dest: list_all2_nthD)

lemma typing_to_wellformed:
shows "\<Xi>, L, K, C, \<Gamma> \<turnstile>  e  : t  \<Longrightarrow> L, K, C \<turnstile>  t  wellformed"
and   "\<Xi>, L, K, C, \<Gamma> \<turnstile>* es : ts \<Longrightarrow> L, K, C \<turnstile>* ts wellformed"
proof (induct rule: typing_typing_all.inducts)
  case typing_var then show ?case
    by (fastforce dest: weakening_nth elim: weakening_comp.cases simp add: kinding_defs empty_def)
next case typing_afun then show ?case
    
    by (clarsimp simp add: kinding_defs instantiate_wellformed list_all2_kinding_wellformedD list_all2_lengthD 
 )
    
next case typing_fun then show ?case
    by (clarsimp simp add: kinding_defs  instantiate_wellformed  list_all2_kinding_wellformedD list_all2_lengthD)
next case typing_esac then show ?case
    by (fastforce dest: filter_member2  simp add: kinding_simps kinding_variant_set list_all_iff)
next case typing_struct then show ?case by (clarsimp simp add: in_set_zip list_all_iff)
next case typing_member then show ?case
    by (fastforce simp add: kinding_defs INT_subset_iff list_all_iff dest: nth_mem split: prod.splits record_state.splits)
next case (typing_put L K C \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
  then show ?case
  proof(induct s rule:sigil_lay_cases)
    case (BoxedLay p ptrl)
    have hyp : " map (\<lambda>(n, t, _). (n, type_lrepr t)) ts 
   =   map (\<lambda>(n, t, _). (n, type_lrepr t)) (ts[f := (n, t, Present)])" 

      using  `f < length ts`
             `ts ! f = (n, t, taken)`      
      by (simp add:list.rel_eq[symmetric] list_all2_conv_all_nth nth_list_update)      

    show ?case
      apply simp
      apply(intro conjI)+
      using BoxedLay apply(fastforce intro:distinct_list_update simp add: map_update   )
      using BoxedLay apply(simp add:list_all_length nth_list_update)
      using BoxedLay apply(simp add: hyp)
        done
    qed
     (clarsimp, auto intro: distinct_list_update simp add: list_all_iff map_update in_set_conv_nth Ball_def nth_list_update)+
(*     matches_type_sigil_taken) *)
  
    
next case typing_promote then show ?case
    using subtyping_wellformed_preservation by blast
qed (auto intro: supersumption simp add: kinding_defs)

lemma upcast_valid_cast_to :
assumes "upcast_valid \<tau> \<tau>'"
    and "lit_type l = Num \<tau>"
obtains x where "cast_to \<tau>' l = Some x"
            and "lit_type x = Num \<tau>'"
using assms by (cases l, auto elim: upcast_valid.elims)

lemma wellformed_imp_bang_type_repr:
  assumes "0, [], C \<turnstile> t wellformed"
  shows "type_repr (bang t) = type_repr t"
  using assms
proof (induct t)
  case (TCon n ts s)
  then show ?case    
    by (cases s, rename_tac p ptrl, case_tac p; auto simp add: list_all_iff)
next
  case (TRecord ts s)
  then show ?case
    by (cases s, rename_tac p ptrl, case_tac p; auto simp add: list_all_iff)
qed (auto simp add: list_all_iff)

lemma wellformed_bang_type_repr[simp]:
  shows "0, [], C \<turnstile> t wellformed \<Longrightarrow> type_repr (bang t) = type_repr t"
    and "0, [], C \<turnstile>* ts wellformed \<Longrightarrow> (map (type_repr \<circ> bang) ts) = map (type_repr) ts "
    and "0, [], C \<turnstile>* map (fst \<circ> snd) xs wellformed \<Longrightarrow> (map (type_repr \<circ>  bang \<circ> fst \<circ> snd) xs) = map (type_repr \<circ> fst \<circ> snd) xs"
    and "0, [], C \<turnstile>* map (fst \<circ> snd) fs wellformed \<Longrightarrow> (map (type_repr \<circ>  bang \<circ> fst \<circ> snd) fs) = map (type_repr \<circ> fst \<circ> snd) fs"
  by (force intro: wellformed_imp_bang_type_repr simp add: kinding_all_set kinding_def)+

lemma bang_type_repr[simp]:
  shows "0, [], C \<turnstile> t :\<kappa> k \<Longrightarrow> (type_repr (bang t) = type_repr t)"
    and "0, [], C \<turnstile>* ts :\<kappa> k \<Longrightarrow> (map (type_repr \<circ> bang) ts) = map (type_repr) ts "
    and "0, [], C \<turnstile>* xs :\<kappa>v k \<Longrightarrow> (map (type_repr \<circ>  bang \<circ> fst \<circ> snd) xs) = map (type_repr \<circ> fst \<circ> snd) xs"
    and "0, [], C \<turnstile>* fs :\<kappa>r k \<Longrightarrow> (map (type_repr \<circ>  bang \<circ> fst \<circ> snd) fs) = map (type_repr \<circ> fst \<circ> snd) fs"
  using wellformed_bang_type_repr
  by (force dest: kinding_to_wellformedD)+

subsection {* Specialisation *}

lemma specialisation:
  assumes well_kinded: 
 "L', K', C' \<turnstile> \<epsilon>, \<delta> :s L, K, C"   
(* "list_all2 (kinding L K C') \<delta> K" *)
shows "\<Xi> , L, K, C, \<Gamma> \<turnstile>  e  : \<tau>  \<Longrightarrow> \<Xi> , L', K', C', instantiate_ctx \<epsilon> \<delta> \<Gamma> \<turnstile> specialise \<epsilon> \<delta> e : instantiate \<epsilon> \<delta> \<tau> "
and   "\<Xi> , L, K, C, \<Gamma> \<turnstile>* es : \<tau>s \<Longrightarrow> \<Xi> , L', K', C', instantiate_ctx \<epsilon> \<delta> \<Gamma> \<turnstile>* map (specialise \<epsilon> \<delta>) es : map (instantiate \<epsilon> \<delta>) \<tau>s"
  using assms
proof (induct rule: typing_typing_all.inducts)
  have f1: "(\<lambda>(c, p). (c, case p of (t, b) \<Rightarrow> (instantiate \<epsilon> \<delta> t, b))) = (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<delta> t, b))"
    by force
 case (typing_case L K C \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> x ts tag t a u b)
  then have "\<Xi>, L', K', C', instantiate_ctx \<epsilon> \<delta> \<Gamma> \<turnstile> Case (specialise \<epsilon> \<delta> x) tag (specialise \<epsilon> \<delta> a) (specialise \<epsilon> \<delta> b) : instantiate \<epsilon> \<delta> u"
  proof (intro typing_typing_all.typing_case)
    have "\<Xi>, L', K', C', instantiate_ctx \<epsilon> \<delta> (Some (TSum (tagged_list_update tag (t, Checked) ts)) # \<Gamma>2) \<turnstile> specialise \<epsilon> \<delta> b : instantiate \<epsilon> \<delta> u"
      using typing_case.hyps(8) typing_case.prems 
      by blast
    moreover have "(map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<delta> t, b)) (tagged_list_update tag (t, Checked) ts)) = (tagged_list_update tag (instantiate \<epsilon> \<delta> t, Checked) (map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<delta> t, b)) ts))"
      using case_prod_conv f1 tagged_list_update_map_over1[where f = id and g = "\<lambda>_ (t,b). (instantiate \<epsilon> \<delta> t, b)", simplified]
      by metis
    ultimately show "\<Xi>, L', K', C', Some (TSum (tagged_list_update tag (instantiate \<epsilon> \<delta> t, Checked) (map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<delta> t, b)) ts))) # instantiate_ctx \<epsilon> \<delta> \<Gamma>2 \<turnstile> specialise \<epsilon> \<delta> b : instantiate \<epsilon> \<delta> u"
      by clarsimp
  qed (force intro: instantiate_ctx_split)+
  then show ?case by simp
next case (typing_afun \<Xi> f nl ks cs t u t' ls ts u' L K C \<Gamma>  )
  moreover have "instantiate \<epsilon> \<delta> (instantiate ls ts t) = instantiate (map (instantiate_lay \<epsilon>) ls) (map (instantiate \<epsilon> \<delta>) ts) t"
    and "instantiate \<epsilon> \<delta> (instantiate ls ts u) = instantiate (map (instantiate_lay \<epsilon>) ls) (map (instantiate \<epsilon> \<delta>) ts) u"
    using typing_afun    
    by(fastforce  intro!: instantiate_instantiate[where \<epsilon>' = "ls", simplified, rotated 1]
simp add: list_all2_lengthD subst_wellformed_def)+
  ultimately show ?case 
    
    apply simp
    using instantiate_ctx_consumed
    apply(intro typing_typing_all.typing_afun [simplified])
         apply(simp_all)
    
    using instantiate_ctx_consumed list_all2_substitutivity

    by (fastforce)

    (* by (auto intro!: list_all2_substitutivity
        typing_typing_all.typing_afun [simplified]
        instantiate_ctx_consumed) *)
    
next case (typing_fun \<Xi> ls ks cs t f u t' \<epsilon>' ts u' L K C \<Gamma>  )
  then also have "instantiate \<epsilon> \<delta> (instantiate \<epsilon>' ts t) = instantiate (map (instantiate_lay \<epsilon>) \<epsilon>') (map (instantiate \<epsilon> \<delta>) ts) t"
    and  "instantiate \<epsilon> \<delta> (instantiate \<epsilon>' ts u) = instantiate (map (instantiate_lay \<epsilon>) \<epsilon>') (map (instantiate \<epsilon> \<delta>) ts) u"
    by (force simp add: list_all2_lengthD subst_wellformed_def intro!: instantiate_instantiate dest!: typing_to_wellformed)+
  ultimately show ?case by (auto intro!: list_all2_substitutivity
        typing_typing_all.typing_fun [simplified]
        instantiate_ctx_consumed)
next
  case (typing_con \<Xi> K L C \<Gamma> x t tag ts ts')
  then show ?case
  proof (clarsimp, intro typing_typing_all.intros)
  next show "L', K', C' \<turnstile> TSum (map (\<lambda>(c, t, b). (c, instantiate \<epsilon> \<delta> t, b)) ts') wellformed"
      using typing_con
      by (fastforce simp add: list_all_iff intro: substitutivity instantiate_wellformed dest: list_all2_kinding_wellformedD list_all2_lengthD)
  qed (force intro: specialisation_subtyping substitutivity)+
next case typing_esac then show ?case
    by (force intro!: typing_typing_all.typing_esac
              simp: filter_map_map_filter_thd3_app2
                    typing_esac.hyps(3)[symmetric])+
next case typing_promote then show ?case
    by (simp, metis specialisation_subtyping typing_to_wellformed(1) typing_typing_all.typing_promote)
next
  case (typing_all_empty \<Gamma> \<Xi> K)
  then show ?case
    by (force intro!: typing_typing_all.intros simp add: instantiate_ctx_def empty_def)

next
  case (typing_take L K C \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t k taken e' u)
  then show ?case 
(* Help Vincent: why doesn't the force after the qed work here? *)
    apply simp
    apply(intro typing_typing_all.intros)    

    by (force intro!: typing_struct_instantiate
                   typing_typing_all.intros
           dest:   substitutivity
                   instantiate_ctx_split
                   instantiate_ctx_split_bang
                   instantiate_ctx_weaken
                   instantiate_ctx_consumed
           simp:   instantiate_ctx_def [where \<Gamma> = "[]", simplified]
                   map_update                   
           split:  prod.splits)+


next
  case (typing_put L K C \<Gamma> \<Gamma>1 \<Gamma>2 \<Xi> e ts s f n t taken k e')
   then show ?case
     apply(simp add:map_update)
    apply(intro typing_typing_all.intros)    

    by (force intro!: typing_struct_instantiate
                   typing_typing_all.intros
           dest:   substitutivity
                   instantiate_ctx_split
                   instantiate_ctx_split_bang
                   instantiate_ctx_weaken
                   instantiate_ctx_consumed
           simp:   instantiate_ctx_def [where \<Gamma> = "[]", simplified]
                   map_update                   
           split:  prod.splits)+
 
qed (force intro!: typing_struct_instantiate
                   typing_typing_all.intros
           dest:   substitutivity
                   instantiate_ctx_split
                   instantiate_ctx_split_bang
                   instantiate_ctx_weaken
                   instantiate_ctx_consumed
           simp:   instantiate_ctx_def [where \<Gamma> = "[]", simplified]
                   map_update
           split:  prod.splits)+



fun expr_size :: "'f expr \<Rightarrow> nat" where
  "expr_size (Let a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (LetBang vs a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (Fun f ts ls) = Suc (expr_size f)"
| "expr_size (Unit) = 0"
| "expr_size (Member x f) = Suc (expr_size x)"
| "expr_size (Cast t x) = Suc (expr_size x)"
| "expr_size (Con c x ts) = Suc (expr_size ts)"
| "expr_size (App a b) = Suc ((expr_size a) + (expr_size b))"
| "expr_size (Prim p as) = Suc (sum_list (map expr_size as))"
| "expr_size (Var v) = 0"
| "expr_size (AFun v va _) = 0"
| "expr_size (Struct v va) = Suc (sum_list (map expr_size va))"
| "expr_size (Lit v) = 0"
| "expr_size (SLit s) = 0"
| "expr_size (Tuple v va) = Suc ((expr_size v) + (expr_size va))"
| "expr_size (Put v va vb) = Suc ((expr_size v) + (expr_size vb))"
| "expr_size (Esac x t) = Suc (expr_size x)"
| "expr_size (If x a b) = Suc ((expr_size x) + (expr_size a) + (expr_size b))"
| "expr_size (Split x y) = Suc ((expr_size x) + (expr_size y))"
| "expr_size (Case x v a b) = Suc ((expr_size x) + (expr_size a) + (expr_size b))"
| "expr_size (Take x f y) = Suc ((expr_size x) + (expr_size y))"
| "expr_size (Promote t x) = Suc (expr_size x)"

lemma specialise_size [simp]:
  shows "expr_size (specialise \<epsilon> \<tau>s x) = expr_size x"
proof -
have "\<forall> as . (\<forall> x. x \<in> set as \<longrightarrow> expr_size (specialise \<epsilon> \<tau>s x) = expr_size x) \<longrightarrow>
  sum_list (map (expr_size \<circ> specialise \<epsilon> \<tau>s) as) = sum_list (map expr_size as)"
by (rule allI, induct_tac as, simp+)
then show ?thesis by (induct x rule: expr_size.induct, auto)
qed


end
