--
-- Copyright 2018, Data61
-- Commonwealth Scientific and Industrial Research Organisation (CSIRO)
-- ABN 41 687 119 230.
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(DATA61_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Cogent.Isabelle.ProofGen where

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core hiding (kind)
import Cogent.Dargent.Allocation
import Cogent.Isabelle.Deep
import Cogent.PrettyPrint
import Cogent.Util
import Data.LeafTree
import Data.Fin
import Data.Nat (Nat(..), SNat(..))
import qualified Data.Nat as Nat
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Data.Vec as Vec

import Lens.Micro.TH (makeLenses)
import Lens.Micro.Mtl ((%=), (.=), use)
import Control.Monad.State.Strict
import Data.List
import Data.Map (Map)
import Data.Maybe (catMaybes)
import qualified Data.Map as M
import Isabelle.InnerAST hiding (Type)
import Cogent.Isabelle.IsabelleName
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))


type Xi a b = [Definition PosTypedExpr a b]
data EnvExpr t v a b = EE { eexprType :: Type t b
                          , eexprExpr :: PosExpr t v a b EnvExpr
                          , eexprEnv  :: Vec v (Maybe (Type t b))
                          } {- FIXME: deriving (Show)-}

instance Functor (EnvExpr t v a) where  -- over @b@
  fmap f (EE t e env) = EE (fmap f t) (ffmap f e) (fmap (fmap $ fmap f) env)

instance Functor (Flip (EnvExpr t v) b) where  -- over @a@
  fmap f (Flip (EE t e env)) = Flip $ EE t (fffmap f e) env

instance Prec (EnvExpr t v a b) where
  prec (EE _ e _) = prec e

instance (Pretty a, Pretty b) => Pretty (EnvExpr t v a b) where
  pretty (EE t e env) = pretty e

data MLOption a = SOME a
                | NONE
  deriving (Show, Eq)

data Thm = Thm String
         | NthThm String Int
         | ThmInst String [(String, String)]

data Thms = Thms String
          | ThmList [Thm]

data Tactic = RuleTac Thm
            | Simplifier Thms Thms
            | SimpSolve Thms Thms
            | Force Thms
            | WeakeningTac Thms
            | SplitsTac [MLOption [Tactic]]
            | SubtypingTac [Tactic]

instance Show Thm where
  show (Thm thm) = "@{thm " ++ thm ++ "}"
  show (NthThm thm n) = "(nth @{thms " ++ thm ++ "} (" ++ show n ++ "-1))"
  show (ThmInst thm insts) = "@{thm " ++ thm ++ "[where " ++
                                intercalate " and " [ var ++ " = \"" ++ term ++ "\"" | (var, term) <- insts ] ++ "]}"

instance Show Thms where
  show (Thms thms) = "@{thms " ++ thms ++ "}"
  show (ThmList thms) = show thms

instance Show Tactic where
  show (RuleTac thm) = "(RTac " ++ show thm ++ ")"
  show (Simplifier adds dels) = "(SimpTac " ++ show (adds, dels) ++ ")"
  show (SimpSolve adds dels) = "(SimpSolveTac " ++ show (adds, dels) ++ ")"
  show (Force adds) = "(ForceTac " ++ show adds ++ ")"
  show (WeakeningTac kindThms) = "(WeakeningTac " ++ show kindThms ++")"
  show (SplitsTac tacs) = "(SplitsTac " ++ show tacs ++ ")"
  show (SubtypingTac tacs) = "(SubtypingTac " ++ show tacs ++ ")"

rule thm = RuleTac (Thm thm)
rule_tac thm insts = RuleTac (ThmInst thm insts)

simp                 = simp_add_del [] []
simp_add thms        = simp_add_del thms []
simp_del thms        = simp_add_del [] thms
simp_add_del add del = Simplifier (ThmList $ map Thm add) (ThmList $ map Thm del)

simp_solve                 = simp_solve_add_del [] []
simp_solve_add thms        = simp_solve_add_del thms []
simp_solve_del thms        = simp_solve_add_del [] thms
simp_solve_add_del add del = SimpSolve (ThmList $ map Thm add) (ThmList $ map Thm del)

force_simp add       = Force (ThmList $ map Thm add)

data Hints = KindingTacs [Tactic]
           | TTSplitBangTacs [Tactic]
           | TypingTacs [Tactic]
  deriving Show

-- Same as `Type' in Core, but without type indices.
data Type'
  = TVar' Int
  | TVarBang' Int
  | TCon' TypeName [Type'] (Sigil ())
  | TFun' Type' Type'
  | TPrim' PrimInt
  | TString'
  | TSum' [(TagName, (Type', Bool))]
  | TProduct' Type' Type'
  | TRecord' RecursiveParameter [(FieldName, (Type', Bool))] (Sigil (DataLayout BitRange))
  | TUnit'
  deriving (Eq, Ord)

deepType' :: Type' -> Term
deepType' (TVar' v) = mkApp (mkId "TVar") [mkInt $ toInteger v]
deepType' (TVarBang' v) = mkApp (mkId "TVarBang") [mkInt $ toInteger v]
deepType' (TCon' tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map deepType' ts), deepSigil s]
deepType' (TFun' ti to) = mkApp (mkId "TFun") [deepType' ti, deepType' to]
deepType' (TPrim' pt) = mkApp (mkId "TPrim") [deepPrimType pt]
deepType' (TString') = mkApp (mkId "TPrim") [mkId "String"]
deepType' (TSum' alts) = mkApp (mkId "TSum") [mkList $ map (\(n,(t,b)) -> mkPair (mkString n) (mkPair (deepType' t) (mkBool b))) alts]
deepType' (TProduct' t1 t2) = mkApp (mkId "TProduct") [deepType' t1, deepType' t2]
deepType' (TRecord' rp fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (deepType' t) (mkBool b)) fs, deepSigil s]  -- FIXME: @rp@ / zilinc
deepType' (TUnit') = mkId "TUnit"

stripType :: Type t b -> Type'
stripType (TVar n) = TVar' (finInt n)
stripType (TVarBang n) = TVarBang' (finInt n)
stripType (TCon t ts s) = TCon' t (map stripType ts) s
stripType (TFun t u) = TFun' (stripType t) (stripType u)
stripType (TPrim t) = TPrim' t
stripType TString = TString'
stripType (TSum ts) = TSum' (map (\(n,(t,b)) -> (n, (stripType t, b))) ts)
stripType (TProduct t u) = TProduct' (stripType t) (stripType u)
-- FIXME: recPars and isabelle
stripType (TRecord rp fs s) = TRecord' rp (map (\(n,(t,b)) -> (n, (stripType t, b))) fs) s
stripType TUnit = TUnit'

{-
We cache some subproofs to avoid duplication.
This needs to be balanced against the cost of writing out the proof props.
-}
cacheWeakeningProofs = False

typingSubproofPrefix = "typing_helper_" -- prefix for subproof lemma names
type SubproofId = Int
type ProofCache params = Map params (SubproofId,
                                     (Bool, Term), -- (schematic?, prop)
                                     [Tactic])     -- proof
data TypingSubproofs = TypingSubproofs
                       { _genId :: SubproofId
                       , _subproofKinding        :: ProofCache ([Kind], Type', Kind)
                       , _subproofAllKindCorrect :: ProofCache ([Kind], [Type'], [Kind])
                       , _subproofSplits         :: ProofCache (String, [Kind], [Maybe Type'], [Maybe Type'], [Maybe Type'])
                       , _subproofWeakens        :: ProofCache ([Kind], [Maybe Type'], [Maybe Type'])
                       , _subproofWellformed     :: ProofCache (Integer, Type')
                       , _tsTypeAbbrevs          :: TypeAbbrevs -- actually just a Reader
                       , _nameMod                :: NameMod
                       }
makeLenses ''TypingSubproofs

thmTypeAbbrev :: String -> State TypingSubproofs Thm
-- we use the "unfolded" theorem attribute when defining thm, instead
{-
thmTypeAbbrev thm = do
  ta <- use tsTypeAbbrevs
  return $ Thm (thm ++ if M.null (fst ta) then "" else "[unfolded " ++ typeAbbrevBucketName ++ "]")
-}
thmTypeAbbrev thm = return (Thm thm)

typingSubproofsInit :: NameMod -> TypeAbbrevs -> TypingSubproofs
typingSubproofsInit mod ta = TypingSubproofs 0 M.empty M.empty M.empty M.empty M.empty ta mod

newSubproofId = do
  i <- use genId
  let i' = i + 1
  i' `seq` genId .= i'
  return i'

tacSequence :: [State a [t]] -> State a [t]
tacSequence = fmap concat . sequence

hintListSequence :: [State TypingSubproofs (LeafTree Hints)] -> State TypingSubproofs (LeafTree Hints)
hintListSequence sths = Branch <$> sequence sths

kindingHint :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs (LeafTree Hints)
kindingHint k t = (pure . KindingTacs) `fmap` kinding k t

wellformedHint :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs (LeafTree Hints)
wellformedHint k t = (pure . KindingTacs) `fmap` wellformed k t

follow_tt :: (Ord b, Pretty b)
          => Vec t Kind
          -> Vec v  (Maybe (Type t b))
          -> Vec vx (Maybe (Type t b))
          -> Vec vy (Maybe (Type t b))
          -> State TypingSubproofs (LeafTree Hints)
follow_tt k env env_x env_y = hintListSequence $ map (kindingHint k) new
  where
    l = Nat.toInt (Vec.length env)
    n_x = take (Nat.toInt (Vec.length env_x) - l) (cvtToList env_x)
    n_y = take (Nat.toInt (Vec.length env_y) - l) (cvtToList env_y)
    new = catMaybes (n_x ++ n_y)

proofSteps :: (Ord b, Show b, Pretty b) => Xi a b -> Vec t Kind -> Type t b -> EnvExpr t v a b
           -> State TypingSubproofs (LeafTree Hints)
proofSteps xi k ti x = hintListSequence [ kindingHint k ti, ttyping xi k x ]

ttyping :: (Ord b, Show b, Pretty b) => Xi a b -> Vec t Kind -> EnvExpr t v a b -> State TypingSubproofs (LeafTree Hints)
ttyping xi k (EE t' (Split a x y) env) = hintListSequence [ -- Ξ, K, Γ ⊢ Split x y : t' if
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                            -- Ξ, K, Γ1 ⊢ x : TProduct t u
  ttyping xi k y                             -- Ξ, K, Some t # Some u # Γ2 ⊢ y : t'
  ]
ttyping xi k (EE u (Let a x y) env) = hintListSequence [ -- Ξ, K, Γ ⊢ Let x y : u if
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                           -- Ξ, K, Γ1 ⊢ x : t
  ttyping xi k y                            -- Ξ, K, Some t # Γ2 ⊢ y : u
  ]
ttyping xi k (EE u (LetBang is a x y) env) = hintListSequence [ -- Ξ, K, Γ ⊢ LetBang is x y : u if
  Branch <$> ttsplit_bang k 0 (map (finInt . fst) is) env (envOf x),
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                                   -- Ξ, K, Γ1 ⊢ x : t
  ttyping xi k y,                                   -- Ξ, K, Some t # Γ2 ⊢ y : u
  kindingHint k (typeOf x)                          -- K ⊢ t :κ k
  ]
ttyping xi k (EE t (If x a b) env) = hintListSequence [ -- Ξ, K, Γ ⊢ If x a b : t if
  ttyping xi k x,                                -- Ξ, K, Γ1 ⊢ x : TPrim Bool
  follow_tt k (envOf x) (envOf a) (envOf b),
  ttyping xi k a,                                -- Ξ, K, Γ2 ⊢ a : t
  ttyping xi k b                                 -- Ξ, K, Γ2 ⊢ b : t
  ]
ttyping xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) = hintListSequence [ -- Ξ, K, Γ ⊢ Case x tag a b : u if
  ttyping xi k x,                                       -- Ξ, K, Γ1 ⊢ x : TSum ts
  follow_tt k (envOf x) (envOf a) (envOf b),
  ttyping xi k a,                                       -- Ξ, K, (Some t # Γ) ⊢ a : u
  ttyping xi k b                                        -- Ξ, K, (Some (TSum (tagged_list_update tag (t, True) ts)) # Γ2) ⊢ b : u
  ]
ttyping xi k (EE u (Take a e@(EE (TRecord _ ts _) _ _) f e') env) = hintListSequence [ -- Ξ, K, Γ T⊢ Take e f e' : u if
  follow_tt k env (envOf e) (envOf e'),
  ttyping xi k e,                             -- Ξ, K, Γ1 T⊢ e : TRecord ts s
  kindingHint k (fst $ snd $ ts !! f),        -- K ⊢ t :κ k
  ttyping xi k e'                             -- Ξ, K, Γ2 T⊢ e' : u
  ]
ttyping xi k e = pure . TypingTacs <$> typingWrapper xi k e

typingWrapper :: (Ord b, Show b, Pretty b) => Xi a b -> Vec t Kind -> EnvExpr t v a b
              -> State TypingSubproofs [Tactic]
typingWrapper xi k (EE t (Variable i loc) env) = tacSequence [ ]
typingWrapper xi k (EE t (Struct fs) env)
    | allVars (map (eexprExpr . snd) fs) = tacSequence [ ]
typingWrapper xi k (EE (TPrim t) (Op o es _) env)
    | allVars (map eexprExpr es) = tacSequence [ ]
typingWrapper xi k e = typing xi k e

allVars :: [PosExpr t v a b e] -> Bool
allVars (Variable _ _ : vs) = allVars vs
allVars [] = True
allVars _ = False

typing :: (Eq b, Ord b, Show b, Pretty b) => Xi a b -> Vec t Kind -> EnvExpr t v a b -> State TypingSubproofs [Tactic]
typing xi k (EE t (Variable i loc) env) = tacSequence [
  return $ [rule "typing_var"],           -- Ξ, K, Γ ⊢ Var i : t if
  weakens k env (singleton (fst i) env),  -- K ⊢ Γ ↝w singleton (length Γ) i t
  return [simp_solve]                     -- i < length Γ
  ]

typing xi k (EE t' (Fun f ts _ _ _) env) = case findfun (unCoreFunName f) xi of
    AbsDecl _ _ ks' _ t u ->
      let ks = fmap snd ks' in tacSequence [
        return [rule "typing_afun'"],  -- Ξ, K, Γ ⊢ AFun f ts : TFun t' u'
        do ta <- use tsTypeAbbrevs
           mod <- use nameMod
           let unabbrev | M.null (fst ta) = ""
                        | otherwise = "[unfolded " ++ typeAbbrevBucketName ++ "]"
           return [simp_add ["\\<Xi>_def", mod (unIsabelleName $ mkIsabelleName $ unCoreFunName f) 
                   ++ "_type_def" ++ unabbrev]],  -- Ξ f = (K', t, u)
        allKindCorrect k ts ks,    -- list_all2 (kinding K) ts ks
        return [simp_solve,        -- t' = instantiate ts t
                simp_solve],       -- u' = instantiate ts u
        wellformed ks (TFun t u),  -- ks ⊢ TFun t u wellformed
        consumed k env             -- K ⊢ Γ consumed
        ]

    FunDef _ _ ks' _ t u _ ->
      let ks = fmap snd ks' in tacSequence [
        return [rule "typing_fun'"],  -- Ξ, K, Γ ⊢ Fun f ts : t' if
        do ta <- use tsTypeAbbrevs
           mod <- use nameMod
           let unabbrev | M.null (fst ta) = "" | otherwise = " " ++ typeAbbrevBucketName
           return [rule (fn_proof (mod (unIsabelleName $ mkIsabelleName $ unCoreFunName f)) unabbrev)],  -- Ξ, K', (TT, [Some t]) ⊢T f : u
        allKindCorrect k ts ks,  -- list_all2 (kinding K) ts K'
        return [simp_solve,      -- t' = instantiate ts t
                simp_solve],     -- u' = instantiate ts u
        wellformed ks t,         -- K' ⊢ t wellformed
        consumed k env           -- K ⊢ Γ consumed
        ]

    _ -> error $ "ProofGen Fun: bad function call " ++ show f

  where findfun f (def@(FunDef _ fn _ _ _ _ _):fs) | f == fn = def
        findfun f (def@(AbsDecl _ fn _ _ _ _) :fs) | f == fn = def
        findfun f (_:fs) = findfun f fs
        findfun f [] = error $ "ProofGen Fun: no such function " ++ show f

        fn_proof fn unabbrev =
          fn ++ "_typecorrect[simplified " ++ fn ++ "_type_def " ++
                              fn ++ "_typetree_def" ++ unabbrev ++ ", simplified]"

typing xi k (EE y (App a b _) env) = tacSequence [
  return [rule "typing_app"],        -- Ξ, K, Γ ⊢ App a b : y if
  splits k env (envOf a) (envOf b),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k a,                     -- Ξ, K, Γ1 ⊢ a : TFun x y
  typing xi k b                      -- Ξ, K, Γ2 ⊢ b : x
  ]

typing xi k (EE tc@(TSum ts) (Con tag e t) env) = tacSequence [
  return [rule "typing_con"],            -- Ξ, K, Γ ⊢ Con ts tag x : TSum ts if
  typing xi k e,                         -- Ξ, K, Γ ⊢ x : t
  return [simp_solve],                   -- (tag, t, Unchecked) ∈ set ts
  wellformed k tc,                       -- K ⊢ TSum ts wellformed
  return [simp_solve]                    -- ts = ts'
  ]

typing xi k (EE u (Cast t e) env) | EE (TPrim pt) _ _ <- e, TPrim pt' <- t, pt /= Boolean = tacSequence [
  return [rule "typing_cast"],   -- Ξ, K, Γ ⊢ Cast τ' e : TPrim (Num τ')
  typing xi k e,                 -- Ξ, K, Γ ⊢ e : TPrim (Num τ)
  return [simp_solve]            -- upcast_valid τ τ'
  ]

typing xi k (EE _ (Tuple t u) env) = tacSequence [
  return [rule "typing_tuple"],      -- Ξ, K, Γ ⊢ Tuple t u : TProduct T U if
  splits k env (envOf t) (envOf u),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k t,                     -- Ξ, K, Γ1 ⊢ t : T
  typing xi k u                      -- Ξ, K, Γ2 ⊢ u : U
  ]

typing xi k (EE t' (Split a x y) env) = tacSequence [
  return [rule "typing_split"],              -- Ξ, K, Γ ⊢ Split x y : t' if
  splits k env (envOf x) (peel2 $ envOf y),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                             -- Ξ, K, Γ1 ⊢ x : TProduct t u
  typing xi k y                              -- Ξ, K, (Some t)#(Some u)#Γ2 ⊢ y : t'
  ]

typing xi k (EE u (Let a x y) env) = tacSequence [
  return [rule "typing_let"],               -- Ξ, K, Γ ⊢ Let x y : u if
  splits k env (envOf x) (peel $ envOf y),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                            -- Ξ, K, Γ1 ⊢ x : t
  typing xi k y                             -- Ξ, K, (Some t # Γ2) ⊢ y : u
  ]

typing xi k (EE u (LetBang is a x y) env) = tacSequence [
  return [rule "typing_letb"],                    -- Ξ, K, Γ ⊢ LetBang is x y : u if
  error "split_bang: should be ttyping LetBang",  -- split_bang K is Γ Γ1 Γ2
  typing xi k x,                                  -- Ξ, K, Γ1 ⊢ x : t
  typing xi k y,                                  -- Ξ, K, (Some t # Γ2) ⊢ y : u
  kinding k (typeOf x),                           -- K ⊢ t :κ k
  return [simp_solve]                             -- E ∈ k
  ]

typing xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) = tacSequence [
  return [rule "typing_case"],  -- Ξ, K, Γ ⊢ Case x tag a b : u if
  splits k env (envOf x) (peel $ envOf b <|> envOf a),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                -- Ξ, K, Γ1 ⊢ x : TSum ts
  return [simp_solve],          -- (tag, (t,False)) ∈ set ts
  typing xi k a,                -- Ξ, K, (Some t # Γ2) ⊢ a : u
  typing xi k b                 -- Ξ, K, (Some (TSum (tagged_list_update tag (t, True) ts)) # Γ2) ⊢ b : u
  ]

typing xi k (EE _ (Esac x) _) = tacSequence [
  return [rule "typing_esac"],  -- Ξ, K, Γ ⊢ Esac x : t if
  typing xi k x,                -- Ξ, K, Γ ⊢ x : TSum ts
  return [simp_solve]           -- [(_, (t,False))] = filter (HOL.Not ∘ snd ∘ snd) ts
  ]

typing xi k (EE t (If x a b) env) = tacSequence [
  return [rule "typing_if"],                     -- Ξ, K, Γ ⊢ If x a b : t if
  splits k env (envOf x) (envOf a <|> envOf b),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                                 -- Ξ, K, Γ1 ⊢ x : TPrim Bool
  typing xi k a,                                 -- Ξ, K, Γ2 ⊢ a : t
  typing xi k b                                  -- Ξ, K, Γ2 ⊢ b : t
  ]

typing xi k (EE (TPrim t) (Op o es _) env) = tacSequence [
  return [rule "typing_prim'"],  -- Ξ, K, Γ ⊢ Prim oper args : TPrim t if
  return [simp_solve,            -- prim_op_type oper = (ts,t)
          simp_solve],           -- ts' = map TPrim ts;
  typingAll xi k env es          -- Ξ, K, Γ ⊢* args : ts'
  ]

typing xi k (EE _ (ILit _ t) env) = tacSequence [
  return [rule "typing_lit'"],  -- Ξ, K, Γ ⊢ Lit l : TPrim t if
  consumed k env,               -- K ⊢ Γ consumed
  return [simp_solve]           -- t = lit_type l
  ]

typing xi k (EE _ (SLit t) env) = tacSequence [
  return [rule "typing_slit"],  -- Ξ, K, Γ ⊢ SLit s : TPrim String
  consumed k env                -- K ⊢ Γ consumed
  ]

typing xi k (EE _ Unit env) = tacSequence [
  return [rule "typing_unit"],  -- Ξ, K, Γ ⊢ Unit : TUnit if
  consumed k env                -- K ⊢ Γ consumed
  ]

typing xi k (EE t (Struct fs) env) = tacSequence [
  return [rule "typing_struct'"],    -- Ξ, K, Γ ⊢ Struct ts es : TRecord ts' Unboxed
  typingAll xi k env (map snd fs),   -- Ξ, K, Γ ⊢* es : ts
  return [simp_solve],               -- ns = map fst ts'
  return (distinct (map fst fs)),    -- distinct ns
  return [simp_solve,                -- map (fst ∘ snd) ts' = ts
          simp_solve]                -- list_all (λp. snd (snd p) = Present) ts'
  ]

typing xi k (EE t (Member e f) env) = tacSequence [
  return [rule "typing_member"],   -- Ξ, K, Γ ⊢ Member e f : t if
  typing xi k e,                   -- Ξ, K, Γ ⊢ e : TRecord ts s
  kinding k (eexprType e),         -- K ⊢ TRecord ts s :κ k (* k introduced *)
  return [simp_solve,              -- S ∈ k
          simp_solve,              -- f < length ts
          simp_solve]              -- ts ! f = (t, False)
  ]

typing xi k (EE u (Take a e@(EE (TRecord _ ts _) _ _) f e') env) = tacSequence [
  return [rule "typing_take"],                -- Ξ, K, Γ ⊢ Take e f e' : u if
  splits k env (envOf e) (peel2 $ envOf e'),  -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k e,                              -- Ξ, K, Γ1 ⊢ e : TRecord ts s
  return [simp_solve,                         -- s ≠ ReadOnly
          simp_solve,                         -- f < length ts
          simp_solve],                        -- ts ! f = (t, False) (* instantiates t *)
  kinding k (fst $ snd $ ts !! f),            -- K ⊢ t :κ k
  return [simp_solve],                        -- S ∈ k ∨ taken (* instantiates taken *)
  return [simp],
  typing xi k e'                              -- Ξ, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # Γ2) ⊢ e' : u
  ]

typing xi k (EE ty (Put e1@(EE (TRecord _ ts _) _ _) f e2@(EE t _ _)) env) = tacSequence [
  return [rule "typing_put'"],                          -- Ξ, K, Γ ⊢ Put e f e' : TRecord ts' s if
  splits k env (envOf e1) (envOf e2),                   -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k e1,                                       -- Ξ, K, Γ1 ⊢ e : TRecord ts s
  return [simp_solve,                                   -- s ≠ ReadOnly
          simp_solve],                                  -- f < length ts
  return [simp_solve_del ["Product_Type.prod.inject"]], -- ts ! f = (t, taken)
  kinding k t,                                          -- K ⊢ t :κ k
  return [simp_solve],                                  -- D ∈ k ∨ taken = Taken
  typing xi k e2,                                       -- Ξ, K, Γ2 ⊢ e' : t
  return [simp_solve]                                   -- ts' = (ts [f := (t,False)])
  ]

typing xi k (EE _ (Promote t e@(EE t' _ _)) env) = tacSequence [
  return [rule "typing_promote"], -- Ξ, K, Γ ⊢ Promote t x : t
  typing xi k e,                  -- Ξ, K, Γ ⊢ x : t'
  pure <$> subtyping k t' t       -- K ⊢ t' ⊑ t
  ]

typing xi k _ = error "attempted to generate proof of ill-typed program"

typingAll :: (Ord b, Show b, Pretty b)
          => Xi a b
          -> Vec t Kind
          -> Vec v (Maybe (Type t b))
          -> [EnvExpr t v a b]
          -> State TypingSubproofs [Tactic]
-- Γ = empty n ⟹  Ξ, K, Γ ⊢* [] : []
typingAll xi k g [] = return [rule_tac "typing_all_empty'" [("n", show . Nat.toInt $ Vec.length g)],
                              simp_add ["empty_def"]]
-- Ξ, K, Γ ⊢* (e # es) : (t # ts)
typingAll xi k g (e:es) =
  let envs = foldl (<|>) (cleared g) (map envOf es) in tacSequence [
    return [rule "typing_all_cons"],
    splits k g (envOf e) envs,  -- K ⊢ Γ ↝ Γ1 | Γ2
    typing xi k e,              -- Ξ, K, Γ1 ⊢  e  : t
    typingAll xi k envs es      -- Ξ, K, Γ2 ⊢* es : ts
    ]


subtyping :: (Eq b, Ord b, Pretty b) => Vec t Kind -> Type t b -> Type t b -> State TypingSubproofs Tactic
subtyping k t1 t2 = SubtypingTac <$> subtyping' k t1 t2

subtyping'  :: (Eq b, Ord b, Pretty b) => Vec t Kind -> Type t b -> Type t b -> State TypingSubproofs [Tactic]
subtyping'' :: (Eq b, Ord b, Pretty b) => Vec t Kind -> Type t b -> Type t b -> State TypingSubproofs [Tactic]

subtyping' k t1 t2 =
  if t1 == t2
  then
    tacSequence [
      return [rule "subtyping_refl"]
      ]
  else subtyping'' k t1 t2

subtyping'' k TVar{}           TVar{}           = return [rule "subty_tvar", simp_solve]
subtyping'' k TVarBang{}       TVarBang{}       = return [rule "subty_tvarb", simp_solve]
subtyping'' k TCon{}           TCon{}           = return [rule "subty_tcon", simp_solve, simp_solve, simp_solve]
subtyping'' k (TFun t1 u1)     (TFun t2 u2)     =
  (rule "subty_tfun" :) <$> liftM2 (++) (subtyping' k t2 t1) (subtyping' k u1 u2)
subtyping'' k TPrim{}          TPrim{}          = return [rule "subty_tprim", simp_solve]
subtyping'' k (TRecord _ f1s _)  (TRecord _ f2s _)  =
  tacSequence [
    return [rule "subty_trecord"],
    (++ [rule "list_all2_nil"]) . join <$>
      zipWithM
        (\t1 t2 -> tacSequence [return [rule "list_all2_cons", simp], subtyping' k t1 t2])
        (fst . snd <$> f1s)
        (fst . snd <$> f2s),
    return [simp_solve],
    (++ [rule "list_all2_nil"]) . join <$>
      zipWithM
        (\(_,(t1,b1)) (_,(t2,b2)) ->
          if b1 == b2
          then
            tacSequence [
              return [rule "list_all2_record_kind_subty_cons_nodrop"],
              return [simp_solve]
              ]
          else
            tacSequence [
              return [rule "list_all2_record_kind_subty_cons_drop"],
              return [simp],
              kinding k t1,
              return
                [simp_solve,
                 simp_solve]
              ])
        f1s
        f2s,
    return [simp_solve]
    ]
subtyping'' k (TProduct t1 u1) (TProduct t2 u2) =
  (rule "subty_tprod" :) <$> liftM2 (++) (subtyping' k t1 t2) (subtyping' k u1 u2)
subtyping'' k (TSum v1s)       (TSum v2s)  =
  tacSequence [
    return [rule "subty_tsum"],
    (++ [rule "list_all2_nil"]) . join . (([rule "list_all2_cons", simp] ++) <$>)
      <$> zipWithM (subtyping' k) (fst . snd <$> v1s) (fst . snd <$> v2s),
    return [simp_solve],
    return [force_simp []]
    ]


kinding :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs [Tactic]
kinding k t = do
  proofId <- kindingRaw k t
  thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
  return [RuleTac thm]

kindingRaw :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs SubproofId
kindingRaw k t = do
  let k' = cvtToList k
      t' = stripType t
      gk = mostGeneralKind k t
  ta <- use tsTypeAbbrevs
  kmap <- use subproofKinding
  case M.lookup (k', t', gk) kmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "kinding") [mkList (map deepKind k'), deepType mod ta t, deepKind gk]
                  tac <- tacSequence
                    [return [force_simp ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]]
                  proofId <- newSubproofId
                  subproofKinding %= M.insert (k', t', gk) (proofId, (False, prop), tac)
                  return proofId
    Just (proofId, _, _) -> return proofId

kinding' :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> Kind -> State TypingSubproofs [Tactic]
kinding' ks t k = do
  let ks' = cvtToList ks
      t' = stripType t
  ta <- use tsTypeAbbrevs
  kmap <- use subproofKinding
  case M.lookup (ks', t', k) kmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "kinding") [mkList (map deepKind ks'), deepType mod ta t, deepKind k]
                  tac <- tacSequence
                    [return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]]
                  proofId <- newSubproofId
                  subproofKinding %= M.insert (ks', t', k) (proofId, (False, prop), tac)
                  thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                  return [RuleTac thm]
    Just (proofId, _, _) -> do thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                               return [RuleTac thm]

-- kind :: Vec t Kind -> Type t -> Kind -> State TypingSubproofs [Tactic]
-- kind ks (TVar v)         k = return [simp, simp]
-- kind ks (TVarBang v)     k = return [simp, simp]
-- kind ks (TUnit)          k = return []
-- kind ks (TProduct t1 t2) k = tacSequence [kinding' ks t1 k, kinding' ks t2 k]
-- kind ks (TSum ts)        k = tacSequence [kindingVariant ks (map snd ts) k, return [simp, simp], kindingAll ks (map (fst . snd) ts) k]
-- kind ks (TFun ti to)     k = tacSequence [kinding ks ti, kinding ks to]
-- kind ks (TRecord ts s)   k = tacSequence [kindingRecord ks (map snd ts) k, return [simp]]
-- kind ks (TPrim i)        k = return []
-- kind ks (TString)        k = return []
-- kind ks (TCon n ts s)    k = tacSequence [kindingAll ks ts k, return [simp]]

kindingAll :: Vec t Kind -> [Type t b] -> Kind -> State TypingSubproofs [Tactic]
kindingAll _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

kindingRecord :: Vec t Kind -> [(Type t b, Bool)] -> Kind -> State TypingSubproofs [Tactic]
kindingRecord _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

kindingVariant :: Vec t Kind -> [(Type t b, Bool)] -> Kind -> State TypingSubproofs [Tactic]
kindingVariant _ _ k = return [simp_add ["kinding_def", "kinding_all_def", "kinding_variant_def", "kinding_record_def"]]

allKindCorrect :: (Ord b, Pretty b) => Vec t' Kind -> [Type t' b] -> Vec t Kind -> State TypingSubproofs [Tactic]
allKindCorrect k ts ks = do
  let k' = cvtToList k
      ts' = map stripType ts
      ks' = cvtToList ks
  ta <- use tsTypeAbbrevs
  akmap <- use subproofAllKindCorrect
  case M.lookup (k', ts', ks') akmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "list_all2")
                               [mkApp (mkId "kinding") [mkList (map deepKind k')], mkList (map (deepType mod ta) ts), mkList (map deepKind ks')]
                  tac <- tacSequence [return [Simplifier (ThmList []) (ThmList [NthThm "HOL.simp_thms" 25, NthThm "HOL.simp_thms" 26])],
                                      allKindCorrect' k ts ks]
                  proofId <- newSubproofId
                  subproofAllKindCorrect %= M.insert (k', ts', ks') (proofId, (False, prop), tac)
                  return [rule $ typingSubproofPrefix ++ show proofId]
    Just (proofId, _, _) -> return [rule $ typingSubproofPrefix ++ show proofId]

allKindCorrect' :: (Ord b, Pretty b) => Vec t' Kind -> [Type t' b] -> Vec t Kind -> State TypingSubproofs [Tactic]
allKindCorrect' kind (t:ts) (Cons k ks)
  = tacSequence [return (breakConj ts), kinding' kind t k, allKindCorrect' kind ts ks]
allKindCorrect' _ [] Nil = return []
allKindCorrect' _ _ _ = error "kind mismatch"

splits :: (Ord b, Show b, Pretty b)
       => Vec t Kind
       -> Vec v (Maybe (Type t b))
       -> Vec v (Maybe (Type t b))
       -> Vec v (Maybe (Type t b))
       -> State TypingSubproofs [Tactic]
splits k g g1 g2 = (:[]) . SplitsTac <$> splitsHint False k g g1 g2

splitsHint :: (Ord b, Show b, Pretty b)
           => Bool
           -> Vec t Kind
           -> Vec v (Maybe (Type t b))
           -> Vec v (Maybe (Type t b))
           -> Vec v (Maybe (Type t b))
           -> State TypingSubproofs [MLOption [Tactic]]
splitsHint b k (Cons Nothing gs) (Cons Nothing xs) (Cons Nothing ys) =
  if b then splitsHint b k gs xs ys else (NONE :) <$> splitsHint True k gs xs ys
splitsHint b k (Cons g gs) (Cons x xs) (Cons y ys) = liftM2 (:) (splitHint k g x y) (splitsHint False k gs xs ys)
splitsHint _ k Nil         Nil         Nil         = return []
#if __GLASGOW_HASKELL__ < 711
splitsHint _ _ _ _ _ = __ghc_t4139 "ProofGen.splitsHint"
#endif

splitHint :: (Ord b, Show b, Pretty b)
          => Vec t Kind
          -> Maybe (Type t b)
          -> Maybe (Type t b)
          -> Maybe (Type t b)
          -> State TypingSubproofs (MLOption [Tactic])
splitHint k Nothing  Nothing  Nothing  = __impossible "splitHint got case none"
splitHint k (Just t) (Just _) Nothing  = (\wf -> SOME $ rule "split_comp.left" : wf) <$> wellformed k t
splitHint k (Just t) Nothing  (Just _) = (\wf -> SOME $ rule "split_comp.right" : wf) <$> wellformed k t
splitHint k (Just t) (Just _) (Just _) = (\wf -> SOME $ rule "split_comp.share" : wf) <$> kinding k t
splitHint k g x y = error $ "bad split: " ++ show (g, x, y)

ttsplit_bang :: (Ord b, Pretty b) => Vec t Kind -> Int -> [Int] -> Vec n (Maybe (Type t b))
             -> Vec n (Maybe (Type t b)) -> State TypingSubproofs [LeafTree Hints]
ttsplit_bang k ix ixs (Cons g gs) (Cons (Just x) xs) = do
    this <- if ix `elem` ixs then Just <$> kindingHint k x else pure Nothing
    rest <- ttsplit_bang k (ix + 1) ixs gs xs
    return $ case this of
              Just this -> this : rest
              Nothing -> rest
ttsplit_bang k ix ixs (Cons g gs) (Cons Nothing xs) =
    if ix `elem` ixs then error "bad split_bang"
        else ttsplit_bang k (ix + 1) ixs gs xs
ttsplit_bang k ix ixs Nil Nil = return []
#if __GLASGOW_HASKELL__ < 711
ttsplit_bang _ _ _ _ _ = error "bad split_bang end"
#endif

distinct _ = [simp_solve]

-- K ⊢ τ wellformed
wellformed :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs [Tactic]
wellformed k t = do
  proofId <- wellformedRaw k t
  thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
  return [rule "type_wellformed_prettyI", Simplifier (ThmList []) (Thms "type_wellformed.simps"), RuleTac thm]

wellformedRaw :: (Ord b, Pretty b) => Vec t Kind -> Type t b -> State TypingSubproofs SubproofId
wellformedRaw k t = do
  let n' = toInteger $ Nat.toInt $ Vec.length k
      t' = stripType t
  ta <- use tsTypeAbbrevs
  wlmap <- use subproofWellformed
  case M.lookup (n', t') wlmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "type_wellformed") [mkInt n', deepType mod ta t]
                  tac <- tacSequence [return $ [force_simp []]]
                  proofId <- newSubproofId
                  subproofWellformed %= M.insert (n', t') (proofId, (False, prop), tac)
                  return proofId
    Just (proofId, _, _) -> return proofId

-- TODO use cached proofs here
-- K ⊢* τs wellformed
wellformedAll :: Vec t Kind -> [Type t b] -> State TypingSubproofs [Tactic]
wellformedAll ks ts = tacSequence [return [simp_solve]]
  -- where k = foldr (<>) mempty (map (mostGeneralKind ks) ts)

-- K ⊢ Γ consumed ≡ K ⊢ Γ ↝w empty (length Γ)
consumed :: (Ord b, Pretty b) => Vec t Kind -> Vec v (Maybe (Type t b)) -> State TypingSubproofs [Tactic]
consumed k g = weakens k g $ cleared g

-- K ⊢ Γ ↝w Γ'
weakens :: (Ord b, Pretty b) => Vec t Kind -> Vec v (Maybe (Type t b)) -> Vec v (Maybe (Type t b)) -> State TypingSubproofs [Tactic]
weakens k g g' = do
  let k' = cvtToList k
      [gl, gl'] = map cvtToList [g, g']
      [glt, glt'] = map (map (fmap stripType)) [gl, gl']
  ta <- use tsTypeAbbrevs
  if not cacheWeakeningProofs
    then do proofIds <- kindingAssms (zip gl gl')
            thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
            return [simp_add ["empty_def"], WeakeningTac (ThmList thms)]
    else do
    wmap <- use subproofWeakens
    case M.lookup (k', glt, glt') wmap of
      Nothing -> do mod <- use nameMod
                    let prop = mkApp (mkId "weakening")
                                 [mkList (map deepKind k'),
                                  mkList (map (deepMaybeTy mod ta) gl),
                                  mkList (map (deepMaybeTy mod ta) gl')]
                    proofIds <- kindingAssms (zip gl gl')
                    thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
                    proofId <- newSubproofId
                    subproofWeakens %= M.insert (k', glt, glt') (proofId, (False, prop), [WeakeningTac (ThmList thms)])
                    thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                    return [simp_add ["empty_def"], RuleTac thm]
      Just (proofId, _, _) -> do thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                                 return [simp_add ["empty_def"], RuleTac thm]
  where kindingAssms [] = return []
        kindingAssms ((Just t, _):xs) = liftM2 (:) (kindingRaw k t) (kindingAssms xs)
        kindingAssms (_:xs) = kindingAssms xs

breakConj :: [t] -> [Tactic]
breakConj (x:xs) = [rule "conjI"]
breakConj []     = []

takeTaken :: FieldIndex -> Vec v (Maybe (Type t b)) -> Bool
takeTaken f (Cons x (Cons (Just (TRecord _ ts _)) _)) = snd $ snd (ts!!f)
takeTaken _ _ = error "invalid call to takeTaken"

singleton :: Fin v -> Vec v (Maybe a) -> Vec v (Maybe a)
singleton v env = update (cleared env) v (env `at` v)

mostGeneralKind :: Vec t Kind -> Type t b -> Kind
mostGeneralKind k (TVar v)         = k `at` v
mostGeneralKind k (TVarBang v)     = k0
mostGeneralKind k (TUnit)          = mempty
mostGeneralKind k (TProduct t1 t2) = mostGeneralKind k t1 <> mostGeneralKind k t2
mostGeneralKind k (TSum ts)        = foldl (<>) mempty $ map (mostGeneralKind k) [t | (_, (t, b)) <- ts, not b]
mostGeneralKind k (TFun ti to)     = mempty
mostGeneralKind k (TRecord _ ts s)   = foldl (<>) (sigilKind s) $ map (mostGeneralKind k) [t | (_, (t, b)) <- ts, not b]
mostGeneralKind k (TPrim i)        = mempty
mostGeneralKind k (TString)        = mempty
mostGeneralKind k (TCon n ts s)    = foldl (<>) (sigilKind s) $ map (mostGeneralKind k) ts

kindRule :: Type t b -> String
kindRule TVar     {} = "kind_tvar"
kindRule TVarBang {} = "kind_tvarb"
kindRule TUnit       = "kind_tunit"
kindRule TProduct {} = "kind_tprod"
kindRule TSum     {} = "kind_tsum"
kindRule TFun     {} = "kind_tfun"
kindRule TRecord  {} = "kind_trec"
kindRule TPrim    {} = "kind_tprim"
kindRule TString     = "kind_tprim"
kindRule TCon     {} = "kind_tcon"

envOf = eexprEnv
typeOf = eexprType

peel :: Vec ('Suc v) t -> Vec v t
peel (Cons x xs) = xs

peel2 = peel . peel

(<|>) :: Vec v (Maybe a) -> Vec v (Maybe a) -> Vec v (Maybe a)
(<|>) (Cons Nothing xs)  (Cons Nothing ys)  = Cons Nothing  (xs <|> ys)
(<|>) (Cons _ xs)        (Cons (Just y) ys) = Cons (Just y) (xs <|> ys)
(<|>) (Cons (Just x) xs) (Cons _ ys)        = Cons (Just x) (xs <|> ys)
(<|>) Nil Nil = Nil
#if __GLASGOW_HASKELL__ < 711
(<|>) _ _ = __ghc_t4139 "ProofGen.<|>"
#endif

cleared :: Vec a (Maybe t) -> Vec a (Maybe t)
cleared = emptyvec . Vec.length
    where emptyvec :: SNat a -> Vec a (Maybe t)
          emptyvec (SSuc n) = Cons Nothing $ emptyvec n
          emptyvec (SZero)  = Nil

deepKindStr (K e s d) = "{" ++ intercalate "," [flag | (f, flag) <- zip [e, s, d] ["E", "S", "D"], f] ++ "}"

deepMaybe :: Maybe Term -> Term
deepMaybe Nothing = mkId "None"
deepMaybe (Just x) = mkApp (mkId "Some") [x]

deepMaybeTy :: (Ord b, Pretty b) => NameMod -> TypeAbbrevs -> Maybe (Type t b) -> Term
deepMaybeTy mod ta = deepMaybe . fmap (deepType mod ta)


