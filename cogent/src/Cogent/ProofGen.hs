--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Cogent.ProofGen where

import Cogent.Common.Types
import Cogent.Common.Syntax
#if __GLASGOW_HASKELL__ < 711
import Cogent.Compiler
#endif
import Cogent.Core
import Cogent.Vec hiding (splitAt, length, zipWith, zip, unzip)
import qualified Cogent.Vec as Vec
import Cogent.Deep
import Cogent.Util

import Control.Lens (makeLenses, (%=), (.=), use)
import Control.Monad.State.Strict
import Data.List
import Data.Map (Map)
import Data.Maybe (catMaybes)
import qualified Data.Map as M
import Isabelle.InnerAST hiding (Type)

type Xi a = [Definition TypedExpr a]
data EnvExpr t v a = EE { eexprType :: Type t , eexprExpr :: Expr t v a EnvExpr , eexprEnv :: Vec v (Maybe (Type t))} deriving (Show)

instance Functor (EnvExpr t v) where
  fmap f (EE t e env) = EE t (ffmap f e) env

data Thm = Thm String
         | NthThm String Int
         | ThmInst String [(String, String)]

data Tactic = RuleTac Thm
            | Simplifier [Thm] [Thm]
            | Force [Thm]
            | WeakeningTac [Thm]
            | SplitsTac Int [(Int, [Tactic])]

instance Show Thm where
  show (Thm thm) = "@{thm " ++ thm ++ "}"
  show (NthThm thm n) = "(nth @{thms " ++ thm ++ "} (" ++ show n ++ "-1))"
  show (ThmInst thm insts) = "@{thm " ++ thm ++ "[where " ++
                                intercalate " and " [ var ++ " = \"" ++ term ++ "\"" | (var, term) <- insts ] ++ "]}"

instance Show Tactic where
  show (RuleTac thm) = "(RTac " ++ show thm ++ ")"
  show (Simplifier adds dels) = "(SimpTac " ++ show (adds, dels) ++ ")"
  show (Force adds) = "(ForceTac " ++ show adds ++ ")"
  show (WeakeningTac kindThms) = "(WeakeningTac " ++ show kindThms ++")"
  show (SplitsTac n tacs) = "(SplitsTac " ++ show (n, tacs) ++ ")"

rule thm = RuleTac (Thm thm)
rule_tac thm insts = RuleTac (ThmInst thm insts)

simp                 = simp_add_del [] []
simp_add thms        = simp_add_del thms []
simp_del thms        = simp_add_del [] thms
simp_add_del add del = Simplifier (map Thm add) (map Thm del)
force_simp add       = Force (map Thm add)

data Hints = KindingTacs [Tactic]
           | TTSplitBangTacs [Tactic]
           | TypingTacs [Tactic]
  deriving Show

data Type'
  = TVar' Int
  | TVarBang' Int
  | TCon' TypeName [Type'] Sigil
  | TFun' Type' Type'
  | TPrim' PrimInt
  | TString'
  | TSum' [(TagName, Type')]
  | TProduct' Type' Type'
  | TRecord' [(FieldName, (Type', Bool))] Sigil
  | TUnit'
  deriving (Eq, Ord)

deepType' :: Type' -> Term
deepType' (TVar' v) = mkApp (mkId "TVar") [mkInt $ toInteger v]
deepType' (TVarBang' v) = mkApp (mkId "TVarBang") [mkInt $ toInteger v]
deepType' (TCon' tn ts s) = mkApp (mkId "TCon") [mkString tn, mkList (map deepType' ts), deepSigil s]
deepType' (TFun' ti to) = mkApp (mkId "TFun") [deepType' ti, deepType' to]
deepType' (TPrim' pt) = mkApp (mkId "TPrim") [deepPrimType pt]
deepType' (TString') = mkApp (mkId "TPrim") [mkId "String"]
deepType' (TSum' alts) = mkApp (mkId "TSum") [mkList $ map (\(n,t) -> mkPair (mkString n) (deepType' t)) alts]
deepType' (TProduct' t1 t2) = mkApp (mkId "TProduct") [deepType' t1, deepType' t2]
deepType' (TRecord' fs s) = mkApp (mkId "TRecord") [mkList $ map (\(fn,(t,b)) -> mkPair (deepType' t) (mkBool b)) fs, deepSigil s]
deepType' (TUnit') = mkId "TUnit"

stripType :: Type t -> Type'
stripType (TVar n) = TVar' (finInt n)
stripType (TVarBang n) = TVarBang' (finInt n)
stripType (TCon t ts s) = TCon' t (map stripType ts) s
stripType (TFun t u) = TFun' (stripType t) (stripType u)
stripType (TPrim t) = TPrim' t
stripType TString = TString'
stripType (TSum ts) = TSum' (map (\(n,(t,_)) -> (n, stripType t)) ts)  -- FIXME: cogent.1
stripType (TProduct t u) = TProduct' (stripType t) (stripType u)
stripType (TRecord fs s) = TRecord' (map (\(n, (t, tk)) -> (n, (stripType t, tk))) fs) s
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
typingSubproofsInit mod ta = TypingSubproofs 0 M.empty M.empty M.empty M.empty ta mod

newSubproofId = do
  i <- use genId
  let i' = i + 1
  i' `seq` genId .= i'
  return i'

tacSequence :: [State a [t]] -> State a [t]
tacSequence = fmap concat . sequence

kindingHint :: Vec t Kind -> Type t -> State TypingSubproofs [Hints]
kindingHint k t = ((:[]) . KindingTacs) `fmap` kinding k t

follow_tt :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec vx (Maybe (Type t))
          -> Vec vy (Maybe (Type t)) -> State TypingSubproofs [Hints]
follow_tt k env env_x env_y = tacSequence (map (kindingHint k) new)
  where
    l = toInt (Vec.length env)
    n_x = take (toInt (Vec.length env_x) - l) (cvtToList env_x)
    n_y = take (toInt (Vec.length env_y) - l) (cvtToList env_y)
    new = catMaybes (n_x ++ n_y)

proofSteps :: Xi a -> Vec t Kind -> Type t -> EnvExpr t v a
           -> State TypingSubproofs [Hints]
proofSteps xi k ti x = tacSequence [ kindingHint k ti, ttyping xi k x ]

ttyping :: Xi a -> Vec t Kind -> EnvExpr t v a -> State TypingSubproofs [Hints]
ttyping xi k (EE t' (Split a x y) env) = tacSequence [ -- Ξ, K, Γ ⊢ Split x y : t' if
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                            -- Ξ, K, Γ1 ⊢ x : TProduct t u
  ttyping xi k y                             -- Ξ, K, Some t # Some u # Γ2 ⊢ y : t'
  ]
ttyping xi k (EE u (Let a x y) env) = tacSequence [ -- Ξ, K, Γ ⊢ Let x y : u if
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                           -- Ξ, K, Γ1 ⊢ x : t
  ttyping xi k y                            -- Ξ, K, Some t # Γ2 ⊢ y : u
  ]
ttyping xi k (EE u (LetBang is a x y) env) = tacSequence [ -- Ξ, K, Γ ⊢ LetBang is x y : u if
  ttsplit_bang k 0 (map (finInt . fst) is) env (envOf x),
  follow_tt k env (envOf x) (envOf y),
  ttyping xi k x,                                   -- Ξ, K, Γ1 ⊢ x : t
  ttyping xi k y,                                   -- Ξ, K, Some t # Γ2 ⊢ y : u
  kindingHint k (typeOf x)                          -- K ⊢ t :κ k
  ]
ttyping xi k (EE t (If x a b) env) = tacSequence [ -- Ξ, K, Γ ⊢ If x a b : t if
  ttyping xi k x,                                -- Ξ, K, Γ1 ⊢ x : TPrim Bool
  ttyping xi k a,                                -- Ξ, K, Γ2 ⊢ a : t
  ttyping xi k b                                 -- Ξ, K, Γ2 ⊢ b : t
  ]
ttyping xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) = tacSequence [ -- Ξ, K, Γ ⊢ Case x tag a b : u if
  follow_tt k (envOf x) (envOf a) (envOf b),
  ttyping xi k x,                                       -- Ξ, K, Γ1 ⊢ x : TSum ts
  ttyping xi k a,                                       -- Ξ, K, (Some t # Γ) ⊢ a : u
  ttyping xi k b                                        -- Ξ, K, (Some (TSum (filter (λ x. fst x ≠ tag) ts)) # Γ2) ⊢ b : u
  ]
ttyping xi k (EE u (Take a e@(EE (TRecord ts s) _ _) f e') env) = tacSequence [ -- Ξ, K, Γ T⊢ Take e f e' : u if
  follow_tt k env (envOf e) (envOf e'),
  ttyping xi k e,                             -- Ξ, K, Γ1 T⊢ e : TRecord ts s
  kindingHint k (fst $ snd $ ts !! f),        -- K ⊢ t :κ k
  ttyping xi k e'                             -- Ξ, K, Γ2 T⊢ e' : u
  ]
ttyping xi k e = fmap ((:[]) . TypingTacs) $ typingWrapper xi k e

typingWrapper :: Xi a -> Vec t Kind -> EnvExpr t v a
              -> State TypingSubproofs [Tactic]
typingWrapper xi k (EE t (Variable i) env) = tacSequence [ ]
typingWrapper xi k (EE t (Struct fs) env)
    | allVars (map (eexprExpr . snd) fs) = tacSequence [ ]
typingWrapper xi k (EE (TPrim t) (Op o es) env)
    | allVars (map eexprExpr es) = tacSequence [ ]
typingWrapper xi k e = typing xi k e

allVars :: [Expr a b c d] -> Bool
allVars (Variable _ : vs) = allVars vs
allVars [] = True
allVars _ = False

typing :: Xi a -> Vec t Kind -> EnvExpr t v a -> State TypingSubproofs [Tactic]
typing xi k (EE _ Unit env) = tacSequence [
  return [rule "typing_unit"], -- Ξ, K, Γ ⊢ Unit : TUnit if
  consumed k env                 -- K ⊢ Γ consumed
  ]

typing xi k (EE _ (ILit _ t) env) = tacSequence [
  return [rule "typing_lit'"], -- Ξ, K, Γ ⊢ Lit l : TPrim t if
  consumed k env,                -- K ⊢ Γ consumed
  return [simp]                  -- t = lit_type l
  ]

typing xi k (EE _ (SLit t) env) = tacSequence [
  return [rule "typing_lit'"], -- Ξ, K, Γ ⊢ Lit l : TPrim t if
  consumed k env,                -- K ⊢ Γ consumed
  return [simp]                  -- t = lit_type l
  ]

typing xi k (EE t (Variable i) env) = tacSequence [
  return $ [rule "typing_var"], -- Ξ, K, Γ ⊢ Var i : t if
  weakens k env (singleton (fst i) env), -- K ⊢ Γ ↝w singleton (length Γ) i t
  return [simp]                          -- i < length Γ
  ]

typing xi k (EE _ (Esac x) _) = tacSequence [
  return [rule "typing_esac"], -- Ξ, K, Γ ⊢ Esac x : t if
  typing xi k x                  -- Ξ, K, Γ ⊢ x : TSum [(tag,t)]
  ]

typing xi k (EE _ (Promote ty e) env)
  | EE (TPrim pt) _ _ <- e, TPrim pt' <- ty, pt /= Boolean = tacSequence [
    return [rule "typing_cast"], -- Ξ, K, Γ ⊢ Cast τ' e : TPrim (Num τ') if
    typing xi k e,                 -- Ξ, K, Γ ⊢ e : TPrim (Num τ)
    return [simp]                  -- upcast_valid τ τ'
    ]
  | EE (TSum _) (Con cn v) _ <- e, TSum as <- ty = typing xi k (EE (TSum as) (Con cn v) env) -- inlined Con
  | TSum as <- ty = tacSequence [
    return [rule "typing_prom"], -- Ξ, K, Γ ⊢ Promote ts' e : TSum ts'
    typing xi k e,                 -- Ξ, K, Γ ⊢ e : TSum ts
    return [simp],                 -- set ts ⊆ set ts'
    wellformedAll k (map (fst . snd) as),  -- K ⊢* (map snd ts') wellformed  -- FIXME: cogent.1
    return (distinct (map fst as)) -- distinct (map fst ts')
    ]

typing xi k (EE y (App a b) env) = tacSequence [
  return [rule "typing_app"], -- Ξ, K, Γ ⊢ App a b : y if
  splits k env (envOf a) (envOf b), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k a,                    -- Ξ, K, Γ1 ⊢ a : TFun x y
  typing xi k b                     -- Ξ, K, Γ2 ⊢ b : x
  ]

typing xi k (EE _ (Tuple t u) env) = tacSequence [
  return [rule "typing_tuple"], -- Ξ, K, Γ ⊢ Tuple t u : TProduct T U if
  splits k env (envOf t) (envOf u), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k t,                    -- Ξ, K, Γ1 ⊢ t : T
  typing xi k u                     -- Ξ, K, Γ2 ⊢ u : U
  ]

typing xi k (EE u (Let a x y) env) = tacSequence [
  return [rule "typing_let"], -- Ξ, K, Γ ⊢ Let x y : u if
  splits k env (envOf x) (peel $ envOf y), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                           -- Ξ, K, Γ1 ⊢ x : t
  typing xi k y                            -- Ξ, K, (Some t # Γ2) ⊢ y : u
  ]

typing xi k (EE t' (Split a x y) env) = tacSequence [
  return [rule "typing_split"], -- Ξ, K, Γ ⊢ Split x y : t' if
  splits k env (envOf x) (peel2 $ envOf y), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                            -- Ξ, K, Γ1 ⊢ x : TProduct t u
  typing xi k y                             -- Ξ, K, (Some t)#(Some u)#Γ2 ⊢ y : t'
  ]

typing xi k (EE t (Member e f) env) = tacSequence [
  return [rule "typing_member"], -- Ξ, K, Γ ⊢ Member e f : t if
  typing xi k e,                   -- Ξ, K, Γ ⊢ e : TRecord ts s
  kinding k (eexprType e),         -- K ⊢ TRecord ts s :κ k (* k introduced *)
  return [simp, simp, simp]        -- S ∈ k;  f < length ts; ts ! f = (t, False)
  ]

typing xi k (EE t (Struct fs) env) = tacSequence [
  return [rule "typing_struct'"], -- Ξ, K, Γ ⊢ Struct es : TRecord ts' Unboxed
  typingAll xi k env (map snd fs),  -- Ξ, K, Γ ⊢* es : ts
  return [simp]                     -- ts' = (zip ts (replicate (length ts) Fal
  ]

typing xi k (EE t (If x a b) env) = tacSequence [
  return [rule "typing_if"], -- Ξ, K, Γ ⊢ If x a b : t if
  splits k env (envOf x) (envOf a <|> envOf b), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                                -- Ξ, K, Γ1 ⊢ x : TPrim Bool
  typing xi k a,                                -- Ξ, K, Γ2 ⊢ a : t
  typing xi k b                                 -- Ξ, K, Γ2 ⊢ b : t
  ]

typing xi k (EE (TPrim t) (Op o es) env) = tacSequence [
  return [rule "typing_prim'"], -- Ξ, K, Γ ⊢ Prim o es : TPrim t if
  return [simp],                  -- prim_op_type oper = (ts,t)
  return [simp],                  -- ts' = map TPrim ts;
  typingAll xi k env es           -- Ξ, K, Γ ⊢* args : ts'
  ]

typing xi k (EE (TSum ts) (Con tag e) env) = tacSequence [
  return [rule "typing_con"], -- Ξ, K, Γ ⊢ Con ts tag x : TSum ts if
  typing xi k e,                 -- Ξ, K, Γ ⊢ x : t
  return [simp],                 -- (tag,t) ∈ set ts
  wellformedAll k (map (fst . snd) ts),  -- K ⊢* (map snd ts) wellformed  -- FIXME: cogent.1
  return (distinct (map fst ts)) -- distinct (map fst ts)
  ]

typing xi k (EE u (Case x _ (_,_,a) (_,_,b)) env) = tacSequence [
  return [rule "typing_case"], -- Ξ, K, Γ ⊢ Case x tag a b : u if
  splits k env (envOf x) (peel $ envOf b <|> envOf a), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k x,                                       -- Ξ, K, Γ1 ⊢ x : TSum ts
  return [simp],                                       -- (tag, t) ∈ set ts
  typing xi k a,                                       -- Ξ, K, (Some t # Γ) ⊢ a : u
  typing xi k b                                        -- Ξ, K, (Some (TSum (filter (λ x. fst x ≠ tag) ts)) # Γ2) ⊢ b : u
  ]

typing xi k (EE u (Take a e@(EE (TRecord ts s) _ _) f e') env) = tacSequence [
  return [rule "typing_take"], -- Ξ, K, Γ ⊢ Take e f e' : u if
  splits k env (envOf e) (peel2 $ envOf e'), -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k e,                             -- Ξ, K, Γ1 ⊢ e : TRecord ts s
  return [simp, simp, simp],                 -- s ≠ ReadOnly; f < length ts; ts ! f = (t, False) (* instantiates t *)
  kinding k (fst $ snd $ ts !! f),           -- K ⊢ t :κ k
  return (sharableOrTaken f (envOf e')),     -- S ∈ k ∨ taken (* instantiates taken *)
  return [simp],
  typing xi k e'                             -- Ξ, K, (Some t # Some (TRecord (ts [f := (t,taken)]) s) # Γ2) ⊢ e' : u
  ]

typing xi k (EE ty (Put e1@(EE (TRecord ts s) _ _) f e2@(EE t _ _)) env) = tacSequence [
  return [rule "typing_put'"], -- Ξ, K, Γ ⊢ Put e f e' : TRecord ts' s if
  splits k env (envOf e1) (envOf e2),                -- K ⊢ Γ ↝ Γ1 | Γ2
  typing xi k e1,                                    -- Ξ, K, Γ1 ⊢ e : TRecord ts s
  return [simp, simp],                               -- s ≠ ReadOnly; f < length ts;
  return [simp_del ["Product_Type.prod.inject"]],    -- ts ! f = (t, taken)
  kinding k t,                                       -- K ⊢ t :κ k
  return (destroyableOrTaken (snd $ snd $ ts !! f)), -- D ∈ k ∨ taken
  typing xi k e2,                                    -- Ξ, K, Γ2 ⊢ e' : t
  return [simp]                                      -- ts' = (ts [f := (t,False)])
  ]

typing xi k (EE t' (Fun f ts _) env) = case findfun f xi of
    FunDef _ _ ks' t u _ ->
      let ks = fmap snd ks' in tacSequence [
        return [rule "typing_fun'"], -- Ξ, K, Γ ⊢ Fun f ts : t' if
        do ta <- use tsTypeAbbrevs
           mod <- use nameMod
           let unabbrev | M.null (fst ta) = "" | otherwise = " " ++ typeAbbrevBucketName
           return [rule (fn_proof (mod f) unabbrev)], -- Ξ, ks, (tt, [Some t]) T⊢ f : u
        allKindCorrect k ts ks, -- list_all2 (kinding K) ts ks
        return [simp],          -- t' = instantiate ts (TFun t u)
        wellformed ks t,        -- ks ⊢ t wellformed
        consumed k env          -- K ⊢ Γ consumed
        ]
    AbsDecl _ _ ks' t u ->
      let ks = fmap snd ks' in tacSequence [
        return [rule "typing_afun'"], -- Ξ, K, Γ ⊢ AFun f ts : t' if
        do ta <- use tsTypeAbbrevs
           mod <- use nameMod
           let unabbrev | M.null (fst ta) = ""
                        | otherwise = "[unfolded " ++ typeAbbrevBucketName ++ "]"
           return [simp_add ["\\<Xi>_def", mod f ++ "_type_def" ++ unabbrev]], -- Ξ f = (ks, t, u)
        allKindCorrect k ts ks,   -- list_all2 (kinding K) ts ks
        return [simp],            -- t' = instantiate ts (TFun t u)
        wellformed ks (TFun t u), -- ks ⊢ TFun t u wellformed
        consumed k env            -- K ⊢ Γ consumed
        ]

    _ -> error $ "ProofGen Fun: bad function call " ++ show f

  where findfun f (def@(FunDef _ fn _ _ _ _):fs) | f == fn = def
        findfun f (def@(AbsDecl _ fn _ _ _) :fs) | f == fn = def
        findfun f (_:fs) = findfun f fs
        findfun f [] = error $ "ProofGen Fun: no such function " ++ show f

        fn_proof fn unabbrev =
          fn ++ "_typecorrect[simplified " ++ fn ++ "_type_def " ++
                              fn ++ "_typetree_def" ++ unabbrev ++ ", simplified]"

typing xi k (EE u (LetBang is a x y) env) = tacSequence [
  return [rule "typing_letb"], -- Ξ, K, Γ ⊢ LetBang is x y : u if
  error "split_bang: should be ttyping LetBang",
  typing xi k x,                                  -- Ξ, K, Γ1 ⊢ x : t
  typing xi k y,                                  -- Ξ, K, (Some t # Γ2) ⊢ y : u
  kinding k (typeOf x),                           -- K ⊢ t :κ k
  return [simp]                                   -- E ∈ k
  ]

typing xi k _ = error "attempted to generate proof of ill-typed program"

typingAll :: Xi a -> Vec t Kind -> Vec v (Maybe (Type t)) -> [EnvExpr t v a] -> State TypingSubproofs [Tactic]
-- Γ = empty n ⟹ Ξ, K, Γ ⊢* [] : []
typingAll xi k g [] = return [rule_tac "typing_all_empty'" [("n", show . Vec.toInt . Vec.length $ g)],
                              simp_add ["empty_def"]]
-- Ξ, K, Γ ⊢* (e # es) : (t # ts)
typingAll xi k g (e:es) =
  let envs = foldl (<|>) (cleared g) (map envOf es) in tacSequence [
    return [rule "typing_all_cons"], splits k g (envOf e) envs, typing xi k e, typingAll xi k envs es
    ]

kinding :: Vec t Kind -> Type t -> State TypingSubproofs [Tactic]
kinding k t = do
  proofId <- kindingRaw k t
  thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
  return [RuleTac thm]

kindingRaw :: Vec t Kind -> Type t -> State TypingSubproofs SubproofId
kindingRaw k t = do
  let k' = cvtToList k
      t' = stripType t
      gk = mostGeneralKind k t
  ta <- use tsTypeAbbrevs
  kmap <- use subproofKinding
  case M.lookup (k', t', gk) kmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "kinding") [mkList (map deepKind k'), deepType mod ta t, deepKind gk]
                  tac <- tacSequence [return [rule_tac (kindRule t) [("k", deepKindStr gk)]], kind k t gk]
                  proofId <- newSubproofId
                  subproofKinding %= M.insert (k', t', gk) (proofId, (False, prop), tac)
                  return proofId
    Just (proofId, _, _) -> return proofId

kinding' :: Vec t Kind -> Type t -> Kind -> State TypingSubproofs [Tactic]
kinding' ks t k = do
  let ks' = cvtToList ks
      t' = stripType t
  ta <- use tsTypeAbbrevs
  kmap <- use subproofKinding
  case M.lookup (ks', t', k) kmap of
    Nothing -> do mod <- use nameMod
                  let prop = mkApp (mkId "kinding") [mkList (map deepKind ks'), deepType mod ta t, deepKind k]
                  tac <- tacSequence [return [rule (kindRule t)], kind ks t k]
                  proofId <- newSubproofId
                  subproofKinding %= M.insert (ks', t', k) (proofId, (False, prop), tac)
                  thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                  return [RuleTac thm]
    Just (proofId, _, _) -> do thm <- thmTypeAbbrev $ typingSubproofPrefix ++ show proofId
                               return [RuleTac thm]

kind :: Vec t Kind -> Type t -> Kind -> State TypingSubproofs [Tactic]
kind ks (TVar v)         k = return [simp, simp]
kind ks (TVarBang v)     k = return [simp, simp]
kind ks (TUnit)          k = return []
kind ks (TProduct t1 t2) k = tacSequence [kinding' ks t1 k, kinding' ks t2 k]
kind ks (TSum ts)        k = tacSequence [return [simp, simp], kindingAll ks (map (fst . snd) ts) k]  -- FIXME: cogent.1
kind ks (TFun ti to)     k = tacSequence [kinding ks ti, kinding ks to]
kind ks (TRecord ts s)   k = tacSequence [kindingRecord ks (map snd ts) k, return [simp]]
kind ks (TPrim i)        k = return []
kind ks (TString)        k = return []
kind ks (TCon n ts s)    k = tacSequence [kindingAll ks ts k, return [simp]]


kindingAll :: Vec t Kind -> [Type t] -> Kind -> State TypingSubproofs [Tactic]
kindingAll ks []     k = return [rule "kind_all_empty"]
kindingAll ks (t:ts) k = tacSequence [return [rule "kind_all_cons"], kinding' ks t k, kindingAll ks ts k]

kindingRecord :: Vec t Kind -> [(Type t, Bool)] -> Kind -> State TypingSubproofs [Tactic]
kindingRecord ks ((t, False):ts) k = tacSequence [return [rule "kind_record_cons1"], kinding' ks t k, kindingRecord ks ts k]
kindingRecord ks ((t, True) :ts) k = tacSequence [return [rule "kind_record_cons2"], kinding ks t, kindingRecord ks ts k]
kindingRecord _ [] _ = return [rule "kind_record_empty"]

allKindCorrect :: Vec t' Kind -> [Type t'] -> Vec t Kind -> State TypingSubproofs [Tactic]
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
                  tac <- tacSequence [return [Simplifier [] [NthThm "HOL.simp_thms" 25, NthThm "HOL.simp_thms" 26]],
                                      allKindCorrect' k ts ks]
                  proofId <- newSubproofId
                  subproofAllKindCorrect %= M.insert (k', ts', ks') (proofId, (False, prop), tac)
                  return [rule $ typingSubproofPrefix ++ show proofId]
    Just (proofId, _, _) -> return [rule $ typingSubproofPrefix ++ show proofId]

allKindCorrect' :: Vec t' Kind -> [Type t'] -> Vec t Kind -> State TypingSubproofs [Tactic]
allKindCorrect' kind (t:ts) (Cons k ks) = tacSequence [return (breakConj ts), kinding' kind t k, allKindCorrect' kind ts ks]
allKindCorrect' _ [] Nil = return []
allKindCorrect' _ _ _ = error "kind mismatch"

splits :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs [Tactic]
splits k g g1 g2 = ((:[]) . SplitsTac (length (cvtToList g))) `fmap` splitsHint 0 k g g1 g2

ttsplit_innerHint :: Vec t Kind -> Maybe (Type t) -> Maybe (Type t) -> Maybe (Type t) -> State TypingSubproofs [Hints]
ttsplit_innerHint k Nothing Nothing Nothing = return []
ttsplit_innerHint k (Just t) _ _            = kindingHint k t
ttsplit_innerHint _ g x y = error $ "bad ttsplit: " ++ show (g, x, y)

split :: Vec t Kind -> Maybe (Type t) -> Maybe (Type t) -> Maybe (Type t) -> State TypingSubproofs [Tactic]
split k Nothing  Nothing  Nothing  = return [rule "split_comp.none"]
split k (Just t) (Just _) Nothing  = tacSequence [return [rule "split_comp.left"], kinding k t]
split k (Just t) Nothing  (Just _) = tacSequence [return [rule "split_comp.right"], kinding k t]
split k (Just t) (Just _) (Just _) = tacSequence [return [rule "split_comp.share"], kinding k t, return [simp]]
split k g x y = error $ "bad split: " ++ show (g, x, y)

splitsHint :: Int -> Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs [(Int, [Tactic])]
splitsHint n k (Cons g gs) (Cons x xs) (Cons y ys) = liftM2 (++) (splitHint n k g x y) (splitsHint (n+1) k gs xs ys)
splitsHint _ k Nil         Nil         Nil         = return []
#if __GLASGOW_HASKELL__ < 711
splitsHint _ _ _ _ _ = __ghc_t4139 "ProofGen.splitsHint"
#endif

splitHint :: Int -> Vec t Kind -> Maybe (Type t) -> Maybe (Type t) -> Maybe (Type t) -> State TypingSubproofs [(Int, [Tactic])]
splitHint _ k Nothing  Nothing  Nothing  = return []
splitHint n k (Just t) (Just _) Nothing  = (\t -> [(n, [rule "split_comp.left"] ++ t)]) `fmap` kinding k t
splitHint n k (Just t) Nothing  (Just _) = (\t -> [(n, [rule "split_comp.right"] ++ t)]) `fmap` kinding k t
splitHint n k (Just t) (Just _) (Just _) = (\t -> [(n, [rule "split_comp.share"] ++ t ++ [simp])]) `fmap` kinding k t
splitHint _ k g x y = error $ "bad split: " ++ show (g, x, y)

ttsplit_bang :: Vec t Kind -> Int -> [Int] -> Vec v (Maybe (Type t))
             -> Vec v (Maybe (Type t)) -> State TypingSubproofs [Hints]
ttsplit_bang k ix ixs (Cons g gs) (Cons (Just x) xs) = do
    this <- if ix `elem` ixs then kindingHint k x else return []
    rest <- ttsplit_bang k (ix + 1) ixs gs xs
    return (this ++ rest)
ttsplit_bang k ix ixs (Cons g gs) (Cons Nothing xs) =
    if ix `elem` ixs then error "bad split_bang"
        else ttsplit_bang k (ix + 1) ixs gs xs
ttsplit_bang k ix ixs Nil Nil = return []
#if __GLASGOW_HASKELL__ < 711
ttsplit_bang _ _ _ _ _ = error "bad split_bang end"
#endif
distinct _ = [simp]

-- K ⊢ τ wellformed ≡ ∃k. K ⊢ τ :κ k
wellformed :: Vec t Kind -> Type t -> State TypingSubproofs [Tactic]
wellformed ks t = tacSequence [return [simp, rule_tac "exI" [("x", deepKindStr $ mostGeneralKind ks t)]], kinding ks t]

-- K ⊢* τs wellformed ≡ ∃k. K ⊢* τs :κ k
wellformedAll :: Vec t Kind -> [Type t] -> State TypingSubproofs [Tactic]
wellformedAll ks ts = tacSequence [return [simp, rule_tac "exI" [("x", deepKindStr k)]],
                                   kindingAll ks ts k]
  where k = foldr kIntersect topKind (map (mostGeneralKind ks) ts)

-- K ⊢ Γ consumed ≡ K ⊢ Γ ↝w empty (length Γ)
consumed :: Vec t Kind -> Vec v (Maybe (Type t)) -> State TypingSubproofs [Tactic]
consumed k g = weakens k g $ cleared g

-- K ⊢ Γ ↝w Γ'
weakens :: Vec t Kind -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> State TypingSubproofs [Tactic]
weakens k g g' = do
  let k' = cvtToList k
      [gl, gl'] = map cvtToList [g, g']
      [glt, glt'] = map (map (fmap stripType)) [gl, gl']
  ta <- use tsTypeAbbrevs
  if not cacheWeakeningProofs
    then do proofIds <- kindingAssms (zip gl gl')
            thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
            return [simp_add ["empty_def"], WeakeningTac thms]
    else do
    wmap <- use subproofWeakens
    case M.lookup (k', glt, glt') wmap of
      Nothing -> do mod <- use nameMod
                    let prop = mkApp (mkId "weakening")
                                 [mkList (map deepKind k'), mkList (map (deepMaybeTy mod ta) gl), mkList (map (deepMaybeTy mod ta) gl')]
                    proofIds <- kindingAssms (zip gl gl')
                    thms <- mapM (thmTypeAbbrev . (typingSubproofPrefix ++) . show) (nub proofIds)
                    proofId <- newSubproofId
                    subproofWeakens %= M.insert (k', glt, glt') (proofId, (False, prop), [WeakeningTac thms])
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

takeTaken :: FieldIndex -> Vec v (Maybe (Type t)) -> Bool
takeTaken f (Cons x (Cons (Just (TRecord ts s)) _)) = snd $ snd (ts!!f)
takeTaken _ _ = error "invalid call to takeTaken"

sharableOrTaken :: FieldIndex -> Vec v (Maybe (Type t)) -> [Tactic]
sharableOrTaken f e | takeTaken f e = [rule_tac "disjI2" [("Q", "True")], simp]
                    | otherwise     = [rule "disjI1", simp]

destroyableOrTaken True  = [rule_tac "disjI2" [("Q", "True")], simp]
destroyableOrTaken False = [rule "disjI1", simp]

singleton :: Fin v -> Vec v (Maybe a) -> Vec v (Maybe a)
singleton v env = update (cleared env) v (env `at` v)

mostGeneralKind :: Vec t Kind -> Type t -> Kind
mostGeneralKind k (TVar v)         = k `at` v
mostGeneralKind k (TVarBang v)     = sigilKind ReadOnly
mostGeneralKind k (TUnit)          = topKind
mostGeneralKind k (TProduct t1 t2) = mostGeneralKind k t1 `kIntersect` mostGeneralKind k t2
mostGeneralKind k (TSum ts)        = foldl kIntersect topKind $ map (mostGeneralKind k . fst . snd) ts  -- FIXME: cogent.1
mostGeneralKind k (TFun ti to)     = topKind
mostGeneralKind k (TRecord ts s)   = foldl kIntersect (sigilKind s) $ map (mostGeneralKind k) [t | (_, (t, b)) <- ts, not b]
mostGeneralKind k (TPrim i)        = topKind
mostGeneralKind k (TString)        = topKind
mostGeneralKind k (TCon n ts s)    = foldl kIntersect (sigilKind s) $ map (mostGeneralKind k) ts


kindRule :: Type t -> String
kindRule (TVar v)         = "kind_tvar"
kindRule (TVarBang v)     = "kind_tvarb"
kindRule (TUnit)          = "kind_tunit"
kindRule (TProduct t1 t2) = "kind_tprod"
kindRule (TSum ts)        = "kind_tsum"
kindRule (TFun ti to)     = "kind_tfun"
kindRule (TRecord ts s)   = "kind_trec"
kindRule (TPrim i)        = "kind_tprim"
kindRule (TString)        = "kind_tprim"
kindRule (TCon n ts s)    = "kind_tcon"

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


topKind = K True True True

-- kind intersection
kIntersect :: Kind -> Kind -> Kind
kIntersect (K a b c) (K a' b' c') = K (a && a') (b && b') (c && c')

deepKindStr (K e s d) = "{" ++ intercalate "," [flag | (f, flag) <- zip [e, s, d] ["E", "S", "D"], f] ++ "}"

deepMaybe :: Maybe Term -> Term
deepMaybe Nothing = mkId "None"
deepMaybe (Just x) = mkApp (mkId "Some") [x]

deepMaybeTy :: NameMod -> TypeAbbrevs -> Maybe (Type t) -> Term
deepMaybeTy mod ta = deepMaybe . fmap (deepType mod ta)


