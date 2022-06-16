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
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuasiQuotes #-}

module Cogent.Isabelle.TypeProofs where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Core
import Cogent.Inference
import Cogent.Isabelle.Deep (deepDefinitions, deepTypeAbbrevs, getTypeAbbrevs, TypeAbbrevs)
import Cogent.Isabelle.IsabelleName
import Cogent.Isabelle.ProofGen
import Cogent.Util (NameMod)
import Data.Fin
import Data.LeafTree
import Data.Vec hiding (splitAt, length, zipWith, zip, unzip, head)
import qualified Data.Vec as V
import Isabelle.ExprTH
import qualified Isabelle.InnerAST as I
import Isabelle.InnerAST hiding (Type)
import Isabelle.OuterAST as O

import Control.Arrow (second)
import Control.Monad.State.Strict
import Data.Char
import Data.Foldable
#if MIN_VERSION_base(4,15,0)
import Data.List hiding (singleton)
#else
import Data.List
#endif
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Nat as Nat
import Data.Nat ( (=?) )
import Data.Maybe (mapMaybe)
import Data.Ord (comparing)
import Data.PropEq( (:=:)( Refl ) )
import Lens.Micro ((^.))
import Lens.Micro.Mtl (use)
import Numeric
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen hiding ((</>))
import Text.Printf
import Text.Show

data TypeSplitKind = TSK_R | TSK_L | TSK_S | TSK_NS
  deriving Eq
data TypingTree t = TyTrLeaf
                  | TyTrSplit [Maybe TypeSplitKind] (TreeCtx t) (TreeCtx t)
type TreeCtx t = ([Maybe (Type t VarName)], TypingTree t)

deepTypeProof :: (Pretty a) => NameMod -> Bool -> Bool -> String -> [Definition TypedExpr a VarName] -> Map FunName (FunctionType VarName) -> String -> Doc
deepTypeProof mod withDecls withBodies thy decls fts log =
  let header = (string ("(*\n" ++ log ++ "\n*)\n") <$>)
      ta = getTypeAbbrevs mod decls
      imports = if __cogent_fml_typing_tree
                then
                  ["Cogent.TypeProofGen",
                   "Cogent.AssocLookup"]
                else ["Cogent.CogentHelper"]
      proofDecls | withDecls  = deepTypeAbbrevs mod ta ++ deepDefinitions mod ta decls fts
                                ++ funTypeEnv mod decls ++ funDefEnv decls
                                ++ funTypeTrees mod ta decls
                 | otherwise = []
      proofBodies | withBodies = [TheoryString "ML \\<open> open TTyping_Tactics \\<close>"] ++
                                 concatMap (\(proofId, prop, script) ->
                                              formatSubproof ta (typingSubproofPrefix ++ show proofId) prop script) subproofs ++
                                 proofScript
                  | otherwise = []
        where (proofScript, st) = runState (proofs decls fts) (typingSubproofsInit mod ta)
              subproofs = sortOn ((\(proofId, _, _) -> proofId)) $
                            M.elems (st ^. subproofKinding) ++                            
                            M.elems (st ^. subproofWfSubstitutions) ++
                            M.elems (st ^. subproofSplits) ++
                            M.elems (st ^. subproofWeakens) ++
                            M.elems (st ^. subproofWellformed)
  in header . pretty $ Theory thy (TheoryImports imports) $ proofDecls ++ proofBodies

splitEvery :: Int -> [a] -> [[a]]
splitEvery = splitEveryW (const 1)

splitEveryW :: (a -> Int) -> Int -> [a] -> [[a]]
splitEveryW _ n [] = []
splitEveryW w n xs = let (as, bs) = span ((<= n) . snd) .
                                    snd . mapAccumL (\s (x, w) -> (s+w, (x, s+w))) 0 $
                                    map (ap (,) w) xs
                     in map fst as : splitEveryW w n (map fst bs)

formatMLProof :: String -> String -> [String] -> [TheoryDecl I.Type I.Term]
formatMLProof name typ lines =
  -- Isabelle has trouble with large numbers of @{thm} antiquotations; split into small blocks
  [ TheoryString $ stepsML $ splitEveryW (length . filter (=='@')) 300 lines ]
  where stepsML (steps:stepss) =
          (if null stepss then "" else stepsML stepss) ++
          "ML_quiet \\<open>\nval " ++ name ++ " : " ++ typ ++ " list = [\n" ++
          intercalate ",\n" steps ++ "\n]" ++
          (if null stepss then "" else " @ " ++ name) ++ " \\<close>\n"
        stepsML [] = "ML_quiet \\<open> val " ++ name ++ " : " ++ typ ++ " list = [] \\<close>\n"

formatSubproof :: TypeAbbrevs -> String -> (Bool, I.Term) -> [Tactic] -> [TheoryDecl I.Type I.Term]
formatSubproof ta name (schematic, prop) steps =
  formatMLProof (name ++ "_script") "tac" (map show steps) ++
  [ LemmaDecl (Lemma schematic (Just $ TheoremDecl (Just name)
                                         [                                          
                                           Attribute "unfolded" ["abbreviated_type_defs"]]) [prop]
               (Proof ([MethodModified (Method "unfold" ["abbreviated_type_defs"]) MMOptional] ++
                       [ Method "tactic" ["\\<open> map (fn t => DETERM (interpret_tac t @{context} 1)) " ++
                                          name ++ "_script |> EVERY \\<close>"]                         
                         ])

                ProofDone)) ]

formatMLTreeGen :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeGen name =
  let safeName = unIsabelleName $ mkIsabelleName name
  in [ TheoryString ( "ML_quiet \\<open>\nval " ++ safeName ++ "_ttyping_details_future"
    ++ " = get_all_typing_details_future" ++ (if __cogent_proof_timing then " true " else " false ")
    ++ "@{context} \"" ++ safeName ++ "\"\n"
    ++ "   " ++ safeName ++ "_typecorrect_script"
    ++ "\n\\<close>\n"
  ) ]

formatMLTreeFinalise :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeFinalise name =
  let safeName = unIsabelleName $ mkIsabelleName name
  in [ TheoryString ("ML_quiet \\<open>\nval (_, "
    ++ safeName ++ "_typing_tree, " ++ safeName ++ "_typing_bucket)\n"
    ++ "= Future.join " ++ safeName ++ "_ttyping_details_future\n\\<close>\n"
  )]

formatTypecorrectProof :: String -> [TheoryDecl I.Type I.Term]
formatTypecorrectProof fn =
  let safeFn = unIsabelleName $ mkIsabelleName fn in
  let fnType = safeFn ++ "_type"
  in [ LemmaDecl (Lemma False (Just $ TheoremDecl (Just (safeFn ++ "_typecorrect")) [])
          [mkId $ "\\<Xi>, prod.fst " ++ fnType ++ 
                    ", prod.fst (prod.snd " ++ fnType ++
                    "), prod.fst (prod.snd (prod.snd " ++ fnType ++ ")), (" ++ safeFn ++ 
                    "_typetree, [Some (prod.fst (prod.snd (prod.snd (prod.snd " ++ fnType ++ "))))]) T\\<turnstile> " ++
                  safeFn ++ " : prod.snd (prod.snd (prod.snd (prod.snd " ++ fnType ++ ")))"]
    (Proof (if __cogent_fml_typing_tree then [Method "tactic" ["\\<open> resolve_future_typecorrect @{context} " ++ safeFn ++ "_ttyping_details_future \\<close>"]]
      else [Method "simp" ["add: " ++ safeFn ++ "_type_def " ++ safeFn ++ "_def " ++
                           safeFn ++ "_typetree_def replicate_unfold"
                           ++ " abbreviated_type_defs"],
            Method "tactic" ["\\<open> apply_ttsplit_tacs_simple \"" ++ safeFn ++ "\"\n"
                    ++ "    @{context} " ++ safeFn ++ "_typecorrect_script \\<close>"]])
     ProofDone)) ]

data TreeSteps a = StepDown | StepUp | Val a
    deriving (Eq, Read, Show)

flattenHintTree :: LeafTree Hints -> [TreeSteps Hints]
flattenHintTree (Branch ths) = StepDown : concatMap flattenHintTree ths ++ [StepUp]
flattenHintTree (Leaf h) = [Val h]

proveSorry :: (Pretty a) => Definition TypedExpr a VarName -> State TypingSubproofs [TheoryDecl I.Type I.Term]
proveSorry (FunDef _ fn k _ ti to e) = do
  mod <- use nameMod
  let safeFn = unIsabelleName $ mkIsabelleName fn
  let fnType = safeFn ++ "_type"
  let prf = [ LemmaDecl (Lemma False (Just $ TheoremDecl (Just (mod safeFn ++ "_typecorrect")) [])
          [mkId $ "\\<Xi>, prod.fst " ++ fnType ++ ", prod.fst (prod.snd " ++ fnType ++ 
             "), prod.fst (prod.snd (prod.snd " ++ fnType ++ ")), (" ++ safeFn ++ 
             "_typetree, [Some (prod.fst (prod.snd (prod.snd (prod.snd " ++ fnType ++ "))))]) T\\<turnstile> " ++
                  safeFn ++ " : prod.snd (prod.snd (prod.snd (prod.snd" ++ fnType ++ ")))"]
              (Proof [] ProofSorry)) ]
  return prf
proveSorry _ = return []

prove :: (Pretty a) => [Definition TypedExpr a VarName] 
      -> Map FunName (FunctionType VarName) -> Definition TypedExpr a VarName
      -> State TypingSubproofs ([TheoryDecl I.Type I.Term], [TheoryDecl I.Type I.Term])
prove decls fts (FunDef _ fn k l ti to e) = 
  let (nl, cs) = 
           -- is it a (possibly generated) monomorphised function?
           case (k, l) of
             (V.Nil, V.Nil) -> (0, [])
             _ -> case M.lookup fn fts of
                    Nothing -> error("Error - unable to retrieve the inferred constraints for isabelle function '" ++ fn ++ "'" )                     
                    Just (FT ks nl cs _ _) ->
                    -- this case is to match the type variable of e with the one of ks
                      case V.length ks =? V.length k of
                         Nothing -> __impossible "lengths don't match"
                         Just Refl -> (toInteger $ Nat.toInt nl, cs)
  in
  let ks = fmap snd k in
  do
  mod <- use nameMod
  let eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
      xi = (makeXi fts decls)            
  proofSteps' <- proofSteps xi nl ks cs ti eexpr
  ta <- use tsTypeAbbrevs
  let typecorrect_script = formatMLProof (mod (unIsabelleName $ mkIsabelleName fn) ++ "_typecorrect_script") "hints treestep" (map show $ flattenHintTree proofSteps')
  let fn_typecorrect_proof = typecorrect_script ++ (if __cogent_fml_typing_tree then formatMLTreeGen (mod fn) else []) ++ formatTypecorrectProof (mod fn)
  return (fn_typecorrect_proof, if __cogent_fml_typing_tree then formatMLTreeFinalise (mod fn) else [])
prove _ _ _ = return ([], [])

proofs :: (Pretty a) => [Definition TypedExpr a VarName]
       -> Map FunName (FunctionType VarName) 
       -> State TypingSubproofs [TheoryDecl I.Type I.Term]
proofs decls fts = do
    let (predecls,postdecls) = badHackSplitOnSorryBefore decls
    bsorry <- mapM proveSorry predecls
    bodies <- mapM (prove decls fts) postdecls
    return $ concat $ bsorry ++ map fst bodies ++ map snd bodies

funTypeTree :: (Pretty a) => NameMod -> TypeAbbrevs -> Definition TypedExpr a VarName -> [TheoryDecl I.Type I.Term]
funTypeTree mod ta (FunDef _ fn _ _ ti _ e) = [deepTyTreeDef mod ta fn (typeTree eexpr)]
  where eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
funTypeTree _ _ _ = []

funTypeTrees :: (Pretty a) => NameMod -> TypeAbbrevs -> [Definition TypedExpr a VarName] -> [TheoryDecl I.Type I.Term]
funTypeTrees mod ta decls =
  let (_, decls') = badHackSplitOnSorryBefore decls
  in concatMap (funTypeTree mod ta) decls

badHackSplitOnSorryBefore :: [Definition TypedExpr a VarName] -> ([Definition TypedExpr a VarName], [Definition TypedExpr a VarName])
badHackSplitOnSorryBefore decls =
  if __cogent_type_proof_sorry_before == Nothing
  then ([], decls)
  else break should_sorry decls
 where
  should_sorry (FunDef _ fn _ _ ti _ e) = Just fn == __cogent_type_proof_sorry_before
  should_sorry _ = False

deepTyTreeDef :: NameMod -> TypeAbbrevs -> FunName -> TypingTree t -> TheoryDecl I.Type I.Term
deepTyTreeDef mod ta fn e = let ttfn = mkId $ mod (unIsabelleName $ mkIsabelleName fn) ++ "_typetree"
                                tt = deepCtxTree mod ta e
                             in [isaDecl| definition "$ttfn \<equiv> $tt" |]

deepTypeSplitKind :: TypeSplitKind -> Term
deepTypeSplitKind TSK_R  = mkId "TSK_R"
deepTypeSplitKind TSK_L  = mkId "TSK_L"
deepTypeSplitKind TSK_S  = mkId "TSK_S"
deepTypeSplitKind TSK_NS = mkId "TSK_NS"

deepTreeSplits :: [Maybe TypeSplitKind] -> Term
deepTreeSplits (Nothing : Nothing : tsks) = mkApp (mkId "append") [repl, rest]
  where
    n = length (takeWhile (== Nothing) tsks)
    rest = deepTreeSplits (drop n tsks)
    repl = mkApp (mkId "replicate") [mkInt (toInteger n + 2), deepMaybe Nothing]
deepTreeSplits (tsk : tsks) = mkApp (mkId "Cons")
    [deepMaybe (fmap deepTypeSplitKind tsk), deepTreeSplits tsks]
deepTreeSplits [] = mkList []

deepCtx :: NameMod -> TypeAbbrevs -> [Maybe (Type t VarName)] -> Term
deepCtx mod ta = mkList . map (deepMaybeTy mod ta)

deepCtxTree :: NameMod -> TypeAbbrevs -> TypingTree t -> Term
deepCtxTree mod ta TyTrLeaf = mkId "TyTrLeaf"
deepCtxTree mod ta (TyTrSplit f (lctx, l) (rctx, r)) =
  mkApp (mkId "TyTrSplit") [deepTreeSplits f, deepCtx mod ta lctx, deepCtxTree mod ta l, deepCtx mod ta rctx, deepCtxTree mod ta r]

-- dodgy fix
escapedFunName :: FunName -> String
escapedFunName fn | '\'' `elem` fn = "[" ++ intercalate "," (repr fn) ++ "]"
                  | otherwise = "''" ++ fn ++ "''"
                  where
                    repr :: String -> [String]
                    repr x = if all isAscii x
                                    then map (printf "CHR %#02x" . ord) x
                                    else error "Function name contained a non-ascii char! Isabelle doesn't support this."

  
isaTypeName n = 
  unIsabelleName $ 
    case editIsabelleName (mkIsabelleName n) (++ "_type") of
      Just n' -> n'
      Nothing -> error ("Error generating isabelle name for " ++ n)

isaName = unIsabelleName . mkIsabelleName

funTypeCase :: NameMod -> Definition TypedExpr a VarName -> Maybe Term
funTypeCase mod (FunDef  _ fn _ _ _ _ _) =
  Just $ mkPair (mkId (escapedFunName (isaName fn))) (mkId (mod (isaTypeName fn)))
funTypeCase mod (AbsDecl _ fn _ _ _ _  ) =
  Just $ mkPair (mkId (escapedFunName (isaName fn))) (mkId (mod (isaTypeName fn)))
funTypeCase _ _ = Nothing

funTypeEnv :: NameMod -> [Definition TypedExpr a VarName] -> [TheoryDecl I.Type I.Term]
funTypeEnv mod fs = funTypeEnv' $ mkList $ mapMaybe (funTypeCase mod) fs

funTypeEnv' upds = let unit = mkId "(0, [], {}, TUnit, TUnit)"
                       -- NOTE: as the isa-parser's antiQ doesn't handle terms well and it doesn't
                       -- keep parens, we have to fall back on strings / zilinc
                       tysig = [isaType| string \<Rightarrow> poly_type|]                       
                    in [[isaDecl| definition \<Xi> :: "$tysig"
                                  where "\<Xi> \<equiv> assoc_lookup $upds $unit" |]]

funDefCase :: Definition TypedExpr a VarName -> Maybe Term
funDefCase (AbsDecl _ fn _ _ _ _  ) =
    Just $ mkPair (mkId $ escapedFunName fn) (mkId "(\\<lambda>_ _. False)")
funDefCase _ = Nothing

funDefEnv :: [Definition TypedExpr a VarName] -> [TheoryDecl I.Type I.Term]
funDefEnv fs = funDefEnv' $ mkList $ mapMaybe funDefCase fs

funDefEnv' upds = let unit = mkId "(\\<lambda>_ _. False)"
                   in [[isaDecl| definition "\<xi> \<equiv> assoc_lookup $upds" $unit |]]

(<\>) :: Vec v (Maybe t) -> Vec v (Maybe t) -> Vec v (Maybe t)
(<\>) (Cons x xs) (Cons Nothing ys)  = Cons x       $ xs <\> ys
(<\>) (Cons _ xs) (Cons (Just _) ys) = Cons Nothing $ xs <\> ys
(<\>) Nil Nil = Nil
#if __GLASGOW_HASKELL__ < 711
(<\>) _ _ = error "TypeProofs: unreachable case in <\\>: vectors have mismatching lengths"
#endif

setAt :: [a] -> Int -> a -> [a]
setAt (x:xs) 0 v = v:xs
setAt (x:xs) n v = x:setAt xs (n-1) v
setAt [] _ _ = []

recTaken = snd . snd
recType = fst . snd

bangEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName))
bangEnv ((t, _):is) env = bangEnv is $ update env t $ fmap bang $ env `at` t
bangEnv [] env = env

unbangEnv :: Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName))
unbangEnv Nil Nil = Nil
unbangEnv (Cons (Just _) bs) (Cons e es) = Cons e (unbangEnv bs es)
unbangEnv (Cons Nothing bs)  (Cons _ es) = Cons Nothing (unbangEnv bs es)

selectEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName))
selectEnv [] env = cleared env
selectEnv ((v,_):vs) env = update (selectEnv vs env) v (env `at` v)

-- Annotates a typed expression with the environment required to successfully execute it
splitEnv :: (Pretty a) => Vec v (Maybe (Type t VarName)) -> TypedExpr t v a VarName -> EnvExpr t v a VarName
splitEnv env (TE t Unit)             = EE t Unit          $ cleared env
splitEnv env (TE t (ILit i t'))      = EE t (ILit i t')   $ cleared env
splitEnv env (TE t (SLit s))         = EE t (SLit s)      $ cleared env
splitEnv env (TE t (Fun f ts ls nt)) = EE t (Fun f ts ls nt) $ cleared env  -- FIXME
splitEnv env (TE t (Variable v))     = EE t (Variable v)  $ singleton (fst v) env

splitEnv env (TE t (Esac e))
    = let e' = splitEnv env e
       in EE t (Esac e') $ envOf e'

splitEnv env (TE t (Promote ty e))
    = let e' = splitEnv env e
       in EE t (Promote ty e') $ envOf e'

splitEnv env (TE t (Cast ty e))
    = let e' = splitEnv env e
       in EE t (Cast ty e') $ envOf e'

splitEnv env (TE t (Member e f))
    = let e' = splitEnv env e
       in EE t (Member e' f) $ envOf e'

splitEnv env (TE t (Struct fs))
    = let fs' = map (splitEnv env . snd) fs
       in EE t (Struct (zip (map fst fs) fs')) $ foldl (<|>) (cleared env) (map envOf fs')

splitEnv env (TE t (Op o es))
    = let vs = map (splitEnv env) es
       in EE t (Op o vs) $ foldl (<|>) (cleared env) (map envOf vs)

splitEnv env (TE t (App e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (App e1' e2')   $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Tuple e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (Tuple e1' e2') $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Put e1 f e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv env e2
       in EE t (Put e1' f e2') $ envOf e1' <|> envOf e2'

splitEnv env (TE t (Split a e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv (Cons (Just t1) $ Cons (Just t1') env) e2
          TProduct t1 t1' = typeOf e1'
       in EE t (Split a e1' e2') $ envOf e1' <|> peel2 (envOf e2')

splitEnv env (TE t (Let a e1 e2))
    = let e1' = splitEnv env e1
          e2' = splitEnv (Cons (Just $ typeOf e1') env) e2
       in EE t (Let a e1' e2') $ envOf e1' <|> peel (envOf e2')

splitEnv env (TE t (LetBang vs a e1 e2))
    = let env' = bangEnv vs env
          e1' = splitEnv env' e1
          -- type system requires pushing down vs, even if unused in e1
          e1'' = pushDown (selectEnv vs env' <\> envOf e1') e1'
          e2' = splitEnv (Cons (Just $ typeOf e1'') env) e2
       in EE t (LetBang vs a e1'' e2') $ unbangEnv (envOf e1'') env' <|> peel (envOf e2')

splitEnv env (TE t (Con tag e tau)) =
    let e' = splitEnv env e
     in EE t (Con tag e' tau) $ envOf e'

splitEnv env (TE t (If ec et ee))
    = let ec' = splitEnv env ec
          et' = splitEnv env et
          ee' = splitEnv env ee
       in EE t (If ec' et' ee') $ envOf ec' <|> envOf et' <|> envOf ee'

splitEnv env (TE t (Case e tag (lt,at,et) (le,ae,ee)))
    = let et' = splitEnv (Cons (fmap fst $ lookup tag ts) env) et
          restt = TSum $ adjust tag (second $ const True) ts
          ee' = splitEnv (Cons (Just restt) env) ee
          e'  = splitEnv env e
          TSum ts = typeOf e'
       in EE t (Case e' tag (lt,at,et') (le,ae,ee')) $ envOf e' <|> peel (envOf ee') <|> peel (envOf et')

splitEnv env (TE t (Take a e f e2)) =
    let e' = splitEnv env e
        TRecord rp ts s = typeOf e'
        e2' = splitEnv (Cons (Just $ recType (ts!!f)) (Cons (Just $ TRecord rp (setAt ts f (fst (ts!!f), (recType (ts!!f), True))) s) env)) e2
     in EE t (Take a e' f e2') $ envOf e' <|> peel2 (envOf e2')


-- Ensures that the environment of an expression is equal to the sum of the
-- environments of the subexpressions.
pushDown :: (Pretty a) => Vec v (Maybe (Type t VarName)) -> EnvExpr t v a VarName -> EnvExpr t v a VarName
pushDown unused (EE ty e@Unit      _) = EE ty e unused
pushDown unused (EE ty e@(ILit {}) _) = EE ty e unused
pushDown unused (EE ty e@(SLit {}) _) = EE ty e unused
pushDown unused (EE ty e@(Fun  {}) _) = EE ty e unused
pushDown unused (EE ty e@(Variable _) env) = EE ty e $ unused <|> env

-- This case may be impossible to prove if unused is non-empty (!!)
pushDown unused (EE ty (Op o []) env) = error "TypeProofs: empty Op" -- EE ty (Op o []) $ unused <|> env

pushDown unused (EE ty (Op o (t:ts)) env)
    = let es = pushDown (unused <\> env) t:map (pushDown (cleared env)) ts
       in EE ty (Op o es) $ unused <|> env

pushDown unused (EE ty (Struct fs) env)
    = let fs' = case map snd fs of
                  (t:ts) -> pushDown (unused <\> env) t:map (pushDown (cleared env)) ts
                  []     -> error "TypeProofs: empty Struct" -- [] -- This case may be impossible to prove if unused is non-empty (!!)
       in EE ty (Struct $ zip (map fst fs) fs') $ unused <|> env

pushDown unused (EE ty (App e1 e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env)    e2
       in EE ty (App e1' e2') $ unused <|> env

pushDown unused (EE ty (Let a e1 e2) env)
    = let e1'@(EE t _ _) = pushDown (unused <\> env) e1
          e2' = pushDown (Cons (Just t) (cleared env)) e2
       in EE ty (Let a e1' e2') $ unused <|> env

pushDown unused (EE ty (LetBang vs a e1 e2) env)
    = let -- e1 already pushed down in splitEnv
          e2vs = selectEnv vs env <\> peel (envOf e2)
          e2' = pushDown (Cons (Just (eexprType e1)) (e2vs <|> ((unused <\> env) <\> envOf e1))) e2
       in EE ty (LetBang vs a e1 e2') $ unused <|> env

pushDown unused (EE ty (Tuple e1 e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env) e2
       in EE ty (Tuple e1' e2') $ unused <|> env

pushDown unused (EE ty (Con tag e t) env)
    = let e' = pushDown unused e
       in EE ty (Con tag e' t) $ unused <|> env

pushDown unused (EE ty (If ec et ee) env)
    = let ec' = pushDown (unused <\> env) ec
          et' = pushDown (envOf ee <\> envOf et) et
          ee' = pushDown (envOf et <\> envOf ee) ee
       in EE ty (If ec' et' ee') $ unused <|> env

pushDown unused (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env)
    = let e'@(EE (TSum ts) _ _) = pushDown (unused <\> env) e
          et' = pushDown (Cons (fmap fst $ lookup tag ts) (peel (envOf ee) <\> peel (envOf et))) et
          restt = TSum $ adjust tag (second $ const True) ts
          ee' = pushDown (Cons (Just restt) (peel (envOf et) <\> peel (envOf ee))) ee
      in (EE ty (Case e' tag (lt,at,et') (le,ae,ee')) $ unused <|> env)

pushDown unused (EE ty (Esac e) env)
    = let e' = pushDown unused e
       in EE ty (Esac e') $ unused <|> env

pushDown unused (EE ty (Split a e1 e2) env)
    = let e1'@(EE (TProduct x y) _ _) = pushDown (unused <\> env) e1
          e2' = pushDown (Cons (Just x) (Cons (Just y) (cleared env))) e2
       in EE ty (Split a e1' e2') $ unused <|> env

pushDown unused (EE ty (Member e f) env)
    = let e' = pushDown unused e
       in EE ty (Member e' f) $ unused <|> env

pushDown unused (EE ty (Take a e f e2) env)
    = let e'@(EE rt _ _) = pushDown (unused <\> env) e
          TRecord rp ts s = rt
          e2' = pushDown (Cons (Just $ recType $ ts!!f) (Cons (Just $ TRecord rp (setAt ts f (fst (ts!!f), (recType $ ts!!f, True))) s) (cleared env))) e2
       in EE ty (Take a e' f e2') $ unused <|> env

pushDown unused (EE ty (Put e1 f e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env) e2
       in EE ty (Put e1' f e2') $ unused <|> env

pushDown unused (EE ty (Promote ty' e) env)
    = let e' = pushDown unused e
       in EE ty (Promote ty' e') $ unused <|> env

pushDown unused (EE ty (Cast ty' e) env)
    = let e' = pushDown unused e
       in EE ty (Cast ty' e') $ unused <|> env

pushDown _ e = __impossible $ "pushDown:" ++ show (pretty e) ++ " is not yet implemented"

treeSplit :: Maybe (Type t VarName) -> Maybe (Type t VarName) -> Maybe (Type t VarName) -> Maybe TypeSplitKind
treeSplit Nothing  Nothing  Nothing  = Nothing
treeSplit (Just t) (Just _) Nothing  = Just TSK_L
treeSplit (Just t) Nothing  (Just _) = Just TSK_R
treeSplit (Just t) (Just _) (Just _) = Just TSK_S
treeSplit g x y = error $ "bad split: " ++ show (g, x, y)

treeSplits :: Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName)) -> Vec v (Maybe (Type t VarName)) -> [Maybe TypeSplitKind]
treeSplits (Cons g gs) (Cons x xs) (Cons y ys) = treeSplit g x y:treeSplits gs xs ys
treeSplits Nil         Nil         Nil         = []
#if __GLASGOW_HASKELL__ < 711
treeSplits _ _ _ = __ghc_t4139 "TypeProofs.treeSplits"
#endif

treeBang :: Int -> [Int] -> [Maybe TypeSplitKind] -> [Maybe TypeSplitKind]
treeBang i is (x:xs) | i `elem` is = Just TSK_NS:treeBang (i+1) is xs
                     | otherwise   = x:treeBang (i+1) is xs
treeBang i is [] = []

typeTree :: EnvExpr t v a VarName -> TypingTree t
typeTree (EE ty (Split a e1 e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel2 $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)
typeTree (EE ty (Let a e1 e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero], typeTree e2)

typeTree (EE ty (LetBang vs a e1 e2) env) = TyTrSplit (treeBang 0 (map (finInt . fst) vs) $ treeSplits env (envOf e1) (peel $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero], typeTree e2)
typeTree (EE ty (Take a e1 f e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel2 $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)

typeTree (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env) = TyTrSplit (treeSplits env (envOf e) (peel $ envOf et <|> envOf ee)) ([], typeTree e) ([],
                                                                    TyTrSplit (treeSplits (peel $ envOf ee <|> envOf et) (peel $ envOf et) (peel $ envOf ee)) ([V.head $ envOf et], typeTree et) ([V.head $ envOf ee], typeTree ee))
typeTree (EE ty (If ec et ee) env) = TyTrSplit (treeSplits env (envOf ec) (envOf et <|> envOf ee)) ([], typeTree ec) ([],
                                                                    TyTrSplit (treeSplits (envOf ee <|> envOf et) (envOf et) (envOf ee)) ([], typeTree et) ([], typeTree ee))
typeTree (EE _ (Promote _ e) _) = typeTree e
typeTree _ = TyTrLeaf

