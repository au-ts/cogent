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

module Cogent.TypeProofs where

import Cogent.Common.Syntax
import Cogent.Compiler
import Cogent.Deep (deepDefinitions, deepTypeAbbrevs, getTypeAbbrevs, TypeAbbrevs)
import Cogent.ProofGen
import Cogent.Core
import Cogent.Inference
import Cogent.Util (NameMod)
import Cogent.Vec hiding (splitAt, length, zipWith, zip, unzip, head)
import qualified Cogent.Vec as V

import Control.Arrow (second)
import Control.Lens ((^.), use)
import Control.Monad.State.Strict
import Data.Char
import Data.List
import qualified Data.Map as M
import Data.Ord (comparing)
import Isabelle.ExprTH
import qualified Isabelle.InnerAST as I
import Isabelle.InnerAST hiding (Type)
import Isabelle.OuterAST as O
import Numeric
#if __GLASGOW_HASKELL__ >= 709
import Prelude hiding ((<$>))
#endif
import System.FilePath ((</>))
import Text.PrettyPrint.ANSI.Leijen hiding ((</>))
import Text.Printf

data TypeSplitKind = TSK_L | TSK_S | TSK_NS
  deriving Eq
data TypingTree t = TyTrLeaf
                  | TyTrSplit [Maybe TypeSplitKind] (TreeCtx t) (TreeCtx t)
type TreeCtx t = ([Maybe (Type t)], TypingTree t)

deepTypeProof :: Show a => NameMod -> Bool -> Bool -> String -> [Definition TypedExpr a] -> String -> Doc
deepTypeProof mod withDecls withBodies thy decls log =
  let header = (string ("(*\n" ++ log ++ "\n*)\n") <$>)
      ta = getTypeAbbrevs mod decls
      imports = if __cogent_fml_typing_tree then [__cogent_root_dir </> "c-refinement/TypeProofGen"]
                                          else [__cogent_root_dir </> "cogent/isa/CogentHelper"]
      proofDecls | withDecls  = deepTypeAbbrevs mod ta ++ deepDefinitions mod ta decls
                                ++ funTypeEnv mod decls ++ funDefEnv decls
                                ++ concatMap (funTypeTree mod ta) decls
                 | otherwise = []
      proofBodies | withBodies = [TheoryString "ML {* open TTyping_Tactics *}"] ++
                                 concatMap (\(proofId, prop, script) ->
                                              formatSubproof ta (typingSubproofPrefix ++ show proofId) prop script) subproofs ++
                                 proofScript
                  | otherwise = []
        where (proofScript, st) = runState (proofs decls) (typingSubproofsInit mod ta)
              subproofs = sortBy (comparing (\(proofId, _, _) -> proofId)) $
                            M.elems (st ^. subproofKinding) ++
                            M.elems (st ^. subproofAllKindCorrect) ++
                            M.elems (st ^. subproofSplits) ++
                            M.elems (st ^. subproofWeakens)
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
  [ TheoryString $ stepsML $ splitEveryW (length . filter (=='@')) 500 lines ]
  where stepsML (steps:stepss) =
          (if null stepss then "" else stepsML stepss) ++
          "ML_quiet {*\nval " ++ name ++ " : " ++ typ ++ " list = [\n" ++
          intercalate ",\n" steps ++ "\n]" ++
          (if null stepss then "" else " @ " ++ name) ++ " *}\n"
        stepsML [] = "ML_quiet {* val " ++ name ++ " : " ++ typ ++ " list = [] *}\n"

formatSubproof :: TypeAbbrevs -> String -> (Bool, I.Term) -> [Tactic] -> [TheoryDecl I.Type I.Term]
formatSubproof ta name (schematic, prop) steps =
  formatMLProof (name ++ "_script") "tac" (map show steps) ++
  [ LemmaDecl (Lemma schematic (Just $ TheoremDecl (Just name)
                                         [Attribute "unfolded" ["abbreviated_type_defs"]]) [prop]
               (Proof ([MethodModified (Method "unfold" ["abbreviated_type_defs"]) MMOptional] ++
                       [ Method "tactic" ["{* map (fn t => DETERM (interpret_tac t @{context} 1)) " ++
                                          name ++ "_script |> EVERY *}"]])
                ProofDone)) ]

formatMLTreeGen :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeGen name =
  [ TheoryString ( "ML_quiet {*\nval " ++ name ++ "_ttyping_details_future"
    ++ " = get_all_typing_details_future @{context} \"" ++ name ++ "\"\n"
    ++ "   " ++ name ++ "_typecorrect_script"
    ++ "*}\n"
  ) ]

formatMLTreeFinalise :: String -> [TheoryDecl I.Type I.Term]
formatMLTreeFinalise name =
  [ TheoryString ( "ML_quiet {*\nval (_, "
    ++ name ++ "_typing_tree, " ++ name ++ "_typing_bucket)\n"
    ++ "= Future.join " ++ name ++ "_ttyping_details_future\n*}\n"
  ) ]

formatTypecorrectProof :: String -> [TheoryDecl I.Type I.Term]
formatTypecorrectProof fn =
  [ LemmaDecl (Lemma False (Just $ TheoremDecl (Just (fn ++ "_typecorrect")) [])
          [mkId $ "\\<Xi>, fst " ++ fn ++ "_type, (" ++ fn ++ "_typetree, [Some (fst (snd " ++ fn ++ "_type))]) T\\<turnstile> " ++
                  fn ++ " : snd (snd " ++ fn ++ "_type)"]
    (Proof (if __cogent_fml_typing_tree then [Method "tactic" ["{* resolve_future_typecorrect @{context} " ++ fn ++ "_ttyping_details_future *}"]]
      else [Method "simp" ["add: " ++ fn ++ "_type_def " ++ fn ++ "_def " ++
                           fn ++ "_typetree_def replicate_unfold"
                           ++ " abbreviated_type_defs"],
            Method "tactic" ["{* apply_ttsplit_tacs_simple \"" ++ fn ++ "\"\n"
                    ++ "    @{context} " ++ fn ++ "_typecorrect_script *}"]])
     ProofDone)) ]


prove :: [Definition TypedExpr a] -> Definition TypedExpr a
      -> State TypingSubproofs ([TheoryDecl I.Type I.Term], [TheoryDecl I.Type I.Term])
prove decls (FunDef _ fn k ti to e) = do
  mod <- use nameMod
  proofSteps' <- proofSteps decls (fmap snd k) ti eexpr
  ta <- use tsTypeAbbrevs
  return $ (formatMLProof (mod fn ++ "_typecorrect_script") "hints" (map show proofSteps')
           ++ (if __cogent_fml_typing_tree then formatMLTreeGen (mod fn) else [])
           ++ formatTypecorrectProof (mod fn),
           (if __cogent_fml_typing_tree then formatMLTreeFinalise (mod fn) else []))
  where eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
prove _ _ = return ([], [])

proofs :: [Definition TypedExpr a]
       -> State TypingSubproofs [TheoryDecl I.Type I.Term]
proofs decls = do
    bodies <- mapM (prove decls) decls
    return $ concat $ map fst bodies ++ map snd bodies

funTypeTree :: NameMod -> TypeAbbrevs -> Definition TypedExpr a -> [TheoryDecl I.Type I.Term]
funTypeTree mod ta (FunDef _ fn _ ti _ e) = [deepTyTreeDef mod ta fn (typeTree eexpr)]
  where eexpr = pushDown (Cons (Just ti) Nil) (splitEnv (Cons (Just ti) Nil) e)
funTypeTree _ _ _ = []

deepTyTreeDef :: NameMod -> TypeAbbrevs -> FunName -> TypingTree t -> TheoryDecl I.Type I.Term
deepTyTreeDef mod ta fn e = let ttfn = mkId $ mod fn ++ "_typetree"
                                tt = deepCtxTree mod ta e
                             in [isaDecl| definition "$ttfn \<equiv> $tt" |]

deepTypeSplitKind :: TypeSplitKind -> Term
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

deepCtx :: NameMod -> TypeAbbrevs -> [Maybe (Type t)] -> Term
deepCtx mod ta = mkList . map (deepMaybeTy mod ta)

deepCtxTree :: NameMod -> TypeAbbrevs -> TypingTree t -> Term
deepCtxTree mod ta TyTrLeaf = mkId "TyTrLeaf"
deepCtxTree mod ta (TyTrSplit f (lctx, l) (rctx, r)) =
  mkApp (mkId "TyTrSplit") [deepTreeSplits f, deepCtx mod ta lctx, deepCtxTree mod ta l, deepCtx mod ta rctx, deepCtxTree mod ta r]

-- dodgy fix
escapedFunName :: FunName -> String
escapedFunName fn | '\'' `elem` fn = "[" ++ intercalate "," (map repr fn) ++ "]"
                  | otherwise = "''" ++ fn ++ "''"
                  where binstr = printf "%08s" . flip (showIntAtBase 2 intToDigit . ord) []
                        strint x = fst $ head $ readInt 2 (`elem` "10") digitToInt x
                        repr x = printf "Char Nibble%X Nibble%X" (strint $ take 4 $ binstr x :: Int) (strint $ drop 4 $ binstr x :: Int)

funTypeCase :: NameMod -> Definition TypedExpr a -> [String] -> [String]
funTypeCase mod (FunDef  _ fn _ _ _ _) ds = (escapedFunName fn ++ " \\<Rightarrow> " ++ mod fn ++ "_type"):ds
funTypeCase mod (AbsDecl _ fn _ _ _  ) ds = (escapedFunName fn ++ " \\<Rightarrow> " ++ mod fn ++ "_type"):ds
funTypeCase _ _ ds = ds

funTypeEnv :: NameMod -> [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
funTypeEnv mod fs = funTypeEnv' $ foldr (funTypeCase mod) [] fs

funTypeEnv' fs = let binds = mkId $ intercalate " | " (fs ++ ["_ \\<Rightarrow> ([], TUnit, TUnit)"])
                     tysig = [isaType| string \<Rightarrow> Cogent.kind list \<times> Cogent.type \<times> Cogent.type |]
                  in [[isaDecl| definition \<Xi> :: "$tysig"
                                  where "\<Xi> func_name' \<equiv> case func_name' of $binds" |]]

funDefCase :: Definition TypedExpr a -> [String] -> [String]
funDefCase (AbsDecl _ fn _ _ _  ) ds = (escapedFunName fn ++ " \\<Rightarrow> (\\<lambda>_ _. False)"):ds
funDefCase _ ds = ds

funDefEnv :: [Definition TypedExpr a] -> [TheoryDecl I.Type I.Term]
funDefEnv fs = funDefEnv' $ foldr funDefCase [] fs

funDefEnv' fs = let binds = mkId $ intercalate " | " (fs ++ ["_ \\<Rightarrow> (\\<lambda>_ _. False)"])
             in [[isaDecl| definition "\<xi> func_name' \<equiv> case func_name' of $binds" |]]

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

bangEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
bangEnv ((t, _):is) env = bangEnv is $ update env t $ fmap bang $ env `at` t
bangEnv [] env = env

unbangEnv :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
unbangEnv Nil Nil = Nil
unbangEnv (Cons (Just _) bs) (Cons e es) = Cons e (unbangEnv bs es)
unbangEnv (Cons Nothing bs)  (Cons _ es) = Cons Nothing (unbangEnv bs es)
unbangEnv _ _ = undefined

selectEnv :: [(Fin v, a)] -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t))
selectEnv [] env = cleared env
selectEnv ((v,_):vs) env = update (selectEnv vs env) v (env `at` v)

-- Annotates a typed expression with the environment required to successfully execute it
splitEnv :: Vec v (Maybe (Type t)) -> TypedExpr t v a -> EnvExpr t v a
splitEnv env (TE t Unit)          = EE t Unit          $ cleared env
splitEnv env (TE t (ILit i t'))   = EE t (ILit i t')   $ cleared env
splitEnv env (TE t (SLit s))      = EE t (SLit s)      $ cleared env
splitEnv env (TE t (Fun f ts nt)) = EE t (Fun f ts nt) $ cleared env
splitEnv env (TE t (Variable v))  = EE t (Variable v)  $ singleton (fst v) env

splitEnv env (TE t (Esac e))
    = let e' = splitEnv env e
       in EE t (Esac e') $ envOf e'

splitEnv env (TE t (Promote ty e))
    = let e' = splitEnv env e
       in EE t (Promote ty e') $ envOf e'

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

splitEnv env (TE t (Con tag e)) =
    let e' = splitEnv env e
     in EE t (Con tag e') $ envOf e'

splitEnv env (TE t (If ec et ee))
    = let ec' = splitEnv env ec
          et' = splitEnv env et
          ee' = splitEnv env ee
       in EE t (If ec' et' ee') $ envOf ec' <|> envOf et' <|> envOf ee'

splitEnv env (TE t (Case e tag (lt,at,et) (le,ae,ee)))
    = let et' = splitEnv (Cons (fmap fst $ lookup tag ts) env) et
          restt = if __cogent_fnew_subtyping
                    then TSum $ adjust tag (second $ const True) ts
                    else TSum $ remove tag ts
          ee' = splitEnv (Cons (Just restt) env) ee
          e'  = splitEnv env e
          TSum ts = typeOf e'
       in EE t (Case e' tag (lt,at,et') (le,ae,ee')) $ envOf e' <|> peel (envOf ee') <|> peel (envOf et')

splitEnv env (TE t (Take a e f e2)) =
    let e' = splitEnv env e
        e2' = splitEnv (Cons (Just $ recType (ts!!f)) (Cons (Just $ TRecord (setAt ts f (fst (ts!!f), (recType (ts!!f), True))) sig) env)) e2 -- fix this
        TRecord ts sig = typeOf e'
     in EE t (Take a e' f e2') $ envOf e' <|> peel2 (envOf e2')


-- Ensures that the environment of an expression is equal to the sum of the
-- environments of the subexpressions.
pushDown :: Vec v (Maybe (Type t)) -> EnvExpr t v a -> EnvExpr t v a
pushDown unused (EE ty e@Unit       _) = EE ty e unused
pushDown unused (EE ty e@(ILit _ _) _) = EE ty e unused
pushDown unused (EE ty e@(SLit _)   _) = EE ty e unused
pushDown unused (EE ty e@(Fun _ _ _) _) = EE ty e unused
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

pushDown unused (EE ty (Con tag e) env)
    = let e' = pushDown unused e
       in EE ty (Con tag e') $ unused <|> env

pushDown unused (EE ty (If ec et ee) env)
    = let ec' = pushDown (unused <\> env) ec
          et' = pushDown (envOf ee <\> envOf et) et
          ee' = pushDown (envOf et <\> envOf ee) ee
       in EE ty (If ec' et' ee') $ unused <|> env

pushDown unused (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env)
    = let e'@(EE (TSum ts) _ _) = pushDown (unused <\> env) e
          et' = pushDown (Cons (fmap fst $ lookup tag ts) (peel (envOf ee) <\> peel (envOf et))) et
          restt = if __cogent_fnew_subtyping
                    then TSum $ adjust tag (second $ const True) ts
                    else TSum $ remove tag ts
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

pushDown unused (EE ty (Take a e@(EE (TRecord ts sig) _ _) f e2) env)
    = let e'@(EE (TRecord ts sig) _ _) = pushDown (unused <\> env) e
          e2' = pushDown (Cons (Just $ recType $ ts!!f) (Cons (Just $ TRecord (setAt ts f (fst (ts!!f), (recType $ ts!!f, True))) sig) (cleared env))) e2 -- fix this
       in EE ty (Take a e' f e2') $ unused <|> env

pushDown unused (EE ty (Put e1 f e2) env)
    = let e1' = pushDown (unused <\> env) e1
          e2' = pushDown (cleared env) e2
       in EE ty (Put e1' f e2') $ unused <|> env

pushDown unused (EE ty (Promote ty' e) env)
    = let e' = pushDown unused e
       in EE ty (Promote ty' e') $ unused <|> env

pushDown _ _ = error "TypeProofs: reached default case of pushDown"

treeSplit :: Maybe (Type t) -> Maybe (Type t) -> Maybe (Type t) -> Maybe TypeSplitKind
treeSplit Nothing  Nothing  Nothing  = Nothing
treeSplit (Just t) (Just _) Nothing  = Just TSK_L
treeSplit (Just t) Nothing  (Just _) = Nothing
treeSplit (Just t) (Just _) (Just _) = Just TSK_S
treeSplit g x y = error $ "bad split: " ++ show (g, x, y)

treeSplits :: Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> Vec v (Maybe (Type t)) -> [Maybe TypeSplitKind]
treeSplits (Cons g gs) (Cons x xs) (Cons y ys) = treeSplit g x y:treeSplits gs xs ys
treeSplits Nil         Nil         Nil         = []
#if __GLASGOW_HASKELL__ < 711
treeSplits _ _ _ = __ghc_t4139 "TypeProofs.treeSplits"
#endif

treeBang :: Int -> [Int] -> [Maybe TypeSplitKind] -> [Maybe TypeSplitKind]
treeBang i is (x:xs) | i `elem` is = Just TSK_NS:treeBang (i+1) is xs
                     | otherwise   = x:treeBang (i+1) is xs
treeBang i is [] = []

typeTree :: EnvExpr t v a -> TypingTree t
typeTree (EE ty (Split a e1 e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel2 $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)
typeTree (EE ty (Let a e1 e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero], typeTree e2)

typeTree (EE ty (LetBang vs a e1 e2) env) = TyTrSplit (treeBang 0 (map (finInt . fst) vs) $ treeSplits env (envOf e1) (peel $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero], typeTree e2)
typeTree (EE ty (Take a e1 f e2) env) = TyTrSplit (treeSplits env (envOf e1) (peel2 $ envOf e2)) ([], typeTree e1) ([envOf e2 `at` FZero, envOf e2 `at` FSuc FZero], typeTree e2)

typeTree (EE ty (Case e tag (lt,at,et) (le,ae,ee)) env) = TyTrSplit (treeSplits env (envOf e) (peel $ envOf et <|> envOf ee)) ([], typeTree e) ([],
                                                                    TyTrSplit (treeSplits (peel $ envOf ee <|> envOf et) (peel $ envOf et) (peel $ envOf ee)) ([V.head $ envOf et], typeTree et) ([V.head $ envOf ee], typeTree ee))
typeTree (EE ty (If ec et ee) env) = TyTrSplit (treeSplits env (envOf ec) (envOf et <|> envOf ee)) ([], typeTree ec) ([],
                                                                    TyTrSplit (treeSplits (envOf ee <|> envOf et) (envOf et) (envOf ee)) ([], typeTree et) ([], typeTree ee))
typeTree _ = TyTrLeaf

