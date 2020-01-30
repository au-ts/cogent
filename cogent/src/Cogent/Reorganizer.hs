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


{-# LANGUAGE LambdaCase, PatternGuards #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Reorganizer where

import qualified Cogent.Common.Syntax as Syn
import Cogent.Compiler (__impossible)
import Cogent.Surface
import Cogent.Util
import Cogent.Common.Types

import Control.Arrow
import Control.Monad (forM, forM_)
import Control.Monad.Trans.State
import Data.Char (isUpper)
-- import Data.Foldable hiding (notElem)
import Data.Functor.Compose
import qualified Data.Graph.Wrapper as G
import Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Maybe
import Text.Parsec.Pos

import Debug.Trace

data ReorganizeError = CyclicDependency
                     | DuplicateTypeDefinition
                     | DuplicateValueDefinition
                     | DuplicateRepDefinition
                     | NonStrictlyPositive
                     | RecParShadowsTyVar 

data SourceObject = TypeName  Syn.TypeName
                  | ValName   Syn.VarName
                  | RepName   Syn.RepName
                  | DocBlock' String
                  deriving (Eq, Ord)

instance Show SourceObject where
  show (TypeName  n) = n
  show (ValName   n) = n
  show (RepName   n) = n
  show (DocBlock' s) = s

dependencies :: TopLevel LocType LocPatn LocExpr -> [SourceObject]
dependencies (Include _) = __impossible "dependencies"
dependencies (IncludeStd _) = __impossible "dependencies"
dependencies (TypeDec _ _ t) = map TypeName (fcT (stripLocT t))
                            ++ map ValName  (fvT (stripLocT t))
dependencies (AbsTypeDec _ _ ts) = map TypeName (foldMap (fcT . stripLocT) ts)
                                ++ map ValName  (foldMap (fvT . stripLocT) ts)
dependencies (DocBlock _) = []
dependencies (RepDef (RepDecl _ _ e)) = map RepName (allRepRefs e) 
dependencies (AbsDec _ pt) = map TypeName (foldMap (fcT . stripLocT) pt)
                          ++ map ValName  (foldMap (fvT . stripLocT) pt)
dependencies (FunDef _ pt as) = map TypeName (foldMap (fcT . stripLocT) pt
                                           ++ foldMap (fcA . fmap stripLocE) as)
                             ++ map ValName  (foldMap (fvT . stripLocT) pt
                                           ++ foldMap (fvA . ffmap stripLocP . fmap stripLocE) as)
dependencies (ConstDef _ t e) = map TypeName (fcT (stripLocT t) ++ fcE (stripLocE e))
                             ++ map ValName  (fvT (stripLocT t) ++ fvE (stripLocE e))

classify :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
         -> [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
classify = map (\px -> (sourceObject (thd3 px), px))

sourceObject :: TopLevel LocType LocPatn LocExpr -> SourceObject 
sourceObject (Include _)        = __impossible "sourceObject (in classify)"
sourceObject (IncludeStd _)     = __impossible "sourceObject (in classify)"
sourceObject (DocBlock s)       = DocBlock' s
sourceObject (TypeDec n _ _)    = TypeName n
sourceObject (AbsTypeDec n _ _) = TypeName n
sourceObject (AbsDec n _)       = ValName n
sourceObject (FunDef v _ _)     = ValName v
sourceObject (ConstDef v _ _)   = ValName v
sourceObject (RepDef (RepDecl _ n _))    = RepName n

prune :: [SourceObject]  -- a list of entry-points
      -> [(SourceObject, v, [SourceObject])]
      -> [SourceObject]  -- a list of 'k's that will be included
prune es m = flip execState builtins $ forM_ es
                                     $ flip go
                                     $ map (\(k,_,ks) -> (k,ks)) m 
  where
    builtins = [ TypeName "U8"
               , TypeName "U16"
               , TypeName "U32"
               , TypeName "U64"
               , TypeName "Bool"
               , TypeName "String" 
               ]
    go :: SourceObject -> [(SourceObject, [SourceObject])] -> State [SourceObject] ()
    go k m = do s <- get
                case k `elem` s of
                  True  -> return ()  -- visited
                  False -> case L.lookup k m of
                    Nothing -> error $ show k ++ " is not defined"
                    Just ds -> do put $ k:s
                                  forM_ ds $ flip go m

graphOf :: Ord a => (b -> [a]) -> [(a, b)] -> G.Graph a b
graphOf f = G.fromListLenient . map (\(k,v) -> (k, v, f v))


dependencyGraph_ :: [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
                 -> G.Graph SourceObject (SourcePos, DocString, TopLevel LocType LocPatn LocExpr)
dependencyGraph_ = graphOf (dependencies . thd3)

-- With prune
dependencyGraph :: [SourceObject]
                -> [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
                -> G.Graph SourceObject (SourcePos, DocString, TopLevel LocType LocPatn LocExpr)
dependencyGraph es m =
  let edges = map (\(k,v) -> (k, v, dependencies $ thd3 v)) m
      included = prune es edges
      trimmed = filter (\(k,_,_) -> k `elem` included) edges
   in G.fromListLenient trimmed

checkNoNameClashes :: [(SourceObject, SourcePos)]
                   -> M.Map SourceObject SourcePos
                   -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
checkNoNameClashes [] bindings = return ()
checkNoNameClashes ((s,d):xs) bindings
  | Just x <- M.lookup s bindings = Left (msg, [(s, x), (s, d)])
  | otherwise = let bindings' = case s of DocBlock' _ -> bindings; _ -> M.insert s d bindings
                 in checkNoNameClashes xs bindings'
  where msg = case s of TypeName  _ -> DuplicateTypeDefinition
                        ValName   _ -> DuplicateValueDefinition
                        RepName   _ -> DuplicateRepDefinition
                        DocBlock' _ -> __impossible "checkNoNameClashes"

-- Maps recursive parameters parsed as type variables to actual recursive parameters in the AST
embedRecPars :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)] 
             -> [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
embedRecPars = map (\(s,d,t) -> (s,d,check t))
  where
    -- We need to check: Type definitions, function polytypes
    check :: TopLevel LocType LocPatn LocExpr -> TopLevel LocType LocPatn LocExpr
    check (TypeDec n tvs t) =
      TypeDec n tvs (embedRecPar t)
    check (FunDef  n (PT tvs t) y) =
      FunDef n (PT tvs (embedRecPar t)) y
    check (AbsDec n (PT tvs t)) =
      AbsDec n (PT tvs (embedRecPar t))
    check (AbsTypeDec n tvs ts)
      = AbsTypeDec n tvs (map embedRecPar ts)
    check (ConstDef n t e)
      = ConstDef n (embedRecPar t) e
    -- TODO: Consts?
    check t = t

embedRecPar :: LocType -> LocType
embedRecPar t = erp False (Just M.empty) t
  where
    -- Bool represents whether or not we are in a context
    erp :: Bool -> RecContext LocType -> LocType -> LocType 
    erp b ctxt@(Just c) orig@(LocType p ty) =
      LocType p $ case ty of
        -- If we find a type variable that is in our context, we replace it with a recursive parameter
        -- However if we are currently changing a recursive context (b == True), don't infinitely insert the context
        TVar n b' _ | M.member n c -> TRPar n b' (if b then Nothing else Just (M.map (erp True ctxt) c))
        -- If we find a record, add it's recursive parameter to the context if it exists and recurse
        TRecord rp fs s -> 
          let c' = case rp of 
                        Rec v -> M.insert v orig c
                        _     -> c
          in TRecord rp (map (\(n,(x, y)) -> (n, (erp b (Just c') x, y))) fs) s

        TFun t1 t2  -> TFun (erp b ctxt t1) (erp b ctxt t2) 
        TVariant ts -> TVariant $ M.map (\(ts', x) -> (map (erp b ctxt) ts', x)) ts
        TTuple ts   -> TTuple (map (erp b ctxt) ts)
        TCon n ts s     ->
          TCon n (map (erp b ctxt) ts) s
#ifdef BUILTIN_ARRAYS
        TArray t e  -> TArray (erp b ctxt t) e
#endif
        TUnbox t    -> TUnbox (erp b ctxt t)
        TBang t     -> TBang (erp b ctxt t)
        TTake fs t  -> TTake fs (erp b ctxt t)
        TPut fs t   -> TPut fs (erp b ctxt t)
        t           -> t

allEither :: [Either a ()] -> Either a ()
allEither []             = Right ()
allEither ((Right _):xs) = allEither xs
allEither ((Left x):_)   = Left x

-- Checks that no recursive parameters shadow type variables
checkNoShadowing :: [TopLevel LocType LocPatn LocExpr] 
                 -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
checkNoShadowing [] = return ()
checkNoShadowing (t:ts) = do
  check t
  checkNoShadowing ts
  where
    check x = 
      case x of 
        TypeDec _ tvs t       -> ns tvs t
        FunDef _ (PT tvs t) y -> ns (map fst tvs) t
        AbsTypeDec _ tvs ts   -> allEither $ map (ns tvs) ts
        AbsDec _ (PT tvs t)   -> ns (map fst tvs) t
        ConstDef _ t _        -> ns [] t
        tl                    -> Right ()

    srcObj = sourceObject t
  
    ns :: [Syn.TyVarName] -> LocType -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
    ns tvs (LocType p ty) =
      case ty of
        TRecord (Rec v) fs _ | v `elem` tvs 
                            -> Left (RecParShadowsTyVar, [(srcObj, p)])
        TRecord _ fs _      -> allEither $ map (\(_,(x,_)) -> ns tvs x) fs
        TFun t1 t2  -> do
          ns tvs t1
          ns tvs t2
        TVariant ts -> 
          allEither $ map (\(ts', _) -> (allEither $ map (\t -> ns tvs t) ts')) $ M.elems ts
        TTuple   ts -> allEither $ map (ns tvs) ts
        TCon n ts s     ->
          allEither $ map (ns tvs) ts
#ifdef BUILTIN_ARRAYS
        TArray t e  -> ns tvs t
#endif
        TUnbox t    -> ns tvs t
        TBang t     -> ns tvs t
        TTake fs t  -> ns tvs t
        TPut fs t   -> ns tvs t
        t           -> Right ()

-- Checks that all types are strictly positive
checkStrictlyPositive :: [TopLevel LocType LocPatn LocExpr]
                      -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
checkStrictlyPositive []     = Right ()
checkStrictlyPositive (t:ts) = do
  check t
  checkStrictlyPositive ts
  where
    check x = 
      case x of 
        TypeDec _ _ t       -> sp S.empty S.empty t 
        FunDef _ (PT _ t) y -> sp S.empty S.empty t
        AbsDec _ (PT _ t)   -> sp S.empty S.empty t 
        AbsTypeDec _ _ ts   -> allEither $ map (sp S.empty S.empty) ts
        ConstDef _ t _      -> sp S.empty S.empty t
        tl                  -> Right ()

    srcObj = sourceObject t

    sp :: S.Set Syn.RecParName 
        -> S.Set Syn.RecParName
        -> LocType -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
    sp s b (LocType p ty) = 
      case ty of
        -- If we find a recursive parameter in our 'negative' set, error
        TRPar v _ _       -> if v `S.member` s then Left (NonStrictlyPositive, [(srcObj, p)]) else Right ()
        TRecord rp fs _ -> 
          let b' = (case rp of Rec v -> S.insert v b; _ -> b) in
            allEither $ map (\(_,(x,_)) -> sp s b' x) fs
        TFun t1 t2      -> do
          sp (s `S.union` b) b t1
          sp s b t2
        TVariant ts     -> 
          allEither $ map (\(ts', _) -> (allEither $ map (\t -> sp s b t) ts')) $ M.elems ts
        TTuple ts       ->
          (allEither . map (sp s b)) ts
        TCon _ ts _     ->
          (allEither . map (sp s b)) ts

#ifdef BUILTIN_ARRAYS
        TArray t e      -> sp s b t
#endif
        TUnbox  t       -> sp s b t
        TBang   t       -> sp s b t
        TTake _ t       -> sp s b t
        TPut  _ t       -> sp s b t
        _               -> Right ()

-- Note: it doesn't make much sense to check for unused definitions as they may be used
-- by the FFI. / zilinc
reorganize :: Maybe [String]
           -> [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
           -> Either (ReorganizeError, [(SourceObject, SourcePos)]) [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
reorganize mes bs = do 
                let m = classify bs
                    cs = G.stronglyConnectedComponents $ case mes of
                            Nothing -> dependencyGraph_ m
                            Just es -> dependencyGraph (map parseSourceObject es) m
                    rs = embedRecPars bs
                checkNoNameClashes (map (second fst3) m) M.empty
                -- FIXME: it might be good to preserve the original order as much as possible
                -- see file `tests/pass_wf-take-put-tc-2.cogent` as a bad-ish example / zilinc

                let fnames = funNames (map thd bs)

                cs' <- forM cs $ \case
                          G.AcyclicSCC i ->  Right $ case lookup i m of
                                                      Nothing -> __impossible $ "reorganize: " ++ show i
                                                      Just x  -> [x]
                                            -- Only functions can be recursively defined
                          G.CyclicSCC is -> if all (`elem` fnames) is then
                                              Right $ concatMap (\i -> case lookup i m of
                                                Nothing -> __impossible $ "reorganize: " ++ show i
                                                Just x  -> [x]) is
                                            else
                                              Left $ (CyclicDependency, map (id &&& getSourcePos m) is)

                -- Check recursive parameters are used correctly

                let rs = embedRecPars (concat cs')
                checkNoShadowing      (map thd rs)
                checkStrictlyPositive (map thd rs)

                return rs
                        
  where getSourcePos m i | Just (p,_,_) <- lookup i m = p
                         | otherwise = __impossible "getSourcePos (in reorganize)"

        funNames :: [TopLevel LocType LocPatn LocExpr] -> [SourceObject]
        funNames ((FunDef n _ _):tls) = [ValName n] ++ funNames tls
        funNames ((AbsDec n _):tls) = [ValName n] ++ funNames tls
        funNames (t:tls) = funNames tls
        funNames [] = []

        -- FIXME: proper parsing / zilinc
        parseSourceObject :: String -> SourceObject
        parseSourceObject (c:cs) | isUpper c = TypeName (c:cs)
                                 | otherwise = ValName  (c:cs)
        thd (_,_,x) = x