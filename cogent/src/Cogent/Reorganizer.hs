--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE LambdaCase, PatternGuards #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Reorganizer where

import Cogent.Common.Syntax
import Cogent.Compiler (__impossible)
import Cogent.Surface
import Cogent.Util

import Control.Arrow
import Control.Monad (forM)
-- import Data.Foldable hiding (notElem)
import Data.Functor.Compose
import qualified Data.Graph.Wrapper as G
import qualified Data.Map as M
import qualified Data.Maybe as Maybe
import Text.Parsec.Pos

data ReorganizeError = CyclicDependency
                     | DuplicateTypeDefinition
                     | DuplicateValueDefinition

fvA :: Alt RawPatn RawExpr -> [VarName]
fvA (Alt p _ e) = let locals = fvP p
                   in filter (`notElem` locals) (fvE e)

fvB :: Binding RawType RawIrrefPatn RawExpr -> ([VarName], [VarName])
fvB (Binding ip _ e _) = (fvIP ip, fvE e)

fvP :: RawPatn -> [VarName]
fvP (RP (PCon _ ips)) = foldMap fvIP ips
fvP (RP (PIrrefutable ip)) = fvIP ip
fvP _ = []

fvIP :: RawIrrefPatn -> [VarName]
fvIP (RIP (PVar pv)) = [pv]
fvIP (RIP (PTuple ips)) = foldMap fvIP ips
fvIP (RIP (PUnboxedRecord mfs)) = foldMap (fvIP . snd) $ Compose mfs
fvIP (RIP (PTake pv mfs)) = foldMap (fvIP . snd) $ Compose mfs
fvIP _ = []

fcB :: Binding RawType RawIrrefPatn RawExpr -> [TagName]
fcB (Binding _ t e _) = foldMap fcT t ++ fcE e

fcA :: Alt v RawExpr -> [TagName]
fcA (Alt _ _ e) = fcE e

fcE :: RawExpr -> [TagName]
fcE (RE (Let bs e)) = fcE e ++ foldMap fcB bs
fcE (RE (Match e _ as)) = fcE e ++ foldMap fcA as
fcE (RE (TypeApp _ ts _)) = foldMap fcT (Compose ts)
fcE (RE e) = foldMap fcE e

fvE :: RawExpr -> [VarName]
fvE (RE (TypeApp v _ _)) = [v]
fvE (RE (Var v)) = [v]
fvE (RE (Match e _ alts)) = fvE e ++ foldMap fvA alts
fvE (RE (Let (b:bs) e)) = let (locals, fvs) = fvB b
                              fvs' = filter (`notElem` locals) (fvE (RE (Let bs e)))
                           in fvs ++ fvs'
fvE (RE e) = foldMap fvE e

fcT :: RawType -> [TagName]
fcT (RT (TCon n ts _)) = n : foldMap fcT ts
fcT (RT t) = foldMap fcT t

data SourceObject = TypeName TypeName
                  | ValName  VarName
                  | DocBlock' String
                  deriving (Eq, Ord)

dependencies :: TopLevel LocType LocPatn LocExpr -> [SourceObject]
dependencies (Include _) = __impossible "dependencies"
dependencies (IncludeStd _) = __impossible "dependencies"
dependencies (TypeDec _ _ t) = map TypeName (fcT (stripLocT t))
dependencies (AbsTypeDec _ _) = []
dependencies (DocBlock _) = []
dependencies (AbsDec _ pt) = map TypeName (foldMap (fcT . stripLocT) pt)
dependencies (FunDef _ pt as) = map TypeName (foldMap (fcT . stripLocT) pt
                                           ++ foldMap (fcA . fmap stripLocE) as)
                             ++ map ValName  (foldMap (fvA . ffmap stripLocP . fmap stripLocE) as)
dependencies (ConstDef _ t e) = map TypeName (fcT (stripLocT t))
                             ++ map ValName  (fvE (stripLocE e))

classify :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
         -> [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
classify = map (\px -> (sourceObject (thd3 px), px))
  where sourceObject (Include _)      = __impossible "sourceObject (in classify)"
        sourceObject (IncludeStd _)   = __impossible "sourceObject (in classify)"
        sourceObject (DocBlock s)     = DocBlock' s
        sourceObject (TypeDec n _ _)  = TypeName n
        sourceObject (AbsTypeDec n _) = TypeName n
        sourceObject (AbsDec n _)     = ValName n
        sourceObject (FunDef v _ _)   = ValName v
        sourceObject (ConstDef v _ _) = ValName v

graphOf :: Ord a => (b -> [a]) -> [(a, b)] -> G.Graph a b
graphOf f = G.fromListLenient . map (\(k,v) -> (k, v, f v))

dependencyGraph :: [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
                -> G.Graph SourceObject (SourcePos, DocString, TopLevel LocType LocPatn LocExpr)
dependencyGraph = graphOf (dependencies . thd3)

checkNoNameClashes :: [(SourceObject, SourcePos)]
                   -> M.Map SourceObject SourcePos
                   -> Either (ReorganizeError, [(SourceObject, SourcePos)]) ()
checkNoNameClashes [] bindings = return ()
checkNoNameClashes ((s,d):xs) bindings
  | Just x <- M.lookup s bindings = Left (msg, [(s, x), (s, d)])
  | otherwise = let bindings' = case s of DocBlock' _ -> bindings; _ -> M.insert s d bindings
                 in checkNoNameClashes xs bindings'
  where msg = case s of TypeName _ -> DuplicateTypeDefinition; ValName _ -> DuplicateValueDefinition; DocBlock' _ -> error "WTF just happened"

-- Note: it doesn't make much sense to check for unused definitions as they may be used
-- by the FFI. / zilinc
reorganize :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
           -> Either (ReorganizeError, [(SourceObject, SourcePos)]) [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
reorganize bs = do let m = classify bs
                       cs = G.stronglyConnectedComponents (dependencyGraph m)
                   checkNoNameClashes (map (second fst3) m) M.empty
                   forM cs $ \case
                     G.AcyclicSCC i -> Right $ Maybe.fromJust $ lookup i m
                     G.CyclicSCC is -> Left  $ (CyclicDependency, map (id &&& getSourcePos m) is)
  where getSourcePos m i | Just (p,_,_) <- lookup i m = p
                         | otherwise = __impossible "getSourcePos (in reorganize)"

