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
                     | DuplicateRepDefinition

data SourceObject = TypeName TypeName
                  | ValName  VarName
                  | RepName RepName
                  | DocBlock' String
                  deriving (Eq, Ord)

dependencies :: TopLevel LocType LocPatn LocExpr -> [SourceObject]
dependencies (Include _) = __impossible "dependencies"
dependencies (IncludeStd _) = __impossible "dependencies"
dependencies (TypeDec _ _ t) = map TypeName (fcT (stripLocT t))
dependencies (AbsTypeDec _ _ ts) = map TypeName (foldMap (fcT . stripLocT) ts)
dependencies (DocBlock _) = []
dependencies (RepDef {}) = [] -- for now
dependencies (AbsDec _ pt) = map TypeName (foldMap (fcT . stripLocT) pt)
dependencies (FunDef _ pt as) = map TypeName (foldMap (fcT . stripLocT) pt
                                           ++ foldMap (fcA . fmap stripLocE) as)
                             ++ map ValName  (foldMap (fvA . ffmap stripLocP . fmap stripLocE) as)
dependencies (ConstDef _ t e) = map TypeName (fcT (stripLocT t))
                             ++ map ValName  (fvE (stripLocE e))

classify :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
         -> [(SourceObject, (SourcePos, DocString, TopLevel LocType LocPatn LocExpr))]
classify = map (\px -> (sourceObject (thd3 px), px))
  where sourceObject (Include _)        = __impossible "sourceObject (in classify)"
        sourceObject (IncludeStd _)     = __impossible "sourceObject (in classify)"
        sourceObject (DocBlock s)       = DocBlock' s
        sourceObject (TypeDec n _ _)    = TypeName n
        sourceObject (RepDef (RepDecl _ n _ _))    = RepName n
        sourceObject (AbsTypeDec n _ _) = TypeName n
        sourceObject (AbsDec n _)       = ValName n
        sourceObject (FunDef v _ _)     = ValName v
        sourceObject (ConstDef v _ _)   = ValName v

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
  where msg = case s of TypeName  _ -> DuplicateTypeDefinition
                        ValName   _ -> DuplicateValueDefinition
                        RepName   _ -> DuplicateRepDefinition
                        DocBlock' _ -> __impossible "checkNoNameClashes"

-- Note: it doesn't make much sense to check for unused definitions as they may be used
-- by the FFI. / zilinc
reorganize :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
           -> Either (ReorganizeError, [(SourceObject, SourcePos)]) [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)]
reorganize bs = do let m = classify bs
                       cs = G.stronglyConnectedComponents (dependencyGraph m)
                   checkNoNameClashes (map (second fst3) m) M.empty
                   -- FIXME: it might be good to preserve the original order as much as possible
                   -- see file `tests/pass_wf-take-put-tc-2.cogent` as a bad-ish example / zilinc
                   forM cs $ \case
                     G.AcyclicSCC i -> Right $ Maybe.fromJust $ lookup i m
                     G.CyclicSCC is -> Left  $ (CyclicDependency, map (id &&& getSourcePos m) is)
  where getSourcePos m i | Just (p,_,_) <- lookup i m = p
                         | otherwise = __impossible "getSourcePos (in reorganize)"

