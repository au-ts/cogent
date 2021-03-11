{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}




-- | Haskell PBT generator
--
-- Generates Hs functions which are used in Property-Based Testing

module Cogent.Haskell.PBT.Builders.Welf (
    genDecls''
) where

import Cogent.Haskell.PBT.Builders.Absf
import Cogent.Haskell.PBT.Builders.Rrel

import Cogent.Isabelle.ShallowTable (TypeStr(..), st)
import qualified Cogent.Core as CC
import Cogent.Core (TypedExpr(..))
import Cogent.C.Syntax
import Cogent.Common.Syntax
import Cogent.Haskell.HscGen
import Cogent.Util ( concatMapM, Stage(..), delimiter, secondM, toHsTypeName, concatMapM, (<<+=) )
import Cogent.Compiler (__impossible)
import qualified Cogent.Haskell.HscSyntax as Hsc
import qualified Data.Map as M
import Language.Haskell.Exts.Build
import Language.Haskell.Exts.Pretty
import Language.Haskell.Exts.Syntax as HS
import Language.Haskell.Exts.SrcLoc
import Text.PrettyPrint
import Debug.Trace
import Cogent.Haskell.PBT.DSL.Types
import Cogent.Haskell.PBT.Types
import Cogent.Haskell.Shallow as SH
import Prelude as P
import Data.Tuple
import Data.Function
import Data.Maybe
import Data.Either
import Data.List (find, partition, group, sort)
import Data.Generics.Schemes (everything)
import Control.Arrow (second, (***), (&&&))
import Control.Applicative
import Lens.Micro
import Lens.Micro.TH
import Lens.Micro.Mtl
import Control.Monad.RWS hiding (Product, Sum, mapM)
import Data.Vec as Vec hiding (sym)
import Cogent.Isabelle.Shallow (isRecTuple)

-- | top level builder for gen_* :: Gen function 
-- -----------------------------------------------------------------------
genDecls'' :: PbtDescStmt -> [CC.Definition TypedExpr VarName b] -> SG [Decl ()]
genDecls'' stmt defs = do
        icTy <- getFnIcTy (stmt ^. funcname) defs
        let (_, _, predExp) = findKvarsInDecl Welf Pred $ stmt ^. decls
            fnName = "gen_" ++ stmt ^. funcname
            genCon = TyCon () (mkQName "Gen")
            tyOut = TyApp () genCon $ TyParen () icTy
            e = mkGenBody predExp
            
            sig    = TypeSig () [mkName fnName] tyOut
            -- TODO: better gen_* body
            --       - what else do you need for arbitrary?
            dec    = FunBind () [Match () (mkName fnName) [] (UnGuardedRhs () $ e) Nothing]
            -- TODO: this is a dummy HS spec function def -> replace with something better
            hs_dec    = FunBind () [Match () (mkName $ "hs_"++(stmt ^. funcname)) [] (UnGuardedRhs () $
                           function "undefined") Nothing]
          in return [sig, dec, hs_dec]

-- this needs to take a predicate and turn it into a generator
-- this is naive method so far
-- TODO: advanced method
--  -> convert predicate into functions, this is refinement in a way
--  -> see figuring out
mkGenBody :: Maybe (Exp ()) -> Exp ()
mkGenBody predExp = case predExp of 
                      Just x -> infixApp genfn predOp $ predFunc x
                      Nothing -> genfn
    where genfn = function "arbitrary" -- "arbitrary"
          predOp = op $ mkName "suchThat"
          predFunc x = lamE [pvar $ mkName "ic"] x


getFnIcTy :: String -> [CC.Definition TypedExpr VarName b] -> SG (Type ())
getFnIcTy funcname defs =
    let fnDef = fromJust $ find (\x -> CC.getDefinitionId x == funcname) defs
      in getFnIcTy' fnDef

getFnIcTy' :: CC.Definition TypedExpr VarName b -> SG (Type ())
getFnIcTy' (CC.FunDef _ fn ps _ ti to _) = shallowType ti
getFnIcTy' (CC.AbsDecl _ fn ps _ ti to) = shallowType ti
getFnIcTy' _ = __impossible "could not get input type"
