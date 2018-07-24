
module Cogent.TypeCheck.Assignment where

import Cogent.Compiler
import Cogent.Surface
import Cogent.TypeCheck.Base
import Cogent.Util

import Data.Monoid hiding (Alt)
import qualified Data.IntMap as M
import Prelude as P hiding (lookup)

newtype Assignment = Assignment (M.IntMap SExpr)


lookup :: Assignment -> Int -> RawType -> SExpr
lookup a@(Assignment m) i t = maybe (SU i t) (assign a) (M.lookup i m)

singleton :: Int -> SExpr -> Assignment
singleton i e = Assignment (M.fromList [(i, e)])

null :: Assignment -> Bool
null (Assignment x) = M.null x

#if __GLASGOW_HASKELL__ < 803
instance Monoid Assignment where
  mempty = Assignment M.empty
  mappend (Assignment a) (Assignment b) = Assignment (a <> b)
#else
instance Semigroup Assignment where
  Assignment a <> Assignment b = Assignment (a <> b)
instance Monoid Assignment where
  mempty = Assignment M.empty
#endif

forUnknowns :: (Int -> RawType -> SExpr) -> SExpr -> SExpr
forUnknowns f (SU x t) = f x t
forUnknowns f (SE x) = SE (fmap (forUnknowns f) x)

assign :: Assignment -> SExpr -> SExpr
assign = forUnknowns . lookup

assignAlts :: Assignment -> [Alt TCPatn TCExpr] -> [Alt TCPatn TCExpr]
assignAlts = map . assignAlt

assignAlt :: Assignment -> Alt TCPatn TCExpr -> Alt TCPatn TCExpr
assignAlt a = fmap (assignE a) . ffmap (fmap (assignT a))

assignE :: Assignment -> TCExpr -> TCExpr
assignE a (TE t e l) = TE (assignT a t)
                          (ffffmap (assignT a) $
                           fffmap (fmap (assignT a)) $
                           ffmap (fmap (assignT a)) $
                           fmap (assignE a) e)
                          l

assignT :: Assignment -> TCType -> TCType
assignT a (T t) = T $ ffmap (assign a) $ fmap (assignT a) t
assignT a (U n) = U n

assignC :: Assignment -> Constraint -> Constraint
assignC a (t1 :< t2) = (fmap (assignT a) t1) :< (fmap (assignT a) t2)
assignC a (c1 :& c2) = assignC a c1 :& assignC a c2
assignC a (Upcastable t1 t2) = Upcastable (assignT a t1) (assignT a t2)
assignC a (Share t m) = Share (assignT a t) m
assignC a (Drop t m) = Drop (assignT a t) m
assignC a (Escape t m) = Escape (assignT a t) m
assignC a (c :@ e) = assignC a c :@ e
assignC a (Unsat e) = Unsat $ assignErr a e
assignC a (SemiSat w) = SemiSat $ assignWarn a w
assignC a (Sat) = Sat
assignC a (Exhaustive t ps) = Exhaustive (assignT a t) ps
assignC a (Exists e) = Exists (assign a e)
assignC a (ForAll e) = ForAll (assign a e)

assignErr :: Assignment -> TypeError -> TypeError
assignErr a e = e  -- TODO

assignWarn :: Assignment -> TypeWarning -> TypeWarning
assignWarn a w = w  -- TODO

assignCtx :: Assignment -> ErrorContext -> ErrorContext
assignCtx a c = c  -- TODO

