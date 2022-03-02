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
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
--{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
#if __GLASGOW_HASKELL__ < 709
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans -Wwarn #-}


module Cogent.C.Monad where

import           Cogent.C.Syntax       as C hiding (BinOp (..), UnOp (..))
import qualified Cogent.C.Syntax       as C (BinOp (..), UnOp (..))
import           Cogent.Compiler
import           Cogent.Common.Syntax  as Syn
import           Cogent.Common.Types   as Typ
import           Cogent.Core           as CC
import           Cogent.Inference            (kindcheck_)
import           Cogent.Isabelle.Deep
import           Cogent.Mono                 (Instance)
import           Cogent.Normal               (isAtom)
import           Cogent.Util                 (decap, tupleFieldNames, toCName,
                                        extTup2l, extTup3r, first3, flip3, secondM, whenM)
import qualified Data.DList          as DList
import           Data.Fin                    (Fin (..))
import           Data.Nat            as Nat
import qualified Data.OMap           as OMap
import           Data.Vec            as Vec  hiding (repeat, zipWith)

import           Control.Applicative         hiding (empty)
import           Control.Arrow                      ((***), (&&&), second)
import           Control.Monad.RWS.Strict    hiding (mapM, mapM_, Dual, (<>), Product, Sum)
import           Data.Binary
import           Data.Char                   (isAlphaNum, toUpper)
#if __GLASGOW_HASKELL__ < 709
import           Data.Foldable               (mapM_)
#endif
import           Data.Functor.Compose
import qualified Data.List           as L
import           Data.Loc                    (noLoc)  -- FIXME: remove
import qualified Data.Map            as M
import           Data.Maybe                  (catMaybes, fromJust)
import           Data.Monoid                 ((<>))
-- import           Data.Semigroup.Monad
-- import           Data.Semigroup.Reducer      (foldReduce)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable            (mapM)
import           Data.Tuple                  (swap)
import           GHC.Generics                (Generic)
import           Lens.Micro                  hiding (at)
import           Lens.Micro.Mtl              hiding (assign)
import           Lens.Micro.TH
#if __GLASGOW_HASKELL__ < 709
import           Prelude             as P    hiding (mapM, mapM_)
#else
import           Prelude             as P    hiding (mapM)
#endif
import           System.IO (Handle, hPutChar)
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))

-- import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)

-- *****************************************************************************
-- * The state for code-generation

-- | A FunClass is a map from the structural types of functions to a set of all names
--   of declared functions with that structural type. It is used to generate the
--   dispatch functions needed to implement higher order functions in C.
type FunClass  = M.Map StrlType (S.Set (FunName, Attr))  -- ^ @c_strl_type &#x21A6; funnames@
type VarPool   = M.Map CType [CId]  -- ^ vars available @(ty_id &#x21A6; [var_id])@

-- | The 'i'th element of the vector is the C expression bound to the variable in scope
--   with DeBruijn index 'i'. The type parameter 'v' is the number of variables in scope.
type GenRead v = Vec v CExpr

data GenState  = GenState
  { _cTypeDefs    :: [(StrlType, CId)]
  , _cTypeDefMap  :: M.Map StrlType CId
    -- ^ Maps structural types we've seen so far to the
    --   C identifiers corresponding to the structural type.
    --
    --   We keep both a Map and a List because the list remembers the order,
    --   but the map gives performant reads.

  , _typeSynonyms :: M.Map TypeName CType
  , _typeCorres   :: DList.DList (CId, CC.Type 'Zero VarName)
    -- ^ C type names corresponding to Cogent types
  , _typeCorres'  :: OMap.OMap CId Sort
    -- ^ The new C :-> Cogent * getter/setter table

  , _absTypes     :: M.Map TypeName (S.Set [CId])
    -- ^ Maps TypeNames of abstract Cogent types to
    --   the Set of all monomorphised type argument lists
    --   which the abstract type is applied to in the program.

  , _recParCIds      :: M.Map (CC.Type 'Zero VarName) CId
  -- ^ Maps a global recursive parameter type to a cid
  , _recParRecordIds :: M.Map RecParName CId
  -- ^ Maps a local recursive parameter name to the CId of the record it references.

  , _custTypeGen  :: M.Map (CC.Type 'Zero VarName) (CId, CustTyGenInfo)
  , _funClasses   :: FunClass
  , _localOracle  :: Integer
  , _globalOracle :: Integer
  , _varPool      :: VarPool
  , _ffiFuncs     :: M.Map FunName (CType, CType)
    -- ^ A map containing functions that need to generate C FFI functions.
    --   The map is from the original function names (before prefixing with @\"ffi_\"@ to a pair of @(marshallable_arg_type, marshallable_ret_type)@.
    --   This map is needed when we generate the Haskell side of the FFI.

  , _boxedRecordSetters :: M.Map StrlCogentType (M.Map FieldName FunName)
  , _boxedRecordGetters :: M.Map StrlCogentType (M.Map FieldName FunName)
    -- ^ The expressions to call the generated setter and getter functions for the fields of boxed cogent records.
  , _boxedArraySetters :: M.Map (CC.Type 'Zero VarName) FunName
  , _boxedArrayGetters :: M.Map (CC.Type 'Zero VarName) FunName
  } deriving (Generic)

instance Binary GenState

makeLenses ''GenState

newtype Gen v a = Gen { runGen :: RWS (GenRead v) [CExtDecl] GenState a }
                deriving (Functor, Applicative, Monad,
                          MonadReader (GenRead v),
                          MonadWriter [CExtDecl],
                          MonadState  GenState)

#if MIN_VERSION_base(4,13,0)
instance MonadFail (Gen v) where
  fail = __impossible
#endif

freshLocalCId :: Char -> Gen v CId
freshLocalCId c = do (localOracle += 1); (c:) . show <$> use localOracle

freshGlobalCId :: Char -> Gen v CId
freshGlobalCId c = do (globalOracle += 1); (c:) . show <$> use globalOracle

