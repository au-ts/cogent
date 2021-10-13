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
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Glue where

import qualified Cogent.C         as CG
import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import qualified Cogent.Context   as Ctx
import qualified Cogent.Core      as CC
import           Cogent.Dargent.TypeCheck
import qualified Cogent.Desugar   as DS
import qualified Cogent.Inference as IN
import qualified Cogent.Mono      as MN
import qualified Cogent.Parser    as PS
import           Cogent.PrettyPrint
import qualified Cogent.Surface   as SF
import qualified Cogent.TypeCheck.Base       as TC
import qualified Cogent.TypeCheck.Errors     as TC
import qualified Cogent.TypeCheck.Generator  as TC
import qualified Cogent.TypeCheck.Post       as TC
import qualified Cogent.TypeCheck.Solver     as TC
import qualified Cogent.TypeCheck.Subst      as TC
import qualified Cogent.TypeCheck.Errors     as TC

import           Cogent.Util
import qualified Data.DList as DList
import           Data.Ex
import           Data.Nat (Nat(Zero,Suc))
import qualified Data.OMap as OMap
import           Data.Vec as Vec hiding (repeat)

import           Control.Applicative
import           Control.Arrow (Arrow(..), second, (&&&))
import           Control.Monad.Except hiding (sequence, mapM_, mapM)
import           Control.Monad.Reader
import           Control.Monad.RWS.Strict
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Maybe

import qualified Data.ByteString.Char8 as B
import           Data.Loc
import           Data.List as L
import           Data.Map as M
import           Data.Maybe (fromJust, fromMaybe, isJust, maybe, catMaybes)
import qualified Data.Sequence as Seq
import           Data.Set as S

import           GHC.Generics

import           Language.C.Parser as CP hiding (parseExp, parseType)
import           Language.C.Syntax as CS
import           Lens.Micro hiding (to)
import           Lens.Micro.Mtl
import           Lens.Micro.TH
import           System.FilePath (replaceBaseName, replaceExtension, takeBaseName, takeExtension, (<.>))
import           System.IO (hPutStrLn, stderr)
import           Text.Parsec.Pos (newPos, SourcePos)
import           Text.Parsec.Prim as PP hiding (State)
import           Text.PrettyPrint.ANSI.Leijen (vsep)
import           Unsafe.Coerce

import           Debug.Trace

-- Parse the anti-quoted C source code to produce a sequence of C definitions.

parseFile :: [Extensions] -> [String] -> FilePath -> ExceptT String IO [CS.Definition]
parseFile exts deftypnames filename = do
#if MIN_VERSION_language_c_quote(0,11,1)
  let start = Just $ startPos filename
#else
  let start = startPos filename
#endif
  s <- lift $ B.readFile filename
  typnames <- case __cogent_ext_types of Nothing -> lift (return deftypnames); Just f -> lift $ simpleLineParser f
  case CP.evalP (__fixme CP.parseUnit) (CP.emptyPState exts typnames s start) of -- FIXME: check for other antiquotes
    Left err -> throwE $ "Error: Failed to parse C: " ++ show err
    Right ds -> return ds

defaultExts :: [Extensions]
defaultExts = [Antiquotation, C99, Gcc]

defaultTypnames :: [String]
defaultTypnames = []


-- Desugaring, Monomorphising, and CG

data TcState = TcState { _tfuncs :: Map FunName (SF.Polytype TC.TCType)
                       , _ttypes :: TC.TypeDict
                       , _consts :: Map VarName (TC.TCType, TC.TCExpr, SourcePos)
                       , _dldefs :: NamedDataLayouts
                       }

data DsState = DsState { _typedefs  :: DS.Typedefs
                       , _constdefs :: DS.Constants
                       }

data CoreTcState = CoreTcState { _funtypes :: Map FunName (CC.FunctionType VarName)
                               , _typesyns :: [CC.Definition CC.TypedExpr VarName VarName]
                               }

data MnState = MnState { _funMono  :: MN.FunMono VarName
                       , _typeMono :: MN.InstMono VarName
                       }

data CgState = CgState { _cTypeDefs    :: [(CG.StrlType, CG.CId)]
                       , _cTypeDefMap  :: M.Map CG.StrlType CG.CId
                       , _typeSynonyms :: M.Map TypeName CG.CType
                       , _typeCorres   :: DList.DList (CG.CId, CC.Type 'Zero VarName)
                       , _typeCorres'  :: OMap.OMap CG.CId CG.Sort
                       , _absTypes     :: M.Map TypeName (S.Set [CG.CId])
                       , _custTypeGen  :: M.Map (CC.Type 'Zero VarName) (CG.CId, CustTyGenInfo)
                       , _funClasses   :: CG.FunClass
                       , _localOracle  :: Integer  -- FIXME: should be moved to DefnState
                       , _globalOracle :: Integer
                       }

data GlState = GlState { _tcDefs   :: [SF.TopLevel TC.DepType TC.TypedPatn TC.TypedExpr]
                       , _tcState  :: TcState
                       , _dsState  :: DsState
                       , _coreTcState  :: CoreTcState
                       , _mnState  :: MnState
                       , _cgState  :: CgState
                       , _defns  :: Map CS.Definition String -- C definitions mapped to their Cogent type name                       
                       }

data FileState = FileState { _file :: FilePath }

data DefnState t = DefnState { _kenv :: Vec t (TyVarName, Kind)
                             , _ectx :: [TC.ErrorContext]
                             }

data MonoState = MonoState { _inst :: (MN.Instance VarName, Maybe Int) }  -- Either ([], Nothing), or (_:_, Just _)

makeLenses ''TcState
makeLenses ''DsState
makeLenses ''CoreTcState
makeLenses ''MnState
makeLenses ''CgState
makeLenses ''GlState
makeLenses ''FileState
makeLenses ''DefnState
makeLenses ''MonoState

type GlMono t = ReaderT (MonoState  ) (GlDefn t)
type GlDefn t = ReaderT (DefnState t) (GlFile  )
type GlFile   = ReaderT (FileState  ) (Gl      )
type Gl       = StateT  (GlState    ) (GlErr   )
type GlErr    = ExceptT (String     ) (IO      )


{-- The purpose of this module is to parse anti-quoted C source code,
 -- parsing the embedded Cogent fragments into C.

 -- We define two type classes for handling anti-quotes via generic
 -- representations. Thus any type with a generic representation can be
 -- given the default implementation for handling anti-quotes. --}

class Monad m => HandleQuotes1 f m where
  handleQuotes1 :: f p -> m (f p)

defaultHandleQuotes :: (Generic a, Monad m, HandleQuotes1 (Rep a) m) => a -> m a
defaultHandleQuotes x = to <$> handleQuotes1 (from x)

instance Monad m => HandleQuotes1 V1 m where
  handleQuotes1 x = return x

instance Monad m => HandleQuotes1 U1 m where
  handleQuotes1 x = return x

instance (Monad m, HandleQuotes c m) => HandleQuotes1 (K1 i c) m where
  handleQuotes1 x = K1 <$> handleQuotes (unK1 x)

instance (Monad m, HandleQuotes1 f m) => HandleQuotes1 (M1 i c f) m where
  handleQuotes1 (M1 x) = M1 <$> handleQuotes1 x

instance (Monad m, HandleQuotes1 f m, HandleQuotes1 g m) => HandleQuotes1 (f :+: g) m where
  handleQuotes1 (L1 x) = L1 <$> handleQuotes1 x
  handleQuotes1 (R1 x) = R1 <$> handleQuotes1 x

instance (Monad m, HandleQuotes1 f m, HandleQuotes1 g m) => HandleQuotes1 (f :*: g) m where
  handleQuotes1 (f :*: g) = (:*:) <$> (handleQuotes1 f) <*> (handleQuotes1 g)

class Monad m => HandleQuotes a m where
  handleQuotes :: a -> m a
  default handleQuotes :: (Generic a, Monad m, HandleQuotes1 (Rep a) m) => a -> m a
  handleQuotes = defaultHandleQuotes


{-- Automatically derive generic representations for the C AST. -}
deriving instance Generic CS.AsmIn
deriving instance Generic CS.ArraySize
deriving instance Generic CS.Attr
deriving instance Generic CS.BlockItem
deriving instance Generic CS.BlockType
deriving instance Generic CS.CEnum
deriving instance Generic CS.Decl
deriving instance Generic CS.DeclSpec
deriving instance Generic CS.Definition
deriving instance Generic CS.Designation
deriving instance Generic CS.Designator
deriving instance Generic CS.Exp
deriving instance Generic CS.ExeConfig
deriving instance Generic CS.Field
deriving instance Generic CS.FieldGroup
deriving instance Generic CS.Func
deriving instance Generic CS.Init
deriving instance Generic CS.InitGroup
deriving instance Generic CS.Initializer
deriving instance Generic CS.Param
deriving instance Generic CS.Params
deriving instance Generic CS.Stm
deriving instance Generic CS.Type
deriving instance Generic CS.Typedef
deriving instance Generic CS.TypeQual
deriving instance Generic CS.TypeSpec

{-- Terminal instances of anti-quote handling. --}
instance Monad m => HandleQuotes AsmOut m where
  handleQuotes x = return x

instance Monad m => HandleQuotes AssignOp m where
  handleQuotes x = return x

instance Monad m => HandleQuotes BinOp m where
  handleQuotes x = return x

instance Monad m => HandleQuotes Bool m where
  handleQuotes x = return x

instance Monad m => HandleQuotes Char m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.Const m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.Id m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.LambdaIntroducer m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.LambdaDeclarator m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCArg m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCCatch m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCDictElem m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCIfaceDecl m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCRecv m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCIvarDecl m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.ObjCMethodProto m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.Sign m where
  handleQuotes x = return x

instance Monad m => HandleQuotes SrcLoc m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.Storage m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.StringLit m where
  handleQuotes x = return x

instance Monad m => HandleQuotes CS.UnOp m where
  handleQuotes x = return x

instance (Monad m, HandleQuotes a m, HandleQuotes b m) => HandleQuotes (a,b) m

{-- Leverage the generic representations to automatically derive
 -- instances of anti-quote handling for the C AST components. -}
instance HandleQuotes CS.AsmIn (GlMono t)
instance HandleQuotes CS.ArraySize (GlMono t)
instance HandleQuotes CS.Attr (GlMono t)
instance HandleQuotes CS.BlockItem (GlMono t)
instance HandleQuotes CS.BlockType (GlMono t)
instance HandleQuotes CS.CEnum (GlMono t)
instance HandleQuotes CS.Designation (GlMono t)
instance HandleQuotes CS.Designator (GlMono t)
instance HandleQuotes CS.ExeConfig (GlMono t)
instance HandleQuotes CS.Field (GlMono t)
instance HandleQuotes CS.FieldGroup (GlMono t)
instance HandleQuotes CS.Func (GlMono t)
instance HandleQuotes CS.Init (GlMono t)
instance HandleQuotes CS.InitGroup (GlMono t)
instance HandleQuotes CS.Initializer (GlMono t)
instance HandleQuotes CS.Param (GlMono t)
instance HandleQuotes CS.Params (GlMono t)
instance HandleQuotes CS.Typedef (GlMono t)
instance HandleQuotes CS.TypeQual (GlMono t)

instance (Monad m, HandleQuotes a m) => HandleQuotes (Maybe a) m

instance HandleQuotes (Either CS.InitGroup (Maybe Exp)) (GlMono t)
{--
 where
  handleQuotes (Left initgrp) = Left <$> handleQuotes initgrp
  handleQuotes (Right (Just e)) = Right $ Just <$> handleQuotes e
  handleQuotes (Right Nothing) = return $ Right Nothing
-}

instance (Monad m, HandleQuotes a m) => HandleQuotes [a] m

--instance (Monad m,HandleQuotes 

{-- Now we define the interesting cases for a C Definition. --}

-- Handling quotations in a C function definition relies on the GlMono
-- monad for reading from the environment and performing the
-- appropriate liftings.
instance HandleQuotes CS.Definition (GlMono t) where
  handleQuotes (CS.FuncDef (CS.Func dcsp (CS.AntiId fn loc2) decl ps body loc1) loc0) = do
    idx <- view (inst._2)
    (fnName, _) <- lift . lift $ genFuncId fn loc2
    let fnNameInC = toCName $ MN.monoName (unsafeNameToCoreFunName fnName) idx
        func = CS.Func dcsp (CS.Id fnNameInC loc2) decl ps body loc1
        def = CS.FuncDef func loc0
    -- Now handle anti-quotes in all other sub-terms.
    defaultHandleQuotes def
  handleQuotes (CS.AntiEsc s l) = return $ CS.EscDef s l
  handleQuotes (CS.DecDef initgrp loc0)
    | CS.InitGroup dcsp attr0 init loc1 <- initgrp
    , CS.DeclSpec store tyqual tysp loc2 <- dcsp
    , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
    , Just (CS.AntiId ty loc4) <- mid = do
        tn' <- (lift . lift) (parseType ty loc4) >>= lift . tcType  >>=
          lift . desugarType >>= lift . expandType >>= monoType >>= lift . lift. lift . genTypeId
        let mid' = Just (CS.Id (toCName tn') loc4)
            tysp' = CS.Tstruct mid' fldgrp attr1 loc3
            dcsp' = CS.DeclSpec store tyqual tysp' loc2
            initgrp' = CS.InitGroup dcsp' attr0 init loc1
        -- Handle quotes from any sub-terms of the definition.
        decdef <- defaultHandleQuotes (CS.DecDef initgrp' loc0)
        -- Update the mapping of C definitions to their generated type names
        lift . lift . lift $ StateT $ \s -> return (decdef , over defns (M.insert decdef tn') s)
  handleQuotes (CS.DecDef initgrp loc0)
    | CS.TypedefGroup dcsp attr0 [tydef] loc1 <- initgrp
    , CS.DeclSpec store tyqual tysp loc2 <- dcsp
    , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
    , Just (CS.AntiId ty loc4) <- mid
    , CS.Typedef (CS.AntiId syn loc6) decl attr2 loc5 <- tydef = do
        tn'  <- (lift . lift) (parseType ty  loc4) >>= lift . tcType >>=
          lift . desugarType >>= lift . expandType >>= monoType >>= lift . lift . lift . genTypeId
        syn' <- (lift . lift) (parseType syn loc6) >>= lift . tcType >>=
          lift . desugarType >>= lift . expandType >>= monoType >>= lift . lift . lift . genTypeId
        when (tn' /= syn') $ throwError $
          "Error: Type synonyms `" ++ syn ++ "' is somewhat different from the type `" ++ ty ++ "'"
        let tydef' = CS.Typedef (CS.Id (toCName syn') loc6) decl attr2 loc5
            mid' = Just (CS.Id (toCName tn') loc4)
            tysp' = CS.Tstruct mid' fldgrp attr1 loc3
            dcsp' = CS.DeclSpec store tyqual tysp' loc2
            initgrp' = CS.TypedefGroup dcsp' attr0 [tydef'] loc1
        decdef <- defaultHandleQuotes (CS.DecDef initgrp' loc0)
        lift . lift . lift $ StateT $ \s -> return (decdef , over defns (M.insert decdef tn') s)
  handleQuotes (CS.DecDef initgrp loc0)
    | CS.TypedefGroup dcsp attr0 [tydef] loc1 <- initgrp
    , CS.Typedef (CS.AntiId syn loc6) decl attr2 loc5 <- tydef = do
        syn' <- (lift . lift) (parseType syn loc6) >>= lift . tcType >>=
          lift . desugarType >>= lift . expandType >>= monoType >>= lift . lift . lift . genTypeId
        let tydef' = CS.Typedef (CS.Id (toCName syn') loc6) decl attr2 loc5
            initgrp' = CS.TypedefGroup dcsp attr0 [tydef'] loc1
        decdef <- defaultHandleQuotes (CS.DecDef initgrp' loc0)
        lift . lift . lift $ StateT $ \s -> return (decdef , over defns (M.insert decdef syn') s)
  handleQuotes x = defaultHandleQuotes x


-- Any monad instance is compatible with quotation handling for C
-- statements since we just need return to be defined.
instance HandleQuotes CS.Stm (GlMono t) where
  handleQuotes (CS.AntiEscStm s l) = return $ CS.EscStm s l
  handleQuotes x = defaultHandleQuotes x

instance HandleQuotes CS.Exp (GlMono t) where
  handleQuotes (CS.FnCall (CS.AntiExp fn loc1) [e] loc0) = do
    e'  <- lift . lift . lift . genFn =<< monoExp =<< lift . expandExp =<< lift . coreTcExp =<<
           lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
    fn' <- lift . lift . lift . genFnCall =<< return . CC.exprType =<< monoExp =<< lift . expandExp =<< lift . coreTcExp =<<
           lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
    defaultHandleQuotes $ CS.FnCall fn' [e',e] loc0
  handleQuotes (CS.FnCall (CS.Cast ty e1 loc1) [e2] loc0)
    | CS.Type dcsp decl loc2 <- ty
    , CS.AntiDeclSpec s loc3 <- dcsp = do
        disp <- lift . lift . lift . genFnCall =<< monoType =<< lift . expandType =<< lift . desugarType =<<
                lift . tcType =<< (lift . lift) (parseType s loc3)
        defaultHandleQuotes (CS.FnCall disp [e1,e2] loc0)
  handleQuotes (CS.AntiExp s loc) = (lift . lift) (parseExp s loc) >>=
    lift . flip tcExp Nothing >>= lift . desugarExp >>= lift . coreTcExp >>= lift . expandExp >>=
    monoExp >>= lift . lift . lift . genExp
  handleQuotes e = defaultHandleQuotes e

{-- Handle anti-quotes within C type declarations. --}

instance HandleQuotes CS.DeclSpec (GlMono t) where
  handleQuotes (CS.AntiTypeDeclSpec strg qual s l) = do
    CS.DeclSpec [] [] tysp loc <- (fst . CG.splitCType) <$> (lift . lift . lift . genType =<<
      monoType =<< lift . expandType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
    defaultHandleQuotes (CS.DeclSpec strg qual tysp loc)
  handleQuotes x = defaultHandleQuotes x

instance HandleQuotes CS.Decl (GlMono t) where
  handleQuotes (CS.AntiTypeDecl s l) = (snd . CG.splitCType) <$>
    (lift . lift . lift . genType =<< monoType =<< lift . expandType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
  handleQuotes x = defaultHandleQuotes x

instance HandleQuotes CS.Type (GlMono t) where
  handleQuotes (CS.AntiType s l) = CG.cType <$>
    (lift . lift . lift . genType =<< monoType =<< lift . expandType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
  handleQuotes x = defaultHandleQuotes x

instance HandleQuotes CS.TypeSpec (GlMono t) where
  handleQuotes (CS.Tstruct mid fldgrp attr loc0)
    | Just (CS.AntiId ty loc1) <- mid = do
        tn' <- (lift . lift) (parseType ty loc1) >>= lift . tcType >>=
               lift . desugarType >>= lift . expandType >>= monoType >>= lift . lift . lift . genTypeId
        defaultHandleQuotes (CS.Tstruct (Just $ CS.Id (toCName tn') loc1) fldgrp attr loc0)
  handleQuotes x = defaultHandleQuotes x

-- Monad transformers

-- NOTE: The 4th argument @offset'@ is used to produce more accurate source positions.
-- It also helps work around the @avoidInitial@ when parsing things. / zilinc
parseAnti :: String -> PP.Parsec String PS.S a -> SrcLoc -> Int -> GlFile a
parseAnti s parsec loc offset' = do
  filename <- view file
  let pos = case loc of
              SrcLoc (Loc (Pos _ line col offset) _) -> newPos filename line (col + offset + offset')
              SrcLoc NoLoc -> newPos filename 0 0
  case PP.runParser (PP.setPosition pos >> parsec) (PS.ParserState False) filename s of
    Left err -> throwError $ "Error: Cannot parse antiquote: \n" ++ show err
    Right t  -> return t

tcAnti :: (a -> TC.TcM b) -> a -> GlDefn t b
tcAnti f a = lift . lift $
  StateT $ \s -> let state = TC.TcState { TC._knownFuns        = view (tcState.tfuncs) s
                                        , TC._knownTypes       = view (tcState.ttypes) s
                                        , TC._knownConsts      = view (tcState.consts) s
                                        , TC._knownDataLayouts = view (tcState.dldefs) s
                                        }
                     turn :: s -> (Maybe b, TC.TcLogState) -> Either String (b,s)
                     turn s (Just x, TC.TcLogState l _) = Right (x,s)  -- FIXME: ignore warnings atm / zilinc
                     turn _ (_, TC.TcLogState l _) = Left $ "Error: Typecheck antiquote failed:\n" ++
                                         show (vsep $ L.map (prettyTWE __cogent_ftc_ctx_len) l)
                                         -- FIXME: may need a pp modifier `plain' / zilinc
                  in ExceptT $ fmap (turn s) (flip evalStateT state .
                                              flip runStateT mempty .
                                              runMaybeT $ f a)

desugarAnti :: (a -> DS.DS t 'Zero 'Zero b) -> a -> GlDefn t b
desugarAnti m a = view kenv >>= \(fmap fst -> ts) -> lift . lift $
  StateT $ \s -> let tdefs = view (dsState.typedefs ) s
                     cdefs = view (dsState.constdefs) s
                  in return (fst (flip3 evalRWS (DS.DsState ts Nil Nil 0 0 [] []) (tdefs, cdefs) $ DS.runDS $ m a), s)  -- FIXME: pragmas / zilinc

coreTcAnti :: (a -> IN.TC t 'Zero VarName b) -> a -> GlDefn t b
coreTcAnti m a = view kenv >>= \(fmap snd -> ts) -> lift . lift $
  StateT $ \s -> let reader = (ts, view (coreTcState.funtypes) s, view (coreTcState.typesyns) s)
                  in case flip evalState Nil $ flip runReaderT reader $ runExceptT $ IN.unTC $ m a of
                       Left  e -> __impossible "coreTcAnti"
                       Right x -> return (x, s)

monoAnti :: (a -> MN.Mono VarName b) -> a -> GlMono t b
monoAnti m a = view (inst._1) >>= \is -> lift . lift . lift $
  StateT $ \s -> let fmono = view (mnState.funMono ) s
                     tmono = view (mnState.typeMono) s
                  in return (fst (flip3 evalRWS (fmono,tmono) is $ MN.runMono $ m a), s)

genAnti :: (a -> CG.Gen 'Zero b) -> a -> Gl b
genAnti m a =
  StateT $ \s -> let reader = Nil
                     state  = CG.GenState { CG._cTypeDefs    = view (cgState.cTypeDefs   ) s
                                          , CG._cTypeDefMap  = view (cgState.cTypeDefMap ) s
                                          , CG._typeSynonyms = view (cgState.typeSynonyms) s
                                          , CG._typeCorres   = view (cgState.typeCorres  ) s
                                          , CG._typeCorres'  = view (cgState.typeCorres' ) s
                                          , CG._absTypes     = view (cgState.absTypes    ) s
                                          , CG._custTypeGen  = view (cgState.custTypeGen ) s
                                          , CG._funClasses   = view (cgState.funClasses  ) s
                                          , CG._localOracle  = view (cgState.localOracle ) s   -- FIXME
                                          , CG._globalOracle = view (cgState.globalOracle) s
                                          , CG._recParCIds   = M.empty
                                          , CG._recParRecordIds = M.empty
                                          , CG._varPool      = M.empty
                                          , CG._ffiFuncs     = M.empty
                                          , CG._boxedRecordSetters     = M.empty
                                          , CG._boxedRecordGetters     = M.empty
                                          , CG._boxedArraySetters      = M.empty
                                          , CG._boxedArrayGetters      = M.empty
                                          , CG._boxedArrayElemSetters  = M.empty
                                          , CG._boxedArrayElemGetters  = M.empty
                                          }
                  in return (fst $ evalRWS (CG.runGen $ m a) reader state, s)

-- Types

parseType :: String -> SrcLoc -> GlFile SF.LocType
parseType s loc = parseAnti s PS.monotype loc 4


tcType :: SF.LocType -> GlDefn t TC.DepType
tcType t = do
  let ?loc = SF.posOfT t
  tvs <- L.map fst <$> (Vec.cvtToList <$> view kenv)
  flip tcAnti t $ \t -> do TC.errCtx %= (TC.AntiquotedType t :)
                           base <- lift . lift $ use TC.knownConsts
                           let ctx = Ctx.addScope (fmap (\(t,e,p) -> (t, p, Seq.singleton p)) base) Ctx.empty
                           ((ct,t'), flx, os) <- TC.runCG ctx tvs [] $ TC.validateType $ SF.stripLocT t
                           (gs, subst) <- TC.runSolver (TC.solve (L.zip tvs $ repeat k2) [] $ ct) flx 
                           TC.exitOnErr $ TC.toErrors os gs
                           let t'' = TC.apply subst t'
                           TC.postT t''

desugarType :: TC.DepType -> GlDefn t (CC.Type t VarName)
desugarType = desugarAnti DS.desugarType

expandType :: CC.Type t VarName -> GlDefn t (CC.Type t VarName)
expandType = coreTcAnti IN.unfoldSynsDeepM

monoType :: CC.Type t VarName -> GlMono t (CC.Type 'Zero VarName)
monoType = monoAnti MN.monoType

genType :: CC.Type 'Zero VarName -> Gl CG.CType
genType = genAnti CG.genType

-- Function calls

parseFnCall :: String -> SrcLoc -> GlFile SF.LocExpr
parseFnCall s loc = parseAnti s PS.basicExpr' loc 4

tcFnCall :: SF.LocExpr -> GlDefn t TC.TypedExpr
tcFnCall e = do
  f <- case e of
         SF.LocExpr _ (SF.TLApp f ts _ _) -> return f  -- TODO: make use of Inline to perform glue code inlining / zilinc
         SF.LocExpr _ (SF.Var f) -> return f
         otherwise -> throwError $ "Error: Not a function in $exp antiquote"
  f `seq` tcExp e Nothing

genFn :: CC.TypedExpr 'Zero 'Zero VarName VarName -> Gl CS.Exp
genFn = genAnti $ \case
  CC.TE t (CC.Fun fn _ _ _) -> return (CS.Var (CS.Id (CG.funEnum (unCoreFunName fn)) noLoc) noLoc)
  _ -> __impossible "genFn"

genFnCall :: CC.Type 'Zero VarName -> Gl CS.Exp
genFnCall = genAnti $ \t -> do
    enumt <- CG.typeCId t
    return (CS.Var (CS.Id (CG.funDispatch $ toCName enumt) noLoc) noLoc)

-- Expressions

parseExp :: String -> SrcLoc -> GlFile SF.LocExpr
parseExp s loc = parseAnti s (PS.expr 1) loc 4

tcExp :: SF.LocExpr -> Maybe TC.TCType -> GlDefn t TC.TypedExpr
tcExp e mt = do
  base <- lift . lift $ use (tcState.consts)
  let ctx = Ctx.addScope (fmap (\(t,_,p) -> (t, p, Seq.singleton p)) base) Ctx.empty
  vs <- Vec.cvtToList <$> view kenv
  flip tcAnti e $ \e ->
    do let ?loc = SF.posOfE e
       TC.errCtx %= (TC.AntiquotedExpr e :)
       ((c,e'),flx,os) <- TC.runCG ctx (L.map fst vs) []
                            (TC.cg e =<< maybe (TC.freshTVar (TC.TypeOfExpr (SF.stripLocE e) [] ?loc)) return mt)
       (cs, subst) <- TC.runSolver (TC.solve vs [] c) flx
       TC.exitOnErr $ TC.toErrors os cs
       -- TC.exitOnErr $ mapM_ TC.logTc logs
       TC.postE $ TC.applyE subst e'

desugarExp :: TC.TypedExpr -> GlDefn t (CC.UntypedExpr t 'Zero VarName VarName)
desugarExp = desugarAnti DS.desugarExpr

coreTcExp :: CC.UntypedExpr t 'Zero VarName VarName -> GlDefn t (CC.TypedExpr t 'Zero VarName VarName)
coreTcExp = coreTcAnti IN.infer

expandExp :: CC.TypedExpr t 'Zero VarName VarName -> GlDefn t (CC.TypedExpr t 'Zero VarName VarName)
expandExp = coreTcAnti IN.unfoldSynsDeepInTEM

monoExp :: CC.TypedExpr t 'Zero VarName VarName -> GlMono t (CC.TypedExpr 'Zero 'Zero VarName VarName)
monoExp = monoAnti MN.monoExpr

genExp :: CC.TypedExpr 'Zero 'Zero VarName VarName -> Gl CS.Exp
genExp = genAnti $ \e -> do (v,vdecl,vstm,_) <- CG.genExpr Nothing e
                            let bis' = L.map CG.cBlockItem (vdecl ++ vstm)
                                v'   = CG.cExpr v
                            return $ CS.StmExpr (bis' ++ [CS.BlockStm (CS.Exp (Just v') noLoc)]) noLoc

-- Function Id

genFuncId :: String -> SrcLoc -> GlFile (FunName, [Maybe SF.LocType])
genFuncId fn loc = do
  surfaceFn <- parseFnCall fn loc
  case surfaceFn of
    SF.LocExpr _ (SF.TLApp f ts _ _) -> return (f, ts)
    SF.LocExpr _ (SF.Var f)          -> return (f, [])
    _ -> throwError $ "Error: `" ++ fn ++
                      "' is not a valid function Id (with optional type arguments) in a $id antiquote"

-- Type Id

parseTypeId :: String -> SrcLoc -> GlFile (TypeName, [TyVarName])
parseTypeId s loc = parseAnti s ((,) <$> PS.typeConName <*> PP.many PS.variableName) loc 4

genTypeId :: CC.Type 'Zero VarName -> Gl CG.CId
genTypeId = genAnti CG.typeCId

-- Definition

traversals :: [(MN.Instance VarName, Maybe Int)] -> CS.Definition -> GlDefn t [CS.Definition]
-- No type arguments, either monomorphic Cogent function, or not defined in Cogent
-- If any instances of a polymorphic function are not used anywhere, then no mono function will be generated
traversals insts d = forM insts $ \inst -> flip runReaderT (MonoState inst) $ handleQuotes d

traverseOneFunc :: String -> CS.Definition -> SrcLoc -> GlFile [CS.Definition]
traverseOneFunc fn d loc = do
  -- First we need to __parse__ the function name, get the function name and the optional explicit type arguments.
  -- If the function has no explicit type arguments, then we treat it as a poly-definition;
  -- if it's applied to type arguments, then we consider it defined only for the applied types.
  -- At this point, we can't further compile this function id (treated as a function call FnCall as it
  -- can take type arguments), because any process beyond parsing requires us knowing what function it
  -- is (in a monad at least 'GlDefn'), but this is indeed what we are trying to work out. The loop-breaker
  -- is to manually extract the function name after parsing.
  (fnName, targs) <- genFuncId fn loc
  -- After getting the function name, we can construct a 'GlDefn' monad environment.
  lift $ cgState.localOracle .= 0
  monos <- lift $ use $ mnState.funMono  -- acquire all valid instantiations used in this unit.
  defs  <- lift $ use tcDefs
  case M.lookup fnName monos of
    -- This 'mono' should have entries for __all__ monomorphic (be it original monomorphic or monomorphised)
    -- functions that appear in this unit. If @Nothing@, then it means this function is not defined in Cogent
    -- or not used at all. The reason why we
    -- don't throw an exception is, IIRC, if the library implementation (or some large system) is
    -- arranged in such a way that a single @.ac@ file contains definitions for many @.cogent@
    -- files or definitions of unused Cogent functions. / zilinc (28/11/18)
    Nothing -> return []
    Just mp ->
      case L.find (SF.absFnDeclId fnName) defs of  -- function declared/defined in Cogent
        Nothing -> throwError $ "Error: Function `" ++ fn ++
                                "' is not an abstract Cogent function and thus cannot be antiquoted"
        Just tl -> do
          let ts = tyVars tl
          -- Here we need to match the type argument given in the @.ac@ definition and the ones in the
          -- original Cogent definition, in order to decide which instantiations should be generated.
          case Vec.fromList ts of
            ExI (Flip ts') -> flip runReaderT (DefnState ts' [TC.InAntiquotedCDefn fn]) $ do
              -- NOTE: if there are type variables in the type application, the type vars must be in-scope,
              -- i.e. they must be the same ones as in the Cogent definition.

              -- NOTE: We now try to fill in missing type arguments, otherwise the typechecker might have
              -- difficulty in inferring the types. This is partially for backward compatibility reasons:
              -- For implicitly applied type arguments, if the typechecker cannot infer when you write
              -- the same in a Cogent program, it won't infer in a @.ac@ file either. Unlike before,
              -- where we never typecheck them.

              -- If the type arguments are omitted, we add them back
              let targs' = L.zipWith
                             (\tv mta -> Just $ fromMaybe (SF.dummyLocT . SF.RT $ SF.TVar tv False False) mta)
                             (L.map fst ts)
                             (targs ++ repeat Nothing)

              -- Then we can continue the normal compilation process.
              let SrcLoc (Loc (Pos filepath line col _) _) = loc
                  pos = newPos filepath line col
              CC.TE _ (CC.Fun _ coreTargs _ _) <- (flip tcExp (Nothing) >=>
                                                   desugarExp >=>
                                                   coreTcExp >=> expandExp) $
                                                  (SF.LocExpr pos (SF.TLApp fnName targs' [] SF.NoInline))
              -- Matching @coreTargs@ with @ts@. More specifically: match them in @mp@, and trim
              -- those in @mp@ that don't match up @coreTargs@.
              -- E.g. if @ts = [U8,a]@ and in @mp@ we find @[U8,U32]@ and @[U8,Bool]@, we instantiate this
              --      function definition to these two types.
              --      if @ts = [U8,a]@ and @mp = ([Bool,U8],[U32,U8])@ then there's nothing we generate.
              let match :: (Eq b) => [CC.Type t b] -> [CC.Type 'Zero b] -> Bool
                  match [] [] = True
                  match xs ys | L.null xs || L.null ys
                    = __impossible "match (in traverseOneFunc): number of type arguments don't match"
                  -- We for now ignore 'TVarBang's, and treat them as not matching anything.
                  match (x:xs) (y:ys) = (unsafeCoerce x == y || CC.isTVar x) && match xs ys
              let instantiations = if L.null ts then [(([], []), Nothing)]
                                   else L.filter (\((ms,_),_) -> match coreTargs ms)
                                        $ L.map (second Just) (M.toList mp)
              traversals instantiations d


traverseOneType :: String -> SrcLoc -> CS.Definition -> GlFile [CS.Definition]
traverseOneType ty l d = do   -- type defined in Cogent
  monos <- lift $ use $ mnState.typeMono
  defs  <- lift $ use tcDefs
  (tn,ts) <- parseTypeId ty l
  case M.lookup tn monos of  -- NOTE: It has to be an abstract type / zilinc
    Nothing -> return [] -- throwError $ "Error: Type `" ++ tn ++ "' is not defined / used in Cogent and thus cannot be antiquoted"
    Just s  -> do case L.find (SF.absTyDeclId tn) defs of
                    Nothing -> throwError $ "Error: Type `" ++ tn ++ "' is not an abstract Cogent type and thus cannot be antiquoted"
                    Just tl -> do let ts' = tyVars tl
                                  when (ts /= L.map fst ts') $
                                    throwError $ "Error: Type parameters in `" ++ ty ++ "' are different from those in Cogent"
                                  when (L.null ts') $
                                    throwError $ "Error: Non-parametric abstract Cogent type `" ++ tn ++ "' should not use antiquotation"
                                  case Vec.fromList ts' of
                                    ExI (Flip ts'') -> flip runReaderT (DefnState ts'' [TC.InAntiquotedCDefn ty]) $ do
                                      s' <- nubByName $ S.toList s
                                      traversals (L.zip s' (repeat Nothing)) d
 where
   nubByName :: [MN.Instance VarName] -> GlDefn t [MN.Instance VarName]
   nubByName ins = lift . lift $
     nubByM (\i1 i2 -> do tn1 <- mapM (genAnti CG.genType) (fst i1)
                          tn2 <- mapM (genAnti CG.genType) (fst i2)
                          return (tn1 == tn2)) ins

traverseOne :: CS.Definition -> GlFile [CS.Definition]
traverseOne d@(CS.FuncDef (CS.Func _ (CS.AntiId fn loc) _ _ _ _) _) = traverseOneFunc fn d loc
traverseOne d@(CS.DecDef initgrp _)
  | CS.InitGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
  | CS.TypedefGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
  | CS.TypedefGroup _ _ [tydef] _ <- initgrp
  , CS.Typedef (CS.AntiId ty l) _ _ _ <- tydef = traverseOneType ty l d
traverseOne d =
  flip runReaderT (DefnState Nil [TC.InAntiquotedCDefn $ show d]) $ traversals [(([], []), Nothing)] d  -- anything not defined in Cogent

-- | This function returns a list of pairs, of each the second component is the type name if
--   the first component is a type definition. We use the type name to generate a dedicated @.h@
--   file for that type. If the first is a function definition, then the second is always 'Nothing'.
traverseAll :: [CS.Definition] -> GlFile [CS.Definition]
traverseAll ds = concat <$> mapM traverseOne ds


-- Interface

data GlueMode = TypeMode | FuncMode deriving (Eq, Show)

glue :: GlState -> [TypeName] -> GlueMode -> [FilePath] -> ExceptT String IO [(FilePath, [CS.Definition])]
glue s typnames mode filenames = liftA (M.toList . M.fromListWith (flip (++)) . concat) .
  forM filenames $ \filename -> do
    ds <- parseFile defaultExts typnames filename
    (ds', s') <- flip runStateT s . flip runReaderT (FileState filename) $ {-# SCC traverseAll_ds #-} traverseAll ds
    case mode of
      TypeMode -> forM ds' $ \d -> case M.lookup d (_defns s') of
        Nothing -> throwE $ "Error: Cannot define functions in type mode (" ++ show d ++ ")"
        Just f  -> return (__cogent_abs_type_dir ++ "/abstract/" ++ f <.> __cogent_ext_of_h, [d])
      FuncMode -> let ext = if | takeExtension filename == __cogent_ext_of_ah -> __cogent_ext_of_h
                               | takeExtension filename == __cogent_ext_of_ac -> __cogent_ext_of_c
                               | otherwise -> __cogent_ext_of_c
                  in return [ (replaceExtension ((replaceBaseName filename (takeBaseName filename ++ __cogent_suffix_of_inferred))) ext
                            , ds') ]

mkGlState :: [SF.TopLevel TC.DepType TC.TypedPatn TC.TypedExpr]
          -> TC.TcState
          -> Last (DS.Typedefs, DS.Constants, [CC.CoreConst CC.UntypedExpr])
          -> M.Map FunName (CC.FunctionType VarName)
          -> [CC.Definition CC.TypedExpr VarName VarName]
          -> (MN.FunMono VarName, MN.InstMono VarName)
          -> CG.GenState
          -> GlState
mkGlState tced tcState (Last (Just (typedefs, constdefs, _))) ftypes typesyndefs (funMono, typeMono) genState =
  GlState { _tcDefs  = tced
          , _tcState = TcState { _tfuncs = view TC.knownFuns        tcState
                               , _ttypes = view TC.knownTypes       tcState
                               , _consts = view TC.knownConsts      tcState
                               , _dldefs = view TC.knownDataLayouts tcState
                               }
          , _dsState = DsState typedefs constdefs
          , _coreTcState = CoreTcState ftypes typesyndefs
          , _mnState = MnState funMono typeMono
          , _cgState = CgState { _cTypeDefs    = view CG.cTypeDefs    genState
                               , _cTypeDefMap  = view CG.cTypeDefMap  genState
                               , _typeSynonyms = view CG.typeSynonyms genState
                               , _typeCorres   = view CG.typeCorres   genState
                               , _typeCorres'  = view CG.typeCorres'  genState
                               , _absTypes     = view CG.absTypes     genState
                               , _custTypeGen  = view CG.custTypeGen  genState
                               , _funClasses   = view CG.funClasses   genState
                               , _localOracle  = view CG.localOracle  genState
                               , _globalOracle = view CG.globalOracle genState
                               }
          , _defns = M.empty
          }
mkGlState _ _ _ _ _ _ _ = __impossible "mkGlState"


-- Misc.

tyVars :: SF.TopLevel TC.DepType pv e -> [(TyVarName, Kind)]
tyVars (SF.FunDef _ (SF.PT ts _ _) _) = ts
tyVars (SF.AbsDec _ (SF.PT ts _ _)  ) = ts
tyVars (SF.TypeDec    _ ts _) = L.zip ts $ repeat k2
tyVars (SF.AbsTypeDec _ ts _) = L.zip ts $ repeat k2
tyVars _ = __impossible "tyVars"


-- /////////////////////////////////////////////////////////////////////////////
--
-- A simpler compilation process for the @--entry-funcs@ file.

readEntryFuncs :: [SF.TopLevel TC.DepType TC.TypedPatn TC.TypedExpr]
               -> TC.TcState
               -> Last (DS.Typedefs, DS.Constants, [CC.CoreConst CC.UntypedExpr])
               -> M.Map FunName (CC.FunctionType VarName)
               -> [String]
               -> IO (Maybe (MN.FunMono VarName))
readEntryFuncs tced tcState dsState ftypes lns
  = foldM run (Just M.empty) lns
  where
    run md ln = do 
      f <- readEntryFunc ln
      return $ do
        m <- md
        (fn, inst) <- f
        return $ updateFunMono m fn inst

    updateFunMono m fn ([],[]) = M.insertWith (\_ entry -> entry) fn M.empty m
    updateFunMono m fn inst    = M.insertWith (\_ entry -> M.insertWith (flip const) inst (M.size entry) entry) fn (M.singleton inst 0) m

    -- Each string is a line in the @--entry-funcs@ file.
    readEntryFunc :: String -> IO (Maybe (FunName, MN.Instance VarName))
    readEntryFunc ln = do
      er <- runExceptT $ flip evalStateT (mkGlState [] tcState dsState mempty [] (mempty, mempty) undefined) $
              flip runReaderT (FileState "--entry-funcs file") $ do
                (fnName, targs) <- genFuncId ln noLoc
                let nargs = SF.numTypeVars $
                      case find (isFnName fnName) tced of
                          Just f  -> f
                          Nothing -> __impossible "Could not find function in top level declarations"
                if nargs /= L.length targs then do
                  throwError ("Number of type arguments for function " ++
                              fnName ++ " (" ++ show nargs ++
                              ") does not match amount specified in --entry-funcs file (" ++
                              show (L.length targs) ++ ").\n" ++
                              optMsg (nargs > L.length targs))
                else do
                  inst <- forM targs $ \mt ->
                            case mt of
                              Nothing -> throwError "Use of wildcard disallowed in --entry-funcs file"
                              Just t  -> flip runReaderT (DefnState Vec.Nil []) $
                                         flip runReaderT (MonoState (([], []), Nothing))
                                                         (lift . tcType >=> lift . desugarType >=> lift . expandType >=> monoType $ t)
                  return (fnName, inst)
      case er of Left s  -> hPutStrLn stderr ("\nError: " ++ s) >> return Nothing
                 Right r -> return $ Just $ (fst r,) (snd r, [])

    isFnName n (SF.FunDef fn _ _) = fn == n
    isFnName n (SF.AbsDec fn _) = fn == n
    isFnName _ _ = False

    optMsg :: Bool -> String
    optMsg b = if b then
                 "Functions in a --entry-funcs file cannot be partially applied."
               else
                 "Did you apply too many type arguments in an --entry-funcs file?"
