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
{-# LANGUAGE DeriveFunctor #-}
{- LANGUAGE FlexibleContexts -}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{- LANGUAGE LiberalTypeSynonyms -}
{- LANGUAGE MultiParamTypeClasses -}
{-# LANGUAGE MultiWayIf #-}
{- LANGUAGE OverlappingInstances -}
{-# LANGUAGE PackageImports #-}
{- LANGUAGE RankNTypes -}
{- LANGUAGE ScopedTypeVariables -}
{- LANGUAGE StandaloneDeriving -}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wwarn #-}

module Cogent.Glue where

import qualified Cogent.CodeGen as CG
import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler
import qualified Cogent.Desugar   as DS
import qualified Cogent.DList     as DList
import qualified Cogent.Mono      as MN
import qualified Cogent.Parser    as PS
-- import Cogent.PrettyPrint
import qualified Cogent.Sugarfree as SF
import qualified Cogent.Surface   as SR
import qualified Cogent.TypeCheck.Base as TC
import Cogent.Util
import Cogent.Vec as Vec hiding (repeat)

import Control.Applicative
import Control.Arrow (Arrow(..), second, (&&&))
import Control.Lens hiding ((<.>))
import Control.Monad.Except hiding (sequence, mapM_, mapM)
import Control.Monad.Reader
import Control.Monad.RWS.Strict
import Control.Monad.State
import Control.Monad.Trans.Either
--import Control.Monad.Trans.Except
--import Control.Monad.Writer
import qualified Data.ByteString.Char8 as B
import Data.Data
import Data.Function.Flippers
import Data.Generics
import Data.Loc
import Data.List as L
import Data.Map as M
import Data.Semigroup.Applicative
import Data.Set as S
import "language-c" Language.C               as LC
import "language-c-quote" Language.C.Parser  as CP hiding (parseExp, parseType)
-- import Language.C.Parser.Tokens as CT
import "language-c-quote" Language.C.Syntax  as CS
import System.FilePath (replaceBaseName, replaceExtension, takeBaseName, takeExtension, (<.>))
import Text.Parsec.Pos (newPos, SourcePos)
import Text.Parsec.Prim as PP hiding (State)
import Text.PrettyPrint.ANSI.Leijen (vsep)

-- import Debug.Trace

-- Parsing

parseFile :: [Extensions] -> [String] -> FilePath -> EitherT String IO [CS.Definition]
parseFile exts deftypnames filename = do
#if MIN_VERSION_language_c_quote(0,11,1)
  let start = Just $ startPos filename
#else
  let start = startPos filename
#endif
  s <- lift $ B.readFile filename
  typnames <- case __cogent_ext_types of Nothing -> lift (return deftypnames); Just f -> lift $ getTypnames f
  case CP.evalP (__fixme CP.parseUnit) (CP.emptyPState exts typnames s start) of -- FIXME: check for other antiquotes
    Left err -> hoistEither . Left  $ "Error: Failed to parse C: " ++ show err
    Right ds -> hoistEither . Right $ ds

defaultExts :: [Extensions]
defaultExts = [Antiquotation, C99, Gcc]

defaultTypnames :: [String]
defaultTypnames = []

getTypnames :: FilePath -> IO [String]
getTypnames = liftA lines . readFile


-- Another parser

parseFile' :: FilePath -> EitherT String IO CTranslUnit
parseFile' filename = do
  instream <- lift $ readInputStream filename
  let pos = initPos filename
  case parseC instream pos of
    Left err -> hoistEither . Left $ "Error: Failed to parse C: " ++ show err
    Right u  -> hoistEither . Right $ u


-- Desugaring, Monomorphising, and CG

data TcState = TcState { _tfuncs :: [(VarName, SR.Polytype SR.RawType)]
                       , _ttypes :: [(TypeName, ([VarName], Maybe SR.RawType))]
                       , _consts :: [(VarName, Either SourcePos SR.RawType)]
                       }

data DsState = DsState { _typedefs  :: DS.Typedefs
                       , _constdefs :: DS.Constants
                       }

data IcState = IcState { _funtypes :: Map FunName SF.FunctionType }

data MnState = MnState { _funMono  :: MN.FunMono
                       , _typeMono :: MN.TypeMono
                       }

data CgState = CgState { _cTypeDefs    :: [(CG.StrlType, CG.CId)]
                       , _cTypeDefMap  :: M.Map CG.StrlType CG.CId
                       , _typeSynonyms :: M.Map TypeName CG.CType
                       , _typeCorres   :: DList.DList (CG.CId, SF.Type 'Zero)
                       , _absTypes     :: M.Map TypeName (S.Set [CG.CId])
                       , _funClasses   :: CG.FunClass
                       , _localOracle  :: Integer  -- FIXME: should be moved to DefnState
                       , _globalOracle :: Integer
                       }

data GlState = GlState { _tcDefs   :: [SR.TopLevel SR.RawType TC.TypedName TC.TypedExpr]
                       , _tcState  :: TcState
                       , _dsState  :: DsState
                       , _icState  :: IcState
                       , _mnState  :: MnState
                       , _cgState  :: CgState
                       }

data FileState = FileState { _file :: FilePath }

data DefnState t = DefnState { _kenv :: Vec t (TyVarName, Kind) }

data MonoState = MonoState { _inst :: (MN.Instance, Maybe Int) }  -- Either ([], Nothing), or (_:_, Just _)

makeLenses ''TcState
makeLenses ''DsState
makeLenses ''IcState
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
type GlErr    = Except  String


-- Monad transformers

parseAnti :: String -> PP.Parsec String () a -> SrcLoc -> Int -> GlFile a
parseAnti s parsec loc offset' = do
  let SrcLoc (Loc (Pos _ line col offset) _) = loc
  filename <- view file
  case PP.parse (PP.setPosition (newPos filename line (col + offset + offset')) >> parsec) filename s of
    Left err -> throwError $ "Error: Cannot parse antiquote: \n" ++ show err
    Right t  -> return t

tcAnti :: (a -> TC.TC b) -> a -> GlDefn t b
tcAnti m a = undefined
{- view kenv >>= \(cvtToList -> ts) -> lift . lift $
  StateT $ \s -> let state = TC.TCState { TC._knownFuns    = view (tcState.tfuncs) s
                                        , TC._context      = view (tcState.consts) s
                                        , TC._errorContext = []
                                        , TC._kindContext  = ts
                                        , TC._knownTypes   = view (tcState.ttypes) s
                                        }
                  in case (flip evalState state . runWriterT . runExceptT . TC.runTC $ m a) of
                       (Right x, []) -> return (x, s)
                       (_, err) -> throwE $ "Error: Typecheck antiquote failed:\n" ++
                                            show (vsep $ L.map (prettyTWE __cogent_ftc_ctx_len) err)
                                            -- FIXME: may need a pp modifier `plain' / zilinc
-}

desugarAnti :: (a -> DS.DS t 'Zero b) -> a -> GlDefn t b
desugarAnti m a = view kenv >>= \(fmap fst -> ts) -> lift . lift $
  StateT $ \s -> let tdefs = view (dsState.typedefs ) s
                     cdefs = view (dsState.constdefs) s
                  in return (fst (flip3 evalRWS (ts, Nil, 0) (tdefs, cdefs, []) $ DS.runDS $ m a), s)  -- FIXME: pragmas / zilinc

icAnti :: (a -> SF.TC t 'Zero b) -> a -> GlDefn t b
icAnti m a = view kenv >>= \(fmap snd -> ts) -> lift . lift $
  StateT $ \s -> let reader = (ts, view (icState.funtypes) s)
                  in case flip evalState Nil $ flip runReaderT reader $ runExceptT $ SF.unTC $ m a of
                       Left  e -> __impossible "icAnti"
                       Right x -> return (x, s)

monoAnti :: (a -> MN.Mono b) -> a -> GlMono t b
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
                                          , CG._absTypes     = view (cgState.absTypes    ) s
                                          , CG._funClasses   = view (cgState.funClasses  ) s
                                          , CG._localOracle  = view (cgState.localOracle ) s   -- FIXME
                                          , CG._globalOracle = view (cgState.globalOracle) s
                                          , CG._varPool      = M.empty
                                          }
                  in return (fst $ evalRWS (CG.runGen $ m a) reader state, s)

traverseAnti :: (Typeable a, Data b, Monad m) => (a -> m a) -> b -> m b
traverseAnti m = everywhereM $ mkM $ m


-- Types

parseType :: String -> SrcLoc -> GlFile SR.LocType
parseType s loc = parseAnti s PS.monotype loc 4


tcType :: SR.LocType -> GlDefn t SR.RawType
tcType t = undefined {- tcAnti (TC.inEContext (TC.AntiquotedType t) . TC.validateType) t -}

desugarType :: SR.RawType -> GlDefn t (SF.Type t)
desugarType = desugarAnti DS.desugarType

monoType :: SF.Type t -> GlMono t (SF.Type 'Zero)
monoType = monoAnti MN.monoType

genType :: SF.Type 'Zero -> Gl CG.CType
genType = genAnti CG.genType

transDeclSpec :: CS.DeclSpec -> GlMono t CS.DeclSpec
transDeclSpec (CS.AntiTypeDeclSpec strg qual s l) = do
  CS.DeclSpec [] [] tysp loc <- (fst . CG.splitCType) <$> (lift . lift . lift . genType =<<
    monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
  return $ CS.DeclSpec strg qual tysp loc
transDeclSpec x = return x

transDecl :: CS.Decl -> GlMono t CS.Decl
transDecl (CS.AntiTypeDecl s l) =
  (snd . CG.splitCType) <$> (lift . lift . lift . genType =<< monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
transDecl x = return x

transType :: CS.Type -> GlMono t CS.Type
transType (CS.AntiType s l) =
  CG.cType <$> (lift . lift . lift . genType =<< monoType =<< lift . desugarType =<< lift . tcType =<< (lift . lift) (parseType s l))
transType x = return x

traverseDeclSpec = traverseAnti transDeclSpec
traverseDecl     = traverseAnti transDecl
traverseType     = traverseAnti transType

-- Function calls

parseFnCall :: String -> SrcLoc -> GlFile SR.LocExpr
parseFnCall s loc = parseAnti s PS.basicExpr' loc 4

tcFnCall :: SR.LocExpr -> GlDefn t TC.TypedExpr
tcFnCall e = undefined {-  do
  f <- case e of
         SR.LocExpr _ (SR.TypeApp f ts _) -> return f  -- FIXME: make use of Inline to perform glue code inlining / zilinc
         SR.LocExpr _ (SR.Var f) -> return f
         otherwise -> throwError $ "Error: Not a function in $exp antiquote"
  tcAnti (TC.inEContext (TC.AntiquotedExpr e) . TC.infer) e
-}

genFn :: SF.TypedExpr 'Zero 'Zero VarName -> Gl CS.Exp
genFn = genAnti $ \case
  SF.TE t (SF.Fun fn _ _) -> return (CS.Var (CS.Id (CG.funEnum fn) noLoc) noLoc)
  _ -> __impossible "genFn"

genFnCall :: SF.Type 'Zero -> Gl CS.Exp
genFnCall = genAnti $ \t -> do
    enumt <- CG.typeCId t
    return (CS.Var (CS.Id (CG.funDispatch $ toCName enumt) noLoc) noLoc)

transFnCall :: CS.Exp -> GlMono t CS.Exp
transFnCall (CS.FnCall (CS.AntiExp fn loc1) [e] loc0) = do
  e'  <- lift . lift . lift . genFn =<< monoExp =<< lift . icExp =<<
         lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
  fn' <- lift . lift . lift . genFnCall =<< return . SF.exprType =<< monoExp =<< lift . icExp =<<
         lift . desugarExp =<< lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc1)
  return $ CS.FnCall fn' [e',e] loc0
transFnCall e = return e

transDispatch :: CS.Exp -> GlMono t CS.Exp
transDispatch (CS.FnCall (CS.Cast ty e1 loc1) [e2] loc0)
  | CS.Type dcsp decl loc2 <- ty
  , CS.AntiDeclSpec s loc3 <- dcsp = do
    disp <- lift . lift . lift . genFnCall =<< monoType =<< lift . desugarType =<<
            lift . tcType =<< (lift . lift) (parseType s loc3)
    return $ CS.FnCall disp [e1,e2] loc0
transDispatch e = return e

traverseFnCall   = traverseAnti transFnCall
traverseDispatch = traverseAnti transDispatch


-- Expressions

parseExp :: String -> SrcLoc -> GlFile SR.LocExpr
parseExp s loc = parseAnti s (PS.expr 1) loc 4

tcExp :: SR.LocExpr -> GlDefn t TC.TypedExpr
tcExp e = undefined {- tcAnti (TC.inEContext (TC.AntiquotedExpr e) . TC.infer) e -}

desugarExp :: TC.TypedExpr -> GlDefn t (SF.UntypedExpr t 'Zero VarName)
desugarExp = desugarAnti DS.desugarExpr

icExp :: SF.UntypedExpr t 'Zero VarName -> GlDefn t (SF.TypedExpr t 'Zero VarName)
icExp = icAnti SF.typecheck

monoExp :: SF.TypedExpr t 'Zero VarName -> GlMono t (SF.TypedExpr 'Zero 'Zero VarName)
monoExp = monoAnti MN.monoExpr

genExp :: SF.TypedExpr 'Zero 'Zero VarName -> Gl CS.Exp
genExp = genAnti $ \e -> do (v,vdecl,vstm,_) <- CG.genExpr Nothing e
                            let bis' = L.map CG.cBlockItem (vdecl ++ vstm)
                                v'   = CG.cExpr v
                            return $ CS.StmExpr (bis' ++ [CS.BlockStm (CS.Exp (Just v') noLoc)]) noLoc

transExp :: CS.Exp -> GlMono t CS.Exp
transExp (CS.AntiExp s loc) = (lift . lift) (parseExp s loc) >>= lift . tcExp >>=
                              lift . desugarExp >>= lift . icExp >>= monoExp >>= lift . lift . lift . genExp
transExp e = return e

traverseExp = traverseAnti transExp

-- Function Id

transFuncId :: CS.Definition -> GlMono t CS.Definition
transFuncId (CS.FuncDef (CS.Func dcsp (CS.AntiId fn loc2) decl ps body loc1) loc0) =
  view (inst._2) >>= \idx ->
  return $ CS.FuncDef (CS.Func dcsp (CS.Id (toCName $ MN.monoName fn idx) loc2) decl ps body loc1) loc0
transFuncId d = return d


-- Type Id

parseTypeId :: String -> SrcLoc -> GlFile (TypeName, [TyVarName])
parseTypeId s loc = parseAnti s ((,) <$> PS.typeConName <*> PP.many PS.variableName) loc 4

genTypeId :: SF.Type 'Zero -> Gl CG.CId
genTypeId = genAnti CG.typeCId

transTypeId :: CS.Definition -> GlMono t (CS.Definition, Maybe String)
transTypeId (CS.DecDef initgrp loc0)
  | CS.InitGroup dcsp attr0 init loc1 <- initgrp
  , CS.DeclSpec store tyqual tysp loc2 <- dcsp
  , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
  , Just (CS.AntiId ty loc4) <- mid = do
    tn' <- (lift . lift) (parseType ty loc4) >>= lift . tcType  >>= lift . desugarType >>= monoType >>= lift . lift. lift . genTypeId
    let mid' = Just (CS.Id (toCName tn') loc4)
        tysp' = CS.Tstruct mid' fldgrp attr1 loc3
        dcsp' = CS.DeclSpec store tyqual tysp' loc2
        initgrp' = CS.InitGroup dcsp' attr0 init loc1
    return (CS.DecDef initgrp' loc0, Just tn')
transTypeId (CS.DecDef initgrp loc0)
  | CS.TypedefGroup dcsp attr0 [tydef] loc1 <- initgrp
  , CS.DeclSpec store tyqual tysp loc2 <- dcsp
  , CS.Tstruct mid fldgrp attr1 loc3 <- tysp
  , Just (CS.AntiId ty loc4) <- mid
  , CS.Typedef (CS.AntiId syn loc6) decl attr2 loc5 <- tydef = do
    tn'  <- (lift . lift) (parseType ty  loc4) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    syn' <- (lift . lift) (parseType syn loc6) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    when (tn' /= syn') $ throwError $ "Error: Type synonyms `" ++ syn ++ "' is somewhat different from the type `" ++ ty ++ "'"
    let tydef' = CS.Typedef (CS.Id (toCName syn') loc6) decl attr2 loc5
        mid' = Just (CS.Id (toCName tn') loc4)
        tysp' = CS.Tstruct mid' fldgrp attr1 loc3
        dcsp' = CS.DeclSpec store tyqual tysp' loc2
        initgrp' = CS.TypedefGroup dcsp' attr0 [tydef'] loc1
    return (CS.DecDef initgrp' loc0, Just tn')
transTypeId d = return (d, Nothing)

transTypeId' :: CS.TypeSpec -> GlMono t CS.TypeSpec
transTypeId' (CS.Tstruct mid fldgrp attr loc0)
  | Just (CS.AntiId ty loc1) <- mid = do
    tn' <- (lift . lift) (parseType ty loc1) >>= lift . tcType >>= lift . desugarType >>= monoType >>= lift . lift . lift . genTypeId
    return (CS.Tstruct (Just $ CS.Id (toCName tn') loc1) fldgrp attr loc0)
transTypeId' x = return x

traverseTypeId' :: CS.Definition -> GlMono t CS.Definition
traverseTypeId' (CS.DecDef initgrp loc) = CS.DecDef <$> traverseAnti transTypeId' initgrp <*> pure loc
traverseTypeId' d = return d


-- External definition

transEsc :: CS.Definition -> CS.Definition
transEsc (CS.AntiEsc s l) = CS.EscDef s l
transEsc d = d


-- Definition

traversals :: [(MN.Instance, Maybe Int)] -> CS.Definition -> GlDefn t [(CS.Definition, Maybe String)]
-- No type arguments, either monomorphic Cogent function, or not defined in Cogent
-- If any instances of a polymorphic function are not used anywhere, then no mono function will be generated
traversals insts d = forM insts $ \inst ->
                       flip runReaderT (MonoState inst) $
                         (traverseDecl >=> traverseDeclSpec >=> traverseType >=>
                         traverseFnCall >=> traverseDispatch >=> traverseExp >=>
                           -- NOTE: `traverseExp' has to be after `traverseFnCall' because they overlap / zilinc
                         return . transEsc >=>
                         transFuncId >=> transTypeId >=> firstM traverseTypeId') d

traverseOneFunc :: String -> CS.Definition -> GlFile [(CS.Definition, Maybe String)]
traverseOneFunc fn d = do
  lift $ cgState.localOracle .= 0
  monos <- lift $ use $ mnState.funMono
  defs  <- lift $ use tcDefs
  case M.lookup fn monos of
    Nothing -> return [] -- throwError $ "Error: Function `" ++ fn ++ "' is not defined in Cogent and thus cannot be antiquoted"
    Just mp -> case L.find (SR.absFnDeclId fn) defs of  -- function declared/defined in Cogent
                 Nothing -> throwError $ "Error: Function `" ++ fn ++ "' is not an abstract Cogent function and thus cannot be antiquoted"
                 Just tl -> do let ts = tyVars tl
                               case Vec.fromList ts of
                                 ExI (Flip ts') -> let l = if L.null ts then [([], Nothing)] else L.map (second Just) (M.toList mp)
                                                    in flip runReaderT (DefnState ts') $ traversals l d

traverseOneType :: String -> SrcLoc -> CS.Definition -> GlFile [(CS.Definition, Maybe String)]
traverseOneType ty l d = do   -- type defined in Cogent
  monos <- lift $ use $ mnState.typeMono
  defs  <- lift $ use tcDefs
  (tn,ts) <- parseTypeId ty l
  case M.lookup tn monos of  -- NOTE: It has to be an abstract type / zilinc
    Nothing -> return [] -- throwError $ "Error: Type `" ++ tn ++ "' is not defined / used in Cogent and thus cannot be antiquoted"
    Just s  -> do case L.find (SR.absTyDeclId tn) defs of
                    Nothing -> throwError $ "Error: Type `" ++ tn ++ "' is not an abstract Cogent type and thus cannot be antiquoted"
                    Just tl -> do let ts' = tyVars tl
                                  when (ts /= L.map fst ts') $
                                    throwError $ "Error: Type parameters in `" ++ ty ++ "' are different from those in Cogent"
                                  when (L.null ts') $
                                    throwError $ "Error: Non-parametric abstract Cogent type `" ++ tn ++ "' should not use antiquotation"
                                  case Vec.fromList ts' of
                                    ExI (Flip ts'') -> flip runReaderT (DefnState ts'') $ do
                                      s' <- nubByName $ S.toList s
                                      traversals (L.zip s' (repeat Nothing)) d
 where
   nubByName :: [MN.Instance] -> GlDefn t [MN.Instance]
   nubByName ins = do
     gl <- lift $ lift get
     return $ L.nubBy (\i1 i2 -> case runExcept $ flip evalStateT gl $ do
                                     tn1 <- mapM (genAnti CG.genType) i1
                                     tn2 <- mapM (genAnti CG.genType) i2
                                     return (tn1 == tn2) of
                                   Left  _ -> __impossible "nubByName (in traverseOneType)"
                                   Right b -> b) ins

traverseOne :: CS.Definition -> GlFile [(CS.Definition, Maybe String)]
traverseOne d@(CS.FuncDef (CS.Func _ (CS.AntiId fn _) _ _ _ _) _) = traverseOneFunc fn d
traverseOne d@(CS.DecDef initgrp  _)
  | CS.InitGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
  | CS.TypedefGroup dcsp _ _ _ <- initgrp
  , CS.DeclSpec _ _ tysp _ <- dcsp
  , CS.Tstruct mid _ _ _ <- tysp
  , Just (CS.AntiId ty l) <- mid = traverseOneType ty l d
traverseOne d = flip runReaderT (DefnState Nil) $ traversals [([], Nothing)] d  -- anything not defined in Cogent

traverseAll :: [CS.Definition] -> GlFile [(CS.Definition, Maybe String)]
traverseAll ds = concat <$> mapM traverseOne ds


-- Interface

data GlueMode = TypeMode | FuncMode deriving (Eq, Show)

glue :: GlState -> [TypeName] -> GlueMode -> [FilePath] -> EitherT String IO [(FilePath, [CS.Definition])]
glue s typnames mode filenames = liftA (M.toList . M.fromListWith (flip (++)) . concat) .
  forM filenames $ \filename -> do
    let EitherT m = lift $ parseFile defaultExts typnames filename
    m >>= \case
      Left err -> hoistEither $ Left err
      Right ds -> case runExcept . flip evalStateT s . flip runReaderT (FileState filename) $ traverseAll ds of
                    Right ds' -> -- lift (putStrLn $ show ds') >>
                                 case mode of
                                   TypeMode -> forM ds' $ \(d, mbf) -> case mbf of
                                     Nothing -> hoistEither $ Left "Error: Cannot define functions in type mode"
                                     Just f  -> return (__cogent_abs_type_dir ++ "/abstract/" ++ f <.> __cogent_ext_of_h, [d])
                                   FuncMode -> let ext = if | takeExtension filename == __cogent_ext_of_ah -> __cogent_ext_of_h
                                                            | takeExtension filename == __cogent_ext_of_ac -> __cogent_ext_of_c
                                                            | otherwise -> __cogent_ext_of_c

                                               in return [ (replaceExtension ((replaceBaseName filename (takeBaseName filename ++ __cogent_suffix_of_inferred))) ext
                                                         , L.map fst ds')]
                    Left err  -> hoistEither . Left $ err

mkGlState :: [SR.TopLevel SR.RawType TC.TypedName TC.TypedExpr]
          -> TC.TCState
          -> Last (DS.Typedefs, DS.Constants, [SF.SFConst SF.UntypedExpr])
          -> M.Map FunName SF.FunctionType
          -> (MN.FunMono, MN.TypeMono)
          -> CG.GenState
          -> GlState
mkGlState tced tcState (Last (Just (typedefs, constdefs, _))) ftypes (funMono, typeMono) genState = undefined {- 
  GlState { _tcDefs  = tced
          , _tcState = TcState { _tfuncs = view TC.knownFuns  tcState
                               , _ttypes = view TC.knownTypes tcState
                               , _consts = view TC.context    tcState
                               }
          , _dsState = DsState typedefs constdefs
          , _icState = IcState ftypes
          , _mnState = MnState funMono typeMono
          , _cgState = CgState { _cTypeDefs    = view CG.cTypeDefs    genState
                               , _cTypeDefMap  = view CG.cTypeDefMap  genState
                               , _typeSynonyms = view CG.typeSynonyms genState
                               , _typeCorres   = view CG.typeCorres   genState
                               , _absTypes     = view CG.absTypes     genState
                               , _funClasses   = view CG.funClasses   genState
                               , _localOracle  = view CG.localOracle  genState
                               , _globalOracle = view CG.globalOracle genState
                               }
          } -}
mkGlState _ _ _ _ _ _ = __impossible "mkGlState"


-- Misc.

tyVars :: SR.TopLevel SR.RawType pv e -> [(TyVarName, Kind)]
tyVars (SR.FunDef _ (SR.PT ts _) _) = ts
tyVars (SR.AbsDec _ (SR.PT ts _)  ) = ts
tyVars (SR.TypeDec    _ ts _) = L.zip ts $ repeat k2
tyVars (SR.AbsTypeDec _ ts  ) = L.zip ts $ repeat k2
tyVars _ = __impossible "tyVars"


-- ////////////////////////////////////////////////////////////////////////////
--

collect :: GlState -> [TypeName] -> GlueMode -> [FilePath] -> EitherT String IO (MN.FunMono, MN.TypeMono)
collect s typnames mode filenames = do
  ds <- liftA concat . forM filenames $ \filename -> do
          let EitherT m = lift $ parseFile defaultExts typnames filename
          m >>= \case
            Left err -> hoistEither $ Left err
            Right ds -> return ds
  case runExcept . flip execStateT s $ collectAll ds of
    Right s -> return $ (view (mnState.funMono) &&& view (mnState.typeMono)) s
      -- NOTE: Lens doesn't support Arrow. See http://www.reddit.com/r/haskell/comments/1nwetz/lenses_that_work_with_arrows/ / zilinc
    Left err  -> hoistEither . Left $ err

collectAnti :: (Typeable a, Data a, Typeable b, Monoid r) => (b -> Gl r) -> a -> Gl r
collectAnti f a = getAp $ everything mappend (mkQ mempty (Ap . f)) a

collectFuncId :: CS.Definition -> Gl [(String, SrcLoc)]
-- collectFuncId (CS.FuncDef (CS.Func _ (CS.AntiId fn loc) _ _ bis _) _) = (fn, loc) : collectAnti collectFnCall bis
collectFuncId (CS.FuncDef (CS.Func _ (CS.Id _ _) _ _ bis _) _) = collectAnti collectFnCall bis  -- NOTE: we restrict entry points have to be C functions
collectFuncId d = return []

collectFnCall :: CS.Exp -> Gl [(String, SrcLoc)]
collectFnCall (CS.FnCall (CS.Var (CS.AntiId fn loc) _) args _) = return [(fn, loc)]
collectFnCall _ = return []

analyseFuncId :: [(String, SrcLoc)] -> GlDefn t [(FunName, MN.Instance)]
analyseFuncId ss = forM ss $ \(fn, loc) -> flip runReaderT (MonoState ([], Nothing)) $ do
  (SF.TE _ (SF.Fun fn' ts _)) <- monoExp =<< lift . icExp =<< lift . desugarExp =<<
                                 lift . tcFnCall =<< (lift . lift) (parseFnCall fn loc)
  return (fn', ts)

collectOneFunc :: CS.Definition -> Gl ()
collectOneFunc d = do
  ss <- collectFuncId d
  fins <- flip runReaderT (FileState "") . flip runReaderT (DefnState Nil) $ analyseFuncId ss
  forM_ fins $ \(fn, inst) -> do
    case inst of
      [] -> mnState.funMono %= (M.insert fn M.empty)
      ts -> mnState.funMono %= (M.insertWith (\_ m -> insertWith (flip const) ts (M.size m) m) fn (M.singleton ts 0))

collectOne :: CS.Definition -> Gl ()
collectOne d@(CS.FuncDef {}) = collectOneFunc d
collectOne _ = return ()

collectAll :: [CS.Definition] -> Gl ()
collectAll = mapM_ collectOne
