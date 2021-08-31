--
-- Copyright 2019, Data61
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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cogent.Interpreter where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import qualified Cogent.Context     as Ctx
import           Cogent.Core        as Core
import qualified Cogent.Desugar     as Ds
import           Cogent.Dargent.Core
import           Cogent.Dargent.Allocation
import qualified Cogent.Inference   as Core
import           Cogent.Mono
import qualified Cogent.Parser      as Parser
import           Cogent.PrettyPrint as Pretty hiding (associativity, primop)
import qualified Cogent.Reorganizer as Reorg
import qualified Cogent.Surface             as S
import           Cogent.TypeCheck           as Tc
import qualified Cogent.TypeCheck.Base      as Tc
import           Cogent.TypeCheck.Generator as Tc hiding (validateType)
import qualified Cogent.TypeCheck.Post      as Tc
import           Cogent.TypeCheck.Solver    as Tc
import           Cogent.TypeCheck.Errors    as Tc
import qualified Cogent.TypeCheck.Subst     as Subst
import           Cogent.Util
import           Data.Nat hiding (toInt)
import qualified Data.Vec as V

import Control.Monad.RWS.Strict
import Control.Monad.State
import Data.Bits
import Data.Either (fromLeft, fromRight, isLeft)
import Data.Function ((&))
import Data.IORef
import Data.List (isPrefixOf, isSuffixOf, partition)
import qualified Data.Map as M
import Data.Maybe (fromJust)
#if __GLASGOW_HASKELL__ < 803
import Data.Monoid ((<>))
#endif
import Data.Word
import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH
import System.Exit (exitSuccess)
import System.IO
import Text.Parsec hiding (string)
import Text.Parsec.String
import Text.PrettyPrint.ANSI.Leijen as Leijen hiding ((<$>), char, indent)
import qualified Text.PrettyPrint.ANSI.Leijen as Leijen ((<$>))

data ILit = LU8  Word8
          | LU16 Word16
          | LU32 Word32
          | LU64 Word64
          deriving (Eq, Ord, Show)

toInt :: ILit -> Integer
toInt (LU8  n) = toInteger n
toInt (LU16 n) = toInteger n
toInt (LU32 n) = toInteger n
toInt (LU64 n) = toInteger n

intW :: ILit -> Integer
intW (LU8  _) = 8
intW (LU16 _) = 16
intW (LU32 _) = 32
intW (LU64 _) = 64


data Value a f
  = VInt ILit
  | VBool Bool
  | VString String
  | VUnit
  | VRecord [(FieldName, Maybe (Value a f))]
  | VVariant TagName (Value a f)
  | VProduct (Value a f) (Value a f)
  | VFunction  FunName (TypedExpr 'Zero ('Suc 'Zero) VarName VarName) [Type 'Zero VarName]
  | VThunk (HNF a f)
  deriving (Show)

data HNF a f
  = VOp Op [Value a f]
  | VApp (Value a f) (Value a f)
  | VIf (Value a f) (Value a f) (Value a f)
  | VCase (Value a f) TagName (VarName, Value a f) (VarName, Value a f)
  | VEsac (Value a f)
  | VMember (Value a f) FieldName
  | VPut (Value a f) FieldName (Value a f)
  | VAbstract a
  | VAFunction FunName f [Type 'Zero VarName]
  deriving (Show)

instance (Prec a, Prec f, Prec (HNF a f)) => Prec (Value a f) where
  prec (VVariant tn v) = 9
  prec (VThunk w) = prec w
  prec _ = 0

instance (Prec a, Prec f) => Prec (HNF a f) where
  prec (VOp op _) = prec (associativity op)  -- 9 (unary), 11 ~ 19 (binary)
  prec (VApp {}) = 9
  prec (VIf {}) = 100
  prec (VCase {}) = 100
  prec (VEsac {}) = 9
  prec (VMember {}) = 9
  prec (VPut {}) = 1
  prec (VAbstract {}) = 0
  prec (VAFunction {}) = 0

instance Pretty ILit where
  pretty x = literal $ integer $ toInt x

instance (Pretty a, Pretty f, Prec (Value a f), Pretty (HNF a f)) => Pretty (Value a f) where
  pretty (VInt l) = pretty l
  pretty (VBool b) = literal (string $ show b)
  pretty (VString s) = literal (string $ show s)
  pretty (VUnit) = string "()"
  pretty (VRecord fs) = record $ fmap (\(f,mv) -> fieldname f <+> symbol "=" <+> (case mv of Nothing -> symbol "●"; Just v -> pretty v)) fs
  pretty (VVariant tag v) = tagname tag <+> prettyPrec 1 v
  pretty (VProduct v1 v2) = Pretty.tupled [pretty v1, pretty v2]
  pretty (VFunction fn e ts) = funname fn <> typeargs (fmap pretty ts)
  pretty (VThunk nf) = pretty nf

instance (Pretty a, Pretty f, Prec a, Prec f, Pretty (Value a f), Prec (HNF a f))
      => Pretty (HNF a f) where
  pretty (VOp n [a,b])
    | LeftAssoc  l <- associativity n = prettyPrec (l+1) a <+> primop n <+> prettyPrec l     b
    | RightAssoc l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec (l+1) b
    | NoAssoc    l <- associativity n = prettyPrec l     a <+> primop n <+> prettyPrec l     b
  pretty (VOp n [e])
    | a  <- associativity n = primop n <+> prettyPrec (prec a) e

  pretty (VApp v1 v2) = prettyPrec 10 v1 <+> prettyPrec 9 v2
  pretty (VIf c v1 v2) = keyword "if" <+> pretty c
              Leijen.<$> indent (keyword "then" <+> pretty v1)
              Leijen.<$> indent (keyword "else" <+> pretty v2)
  pretty (VCase s tn (a1,v1) (a2,v2)) = keyword "case" <+> pretty s <+> keyword "of"
                             Leijen.<$> indent (tagname tn <+> varname a1 <+> symbol "->" <+> pretty v1)
                             Leijen.<$> indent (varname a2 <+> symbol "->" <+> pretty v2)
  pretty (VEsac v) = keyword "esac" <+> prettyPrec 9 v
  pretty (VMember r f) = prettyPrec 9 r <> symbol "." <> fieldname f
  pretty (VPut r f v) = prettyPrec 10 r <+> record [fieldname f <+> symbol "=" <+> pretty v]
  pretty (VAbstract _) = dullred $ keyword "\x2753"
  pretty (VAFunction fn f ts) = dullred (keyword "\x300A") <> funname fn <> typeargs (fmap pretty ts) <> dullred (keyword "\x300B")


newtype ReplM (v :: Nat) a f x = ReplM { unReplM :: StateT (ReplState v a f) IO x }
                               deriving (Functor, Applicative, Monad, MonadIO, MonadState (ReplState v a f))

data ReplState v a f = ReplState { _gamma   :: V.Vec v (Value a f)
                                 , _absfuns :: M.Map CoreFunName (Value a f -> Value a f)
                                 , _fundefs :: M.Map CoreFunName (Definition TypedExpr VarName VarName)
                                 }

makeLenses ''ReplState

runReplM :: ReplM v a f x -> ReplState v a f -> IO x
runReplM ma s = evalStateT (unReplM ma) s

getLines c1 c2 = liftM unlines $ takeWhileM' c1 c2 (repeat getLine)

continueGetLines :: String -> Bool
continueGetLines l
  | ":f" `isPrefixOf` l = False
  | ":c" `isPrefixOf` l = False
  | ":r" `isPrefixOf` l = False
  | ":d" `isPrefixOf` l = False
  | ":h" `isPrefixOf` l = False
  | ":q" `isPrefixOf` l = False
  | ";"  `isSuffixOf` l = False
continueGetLines l = True

data PreloadS = PreloadS { surface  :: [S.TopLevel Tc.DepType Tc.TypedPatn Tc.TypedExpr]
                         , tcState  :: Tc.TcState
                         , lastFile :: Maybe FilePath
                         }

#if __GLASGOW_HASKELL__ < 803
instance Monoid PreloadS where
  mempty = PreloadS mempty mempty mempty
  PreloadS s1 t1 l1 `mappend` PreloadS s2 t2 l2 = PreloadS (s1 <> s2) (t1 <> t2) (l1 <> l2)
#else
instance Semigroup PreloadS where
  PreloadS s1 t1 l1 <> PreloadS s2 t2 l2 = PreloadS (s1 <> s2) (t1 <> t2) (l1 <> l2)
instance Monoid PreloadS where
  mempty = PreloadS mempty mempty mempty
#endif

replWithState :: IO ()
replWithState = do
  putStrLn "Welcome to the Cogent REPL. Type :h for help."
  r <- newIORef (PreloadS [] (Tc.TcState M.empty builtinTypes M.empty M.empty) Nothing)
  repl r
  where
    builtinTypes = map (, ([], Nothing)) $ words "U8 U16 U32 U64 String Bool"


repl :: IORef PreloadS -> IO ()
repl r = do putStr "cogenti> "
            hFlush stdout
            s <- getLines null continueGetLines
            let result = readInput s
            case result of
              Left err -> putStrLn $ err ++ "\n(:h for help)"
              Right (EvalExpr s) -> interpExpr QValue r s
              Right (GetType  s) -> interpExpr QType  r s
              Right (LoadFile f) -> loadFile r f
              Right (LoadCode c) -> loadCode r c
              Right (Reload    ) -> reloadFile r
              Right (Clear     ) -> writeIORef r mempty
              Right (Display   ) -> readIORef r >>= \st -> putDoc (vcat $ fmap pretty (surface st) ++ [empty])
              Right (Help) -> putStr $ unlines [ "Cogent REPL:"
                                               , "  :e <EXPR> ;  -- evaluate an expression"
                                               , "  :t <EXPR> ;  -- query the type of an expression"
                                               , "  :f <FILE>    -- load a Cogent file"
                                               , "  :l <CODE> ;  -- load Cogent definitions"
                                               , "  :c           -- clear loaded code"
                                               , "  :r           -- reload last file"
                                               , "  :d           -- display loaded code"
                                               , "  :h           -- show this help"
                                               , "  :q           -- quit the REPL"
                                               ]
              Right (Skip) -> return ()
              Right (Quit) -> exitSuccess
            repl r
  where
    readInput :: String -> Either String ReplOption
    readInput s = do
      case runParser parseCmdline () "<REPL>" s of
        Left  err -> Left $ show err
        Right opt -> Right opt

type Cmdline a = Parser a

data ReplOption = EvalExpr String
                | GetType  String
                | LoadFile String
                | LoadCode String
                | Clear  -- clear all loaded code
                | Reload
                | Display
                | Help
                | Quit
                | Skip
                deriving (Show)

parseCmdline :: Cmdline ReplOption
parseCmdline = do
     (Parser.reservedOp ":e" >> Parser.whiteSpace >> EvalExpr <$> manyTill anyChar (char ';'))
 <|> (Parser.reservedOp ":t" >> Parser.whiteSpace >> GetType  <$> manyTill anyChar (char ';'))
 <|> (Parser.reservedOp ":f" >> Parser.whiteSpace >> LoadFile <$> manyTill anyChar endOfLine)
 <|> (Parser.reservedOp ":l" >> Parser.whiteSpace >> LoadCode <$> manyTill anyChar (char ';'))
 <|> (Parser.reservedOp ":c" >> return Clear)
 <|> (Parser.reservedOp ":r" >> return Reload)
 <|> (Parser.reservedOp ":d" >> return Display)
 <|> (Parser.reservedOp ":h" >> return Help)
 <|> (Parser.reservedOp ":q" >> return Quit)
 <|> (endOfLine >> return Skip)


loadCode :: IORef PreloadS -> String -> IO ()
loadCode r code =
  case runParser Parser.program (Parser.ParserState True) "<REPL>" code of
    Left  err    -> putStrLn $ show err
    Right parsed -> checkPreload r (fmap (\(a,_,s) -> (a,s)) parsed) FromStdin

loadFile :: IORef PreloadS -> FilePath -> IO ()
loadFile r file = do
  modifyIORef r (\(PreloadS s t f) -> PreloadS s t (Just file))
  Parser.parseWithIncludes file [] >>= \case
    Left err -> putStrLn err
    Right (parsed, _) -> case Reorg.reorganize Nothing parsed of
      Left err -> putDoc (Pretty.prettyRE err)
      Right reorged -> checkPreload r (fmap (\(a,_,s) -> (a,s)) reorged) (FromFile file)

reloadFile :: IORef PreloadS -> IO ()
reloadFile r = do
  preldS <- readIORef r
  case lastFile preldS of
    Nothing -> putStrLn "No file loaded."
    Just f  -> loadFile r f

data InputSource = FromFile FilePath | FromStdin

checkPreload :: IORef PreloadS
             -> [(SourcePos, S.TopLevel S.LocType S.LocPatn S.LocExpr)]
             -> InputSource
             -> IO ()
checkPreload r prog src = do
  preldS <- readIORef r
  let tcst0 = tcState preldS
  ((mtced,tclog),tcst) <- Tc.runTc tcst0 (Tc.typecheck prog)
  let (errs,warns) = partition (isLeft . snd) $ tclog^.Tc.errLog
  unless (null $ warns) $ putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) warns ++ [empty])
  if not $ null errs then
    do putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) errs ++ [empty])
       when (and $ map (Tc.isWarnAsError . fromLeft undefined . snd) errs) $ hPutStrLn stderr "Failing due to --Werror."
  else
    case mtced of
      Nothing -> __impossible "loadProgram: no errors found"
      Just tced -> do
        __assert (null errs) "no errors, only warnings"
        case src of
          FromFile f -> putStrLn ("File " ++ f ++ " is loaded.") >>
                        writeIORef r (PreloadS tced tcst (Just f))
          FromStdin  -> modifyIORef r (<> PreloadS tced tcst Nothing)

data Query = QValue | QType

interpExpr :: Query -> IORef PreloadS -> String -> IO ()
interpExpr q r input =
  case runParser parseExpr (Parser.ParserState False) "<REPL>" input of
    Left  err  -> putStrLn $ show err
    Right locE -> do
      ((mbTypedE, tclog), _) <- tcExpr r locE
      let (errs,warns) = partition (isLeft . snd) $ tclog^.Tc.errLog
      unless (null $ warns) $ putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) warns ++ [empty])
      if not $ null errs
        then do
          putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) errs ++ [empty])
          when (and $ map (Tc.isWarnAsError . fromLeft undefined . snd) errs) $ putStrLn "Failing due to --Werror."
        else case mbTypedE of
          Nothing     -> __impossible "intrepExpr: no errors found"
          Just typedE -> do
            case q of
              QType  -> putDoc $ pretty (Tc.getTypeTE typedE) <> line
              QValue -> do
                (desugared, desugaredE) <- dsExpr r typedE
                let coreTced = fromRight [] $ Core.tc_ desugared  -- there shouldn't be any errors
                typedCE <- coreTcExpr coreTced desugaredE  -- the state required will be extracted from @coreTced@
                let absFuns = filter Core.isAbsFun coreTced
                    conFuns = filter Core.isConFun coreTced
                    absFunMap = M.fromList $ fmap (\d -> (CoreFunName . fromJust $ getFuncId d, id)) absFuns
                    conFunMap = M.fromList $ fmap (\d -> (CoreFunName . fromJust $ getFuncId d, d )) conFuns
                v <- runReplM (eval typedCE) (ReplState V.Nil absFunMap conFunMap)
                putDoc $ pretty (v :: Value () ()) <> line


parseExpr :: Parser.Parser S.LocExpr
parseExpr = Parser.expr 0 <* eof

tcExpr :: IORef PreloadS -> S.LocExpr -> IO ((Maybe Tc.TypedExpr, Tc.TcLogState), Tc.TcState)
tcExpr r e = do
  st <- readIORef r
  Tc.runTc (tcState st) $
    do
      ((c,e'), flx, os) <- (Tc.runCG Ctx.empty [] [] (do
        let ?loc = S.posOfE e
        t <- freshTVar
        y <- Tc.cg e t
        pure y))
      (cs, subst) <- runSolver (solve [] [] c) flx
      Tc.exitOnErr $ Tc.toErrors os cs
      Tc.postE $ Subst.applyE subst e'
  where
    knownTypes = map (, ([], Nothing)) $ words "U8 U16 U32 U64 String Bool"

coreTcExpr :: [Definition TypedExpr VarName VarName]
           -> UntypedExpr 'Zero 'Zero VarName VarName
           -> IO (TypedExpr 'Zero 'Zero VarName VarName)
coreTcExpr ds e = do
  let mkFunMap (FunDef  _ fn ps ts ti to _) = (fn, FT (fmap snd ps) (fmap snd ts) ti to)
      mkFunMap (AbsDecl _ fn ps ts ti to  ) = (fn, FT (fmap snd ps) (fmap snd ts) ti to)
      mkFunMap _ = __impossible "coreTcExpr: mkFunMap: not a function definition"
  let funmap = M.fromList $ fmap mkFunMap $ filter (not . isTypeDef) ds
  case fmap snd $ Core.runTC (Core.infer e) (V.Nil, funmap, Core.filterTypeDefs ds) V.Nil of
    Left err -> __impossible "coreTcExpr: there shouldn't be any error here"
    Right e  -> return e

dsExpr :: IORef PreloadS
       -> Tc.TypedExpr
       -> IO ([Definition UntypedExpr VarName VarName], UntypedExpr 'Zero 'Zero VarName VarName)
dsExpr r e = do
  preldS <- readIORef r
  let (tls, constdefs) = partition (not . isConstDef) (surface preldS)
      tls' = filter isDefn tls
  return . fst
         . flip3 evalRWS (Ds.DsState V.Nil V.Nil V.Nil 0 0 [])
                         (M.empty, M.empty, [])
         . Ds.runDS
         $ (,) <$> (fmap fst $ Ds.desugar' tls' constdefs [] []) <*> Ds.desugarExpr e
  where isConstDef S.ConstDef {} = True
        isConstDef _ = False

        isDefn S.Include {} = False
        isDefn S.IncludeStd {} = False
        isDefn S.DocBlock {} = False
        isDefn S.RepDef {} = False
        isDefn _ = True

withBinding :: Value a f -> ReplM (Suc v) a f x -> ReplM v a f x
withBinding v m = ReplM . StateT $ \s -> do
  (x',s') <- runStateT (unReplM m) (s & gamma %~ (V.Cons v))
  return (x',s)

withBindings :: V.Vec k (Value a f) -> ReplM (v :+: k) a f x -> ReplM v a f x
withBindings V.Nil m = m
withBindings (V.Cons v vs) m = withBindings vs $ withBinding v m

withNewBindings :: V.Vec k (Value a f) -> ReplM k a f x -> ReplM v a f x
withNewBindings vs m = ReplM . StateT $ \s -> do
  (x',s') <- runStateT (unReplM m) (s & gamma `set` vs)
  return (x',s)


data ExistsOp1  = ExistsOp1  (forall t. (Integral t, Bits t) => t      -> t   )
data ExistsOp2  = ExistsOp2  (forall t. (Integral t, Bits t) => t -> t -> t   )
data ExistsComp = ExistsComp (forall t. (Integral t)         => t -> t -> Bool)

primWordOp1 :: ExistsOp1 -> ILit -> ILit
primWordOp1 (ExistsOp1 op) (LU8  n) = LU8  $ op n
primWordOp1 (ExistsOp1 op) (LU16 n) = LU16 $ op n
primWordOp1 (ExistsOp1 op) (LU32 n) = LU32 $ op n
primWordOp1 (ExistsOp1 op) (LU64 n) = LU64 $ op n

primWordOp2 :: ExistsOp2 -> ILit -> ILit -> ILit
primWordOp2 (ExistsOp2 op) (LU8  n1)  (LU8  n2) = LU8  $ n1 `op` n2
primWordOp2 (ExistsOp2 op) (LU16  n1) (LU16 n2) = LU16 $ n1 `op` n2
primWordOp2 (ExistsOp2 op) (LU32  n1) (LU32 n2) = LU32 $ n1 `op` n2
primWordOp2 (ExistsOp2 op) (LU64  n1) (LU64 n2) = LU64 $ n1 `op` n2
primWordOp2 (ExistsOp2 op) _ _ = __impossible "primWordOp2: Ill-typed binary operation"

primWordComp :: ExistsComp -> ILit -> ILit -> Bool
primWordComp (ExistsComp op) (LU8  n1) (LU8  n2) = n1 `op` n2
primWordComp (ExistsComp op) (LU16 n1) (LU16 n2) = n1 `op` n2
primWordComp (ExistsComp op) (LU32 n1) (LU32 n2) = n1 `op` n2
primWordComp (ExistsComp op) (LU64 n1) (LU64 n2) = n1 `op` n2
primWordComp (ExistsComp op) _ _ = __impossible "primmWordComp: Ill-typed comparison operation"

evalUnOp :: Op -> Value a f -> Value a f
evalUnOp Not        (VBool b) = VBool $ not b
evalUnOp Complement (VInt  l) = VInt $ primWordOp1 (ExistsOp1 complement) l
evalUnOp op      v@(VThunk _) = VThunk $ VOp op [v]

evalBinOp :: Op -> Value a f -> Value a f -> Value a f
evalBinOp Plus   (VInt l1) (VInt l2) = VInt $ primWordOp2 (ExistsOp2 (+)) l1 l2
evalBinOp Minus  (VInt l1) (VInt l2) = VInt $ primWordOp2 (ExistsOp2 (-)) l1 l2
evalBinOp Times  (VInt l1) (VInt l2) = VInt $ primWordOp2 (ExistsOp2 (*)) l1 l2
evalBinOp Divide (VInt l1) (VInt l2)
  = VInt (primWordOp2 (ExistsOp2 div) l1 l2) &
      if __cogent_fcheck_undefined then (ifThenElse (toInt l2 == 0) (VInt l2)) else id
evalBinOp Mod    (VInt l1) (VInt l2)
  = VInt (primWordOp2 (ExistsOp2 mod) l1 l2) &
      if __cogent_fcheck_undefined then (ifThenElse (toInt l2 == 0) (VInt l2)) else id
evalBinOp And    (VBool b1) (VBool b2) = VBool $ b1 && b2
evalBinOp Or     (VBool b1) (VBool b2) = VBool $ b1 || b2
evalBinOp Gt     (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (>) ) l1 l2
evalBinOp Lt     (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (<) ) l1 l2
evalBinOp Ge     (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (>=)) l1 l2
evalBinOp Le     (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (<=)) l1 l2
evalBinOp Eq     (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (==)) l1 l2
evalBinOp NEq    (VInt  l1) (VInt  l2) = VBool $ primWordComp (ExistsComp (/=)) l1 l2
evalBinOp Eq     (VBool b1) (VBool b2) = VBool $ b1 == b2
evalBinOp NEq    (VBool b1) (VBool b2) = VBool $ b1 /= b2
evalBinOp BitAnd (VInt  l1) (VInt  l2) = VInt $ primWordOp2 (ExistsOp2 (.&.)) l1 l2
evalBinOp BitOr  (VInt  l1) (VInt  l2) = VInt $ primWordOp2 (ExistsOp2 (.|.)) l1 l2
evalBinOp BitXor (VInt  l1) (VInt  l2) = VInt $ primWordOp2 (ExistsOp2 (xor)) l1 l2
evalBinOp LShift (VInt  l1) v2@(VInt  l2)
  = VInt (primWordOp1 (ExistsOp1 $ flip unsafeShiftL (fromIntegral $ toInt l2)) l1) &
      if __cogent_fcheck_undefined then (ifThenElse (toInt l2 >= intW l1) (evalBinOp Minus v2 v2)) else id
evalBinOp RShift (VInt  l1) v2@(VInt  l2)
  = VInt (primWordOp1 (ExistsOp1 $ flip unsafeShiftR (fromIntegral $ toInt l2)) l1) &
      if __cogent_fcheck_undefined then (ifThenElse (toInt l2 >= intW l1) (evalBinOp Minus v2 v2)) else id
evalBinOp op v1@(VThunk {}) v2 = VThunk $ VOp op [v1,v2]
evalBinOp op v1 v2@(VThunk {}) = VThunk $ VOp op [v1,v2]

specialise :: [Type 'Zero VarName] -> TypedExpr t v VarName VarName -> TypedExpr 'Zero v VarName VarName
specialise inst e = __fixme $ fst . fst $ flip3 evalRWS initmap (inst, []) $ runMono (specialiseExpr e >>= pure . (,[]))
  where initmap = (M.empty, M.empty)

-- Mostly a duplicate of 'Mono.monoExpr', but it doesn't try to fiddle with the names
-- of monomorphised functions.
specialiseExpr :: TypedExpr t v VarName VarName -> Mono VarName (TypedExpr 'Zero v VarName VarName)
specialiseExpr (TE t e) = TE <$> monoType t <*> specialiseExpr' e
  where
    specialiseExpr' (Variable var       ) = pure $ Variable var
    specialiseExpr' (Fun fn [] ls notes ) = pure $ Fun fn [] ls notes
    specialiseExpr' (Fun fn ts ls notes ) = Fun fn <$> mapM monoType ts <*> pure ls <*> pure notes
    specialiseExpr' (Op      opr es     ) = Op opr <$> mapM specialiseExpr es
    specialiseExpr' (App     e1 e2      ) = App <$> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (Con     tag e t    ) = Con tag <$> specialiseExpr e <*> monoType t
    specialiseExpr' (Unit               ) = pure Unit
    specialiseExpr' (ILit    n   pt     ) = pure $ ILit n pt
    specialiseExpr' (SLit    s          ) = pure $ SLit s
#ifdef BUILTIN_ARRAYS
    specialiseExpr' (ALit    es         ) = ALit <$> mapM specialiseExpr es
    specialiseExpr' (ArrayIndex e i     ) = ArrayIndex <$> specialiseExpr e <*> specialiseExpr i
    specialiseExpr' (Pop     a e1 e2    ) = Pop a <$> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (Singleton e        ) = Singleton <$> specialiseExpr e
#endif
    specialiseExpr' (Let     a e1 e2    ) = Let a <$> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (LetBang vs a e1 e2 ) = LetBang vs a <$> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (Tuple   e1 e2      ) = Tuple <$> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (Struct  fs         ) = let (ns,ts) = Prelude.unzip fs in Struct <$> zipWithM (\n t -> (n,) <$> specialiseExpr t) ns ts
    specialiseExpr' (If      c e1 e2    ) = If <$> specialiseExpr c <*> specialiseExpr e1 <*> specialiseExpr e2
    specialiseExpr' (Case    c tag (l1,a1,e1) (l2,a2,e2)) = Case <$> specialiseExpr c <*> pure tag <*> ((l1,a1,) <$> specialiseExpr e1) <*> ((l2,a2,) <$> specialiseExpr e2)
    specialiseExpr' (Esac    e          ) = Esac <$> specialiseExpr e
    specialiseExpr' (Split   a tp e     ) = Split a <$> specialiseExpr tp <*> specialiseExpr e
    specialiseExpr' (Member  rec fld    ) = flip Member fld <$> specialiseExpr rec
    specialiseExpr' (Take    a rec fld e) = Take a <$> specialiseExpr rec <*> pure fld <*> specialiseExpr e
    specialiseExpr' (Put     rec fld e  ) = Put  <$> specialiseExpr rec <*> pure fld <*> specialiseExpr e
    specialiseExpr' (Promote ty e       ) = Promote <$> monoType ty <*> specialiseExpr e
    specialiseExpr' (Cast    ty e       ) = Cast <$> monoType ty <*> specialiseExpr e

eval :: TypedExpr 'Zero v VarName VarName -> ReplM v () () (Value () ())
eval (TE _ (Variable (v,_))) = use gamma >>= return . (`V.at` v)
eval (TE _ (Fun fn ts ls _)) = do
  funmap <- use fundefs
  absfunmap <- use absfuns
  case M.lookup fn funmap of
    Just (FunDef  _ _ _ _ ti to e) -> return $ VFunction  (unCoreFunName fn) (specialise ts e) ts
    Nothing  -> case M.lookup fn absfunmap of
      Just af -> return $ VThunk $ VAFunction (unCoreFunName fn) () ts
      Nothing -> __impossible $ "eval: function name " ++ show fn ++ " not found"
eval (TE _ (Op op [e])) = evalUnOp op <$> eval e
eval (TE _ (Op op [e1,e2])) = evalBinOp op <$> eval e1 <*> eval e2
eval (TE _ (App f e)) = do
  vf <- eval f
  ve <- eval e
  case vf of
    VFunction  _  f' ts -> withNewBindings (V.Cons ve V.Nil) (eval f')
    VThunk _  -> return (VThunk $ VApp vf ve)
eval (TE _ (Con tn e t)) = VVariant tn <$> eval e
eval (TE _ (Unit)) = return VUnit
eval (TE _ (ILit n t))
  | U8  <- t = return $ VInt (LU8  $ fromIntegral n)
  | U16 <- t = return $ VInt (LU16 $ fromIntegral n)
  | U32 <- t = return $ VInt (LU32 $ fromIntegral n)
  | U64 <- t = return $ VInt (LU64 $ fromIntegral n)
  | Boolean <- t = return $ VBool (if n == 0 then False else True)
eval (TE _ (SLit s)) = return $ VString s
#ifdef BUILTIN_ARRAYS
eval (TE _ (ALit es)) = undefined
eval (TE _ (ArrayIndex arr idx)) = undefined
eval (TE _ (Pop (a1, a2) e e')) = undefined
eval (TE _ (Singleton e)) = undefined
#endif
eval (TE _ (Let a e e')) = do
  v  <- eval e
  withBinding v (eval e')
eval (TE _ (LetBang _ a e e')) = do
  v  <- eval e
  withBinding v (eval e')
eval (TE _ (Tuple e1 e2)) = VProduct <$> eval e1 <*> eval e2
eval (TE t (Struct fs)) = do
  let TRecord _ fts _ = t
  fvs <- mapM (secondM eval) fs
  let fvs' = for fts $ \(fn,(t,b)) ->
               if b then (fn, Nothing)
                    else let Just v = lookup fn fvs in (fn, Just v)
  return $ VRecord fvs'
eval (TE _ (If c e1 e2)) = do
  vc <- eval c
  case vc of
    VBool  b -> if b then eval e1 else eval e2
    VThunk _ -> VThunk <$> (VIf vc <$> eval e1 <*> eval e2)
eval (TE _ (Case e tag (_, a1, e1) (_, a2, e2))) = do
  vv <- eval e
  case vv of
    VVariant tag' v -> if tag == tag' then withBinding v (eval e1)
                       else withBinding vv (eval e2)
    VThunk _ -> do
      let abs = VThunk $ VAbstract ()
      v1 <- withBinding abs (eval e1)
      v2 <- withBinding vv  (eval e2)
      return $ VThunk $ VCase vv tag (a1,v1) (a2,v2)
eval (TE _ (Esac e)) = do
  vv <- eval e
  case vv of
    VVariant _ v -> return v
    VThunk _     -> return $ VThunk $ VEsac vv
eval (TE _ (Split (a1,a2) e e')) = do
  pair <- eval e
  case pair of
    VProduct v1 v2 -> withBindings (V.Cons v1 (V.Cons v2 V.Nil)) (eval e')
    VThunk _ -> let abs1 = VThunk $ VAbstract ()
                    abs2 = VThunk $ VAbstract ()
                 in withBindings (V.Cons abs1 (V.Cons abs2 V.Nil)) (eval e')
eval (TE _ (Member e f)) = do
  let TRecord _ fs _ = exprType e
      fn = fst $ fs !! f
  rec <- eval e
  case rec of
    VRecord fvs -> return . fromJust . snd $ fvs !! f
    VThunk _ -> return $ VThunk $ VMember rec fn
eval (TE t (Take bs rec f e)) = do
  let TRecord _ fs _ = exprType rec
      fn = fst $ fs !! f
  vrec <- eval rec
  case vrec of
    VRecord fvs ->
      let (fvs1,fvs2) = splitAt f fvs
          v = fromJust . snd $ fvs !! f
          vr = VRecord $ fvs1 ++ (fn, Nothing) : tail fvs2
       in withBindings (V.Cons v (V.Cons vr V.Nil)) $ eval e
    VThunk _ ->
      let vrec' = VThunk $ VAbstract ()
          vfld  = VThunk $ VAbstract ()
       in withBindings (V.Cons vfld (V.Cons vrec' V.Nil)) $ eval e
eval (TE _ (Put rec f e)) = do
  let TRecord _ fs _ = exprType rec
      fn = fst $ fs !! f
  vrec <- eval rec
  v    <- eval e
  case vrec of
    VRecord fvs -> do
      let (fvs1,fvs2) = splitAt f fvs
      return $ VRecord $ fvs1 ++ (fn, Just v) : tail fvs2
    VThunk _ -> return $ VThunk $ VPut vrec fn v
eval (TE _ (Promote _ e)) = eval e
eval (TE _ (Cast _ e)) = eval e

