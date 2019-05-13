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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cogent.Interpreter where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import qualified Cogent.Context     as Ctx
import           Cogent.Core
import qualified Cogent.Desugar     as Ds
import qualified Cogent.Inference   as Core
import           Cogent.Mono
import qualified Cogent.Parser      as Parser
import           Cogent.PrettyPrint as Pretty
import qualified Cogent.Surface             as S
import           Cogent.TypeCheck           as Tc
import qualified Cogent.TypeCheck.Base      as Tc
import           Cogent.TypeCheck.Generator as Tc hiding (validateType)
import qualified Cogent.TypeCheck.Post      as Tc
import           Cogent.TypeCheck.Solver    as Tc
import qualified Cogent.TypeCheck.Subst     as Subst
import           Cogent.Util
import           Data.Nat hiding (toInt)
import qualified Data.Vec as V

import Control.Monad.RWS.Strict
import Control.Monad.State
import Data.Bits
import Data.Either (fromLeft, isLeft)
import Data.Function ((&))
import Data.List (isPrefixOf, isSuffixOf, partition)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Data.Word
import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH
import System.Exit (exitSuccess)
import System.IO
import Text.Parsec hiding (string)
import Text.Parsec.String
import Text.PrettyPrint.ANSI.Leijen as Leijen hiding ((<$>), char)

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
  | VAbstract a
  | VFunction  FunName (TypedExpr 'Zero ('Suc 'Zero) VarName) [Type 'Zero]
  | VAFunction FunName f [Type 'Zero]
  | VBad String
  deriving (Show)

instance (Prec a, Prec f) => Prec (Value a f) where
  prec (VVariant tn v) = 1
  prec _ = 0


instance Pretty ILit where
  pretty x = literal $ integer $ toInt x

instance (Pretty a, Pretty f, Prec (Value a f)) => Pretty (Value a f) where
  pretty (VInt l) = pretty l
  pretty (VBool b) = Pretty.literal (string $ show b)
  pretty (VString s) = Pretty.literal (string $ show s)
  pretty (VUnit) = string "()"
  pretty (VRecord fs) = Pretty.record $ fmap (\(f,mv) -> fieldname f <+> symbol "=" <+> (case mv of Nothing -> symbol "●"; Just v -> pretty v)) fs
  pretty (VVariant tag v) = tagname tag <+> Pretty.prettyPrec 1 v
  pretty (VProduct v1 v2) = Pretty.tupled [pretty v1, pretty v2]
  pretty (VAbstract a) = warn "abstract" <+> pretty a
  pretty (VFunction  fn e ts) = funname fn <> typeargs (fmap pretty ts)
  pretty (VAFunction fn f ts) = warn "abstract" <+> funname fn <> typeargs (fmap pretty ts)
  pretty (VBad s) = errbd "Error:" <+> err s


newtype ReplM (v :: Nat) a f x = ReplM { unReplM :: StateT (ReplState v a f) IO x }
                               deriving (Functor, Applicative, Monad, MonadIO, MonadState (ReplState v a f))

data ReplState v a f = ReplState { _gamma   :: V.Vec v (Value a f)
                                 , _absfuns :: M.Map (CoreFunName, Value a f) (Value a f)
                                 , _fundefs :: M.Map CoreFunName (Definition TypedExpr VarName)
                                 }

makeLenses ''ReplState

runReplM :: ReplM v a f x -> ReplState v a f -> IO x
runReplM ma s = evalStateT (unReplM ma) s

getLines c = liftM unlines $ takeWhileM' c (repeat getLine)

continueGetLines :: String -> Bool
continueGetLines l
  | null l = False
  | ":f" `isPrefixOf` l = False
  | ":h" `isPrefixOf` l = False
  | ":q" `isPrefixOf` l = False
  | ";"  `isSuffixOf` l = False
continueGetLines l = True

repl :: IO ()
repl = do putStr "cogenti> "
          hFlush stdout
          s <- getLines continueGetLines
          let result = readInput s
          case result of
            Left err -> putStrLn err
            Right (EvalExpr s) -> interpExpr s
            Right (GetType  s) -> putStrLn ":t not implemented yet"
            Right (LoadFile f) -> putStrLn ":l not implemented yet"
            Right (LoadCode c) -> putStrLn ":l not implemented yet"
            Right (Help) -> putStr $ unlines [ "Cogent REPL:"
                                             , "  :e <EXPR> ;  -- evaluate an expression"
                                             , "  :t <EXPR> ;  -- query the type of an expression"
                                             , "  :f <FILE>    -- load a Cogent file"
                                             , "  :l <CODE> ;  -- load Cogent definitions"
                                             , "  :h           -- show this help"
                                             , "  :q           -- quit the REPL"
                                             ]
            Right (Quit) -> exitSuccess
          repl
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
 <|> (Parser.reservedOp ":h" >> return Help)
 <|> (Parser.reservedOp ":q" >> return Quit)
 <|> (eof >> return Skip)

loadProg :: FilePath -> ReplM v a f ()
loadProg input = do
  undefined

interpExpr :: String -> IO ()
interpExpr input =
  case runParser parseExpr (Parser.ParserState False) "<REPL>" input of
    Left  errs -> putStrLn $ show errs
    Right locE -> do
      ((mbTypedE, tclog), _) <- tcExpr locE
      let (errs,warns) = partition (isLeft . snd) $ tclog^.Tc.errLog
      unless (null $ warns) $ putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) warns ++ [empty])
      if not $ null errs
        then do
          putDoc (vcat $ fmap (Pretty.prettyTWE __cogent_ftc_ctx_len) errs ++ [empty])
          when (and $ map (Tc.isWarnAsError . fromLeft undefined . snd) errs) $ putStrLn "Failing due to --Werror."
        else case mbTypedE of
          Nothing     -> __impossible "intrepExpr: no errors found"
          Just typedE -> case coreTcExpr $ dsExpr typedE of
            Left err      -> putStrLn err
            Right typedCE -> do
              v <- runReplM (eval typedCE) (ReplState V.Nil M.empty M.empty)
              putDoc $ pretty (v :: Value () ()) <> line


parseExpr :: Parser.Parser S.LocExpr
parseExpr = Parser.expr 0 <* eof

tcExpr :: S.LocExpr -> IO ((Maybe Tc.TypedExpr, Tc.TcLogState), Tc.TcState)
tcExpr e = Tc.runTc $ do
  ((c,e'),flx,os) <- runCG Ctx.empty [] $ do
    let ?loc = S.posOfE e
    t <- freshTVar
    cg e t
  (logs, subst, assn, _) <- runSolver (solve c) [] flx os
  Tc.exitOnErr $ mapM_ Tc.logTc logs
  Tc.postE $ Subst.applyE subst e'


dsExpr :: Tc.TypedExpr -> UntypedExpr 'Zero 'Zero VarName
dsExpr e = fst
           . flip3 evalRWS (Ds.DsState V.Nil V.Nil 0 0 [])
                           (M.empty, M.empty, [])
           . Ds.runDS
           $ Ds.desugarExpr e

coreTcExpr :: UntypedExpr 'Zero 'Zero VarName -> Either String (TypedExpr 'Zero 'Zero VarName)
coreTcExpr e = fmap snd $ Core.runTC (Core.infer e) (V.Nil, M.empty) V.Nil



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


specialise :: [Type 'Zero] -> TypedExpr t v VarName -> TypedExpr 'Zero v VarName
specialise inst e = fst $ flip3 evalRWS initmap inst $ runMono (specialiseExpr e)
  where initmap = (M.empty, M.empty)

specialiseExpr :: TypedExpr t v VarName -> Mono (TypedExpr 'Zero v VarName)
specialiseExpr (TE t (Fun fn [] notes)) = TE <$> monoType t <*> pure (Fun fn [] notes)
specialiseExpr (TE t (Fun fn ts notes)) = do
  t'  <- monoType t
  ts' <- mapM monoType ts
  return $ TE t' (Fun fn ts' notes)
specialiseExpr e = monoExpr e

eval :: TypedExpr 'Zero v VarName -> ReplM v a () (Value a ())
eval (TE _ (Variable (v,_))) = use gamma >>= return . (`V.at` v)
eval (TE _ (Fun fn ts _)) = do
  funmap <- use fundefs
  case M.lookup fn funmap of
    Nothing  -> __impossible "eval: Function is not defined"
    Just (FunDef  _ _ _ ti to e) -> return $ VFunction  (coreFunName fn) (specialise ts e) ts
    Just (AbsDecl _ _ _ ti to  ) -> return $ VAFunction (coreFunName fn) () ts
    _ -> __impossible "eval: A function is expected but I got a type"
eval (TE _ (Op op [e])) = evalUnOp op <$> eval e
eval (TE _ (Op op [e1,e2])) = evalBinOp op <$> eval e1 <*> eval e2
eval (TE _ (App f e)) = do
  vf <- eval f
  ve <- eval e
  case vf of
    VAFunction fn f' ts -> return $ VBad $ "I don't know how to evaluate abstract functions " ++ fn
    VFunction  _ f' ts -> withNewBindings (V.Cons ve V.Nil) (eval f')
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
eval (TE _ (Let _ e e')) = do
  v <- eval e
  withBinding v (eval e')
eval (TE _ (LetBang _ _ e e')) = do
  v <- eval e
  withBinding v (eval e')
eval (TE _ (Tuple e1 e2)) = VProduct <$> eval e1 <*> eval e2
eval (TE t (Struct fs)) = do
  let TRecord fts _ = t
  fvs <- mapM (secondM eval) fs
  let fvs' = for fts $ \(fn,(t,b)) ->
               if b then (fn, Nothing)
                    else let Just v = lookup fn fvs in (fn, Just v)
  return $ VRecord fvs'
eval (TE _ (If c e1 e2)) = do
  VBool b <- eval c
  if b then eval e1 else eval e2
eval (TE _ (Case e tag (_, a1, e1) (_, a2, e2))) = do
 vv@(VVariant tag' v) <- eval e
 if tag == tag' then withBinding v  (eval e1)
                else withBinding vv (eval e2) 
eval (TE _ (Esac e)) = do
  VVariant _ v <- eval e
  return v
eval (TE _ (Split _ e e')) = do
  VProduct v1 v2 <- eval e
  withBindings (V.Cons v1 (V.Cons v2 V.Nil)) (eval e')
eval (TE _ (Member e f)) = do
  VRecord fvs <- eval e
  return . fromJust . snd $ fvs !! f
eval (TE t (Take _ rec f e)) = do
  VRecord fvs <- eval rec
  let (fvs1,fvs2) = splitAt f fvs
      (fn,_) = head fvs2
      v = fromJust . snd $ fvs !! f
      vr = VRecord $ fvs1 ++ (fn, Nothing) : tail fvs2
  withBindings (V.Cons v (V.Cons vr V.Nil)) $ eval e
eval (TE _ (Put rec f e)) = do
  VRecord fvs <- eval rec
  v <- eval e
  let (fvs1,fvs2) = splitAt f fvs
      (fn,_) = head fvs2  -- there must be at least 1 element in fvs2
  return $ VRecord $ fvs1 ++ (fn, Just v) : tail fvs2
eval (TE _ (Promote _ e)) = eval e
eval (TE _ (Cast _ e)) = eval e

