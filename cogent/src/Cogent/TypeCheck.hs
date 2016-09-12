--
-- Copyright 2016, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--


{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Cogent.TypeCheck where

import           Cogent.Common.Syntax
import           Cogent.Common.Types
import           Cogent.Compiler
import           Cogent.Surface
import           Cogent.Util hiding (Warning)

import           Control.Applicative
import           Control.Arrow (first, second, (&&&))
import           Control.Lens
import           Control.Monad hiding (sequence, mapM, mapM_)
import           Control.Monad.Except hiding (sequence, mapM_, mapM)
import           Control.Monad.State hiding (sequence, mapM_, mapM)
#if __GLASGOW_HASKELL__ < 709
import           Control.Monad.Writer hiding (sequence, mapM_, mapM)
#else
import           Control.Monad.Writer hiding (Alt, sequence, mapM_, mapM)
#endif
import           Data.Either (lefts)
import           Data.Function (on)
import           Data.Foldable as F (toList, fold, foldr, all, mapM_)
import           Data.IORef (readIORef)
import           Data.List as L (delete, union)
import qualified Data.Map as M
import           Data.Maybe (fromJust)
-- import qualified Data.Set as S (fromList)
import           Data.Traversable(mapM)
import           Prelude hiding (sequence, mapM, mapM_, all)
import           System.IO.Unsafe (unsafePerformIO)
import           Text.Parsec.Pos

-- import           Debug.Trace

-- ------------------------------------

data TypeError = NotAPolymorphicFunction VarName RawType
               | ValueNotAFunction TypedExpr LocExpr
               | CannotDiscardValue RawType
               | NotATupleType RawType
               | IrrefPatternDoesNotMatchType (IrrefutablePattern VarName) RawType
               | PatternDoesNotMatchType (Pattern VarName) RawType
               | SpuriousAlternatives [Alt VarName LocExpr]
               | NonExhaustivePattern RawType
               | NotInScope VarName
               | VariableAlreadyUsed SourcePos VarName
               | BindingCannotEscapeLetBang  VarName TypedExpr
               | MemberAlreadyUsed SourcePos VarName RawExpr
               | LinearVariableNotDisposedOf VarName RawType
               | ObservedVariableRemainsUnused VarName
               | TypeNotFound RawType
               | IncorrectNumberOfTypeParameters TypeName Int Int
               | IncorrectNumberOfTypeArguments (Polytype RawType) Int
               | TypeVariableNotInScope VarName
               | KindError RawType Kind Kind
               | ConflictingTypeVariables TyVarName (Either TypeName (Polytype LocType))
               | ConflictingDeclarations (Pattern VarName) VarName
               | DuplicateFieldName RawType FieldName
               | DuplicateField RawExpr FieldName
               | CannotFindCommonSupertype RawType RawType
               | VariantsHaveDifferentNumOfTypes TagName [RawType] [RawType]
               | VariableUsedOnlyOnOneSide VarName RawType SourcePos
               | NotAShareableRecord RawType
               | NotARecord RawType
               | NonNumericType RawType
               | FieldNotTaken FieldName RawType
               | RecordTypeMissingField RawType FieldName
               | RecordFieldTaken   RawType FieldName
               | RecordFieldUntaken RawType FieldName
               | CannotPromote RawType TypedExpr
               | NotASubtype RawType TypedExpr
               | NotASubtypeAlts RawType RawType
               | ConstantMustBeShareable VarName RawType
               | FunDefNotOfFunType VarName RawType
               | DynamicVariantPromotionE TypedExpr RawType RawType
               | RedefinitionOfType VarName
               | RedefinitionOfFun VarName
               | RedefinitionOfConst VarName
               | DebugVarTypeNoUnit VarName
               | DebugFunctionReturnNoUnit FunName
               | DebugFunctionHasToBeApplied FunName SourcePos
               | DebugFunctionCannotTakeLinear FunName RawType
               | UnhandledError String
               | WarnError Warning
               deriving (Show)

data Warning = VariableAlreadyInScope VarName (IrrefutablePattern VarName)
             | ImplicitCastPrimInt TypedExpr RawType RawType
             | DynamicVariantPromotionW TypedExpr RawType RawType
             | UnhandledWarning String
             deriving (Show)

-- FIXME: More fine-grained context is appreciated. e.g., only show alternatives that don't unify / zilinc
data ErrorContext = InExpression LocExpr
                  | InExpressionOfType LocExpr RawType
                  | NthAlternative Int (Pattern VarName)
                  | InDefinition SourcePos (TopLevel LocType VarName LocExpr)
                  | AntiquotedType LocType
                  | AntiquotedExpr LocExpr
                  deriving (Show)

type WarningErrorLog   = [(Either TypeError Warning, [ErrorContext])]

failDueToWerror :: [Either TypeError Warning] -> Bool
failDueToWerror = not . null . filter isWError . lefts
  where isWError :: TypeError -> Bool
        isWError (WarnError {}) = True
        isWError _ = False

type TypedName = (VarName, RawType)

data TypedExpr = TE { typeOfTE :: RawType, exprOfTE :: Expr RawType TypedName TypedExpr }
               | Promote { typeOfTE :: RawType, promotedExpr :: TypedExpr }
               | TypeErrorHappened {typeOfTE :: RawType}
               deriving (Show)

isTypeError :: TypedExpr -> Bool
isTypeError (TE _ e) = F.foldr (\x a -> isTypeError x || a) False e
isTypeError (Promote _ te) = isTypeError te
isTypeError (TypeErrorHappened _) = True

toRawExp :: TypedExpr -> RawExpr
toRawExp (TE _ e) = RE (ffmap fst (fmap toRawExp e))
toRawExp (Promote _ te) = toRawExp te
toRawExp (TypeErrorHappened t) = __impossible "toRawExp"

data NameResolution = Function (Polytype RawType) | Value RawType

data TCState = TCState { _knownFuns    :: [(VarName, Polytype RawType)]
                       , _context      :: [(VarName, Either SourcePos RawType)]  -- `Left' for used variables
                       , _errorContext :: [ErrorContext]
                       , _kindContext  :: [(TyVarName, Kind)]
                       , _knownTypes   :: [(TypeName, ([VarName], Maybe RawType))]  -- `Nothing' for abstract types
                       }

makeLenses ''TCState

tc :: [(SourcePos, TopLevel LocType VarName LocExpr)]
   -> ((Either (TypeError, [ErrorContext]) [TopLevel RawType TypedName TypedExpr], WarningErrorLog), TCState)
tc defs = runAllTCs (typecheck defs) initialState

initialState = TCState [] [] [] [] (("Char", ([], Just $ RT (TCon "U8" [] Unboxed))) : map prim primTypeCons)
  where prim = (,([],Nothing))

runAllTCs = runState . runWriterT . runExceptT . runTC

newtype TC a = TC { runTC :: ExceptT (TypeError, [ErrorContext])
                               (WriterT WarningErrorLog
                                 (State TCState))
                                   a }
             deriving ( Monad, Functor, Applicative
                      , MonadError (TypeError,[ErrorContext])
                      , MonadState TCState
                      , MonadWriter WarningErrorLog
                      )

-- FIXME: Is it correct? / zilinc
--
--   a ---Ok----> c a' -------> b a'  .---> result
--   |                     '----------'
--   `---Fail---> error
bracketTE :: TC a -> (a -> TC b) -> (a -> TC c) -> TC c
bracketTE a b c = do a' <- a
                     catchError (Left <$> c a') (return . Right) >>= \case
                       Left ret -> b a' >> return ret
                       Right e  -> b a' >> throwError e

resolveName :: SourcePos -> VarName -> TC NameResolution
resolveName p v = lookup v <$> use knownFuns >>= \case
   Just pt -> return $ Function pt
   Nothing -> Value <$> useVar p v

updateAssoc :: Eq a => a -> b -> [(a,b)] -> [(a,b)]
updateAssoc _ _ [] = []
updateAssoc v r ((x,t):xs) | x == v    = (x,r):xs
                           | otherwise = (x,t):updateAssoc v r xs

useVar :: SourcePos -> VarName -> TC RawType
useVar p v = lookup v <$> use context >>= \case
   Nothing -> typeError (NotInScope v)
   Just (Left l) -> typeError (VariableAlreadyUsed l v)
   Just (Right tau) -> canShare <$> kindcheck tau >>= \case
     True -> return tau
     False -> context %= updateAssoc v (Left p)
           >> return tau

inEContext :: ErrorContext -> TC a -> TC a
inEContext c a = bracketTE (errorContext %= (c:)) (const $ errorContext %= tail) (const a)

typeError :: TypeError -> TC a
typeError e = (Left e,) <$> use errorContext >>= \err -> tell [err] >> throwError (first fromLeft $ err)
  where fromLeft (Left e) = e; fromLeft _ = __impossible "fromLeft (in typeError)"

warning :: Warning -> TC ()
warning w = case unsafePerformIO (readIORef __cogent_warning_switch_ref) of
              Flag_w      -> return ()
              Flag_Wwarn  -> (Right w,) <$> use errorContext >>= \warn -> tell [warn]
              Flag_Werror -> typeError (WarnError w) >> return ()

suppressErrors :: RawType -> TC TypedExpr -> TC TypedExpr
suppressErrors tau a = a `catchError` \_ -> return (TypeErrorHappened tau)

withBinds :: [(VarName, RawType)] -> TC a -> TC a
withBinds bs a = bracketTE (context %= (map (fmap Right) bs ++))
                           (const $ let nbs = length bs
                             in do drops <- take nbs <$> (context <<%= drop nbs)
                                   mapM_ checkOK drops)
                           (const a)
  where checkOK :: (VarName, Either SourcePos RawType) -> TC ()
        checkOK (x, Right t) = canDiscard <$> kindcheck t >>= \case
                                 True -> return ()
                                 False -> typeError (LinearVariableNotDisposedOf x t)
        checkOK (x, Left _ ) = return ()

ensureUsed :: [VarName] -> TC ()
ensureUsed _ = return ()  -- NOTE: This function seems do nothing useful / zilinc
-- XXX | ensureUsed = mapM_ ensureUsed'
-- XXX |   where ensureUsed' v = lookup v <$> use context >>= \case
-- XXX |                           Nothing -> typeError (NotInScope v)
-- XXX |                           Just (Left _) -> return ()
-- XXX |                           Just (Right t) -> canDiscard <$> kindcheck t >>= \case
-- XXX |                             True -> return ()
-- XXX |                             False -> typeError $ ObservedVariableRemainsUnused v

letBang :: [VarName] -> TC TypedExpr -> TC TypedExpr
letBang [] a = a
letBang (x:xs) a = letBang' x (letBang xs a)

letBang' :: VarName -> TC TypedExpr -> TC TypedExpr
letBang' x a = do
  te <- lookup x <$> use context >>= \case
          Nothing -> typeError (NotInScope x)
          Just (Left l) -> typeError (VariableAlreadyUsed l x)
          Just (Right t) -> bracketTE (context %= updateAssoc x (Right (RT (TBang t))))
                                      (const $ context %= updateAssoc x (Right t))
                                      (const a)
  k <- kindcheck (typeOfTE te)
  when (not $ canEscape k) $ typeError (BindingCannotEscapeLetBang x te)
  return te

-- First use typeWHNF to check for well-formedness, then this function returns
-- the kind of the input type
kindcheck :: RawType -> TC Kind
kindcheck tau = typeWHNF tau >>= \case
  (RT (TCon cn ts s)) -> mapM kindcheck ts >> return (sigilKind s)
  (RT (TUnit))  -> return (K True True True)
  (RT (TTuple ts)) -> mconcat <$> mapM kindcheck ts
  (RT (TVariant ts)) -> fold <$> mapM ((mconcat <$>) . mapM kindcheck) ts
  (RT (TRecord fs s)) -> (mappend $ sigilKind s) . mconcat <$> mapM (kindcheck . fst . snd) (filter (not . snd .snd) fs)  -- only untaken fields count
  (RT (TFun a b)) -> kindcheck a >> kindcheck b >> return (K True True True)
  (RT (TVar v b)) -> lookup v <$> use kindContext >>= \case
     Nothing -> typeError (TypeVariableNotInScope v)
     Just k -> return $ (if b then bangKind else id) k
  notInWHNF -> __impossible "kindcheck"

-- Well-formedness check. Output is in WHNF.
typeWHNF :: RawType -> TC RawType
typeWHNF x@(RT (TCon cn ts s)) = lookup cn <$> use knownTypes >>= \case
  Nothing -> typeError (TypeNotFound x)
  Just (vs,Just t) -> do when (length ts /= length vs) $
                           typeError (IncorrectNumberOfTypeParameters cn (length vs) (length ts))
                         typeWHNF (substType (zip vs ts) t)
  Just (vs,Nothing) -> do when (length ts /= length vs) $
                            typeError (IncorrectNumberOfTypeParameters cn (length vs) (length ts))
                          return x
typeWHNF x@(RT (TVar {})) = return x
typeWHNF x@(RT (TFun {})) = return x
typeWHNF x@(RT (TRecord fts s)) = go (map fst fts) >> return x
  where go :: [FieldName] -> TC ()
        go [] = return ()
        go (f:fs) = if f `elem` fs then typeError (DuplicateFieldName x f)
                                   else go fs
typeWHNF x@(RT (TVariant {})) = return x
typeWHNF   (RT (TTuple [])) = __impossible "typeWHNF"
typeWHNF   (RT (TTuple [t])) = __impossible "typeWHNF"
typeWHNF x@(RT (TTuple [t1,t2])) | not __cogent_ftuples_as_sugar = return x  -- make n-tuples into nested 2-tuples
typeWHNF   (RT (TTuple (t:ts@(_:_:_)))) | not __cogent_ftuples_as_sugar = typeWHNF (RT $ TTuple ts) >>= \ts' -> return $ RT $ TTuple [t,ts']
-- typeWHNF x@(RT (TTuple (reverse -> (t:ts)))) = case t of
--   (RT (TTuple ts')) -> typeWHNF (RT . TTuple $ reverse ts ++ ts')
--   _ -> return x
typeWHNF x@(RT (TTuple _)) = return x  -- | __cogent_ftuples_as_sugar
typeWHNF x@(RT (TUnit)) = return x
typeWHNF x@(RT (TUnbox t)) = typeWHNF t >>= \case
  RT (TCon cn ts s) -> return $ RT (TCon cn ts Unboxed)
  RT (TRecord fs s) -> return $ RT (TRecord fs Unboxed)
  x -> typeError (NotARecord x)
typeWHNF (RT (TBang t)) = bangType <$> typeWHNF t
typeWHNF (RT (TTake Nothing t)) = typeWHNF t >>= \case  -- take all untaken fields
  RT (TRecord fs s) -> return $ RT $ TRecord (map (second . second $ const True) fs) s
  x -> typeError (NotARecord x)
typeWHNF (RT (TTake (Just []) t)) = typeWHNF t
typeWHNF (RT (TTake (Just fs) t)) = typeWHNF t >>= \case  -- take untaken fields
  -- (T take fs) take fs': fs are firstly taken, then fs' (although commutative & associative)
  x@(RT (TRecord rs s)) -> x `canTakeFields` fs
  x -> typeError (NotARecord x)
typeWHNF (RT (TPut Nothing t)) = typeWHNF t >>= \case  -- put (a) taken linear fields (b) untaken discardable fields
  RT (TRecord fs s) -> return $ RT $ TRecord (map (second . second $ const False) fs) s
  x -> typeError (NotARecord x)
typeWHNF (RT (TPut (Just []) t)) = typeWHNF t
typeWHNF (RT (TPut (Just fs) t)) = typeWHNF t >>= \case
  x@(RT (TRecord rs s)) -> x `canPutFields` fs
  x -> typeError (NotARecord x)

-- NOTE: assumes WHNF; this function doesn't check the sigil, it only talks about fields
-- Returns the type of the field to be taken
canTakeField :: RawType -> FieldName -> TC RawType
canTakeField r@(RT (TRecord rs s)) f
  | Just (tau,taken) <- lookup f rs = if taken then typeError (RecordFieldTaken r f)
                                               else return tau
  | otherwise               = typeError (RecordTypeMissingField r f)
canTakeField r _ = typeError (NotARecord r)

-- NOTE: assumes WHNF
canTakeFields :: RawType -> [FieldName] -> TC RawType
canTakeFields r [] = return r
canTakeFields r@(RT (TRecord rs s)) (f:fs) = do
   r `canTakeField` f
   -- NOTE: Cannot use `typeWHNF' here, which will lead to non-termination!
   --       This case serves as the basecase for `typeWHNF' / zilinc
   (RT $ TRecord (map (\ft@(f',(t,x)) -> if f' == f then (f,(t,True)) else ft) rs) s) `canTakeFields` fs
canTakeFields _ _ = __impossible "canTakeFields"

-- NOTE: assumes WHNF. anologous to `canTakeField'
canPutField :: RawType -> FieldName -> TC RawType
canPutField r@(RT (TRecord rs s)) f
  | Just (tau,taken) <- lookup f rs
      = if taken then return tau
                 else do b <- canDiscard <$> kindcheck tau
                         if b then return tau else typeError (RecordFieldUntaken r f)
  | otherwise = typeError (RecordTypeMissingField r f)
canPutField r _ = typeError (NotARecord r)

canPutFields :: RawType -> [FieldName] -> TC RawType
canPutFields r [] = return r
canPutFields r@(RT (TRecord rs s)) (f:fs) = do
  r `canPutField` f
  (RT $ TRecord (map (\ft@(f',(t,x)) -> if f' == f then (f,(t,False)) else ft) rs) s) `canPutFields` fs
canPutFields _ _ = __impossible "canPutFields"

substType :: [(VarName, RawType)] -> RawType -> RawType
substType sigma (RT (TVar v b)) | Just t <- lookup v sigma = t
                                | otherwise = RT (TVar v b)
substType sigma (RT (TFun a b)) = RT (TFun (substType sigma a) (substType sigma b))
substType sigma (RT (TRecord fs s)) = RT (TRecord (map (second . first $ substType sigma) fs) s)
substType sigma (RT (TVariant fs)) = RT (TVariant (fmap (fmap $ substType sigma) fs))
substType sigma (RT (TUnit)) = RT TUnit
substType sigma (RT (TTuple fs)) = RT (TTuple (map (substType sigma) fs))
substType sigma (RT (TUnbox t)) = RT (TUnbox $ substType sigma t)
substType sigma (RT (TBang t)) = RT (TBang $ substType sigma t)
substType sigma (RT (TTake fs t)) = RT (TTake fs (substType sigma t))
substType sigma (RT (TPut  fs t)) = RT (TPut  fs (substType sigma t))
substType sigma (RT (TCon c ts s)) = RT (TCon c (map (substType sigma) ts) s)

-- NOTE: assumes WHNF, output is also WHNF
bangType :: RawType -> RawType
bangType (RT (TVar v _)) = RT (TVar v True)
bangType (RT (TRecord fs s)) = RT (TRecord (map (second . first $ RT . TBang) fs) $ bangSigil s)
bangType (RT (TCon x ts s))= RT (TCon x (map (RT . TBang) ts) $ bangSigil s)
bangType (RT TUnit) = RT TUnit
bangType (RT (TFun a b)) = RT (TFun a b)
bangType (RT (TTuple ts)) = RT (TTuple (map (RT . TBang) ts))  -- using `RT . TBang' instead of `bangType' for better errmsgs
bangType (RT (TVariant ts)) = RT (TVariant (fmap (fmap $ RT . TBang) ts))
bangType notInWHNF = __impossible "bangType"

-- XXX | -- FIXME: `l' is not used. We could use it if we had type-context / zilinc
-- XXX | wellformedType :: LocType -> TC RawType
-- XXX | wellformedType (LocType l t) = case t of
-- XXX |     TRecord fs -> RT . TRecord <$> (zip <$> go (map fst fs) <*> mapM (wellformedType . snd) fs)
-- XXX |     TUnboxedRecord fs -> let (ns, ts) = unzip fs
-- XXX |                          in RT . TUnboxedRecord <$> (zip <$> go ns <*> mapM wellformedType ts)
-- XXX |     _ -> RT <$> mapM wellformedType t
-- XXX |   where go :: [FieldName] -> TC [FieldName]
-- XXX |         go [] = return []
-- XXX |         go (x:xs) = if x `elem` xs then typeError (DuplicateFieldName (RT $ fmap stripLocT t) x)
-- XXX |                                    else (x:) <$> go xs

-- This function performs well-formedness check and kindcheck
validateType :: LocType -> TC RawType
validateType ((tunePrim . stripLocT) -> t) = kindcheck t >> return t

tunePrim :: RawType -> RawType
tunePrim (RT (TCon cn ts s))
  | cn `elem` primTypeCons, ts == [] = RT (TCon cn ts Unboxed)
tunePrim (RT t) = RT $ fmap tunePrim t

applyTypes :: Polytype RawType -> [RawType] -> TC RawType
applyTypes (PT sig rt) rts
  | length sig == length rts = let go (v,k) t = do k' <- kindcheck t
                                                   if (k' `satisfies` k)
                                                     then return (v,t)
                                                     else typeError $ KindError t k k'
                                in flip substType rt <$> zipWithM go sig rts
  | otherwise = typeError (IncorrectNumberOfTypeArguments (PT sig rt) (length rts))

satisfies :: Kind -> Kind -> Bool
satisfies a b = a <> b == b

parallel :: TC a -> (a -> TC b) -> TC b
parallel a b = do x <- use context
                  a' <- a
                  xa <- use context
                  context .= x
                  b' <- b a'
                  xb <- use context
                  zipWithM matchContext xa xb
                  return b'
  where matchContext a' b' | a' == b' = return ()
        matchContext (var, Left _) (var', Left _) | var == var' = return ()
        matchContext (var, Right t) (var', Left p) | var == var'
             = typeError (VariableUsedOnlyOnOneSide var t p)
        matchContext (var, Left p) (var', Right t) | var == var'
             = typeError (VariableUsedOnlyOnOneSide var t p)
        matchContext a b = error $ "impossibru matchContext" ++ show (a,b)

parallel' :: TC a -> TC b -> TC (a,b)
parallel' a b = parallel a (\a' -> fmap ((,) a') b)

-- NOTE: this function no more uses `typeDNF', which should generate better errmsgs
lub :: RawType -> RawType -> TC RawType
lub a' b' = (,) <$> fmap unwrap (typeWHNF a') <*> fmap unwrap (typeWHNF b') >>= \case
  (a,b) | a == b -> return $ RT a
  (TCon a [] s1, TCon b [] s2) | s1 == s2, a <: b -> return $ RT $ TCon b [] s1
                               | s1 == s2, b <: a -> return $ RT $ TCon a [] s1
  (TCon a ts s1, TCon b us s2) | s1 == s2, a == b, length ts == length us
                                 -> zipWithM lub ts us >>= \ws -> return (RT $ TCon a ws s1)
  (TFun ta ta', TFun tb tb') -> do ti <- lub ta  tb
                                   to <- lub ta' tb'
                                   return . RT $ TFun ti to
  (TRecord fs s1, TRecord gs s2) | s1 == s2, length fs == length gs
                                 , (ns,(ts,xs)) <- second unzip $ unzip fs
                                 , (ms,(us,ys)) <- second unzip $ unzip gs
                                 , ns == ms, xs == ys
                                   -> zipWithM lub ts us >>= \hs ->
                                        return . RT $ TRecord (zip ns (zip hs xs)) s1
  (TVariant as, TVariant bs) -> let leftBiased = M.unionWith const as bs
                                    rightBiased = M.unionWith (const id) as bs
                                    kvs = M.toList $ M.intersectionWith (,) leftBiased rightBiased
                                 in (forM kvs $ \(k,(vs1,vs2)) -> do
                                      when (length vs1 /= length vs2) $ typeError $ VariantsHaveDifferentNumOfTypes k vs1 vs2
                                      (k,) <$> mapM (uncurry lub) (zip vs1 vs2)
                                    ) <&> (RT . TVariant . M.fromList)
  (TTuple as, TTuple bs) | length as == length bs -> RT . TTuple <$> zipWithM lub as bs
  _ -> typeError $ CannotFindCommonSupertype a' b'
 where unwrap (RT x) = x

(<:) :: TypeName -> TypeName -> Bool
"U8"  <: "U16" = True
"U8"  <: "U32" = True
"U8"  <: "U64" = True
"U16" <: "U32" = True
"U16" <: "U64" = True
"U32" <: "U64" = True
_     <: _     = False

-- Avoid using. Gives bad error messages and is slow
typeDNF :: RawType -> TC RawType
typeDNF t = typeWHNF t >>= \case
  (RT (TCon c as s)) -> RT <$> (TCon c <$> mapM typeDNF as <*> pure s)
  (RT (TFun a b)) -> RT <$> (TFun <$> typeDNF a <*> typeDNF b)
  (RT (TRecord fs s)) -> let (fs',(ts,xs)) = second unzip $ unzip fs
                          in RT <$> (TRecord <$> (zip fs' <$> (flip zip xs <$> mapM typeDNF ts)) <*> pure s)
  (RT (TVariant mts)) -> let (vs',ts) = unzip (M.toList mts)
                          in RT . TVariant . M.fromList . zip vs' <$> mapM (mapM typeDNF) ts
  (RT (TTuple ts)) -> RT . TTuple <$> mapM typeDNF ts
  x -> return x

-- FIXME: use `typeWHNF' instead to get better errmsgs / zilinc
-- If `proper' is True, then return if a' is a proper subtype of b'
isSubtype :: Bool -> RawType -> RawType -> TC Bool
isSubtype proper a' b' = (,) <$> fmap unwrap  (typeDNF a') <*> fmap unwrap (typeDNF b') >>= \case
  (a,b) | a == b -> if proper then return False else return True
  (TCon a [] s1,TCon b [] s2) | s1 == s2 -> return $ a <: b   -- int subtyping
  p@(TVariant as, TVariant bs)                                -- variant subtyping
    | all (`elem` M.keys bs) (M.keys as) -> do  -- all as'es keys are in bs
      bools <- forM (M.keys as) $ \a -> let Just ta = M.lookup a as
                                            Just tb = M.lookup a bs
                                         in and <$> zipWithM (isSubtype False) ta tb
      return (and bools)
    | otherwise -> return False
  (TTuple as, TTuple bs) | length as == length bs -> and <$> zipWithM (isSubtype False) as bs  -- tuple subtyping.
  -- NOTE: we now allow the same in unboxed records / zilinc
  (TRecord fs1 Unboxed, TRecord fs2 Unboxed)
    | length fs1 == length fs2
    , fs1' <- M.fromList fs1, fs2' <- M.fromList fs2
    , and $ zipWith ((==) `on` fst) fs1 fs2 -> do
    bools <- forM (M.keys fs1') $ \f -> let Just (ta,_) = M.lookup f fs1'
                                            Just (tb,_) = M.lookup f fs2'
                                         in isSubtype False ta tb
    return (and bools)
  _ -> return False
 where unwrap (RT x) = x

checkedPromote :: RawType -> TypedExpr -> TC TypedExpr
checkedPromote t e = isSubtype False (typeOfTE e) t >>= \case
  True  -> promote t e
  False -> typeError (NotASubtype t e)

isIntLit :: TypedExpr -> Bool
isIntLit (TE _ (IntLit _)) = True
isIntLit _ = False

isCon :: TypedExpr -> Bool
isCon (TE _ (Con _ _)) = True
isCon _ = False

promote :: RawType -> TypedExpr -> TC TypedExpr
promote t e@(TE te _) = inEContext (InExpressionOfType (dummyLocE $ toRawExp e) te) $ do
                           t'  <- typeWHNF t
                           te' <- typeWHNF te
                           b <- isSubtype True te' t'
                           if b then promote' t' e else return e
  where -- NOTE: assume t is WHNF and promotion is always going to happen
        promote' :: RawType -> TypedExpr -> TC TypedExpr
        promote' t (TE te (PrimOp opr [e])) = TE t <$> (PrimOp opr <$> mapM (promote t) [e])
        promote' t (TE te (PrimOp opr [e1,e2])) = TE t <$> (PrimOp opr <$> mapM (promote t) [e1,e2])
        promote' t (TE te (Match e vs alts)) = TE t <$> (Match e vs <$> promoteAlts t alts)
        promote' t (TE te (Con cn es)) = let RT (TVariant alts)  = t
                                             RT (TVariant altes) = te
                                         in if M.size alts > M.size altes
                                              then  -- width
                                                let altes' = flip M.mapWithKey altes (\k _ -> let Just v' = M.lookup k alts in v')  -- a shorter one with big types
                                                in Promote t <$> promote (RT $ TVariant altes') (TE te $ Con cn es)
                                              else  -- depth
                                                let Just ts' = M.lookup cn alts
                                                in Promote t <$> (TE (RT $ TVariant $ M.singleton cn ts') <$> (Con cn <$> zipWithM promote ts' es))
        promote' t (TE te (Seq e1 e2)) = TE t <$> (Seq e1 <$> promote t e2)
        promote' t (TE te (If c vs th el)) = TE t <$> (If c vs <$> promote t th <*> promote t el)
        promote' t (TE te (Tuple es)) = TE t <$> (Tuple <$> zipWithM promote ts es) where RT (TTuple ts) = t
        promote' t (TE te (UnboxedRecord fs)) = TE t <$> (UnboxedRecord <$> zipWithM (\t' (n,e) -> (n,) <$> promote t' e) ts fs)
          where RT (TRecord rs Unboxed) = t
                ts = map (fst . snd) rs
        promote' t (TE te (Let bs e)) = TE t <$> (Let bs <$> promote t e)
        promote' t (Promote {}) = __impossible "promote' (in promote)"
        promote' _ (TypeErrorHappened {}) = __impossible "promote' (in promote)"
        promote' t e | isIntType t || isVariantType t = do
          when (isIntType t && not (isIntLit e) && __cogent_wimplicit_int_lit_promotion) (warning $ ImplicitCastPrimInt e (typeOfTE e) t)
          if __cogent_fshare_variants
            then when (isVariantType t && not (isCon e)) (typeError $ DynamicVariantPromotionE e (typeOfTE e) t)
            else when (isVariantType t && not (isCon e) && __cogent_wdynamic_variant_promotion) (warning $ DynamicVariantPromotionW e (typeOfTE e) t)
          return $ Promote t e  -- leaf (we can have nested Promotes, due to lack of depth subtyping)
        promote' t e = typeError $ CannotPromote t e
promote t (Promote _ e) = promote t e
promote t _ = __impossible "promote"

promoteAlt :: RawType -> Alt TypedName TypedExpr -> TC (Alt TypedName TypedExpr)
promoteAlt t (Alt p l e) = Alt p l <$> promote t e

checkedPromoteAlts :: RawType -> RawType -> [Alt TypedName TypedExpr] -> TC [Alt TypedName TypedExpr]
checkedPromoteAlts t t' as = isSubtype False t' t >>= \case
   True -> promoteAlts t as
   False -> typeError (NotASubtypeAlts t' t)

promoteAlts :: RawType -> [Alt TypedName TypedExpr] -> TC [Alt TypedName TypedExpr]
promoteAlts t = mapM $ promoteAlt t

deLocInfer :: LocExpr -> (SourcePos -> Expr LocType VarName LocExpr -> TC a) -> TC a
deLocInfer (LocExpr l e) f = inEContext (InExpression (LocExpr l e)) $ f l e

deLocCheck :: LocExpr -> RawType -> (SourcePos -> Expr LocType VarName LocExpr -> TC a) -> TC a
deLocCheck (LocExpr l e) tau f = inEContext (InExpressionOfType (LocExpr l e) tau) $ f l e

inferAlt :: RawType -> Alt VarName LocExpr -> TC (Maybe RawType, RawType, Alt TypedName TypedExpr)
inferAlt rt (Alt pat l e) = do
  (pat',rt') <- matchPattern pat =<< typeWHNF rt
  let vs = toList pat'
  go $ map fst vs
  e' <- withBinds vs $ infer e
  return (rt', typeOfTE e', Alt pat' l e')
  where go :: [VarName] -> TC ()
        go [] = return ()
        go (x:xs) = if x `elem` xs then typeError (ConflictingDeclarations pat x)
                                   else go xs

inferAlts :: Int -> RawType -> [Alt VarName LocExpr] -> TC (RawType, [Alt TypedName TypedExpr])
inferAlts _  _ [] = __impossible "inferAlts"
inferAlts i tau [alt@(Alt p _ _)] = (if i /= 1 then inEContext (NthAlternative i p) else id) (inferAlt tau alt) >>= \case
    (Just tau',_,_)    -> typeError (NonExhaustivePattern tau')
    (Nothing, rho, x') -> return (rho,[x'])
inferAlts i tau (x@(Alt p _ _):xs) =
  parallel (inEContext (NthAlternative i p) (inferAlt tau x)) $ \case
    (Nothing, _ , _)      -> typeError (SpuriousAlternatives xs)
    (Just rest, rho1, x') -> do
      (rho2, xs') <- inferAlts (succ i) rest xs
      rho <- rho1 `lub` rho2
      (rho,) <$> ((:) <$> promoteAlt rho x' <*> promoteAlts rho xs')

-- NOTE: assumes WHNF
-- Returns (typed pattern, the type that hasn't been matched)
--   snd in the pair is for exhausivity check
matchPattern :: Pattern VarName -> RawType -> TC (Pattern TypedName, Maybe RawType)
matchPattern (PCon c irps) (RT (TVariant vs))
           | Just taus' <- M.lookup c vs = mapM typeWHNF taus' >>= \taus ->
               (,newType) . PCon c <$> zipWithM matchIrrefPattern irps taus
  where newType = let m' = M.delete c vs
                   in if M.null m' then Nothing
                                   else Just (RT (TVariant m'))
matchPattern (PIntLit i) (RT (TCon x [] s))
-- NOTE: now it's done in parser / zilinc
-- XXX | NOTE: parser assigns Writable as the sigil, here we introduce proper sigils for prim-ints / zilinc
  | x `elem` ["U8","U16","U32","U64"]  = return (PIntLit i , Just $ RT $ TCon x [] Unboxed)
matchPattern (PCharLit c) (RT (TCon "Char" [] s)) = return (PCharLit c, Just $ RT $ TCon "Char" [] Unboxed)
matchPattern (PBoolLit b) (RT (TCon "Bool" [] s)) = return (PBoolLit b, Just $ RT $ TCon "Bool" [] Unboxed)
matchPattern (PIrrefutable irp) tau = (,Nothing) . PIrrefutable <$> matchIrrefPattern irp tau
matchPattern p tau = typeError $ PatternDoesNotMatchType p tau

-- NOTE: assumes WHNF
matchIrrefPattern :: IrrefutablePattern VarName -> RawType -> TC (IrrefutablePattern TypedName)
matchIrrefPattern (PVar v) t = return $ PVar (v,t)
matchIrrefPattern p@(PTuple _) (RT (TTuple ts)) | not __cogent_ftuples_as_sugar = do
  let PTuple ps = pTupleWHNF p
  __assert (length ps == length ts) "matchIrrefPattern: |ps| /= |ts|"
  fmap PTuple . zipWithM matchIrrefPattern ps =<< mapM typeWHNF ts
  where pTupleWHNF (PTuple (p:ps@(_:_:_))) = PTuple [p, pTupleWHNF $ PTuple ps]
        pTupleWHNF x@(PTuple _) = x
        pTupleWHNF _ = __impossible "pTupleWHNF (in matchIrrefPattern)"
matchIrrefPattern (PTuple ps) (RT (TTuple ts)) | length ps == length ts =  -- | __cogent_ftuples_as_sugar
  fmap PTuple . zipWithM matchIrrefPattern ps =<< mapM typeWHNF ts
-- matchIrrefPattern p@(PTuple _) (RT (TTuple ts)) | PTuple ps <- pTupleWHNF' p, length ps == length ts =
--   fmap PTuple . zipWithM matchIrrefPattern ps =<< mapM typeWHNF ts
--   where pTupleWHNF' :: IrrefutablePattern VarName -> IrrefutablePattern VarName
--         pTupleWHNF' (PTuple []) = __impossible "pTupleWHNF' (in matchIrrefPattern"
--         pTupleWHNF' (PTuple [p]) = __impossible "pTupleWHNF' (in matchIrrefPattern)"
--         pTupleWHNF' x@(PTuple (reverse -> (p:ps))) = case p of
--           PTuple ps' -> pTupleWHNF' $ PTuple $ reverse ps ++ ps'; _ -> x
--         pTupleWHNF' _ = __impossible "pTupleWHNF' (in matchIrrefPattern)"
matchIrrefPattern (PUnderscore) tau = canDiscard <$> kindcheck tau >>= \case
                                        True -> return PUnderscore
                                        False -> typeError (CannotDiscardValue tau)
matchIrrefPattern PUnitel (RT TUnit) = return PUnitel
matchIrrefPattern (PUnboxedRecord []) _ = __impossible "matchIrrefPattern"
matchIrrefPattern p@(PUnboxedRecord ips) rt@(RT (TRecord ts Unboxed)) | Nothing <- last ips = do
  let ipsInit = init ips
      ts' = filter ((`notElem` (map (fst . fromJust) ipsInit)) . fst) ts  -- everything not explicitly mentioned
  -- Give a warning if ts' overlaps with the current context
  forM_ (map fst ts') $ \f -> (f `lookup`) <$> use context >>= \case
                          Just _ -> warning (VariableAlreadyInScope f p)
                          Nothing -> return ()
  matchIrrefPattern (PUnboxedRecord $ ipsInit ++ map (Just . (id &&& PVar) . fst) ts') rt
matchIrrefPattern (PUnboxedRecord (map fromJust -> ips)) rt@(RT (TRecord ts Unboxed))
  | (fs,_) <- unzip ips, (ns,_) <- unzip ts, fs == ns =
      return . PUnboxedRecord =<< (
      forM ips $ \(f, ip) -> do
        tau <- rt `canTakeField` f
        ip' <- matchIrrefPattern ip =<< typeWHNF tau
        return $ Just (f,ip'))
matchIrrefPattern (PTake rv []) rt = matchIrrefPattern (PVar rv) rt
matchIrrefPattern p@(PTake rv ips) rt@(RT (TRecord ts s)) | Nothing <- last ips , s /= ReadOnly = do
      let ipsInit = init ips
          -- get the ones that are not taken and also not explicitly mentioned
          ts' = filter ((`notElem` (map (fst . fromJust) ipsInit)) . fst) $ filter (not . snd . snd) ts
      forM_ (map fst ts') $ \f -> (f `lookup`) <$> use context >>= \case
                              Just _ -> warning (VariableAlreadyInScope f p)
                              Nothing -> return ()
      matchIrrefPattern (PTake rv $ ipsInit ++ map (Just . (id &&& PVar) . fst) ts') rt
matchIrrefPattern (PTake rv (map fromJust -> ips)) rt@(RT (TRecord ts s)) | s /= ReadOnly = do
  (ips', rt') <- flip runStateT rt $ forM ips $ \(f,ip) -> do
    tau <- lift . (`canTakeField` f) =<< get
    ip' <- lift (matchIrrefPattern ip =<< typeWHNF tau)
    get >>= lift . typeWHNF . RT . TTake (Just [f]) >>= put
    return $ Just (f,ip')
  return (PTake (rv,rt') ips')
matchIrrefPattern x y = typeError (IrrefPatternDoesNotMatchType x y)

withIrrefPattern :: IrrefutablePattern VarName -> RawType -> TC a
                 -> TC (IrrefutablePattern TypedName, a)
withIrrefPattern pat tau a = do
   pat' <- matchIrrefPattern pat =<< typeWHNF tau
   x <- withBinds (toList pat') a
   return (pat',x)

tcBinding :: Binding LocType VarName LocExpr -> TC a
          -> TC (Binding RawType TypedName TypedExpr, a)
tcBinding (Binding pat Nothing e vs) a = do
   e' <- letBang vs (infer e)
   (pat', ret) <- withIrrefPattern pat (typeOfTE e') a
   ensureUsed vs
   return (Binding pat' (Just (typeOfTE e')) e' vs, ret)
tcBinding (Binding pat (Just t) e vs) a = do
   e' <- letBang vs . check e =<< validateType t
   (pat', ret) <- withIrrefPattern pat (typeOfTE e') a
   ensureUsed vs
   return (Binding pat' (Just (typeOfTE e')) e' vs, ret)

tcBindings :: [Binding LocType VarName LocExpr] -> TC a
           -> TC ([Binding RawType TypedName TypedExpr], a)
tcBindings [] a = ([],) <$> a
tcBindings (x:xs) a = do
  (x',(xs',ret)) <- tcBinding x (tcBindings xs a)
  return (x':xs',ret)

check :: LocExpr -> RawType -> TC TypedExpr
check locE tau = deLocCheck locE tau . check' =<< typeWHNF tau

-- NOTE: assumes WHNF. This function is only for WHNF-ing tuples / zilinc
check' :: RawType -> SourcePos -> Expr LocType VarName LocExpr -> TC TypedExpr
check' (RT (TTuple taus)) l x@(Tuple _) | not __cogent_ftuples_as_sugar = do
  let Tuple es = tupleWHNF x
  __assert (length es == length taus) "check': |es| /= |taus|"
  TE (RT (TTuple taus)) . Tuple <$> zipWithM check es taus
  where tupleWHNF (Tuple (e:es@(_:_:_))) = Tuple [e, LocExpr l $ tupleWHNF $ Tuple es]
        tupleWHNF x@(Tuple _) = x
        tupleWHNF _ = __impossible "tupleWHNF (in check')"
-- check' (RT (TTuple taus)) l x@(Tuple _) = do
--   let Tuple es = tupleWHNF' x
--   __assert (length es == length taus) "check': |es| /= |taus|"
--   TE (RT (TTuple taus)) . Tuple <$> zipWithM check es taus
--   where tupleWHNF' (Tuple []) = __impossible "tupleWHNF' (in check')"
--         tupleWHNF' (Tuple [_]) = __impossible "tupleWHNF' (in check')"
--         tupleWHNF' x@(Tuple (reverse -> (e:es))) = case e of
--           LocExpr _ (Tuple es') -> tupleWHNF' $ Tuple $ reverse es ++ es'
--           _ -> x
--         tupleWHNF' _ = __impossible "tupleWHNF' (in check')"
check' tau p e = suppressErrors tau (infer' p e >>= checkedPromote tau)

infer :: LocExpr -> TC TypedExpr
infer locE = deLocInfer locE infer'

infer' :: SourcePos -> Expr LocType VarName LocExpr -> TC TypedExpr
infer' p (Var vn) = resolveName p vn >>= \case
  Function _ -> infer' p $ TypeApp vn [] NoInline
  Value    t -> return $ TE t $ Var vn
-- CASE: tests/pass_debug.cogent (line (1) & (2))
infer' p (TypeApp fn@('_':_) ts note) | not __cogent_debug = typeError (DebugFunctionHasToBeApplied fn p)
infer' p (TypeApp fn ts note) = resolveName p fn >>= \case
  Value x -> typeError (NotAPolymorphicFunction fn x)
  Function q -> do ts' <- mapM validateType ts
                   tau <- applyTypes q ts'
                   return $ TE tau (TypeApp fn ts' note)
infer' _ (Con name es) = do es' <- mapM infer es
                            return $ TE (RT $ TVariant $ M.fromList [(name, map typeOfTE es')]) (Con name es')
infer' p' (App (LocExpr p (Var vn@('_':_))) e2) | not __cogent_debug = infer' p' $ App (LocExpr p $ TypeApp vn [] NoInline) e2
infer' _ (App (LocExpr p (TypeApp fn@('_':_) ts note)) e2) | not __cogent_debug = resolveName p fn >>= \case
  Value x -> typeError (NotAPolymorphicFunction fn x)
  Function q -> do ts' <- mapM validateType ts
                   tau <- applyTypes q ts'
                   RT (TFun t1 t2) <- typeDNF tau
                   -- CASE: tests/fail_ticket-93.cogent
                   canDiscard <$> kindcheck t1 >>= flip unless (typeError $ DebugFunctionCannotTakeLinear fn t1)
                   when (t2 /= RT TUnit) $ typeError (DebugFunctionReturnNoUnit fn)
                   e1' <- return $ TE tau (TypeApp fn ts' note)
                   return . TE t2 . App e1' =<< check e2 t1
infer' _ (App e1 e2) = do e1' <- infer e1
                          tau <- typeWHNF $ typeOfTE e1'
                          case tau of
                             RT (TFun t1 t2) -> return . TE t2 . App e1' =<< check e2 t1
                             _ -> typeError $ ValueNotAFunction e1' e2
infer' _ (If c vs t e) = do c' <- letBang vs $ check c (RT $ TCon "Bool" [] Unboxed)
                            (t', e') <- parallel' (infer t) (infer e)
                            tau <- typeOfTE t' `lub` typeOfTE e'
                            t'' <- promote tau t'
                            e'' <- promote tau e'
                            return (TE tau $ If c' vs t'' e'')
infer' _ (Unitel) = return (TE (RT $ TUnit) Unitel)
infer' _ (IntLit i) = return (TE (RT $ TCon minimumBitwidth [] Unboxed) $ IntLit i)
  where minimumBitwidth | i < 256        = "U8"
                        | i < 65536      = "U16"
                        | i < 4294967296 = "U32"
                        | otherwise      = "U64"
infer' _ (BoolLit b) = return (TE (RT boolType) $ BoolLit b)
infer' _ (CharLit c) = return (TE (RT $ TCon "U8" [] Unboxed) $ CharLit c)
infer' _ (StringLit s) = return (TE (RT $ TCon "String" [] Unboxed) $ StringLit s)  -- FIXME: really unboxed? / zilinc
infer' _ (Tuple [ ]) = __impossible "infer'"  -- unit
infer' _ (Tuple [_]) = __impossible "infer'"  -- singleton
infer' _ (Tuple [e1,e2]) | not __cogent_ftuples_as_sugar = do
  es' <- mapM infer [e1,e2]
  return $ TE (RT $ TTuple $ map typeOfTE es') (Tuple es')
infer' l (Tuple (e1:es@(_:_:_))) | not __cogent_ftuples_as_sugar = do
  e1' <- infer e1
  es' <- infer' l $ Tuple es
  return $ TE (RT $ TTuple [typeOfTE e1', typeOfTE es']) $ Tuple [e1',es']
-- infer' l (Tuple (reverse -> (e:es))) | LocExpr _ (Tuple es') <- e =
--   infer' l (Tuple $ reverse es ++ es')
infer' l (Tuple es) = do  -- | __cogent_ftuples_as_sugar
  es' <- mapM infer es
  return $ TE (RT $ TTuple $ map typeOfTE es') $ Tuple es'
infer' l e@(UnboxedRecord fs) = do ns <- go $ map fst fs
                                   ts <- mapM (infer . snd) fs
                                   return . TE (RT $ TRecord (zip ns $ zip (map typeOfTE ts) (repeat False)) Unboxed) $
                                     UnboxedRecord $ zip ns ts
  where go :: [FieldName] -> TC [FieldName]
        go [] = return []
        go (x:xs) = if x `elem` xs then typeError (DuplicateField (stripLocE $ LocExpr l e) x)
                                   else (x:) <$> go xs
infer' _ (Seq e1 e2) = do e1' <- infer e1
                          canDiscard <$> kindcheck (typeOfTE e1')
                            >>= flip unless (typeError $ CannotDiscardValue $ typeOfTE e1')
                          e2' <- infer e2
                          return $ TE (typeOfTE e2') (Seq e1' e2')
infer' _ (Match e vs alts) = do e' <- letBang vs (infer e)
                                (tau, alts') <- inferAlts 1 (typeOfTE e') alts
                                ensureUsed vs
                                return $ TE tau (Match e' vs alts')
infer' _ (Let bs e) = do (bs', e') <- tcBindings bs (infer e)
                         return $ TE (typeOfTE e') (Let bs' e')
infer' _ (Member e f) = do e' <- infer e
                           typeWHNF (typeOfTE e') >>= \case
                             tau@(RT (TRecord fs s)) -> do
                               canShare <$> kindcheck tau >>= \case
                                 True -> do
                                   ft <- tau `canTakeField` f  -- checks if f exists as a field
                                   return $ TE ft $ Member e' f
                                 False -> typeError (NotAShareableRecord tau)  -- not shareable
                             tau -> typeError (NotAShareableRecord tau)  -- not a record
infer' _ (Put e []) = __impossible "infer'"
infer' p (Put e as) | Nothing <- last as = do
  e' <- infer e
  et <- typeWHNF (typeOfTE e')
  case et of
    RT (TRecord fts s) -> do
      let taken = map fst $ filter (snd . snd) fts  -- all taken fields
      discd <- map fst <$> filterM (\ft -> canDiscard <$> kindcheck (fst $ snd ft)) fts  -- all discardable fields
      let canput = taken `L.union` discd
          asInit = map fromJust (init as)
          as_ = M.toList $ M.unionWith const  -- left-biased union
                                       (M.fromList asInit)
                                       (M.fromList $ map (id &&& LocExpr p . Var) taken)  -- mentioned and unmentioned taken fields
      (as',st) <- flip runStateT canput $ forM as_ $ \(f,x) -> do
        tau <- lift $ et `canPutField` f
        ch <- elem f <$> get
        unless ch $ lift $ typeError (FieldNotTaken f et)
        modify (delete f)
        x' <- lift $ check x tau
        return $ Just (f,x')
      let takeRemaining = map (\ft@(n,(t,x)) -> if n `elem` st then ft else (n,(t,False)))
      return $ TE (RT $ TRecord (takeRemaining fts) s) (Put e' as')
    _ -> typeError (NotARecord et)
infer' _ (Put e (map fromJust -> as)) = do
  e' <- infer e
  et <- typeWHNF (typeOfTE e')
  case et of
    RT (TRecord fts s) -> do
      let taken = map fst $ filter (snd . snd) fts  -- all taken fields
      discd <- map fst <$> filterM (\ft -> canDiscard <$> kindcheck (fst $ snd ft)) fts  -- all discardable fields
      let canput = taken `L.union` discd
      (as',st) <- flip runStateT canput $ forM as $ \(f,x) -> do
        tau <- lift $ et `canPutField` f
        ch <- elem f <$> get
        unless ch $ lift $ typeError (FieldNotTaken f et)
        modify (delete f)
        x' <- lift $ check x tau
        return $ Just (f,x')
      let takeRemaining = map (\ft@(n,(t,x)) -> if n `elem` st then ft else (n,(t,False)))
      return $ TE (RT $ TRecord (takeRemaining fts) s) (Put e' as')
    _ -> typeError (NotARecord et)
infer' _ (PrimOp o [e1,e2]) | o `elem` arithOperators ++ bitwiseOperators = do
  e1' <- infer e1
  e2' <- infer e2
  tau <- typeOfTE e1' `lub` typeOfTE e2'
  unless (unRT tau `elem` numericTypes)
     $ typeError (NonNumericType tau)
  e1'' <- promote tau e1'
  e2'' <- promote tau e2'
  return (TE tau (PrimOp o [e1'',e2'']))
infer' _ (PrimOp o [e1,e2]) | o `elem` comparisonOperators = do
  e1' <- infer e1
  e2' <- infer e2
  tau <- typeOfTE e1' `lub` typeOfTE e2'
  unless (unRT tau `elem` numericTypes ||
          (unRT tau == boolType && o `elem` ["==", "/="]))
     $ typeError (NonNumericType tau)
  e1'' <- promote tau e1'
  e2'' <- promote tau e2'
  return (TE (RT boolType) (PrimOp o [e1'',e2'']))
infer' _ (PrimOp o [e1,e2]) | o `elem` booleanOperators = do
  e1' <- check e1 (RT boolType)
  e2' <- check e2 (RT boolType)
  return (TE (RT boolType) (PrimOp o [e1',e2']))
infer' _ (PrimOp "not" [e1]) = do
  e1' <- check e1 (RT boolType)
  return (TE (RT boolType) (PrimOp "not" [e1']))
infer' _ (PrimOp "complement" [e1]) = do
  e1'@(TE tau _) <- infer e1
  unless (unRT tau `elem` numericTypes)
     $ typeError (NonNumericType tau)
  return (TE tau (PrimOp "complement" [e1']))
infer' _ (PrimOp _ _) = __impossible "infer'"

arithOperators, bitwiseOperators, booleanOperators, comparisonOperators :: [String]
arithOperators = words "* / % + -"
bitwiseOperators = words ".&. .^. .|. >> <<"
booleanOperators = words "&& ||"
comparisonOperators = words ">= <= > < == /="

numericTypes = [ TCon n [] Unboxed | n <- ["U8", "U16", "U32", "U64"] ]
boolType = TCon "Bool" [] Unboxed

withKindVars :: [(VarName, Kind)] -> TC a -> TC a
withKindVars vs a = bracketTE (kindContext <.= vs) (kindContext .=) (const a)


typeOughtToBeUnknown :: VarName -> TC ()
typeOughtToBeUnknown n = lookup n <$> use knownTypes >>= \case
  Nothing -> return ()
  _       -> typeError (RedefinitionOfType n)

funOughtToBeUnknown :: VarName -> TC ()
funOughtToBeUnknown n = lookup n <$> use knownFuns >>= \case
  Nothing -> return ()
  _       -> typeError (RedefinitionOfFun n)

constOughtToBeUnknown :: VarName -> TC ()
constOughtToBeUnknown n = lookup n <$> use context >>= \case
  Nothing -> return ()
  _       -> typeError (RedefinitionOfConst n)

dupTyVarNames :: [TyVarName] -> Either TypeName (Polytype LocType) -> TC ()
dupTyVarNames [] ctx = return ()
dupTyVarNames (v:vs) ctx = if v `elem` vs then typeError (ConflictingTypeVariables v ctx) else dupTyVarNames vs ctx

typecheck' (Include _) = __impossible "typecheck'"
typecheck' (TypeDec n vs t) = do
  typeOughtToBeUnknown n
  dupTyVarNames vs (Left n)
  t' <- withKindVars (zip vs (repeat mempty)) (validateType t)
  knownTypes <>= [(n,(vs,Just t'))]
  return (TypeDec n vs t')
typecheck' (AbsTypeDec n vs) = do
  typeOughtToBeUnknown n
  dupTyVarNames vs (Left n)
  knownTypes <>= [(n,(vs,Nothing))]
  return (AbsTypeDec n vs)
typecheck' (AbsDec n pt@(PT vs t)) = do
  funOughtToBeUnknown n
  dupTyVarNames (map fst vs) (Right pt)
  t' <- withKindVars vs (validateType t)
  knownFuns <>= [(n, (PT vs t'))]
  typeWHNF t' >>= \case
    (RT (TFun a b)) -> do knownFuns <>= [(n, (PT vs (RT (TFun a b))))]
                          dnfb <- typeDNF b
                          when (not __cogent_debug && head n == '_' && dnfb /= RT TUnit) $ typeError (DebugFunctionReturnNoUnit n)
                          return (AbsDec n (PT vs t'))
    tau             -> typeError (FunDefNotOfFunType n tau)
typecheck' (FunDef n pt@(PT vs t) as) = do
  funOughtToBeUnknown n
  dupTyVarNames (map fst vs) (Right pt)
  withKindVars vs $ do
    t' <- validateType t
    typeWHNF t' >>= \case
      (RT (TFun a b)) -> do (b', as') <- inferAlts 1 a as
                            as'' <- checkedPromoteAlts b b' as'
                            knownFuns <>= [(n, (PT vs (RT (TFun a b))))]
                            dnfb <- typeDNF b
                            when (not __cogent_debug && head n == '_' && dnfb /= RT TUnit) $ typeError (DebugFunctionReturnNoUnit n)
                            return (FunDef n (PT vs (RT (TFun a b))) as'')
      tau             -> typeError (FunDefNotOfFunType n tau)
typecheck' (ConstDef n t e) = do
  constOughtToBeUnknown n  -- NOTE: this is not used, at least for now / zilinc
  t' <- validateType t
  e' <- check e t'
  x <- canShare <$> kindcheck t'
  when (not x) $ typeError (ConstantMustBeShareable n t')
  context <>= ([(n,Right t')])
  return (ConstDef n t' e')

typecheck :: [(SourcePos, TopLevel LocType VarName LocExpr)] -> TC [TopLevel RawType TypedName TypedExpr]
typecheck [] = return []
typecheck ((p,x):xs) = (:) <$> inEContext (InDefinition p x) (typecheck' x) <*> typecheck xs
