-- |
-- Module      : Minigent.Reorganiser
-- Copyright   : (c) Data61 2018-2019
--                   Commonwealth Science and Research Organisation (CSIRO)
--                   ABN 41 687 119 230
-- License     : BSD3
--
-- this compiler pass is responsible for taking the raw output of the parser
-- and processing it into something the rest of the compiler can understand.
--
-- Specifically, it alerts about duplicate definitions, warns about missing
-- type signatures, and does a pass over each expression to resolve
-- function names (which are indistinguishable from variables to the parser)
-- and check that the types mentioned in the expression only includes
-- in-scope polymorphic type variables.
--
-- May be used qualified or unqualified.
module Minigent.Reorganiser
  ( reorg
  , Error
  )
  where


import Minigent.Syntax
import Minigent.Syntax.Utils
import Minigent.Environment
import qualified Minigent.Syntax.Utils.Row as Row
import Minigent.Syntax.Utils (mapRecPars)

import Control.Monad.Trans.Writer.Strict
import qualified Data.Map as M
import qualified Data.Set as S
import Data.List (nub, (\\), intersperse )

type Error = String

sanityCheckType :: [VarName] -> Type -> Writer [Error] ()
sanityCheckType tvs t = do 
  let leftovers = nub (typeVariables t) \\ tvs
  let nsp = nonStrictlyPositiveVars t
  if leftovers /= [] then
    tell ["Type variables used unquantified:" ++ concat (intersperse ", " leftovers)]
  else if nsp /= [] then
    tell ["Recursive parameters occuring non-strictly positive: " ++ concat (intersperse ", " nsp)]
  else return ()

sanityCheckExpr :: GlobalEnvironments -> [VarName] -> [VarName] -> Expr -> Writer [Error] Expr
sanityCheckExpr envs tvs vs exp = check vs exp
  where
    check vs exp = case exp of 

      PrimOp o es  -> PrimOp o <$> mapM (check vs) es 

      Con cn e     -> Con cn <$> check vs e

      Var n        -> do
        if n `elem` vs 
          then pure exp
          else case M.lookup n (types envs) of 
                 Nothing -> tell ["Variable out of scope: " ++ n] >> pure exp
                 Just _  -> pure (TypeApp n [])

      TypeApp f ts -> do
        case M.lookup f (types envs) of 
          Nothing -> tell ["Function not defined: " ++ f] 
          Just (Forall qts _ _) -> do
            if length ts > length qts 
              then tell ["Too many type arguments given to: " ++ f]
              else mapM_ (sanityCheckType tvs) ts
        pure exp

      Sig e t -> do 
        sanityCheckType tvs t
        e' <- check vs e
        pure (Sig e' t)

      Apply e1 e2 -> Apply <$> check vs e1 <*> check vs e2

      Struct fs -> Struct <$> mapM (\(f,e) -> (,) f <$> check vs e) fs

      If e1 e2 e3 -> If <$> check vs e1 <*> check vs e2 <*> check vs e3

      Let v e1 e2 -> Let v <$> check vs e1 <*> check (v:vs) e2

      LetBang bvs v e1 e2 -> do 
        let leftovers = nub bvs \\ vs
        if null leftovers 
          then return ()
          else tell ["Let! applied to out of scope vars: " ++ concat (intersperse ", " leftovers)]
        LetBang bvs v <$> check vs e1 <*> check (v:vs) e2
   
      Take r f v e1 e2 -> Take r f v <$> check vs e1 <*> check (r:v:vs) e2 

      Put e1 f e2 -> Put <$> check vs e1 <*> pure f <*> check vs e2

      Case e c v1 e1 v2 e2 -> Case <$> check vs e
                                   <*> pure c <*> pure v1 <*> check (v1:vs) e1
                                   <*> pure v2 <*> check (v2:vs) e2 

      Esac e c v1 e1 -> Esac <$> check vs e
                             <*> pure c <*> pure v1 <*> check (v1:vs) e1

      Member e f     -> Member <$> check vs e <*> pure f

      e           -> pure e

reorganiseTopLevel :: RawTopLevel -> GlobalEnvironments -> Writer [Error] GlobalEnvironments
reorganiseTopLevel (TypeSig f pt@(Forall _ _ t)) envs = do 
  case M.lookup f (types envs) of 
    Just _ -> tell ["Duplicate type signature for " ++ f] 
    Nothing -> return ()
  -- Embed recursive parameters
  let pt'@(Forall tvs c t) = embedRecPars pt
  if nub tvs /= tvs
    then tell ["Duplicate quantified type variable in type signature for " ++ f] 
    else return ()
  sanityCheckType (nub tvs) t
  return (envs { types = M.insert f pt' (types envs) })

reorganiseTopLevel (Equation f x e) envs = do 
   case M.lookup f (defns envs) of 
        Just _ -> tell ["Duplicate equation of " ++ f] 
        Nothing -> return ()
   tvs <- case M.lookup f (types envs) of 
            Just (Forall tvs _ _) -> return tvs
            Nothing -> tell ["No type given for " ++ f] >> return []
   e' <- sanityCheckExpr envs tvs [x] e
   return (envs { defns = M.insert f (x,e') (defns envs) })

-- | Given a PolyType definition, changes all recursive parameter references from TypeVar to RecPar 
embedRecPars :: PolyType -> PolyType
embedRecPars (Forall vs cs t) = Forall vs cs $ erp False M.empty t
  where
    erp :: Bool -> M.Map RecParName Type -> Type -> Type
    erp b c (AbsType n s ts)    = AbsType n s $ map (erp b c) ts
    erp b c (Variant row)       = Variant $ Row.mapEntries (\(Entry n t tk) -> Entry n (erp b c t) tk) row
    erp b c (Bang t)            = Bang $ erp b c t 
    -- Check add (if it exists), the recursive parameter to the context
    erp b c r@(Record rp row s) = 
      Record rp (Row.mapEntries (\(Entry n t tk) -> Entry n (erp b (addRecPar rp) t) tk) row) s
      where addRecPar p = case p of
                            Rec v -> (M.insert v r c)
                            _ -> c
    erp b c (Function x y)      = Function (erp b c x) (erp b c y)
    -- Here, we insert `Nothing' if we are embedding a recursive parameter inside a context
    --   (indicated by `b'), and the context otherwise
    erp b c (TypeVar n) 
      | M.member n c = RecPar  n (if b then Nothing else Just (M.map (erp True c) c))
      | otherwise    = TypeVar n
    erp b c (TypeVarBang n) 
      | M.member n c = RecParBang  n (if b then Nothing else Just (M.map (erp True c) c))
      | otherwise    = TypeVarBang n

    erp _ _ t = t

-- | Checks that variables only occur strictly positive.
--   We check the argument and result of the function seperately so as not to
--   trigger the strictly positive case for everything that is an argument.
nonStrictlyPositiveVars :: Type -> [VarName] 
nonStrictlyPositiveVars t = sp t M.empty
  where
    -- Map if variables in scope are in argument position
    -- Bool is True if we are in the argument position of some function currently
    sp ::  Type -> M.Map RecParName Bool -> [VarName]
    sp (PrimType _)     m = []
    sp (AbsType _ _ ts) m = concatMap (\t -> sp t m) ts
    sp (Variant r)      m = 
      concatMap (\(Entry _ t _) -> sp t m) (Row.entries r)
    sp (Bang t)         m = sp t m

    -- Type variables have been replaced with embedded recursive parameters at this point
    sp (TypeVar v)     m = []
    sp (TypeVarBang v) m = []

    -- Records are special - only here can we pick up recursive parameters
    sp (Record rp r _) m =
      concatMap (\(Entry _ t _) -> sp t (addRecPar rp)) (Row.entries r)
      where addRecPar p = case p of
                            Rec v -> (M.insert v False m)
                            _ -> m

    -- Mark that we are in the argument position for all variables in the context
    sp (Function x y) m = 
      sp x (M.map (const True) m) ++ sp y m

    -- If we are in the argument position then return the recursive parameter name
    sp (RecPar n _) m
      | Just True <- M.lookup n m = [n]
      | otherwise                 = []
    sp (RecParBang n _) m
      | Just True <- M.lookup n m = [n]
      | otherwise                 = []
    
    sp _ _ = error "strictlyPositive"

reorganise :: [RawTopLevel] -> GlobalEnvironments -> Writer [Error] GlobalEnvironments
reorganise []     envs = return envs
reorganise (x:xs) envs = reorganise xs =<< reorganiseTopLevel x envs

reorg :: [RawTopLevel] -> (GlobalEnvironments, [Error])
reorg tls = runWriter (reorganise tls emptyGlobalEnvironments)
