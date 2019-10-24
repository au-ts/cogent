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

{- LANGUAGE AllowAmbiguousTypes -}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
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

module Cogent.C.Compile where

import           Cogent.C.Syntax       as C   hiding (BinOp (..), UnOp (..))
import qualified Cogent.C.Syntax       as C   (BinOp (..), UnOp (..))
import           Cogent.C.GenState
import           Cogent.Compiler
import           Cogent.Common.Syntax  as Syn
import           Cogent.Common.Types   as Typ
import           Cogent.Core           as CC
import           Cogent.Dargent.CodeGen       (genBoxedGetSetField, GetOrSet(..))
import           Cogent.Inference             (kindcheck_)
import           Cogent.Isabelle.Deep
import           Cogent.Mono                  (Instance)
import           Cogent.Normal                (isAtom)
import           Cogent.Util                  (behead, decap, extTup2l, extTup3r, first3, secondM, toCName, whenM, flip3)
import qualified Data.DList          as DList
import           Data.Nat            as Nat
import           Data.Vec            as Vec   hiding (repeat, zipWith)

import           Control.Applicative          hiding (empty)
import           Control.Arrow                       ((***), (&&&), second)
import           Control.Monad.RWS.Strict     hiding (mapM, mapM_, Dual, (<>), Product, Sum)
import           Data.Char                    (isAlphaNum, toUpper)
#if __GLASGOW_HASKELL__ < 709
import           Data.Foldable                (mapM_)
#endif
import           Data.Functor.Compose
import           Data.IntMap         as IM    (delete, mapKeys)
import qualified Data.List           as L
import           Data.Loc                     (noLoc)  -- FIXME: remove
import qualified Data.Map            as M
import           Data.Maybe                   (catMaybes, fromJust)
import           Data.Monoid                  ((<>))
-- import           Data.Semigroup.Monad
-- import           Data.Semigroup.Reducer       (foldReduce)
import qualified Data.Set            as S
import           Data.String
import           Data.Traversable             (mapM)
import           Data.Tuple                   (swap)
#if __GLASGOW_HASKELL__ < 709
import           Prelude             as P     hiding (mapM, mapM_)
#else
import           Prelude             as P     hiding (mapM)
#endif
import           System.IO (Handle, hPutChar)
import qualified Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>), (<>))
import           Lens.Micro                   hiding (at)
import           Lens.Micro.Mtl               hiding (assign)
import           Lens.Micro.TH
import           Control.Monad.Identity (runIdentity)
-- import Debug.Trace
import Unsafe.Coerce (unsafeCoerce)

recycleVars :: VarPool -> Gen v ()
recycleVars pool =
  use varPool >>= \pool' ->
  -- varPool .= M.unionWith (\vs1 vs2 -> L.nub (vs1 ++ vs2)) pool' pool
  varPool .= M.unionWith (\vs1 vs2 -> __assert (L.null $ L.intersect vs1 vs2) "recycleVars: found duplicates" >>
                                      (vs1 ++ vs2)) pool' pool

mergePools :: [VarPool] -> VarPool
mergePools = M.unionsWith (\vs1 vs2 -> L.nub (vs1 ++ vs2))

intersectPools :: VarPool -> VarPool -> VarPool
intersectPools = M.intersectionWith L.intersect


-- *****************************************************************************
-- * CodeGen front-end: from Core to the intermediate rep.

-- Generates `enum tag_t' and `tag_t'
genEnum :: Gen v [CExtDecl]
genEnum = do
  tdefs <- use cTypeDefs
  let enums = L.filter (\tdef -> case fst tdef of Variant _ -> True ; _ -> False) tdefs  -- get all variant types
  if null enums
    then return []
    else let tags = S.unions $ P.map ((\(Variant alts) -> S.map tagEnum $ M.keysSet alts) . fst) enums
             enumMembers = P.map (,Nothing) $ S.toList tags
         in return $ [CDecl $ CEnumDecl (Just tagsT) enumMembers, CDecl $ CTypeDecl (CEnum tagsT) [tagsT]]

-- NOTE: It's not used becuase it's defined in cogent-defns.h / zilinc
genBool :: Gen v [CExtDecl]
genBool = pure [ CDecl $ CStructDecl boolT [(CogentPrim U8, Just boolField)]
               , CDecl $ CTypeDecl (CStruct boolT) [boolT]]

-- NOTE: It's not used becuase it's defined in cogent-defns.h / zilinc
genUnit :: Gen v [CExtDecl]
genUnit = pure [ CDecl $ CStructDecl unitT [(CInt True CIntT, Just dummyField)]  -- NOTE: now the dummy field is an int for verification / zilinc
               , CDecl $ CTypeDecl (CStruct unitT) [unitT]]

genLetTrueEnum :: Gen v [CExtDecl]
genLetTrueEnum = mappend <$>
    (whenM __cogent_flet_in_if $ pure $ [CDecl $ CEnumDecl Nothing [(letTrue, Just one)]]) <*>
    (whenM __cogent_fletbang_in_if $ pure $ [CDecl $ CEnumDecl Nothing [(letbangTrue, Just one)]])
  where one = CConst $ CNumConst 1 (CInt True CIntT) DEC

genFunClasses :: Gen v ([CExtDecl], [TypeName])  -- NOTE: also returns a list of c-typenames that represents function types (for #63) / zilinc
genFunClasses = do funclasses <- use funClasses
                   let fas = S.unions $ M.elems funclasses
                       ufe = if __cogent_funtyped_func_enum && not (S.null fas) then genFunEnum untypedFuncEnum fas else []
                   fcls_tns <- forM (M.toList funclasses) $ \(t,fns) -> do
                                 tn <- getStrlTypeCId t
                                 let enum = if not __cogent_funtyped_func_enum
                                              then genFunEnum tn fns
                                              else [CDecl $ CTypeDecl (CIdent untypedFuncEnum) [tn]]
                                     Function ti to = t
                                 disp <- genFunDispatch tn (ti,to) fns
                                 return (enum ++ disp, tn)
                   return (ufe ++ concat (map fst fcls_tns), map snd fcls_tns)
  where genFunEnum :: CId -> S.Set (FunName, Attr) -> [CExtDecl]
        genFunEnum tn (S.toList -> s) =
          let fes = map (funEnum . fst) s
          in [CDecl $ CEnumDecl (Just tn) (map ((,Nothing)) fes), CDecl $ CTypeDecl (CEnum tn) [tn]]

genFunDispatch :: CId -> (CType, CType) -> S.Set (FunName, Attr) -> Gen v [CExtDecl]
genFunDispatch tn (ti, to) (S.toList -> fs) = do
  let tn' = if __cogent_funtyped_func_enum then untypedFuncEnum else tn
      disp = funDispatch tn
  localOracle .= 0
  r' <- freshLocalCId 'a'  -- return
  f' <- freshLocalCId 'a'  -- function
  x' <- freshLocalCId 'a'  -- arg
  let body fm = case fs of
                  []  -> __impossible "genFunDispatch"
                  [(f,a)] -> [CBIStmt $ genInnerFnCall fm a f r' x']
                  _   -> let alts' = flip map (init fs) $ \(f,a) ->
                                       let fncall = genInnerFnCall fm a f r' x'
                                        in (Just (variable $ funEnum f), genBreakWithFnCall fm fncall)
                             deft' = let (f,a) = last fs
                                         fncall = genInnerFnCall fm a f r' x'
                                      in (Nothing, genBreakWithFnCall fm fncall)  -- the last alt will be the `default' case
                          in [CBIStmt $ CSwitch (variable f') (alts'++[deft'])]
  return [CFnMacro (funDispMacro disp) [r',f',x'] [CBIStmt $ CBlock (body True)],  -- macro version
          CFnDefn (to,disp) [(CIdent tn',f'), (ti,x')] (body False) staticInlineFnSpec]  -- funct version
  where
    genInnerFnCall :: Bool -> Attr -> CId -> CId -> CId -> CStmt
    genInnerFnCall fm a f r x = if not fm
      then CReturnFnCall (variable f) [variable x]
      else if fnMacro a
        then CAssignFnCall Nothing (variable $ funMacro f) [variable r, variable x]
        else CAssignFnCall (Just $ variable r) (variable f) [variable x]
    genBreakWithFnCall :: Bool -> CStmt -> CStmt
    genBreakWithFnCall fm s = if fm then CBlock [CBIStmt s, CBIStmt CBreak] else s


-- Add a type synonym
addSynonym :: (CC.Type 'Zero -> Gen v CType) -> CC.Type 'Zero -> TypeName -> Gen v CType
addSynonym f t n = do t' <- f t
                      typeSynonyms %= M.insert n t'
                      return t'


-- (type of assignee/r, assignee, assigner)
assign :: CType -> CExpr -> CExpr -> Gen v ([CBlockItem], [CBlockItem])
assign (CArray t (CArraySize l)) lhs rhs = do
  (i,idecl,istm) <- declareInit u32 (mkConst U32 0) M.empty
  (adecl,astm) <- assign t (CArrayDeref lhs (variable i)) (CArrayDeref rhs (variable i))
  let cond = CBinOp C.Lt (variable i) l
      inc  = CAssign (variable i) (CBinOp C.Add (variable i) (mkConst U32 1))  -- i++
      loop = CWhile cond (CBlock $ astm ++ [CBIStmt inc])
  return (idecl ++ adecl, istm ++ [CBIStmt loop])
assign t lhs rhs = return ([], [CBIStmt $ CAssign lhs rhs])


-- Given a C type, returns a fresh local variable e
declare :: CType -> Gen v (CId, [CBlockItem], [CBlockItem])
declare ty = declareG ty Nothing

-- XXX | Same as `declare', but don't reuse any vars
-- XXX | declareNoReuse :: CType -> Gen v (CId, [CBlockItem], [CBlockItem])
-- XXX | declareNoReuse ty = do
-- XXX |   v <- freshLocalCId 'r'
-- XXX |   let decl = CBIDecl $ CVarDecl ty v True Nothing
-- XXX |   return $ (v,[decl],[])

-- XXX | A var_id given
-- XXX | declare' :: CType -> CId -> Gen v CBlockItem
-- XXX | declare' ty var = declareG' ty var Nothing

-- declareInit ty e: declares a new var, initialises it to e, and recycle variables
-- associated with e
declareInit :: CType -> CExpr -> VarPool -> Gen v (CId, [CBlockItem], [CBlockItem])
declareInit ty@(CArray {}) e p = do
  (v,vdecl,vstm) <- declare ty
  (adecl,astm) <- assign ty (variable v) e
  return (v, vdecl++adecl, vstm++astm)
declareInit ty e p = declareG ty (Just $ CInitE e) <* recycleVars p

-- XXX | declareInit' :: CType -> CId -> CExpr -> Gen v CBlockItem
-- XXX | declareInit' ty v e = declareG' ty v $ Just $ CInitE e

-- declareG ty minit: (optionally) initialises a freshvar of type `ty' to `minit'
declareG :: CType -> Maybe CInitializer -> Gen v (CId, [CBlockItem], [CBlockItem])
declareG ty minit | __cogent_fshare_linear_vars = do
  pool <- use varPool
  case M.lookup ty pool of
    Nothing -> do
      v <- freshLocalCId 'r'
      let decl = [CBIDecl $ CVarDecl ty v True Nothing]
      (adecl,astm) <- case minit of
                        Nothing -> return ([],[])
                        Just (CInitE e) -> assign ty (variable v) e
                        Just (CInitList il) -> assign ty (variable v) (CCompLit ty il)
      return (v, decl++adecl, astm)
    Just []     -> do varPool .= M.delete ty pool; declareG ty minit
    Just (v:vs) -> do
      varPool .= M.update (const $ Just vs) ty pool
      case minit of
        Nothing -> return (v, [], [CBIStmt CEmptyStmt])  -- FIXME: shouldn't have anything in p though / zilinc
        Just (CInitE e) -> extTup2l v <$> assign ty (variable v) e
        Just (CInitList il) -> extTup2l v <$> assign ty (variable v) (CCompLit ty il)
declareG ty minit = do
  v <- freshLocalCId 'r'
  let decl = CBIDecl $ CVarDecl ty v True minit
  return (v,[],[decl])

-- XXX | similar to declareG, with a given name
-- XXX | declareG' :: CType -> CId -> Maybe CInitializer -> Gen v CBlockItem
-- XXX | declareG' ty v minit = return (CBIDecl $ CVarDecl ty v True minit)

-- If assigned to a var, then recycle
maybeAssign :: CType -> Maybe CId -> CExpr -> VarPool -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
maybeAssign _  Nothing  e p = return (e,[],[],p)
maybeAssign ty (Just v) e p
  | __cogent_fintermediate_vars = maybeAssign ty Nothing e p
  | otherwise = do recycleVars p; (adecl,astm) <- assign ty (variable v) e;
                   return (variable v, adecl, astm, M.empty)

maybeDecl :: Maybe CId -> CType -> Gen v (CId, [CBlockItem], [CBlockItem])
maybeDecl Nothing  t = declare t
maybeDecl (Just v) t = return (v,[],[])

-- If assigned to a new var, then recycle
aNewVar :: CType -> CExpr -> VarPool -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
aNewVar t e p | __cogent_simpl_cg && not (isTrivialCExpr e)
  = (extTup3r M.empty) . (first3 variable) <$> declareInit t e p
              | otherwise = return (e,[],[],p)

withBindings :: Vec v' CExpr -> Gen (v :+: v') a -> Gen v a
withBindings vec = Gen . withRWS (\r s -> (r <++> vec, s)) . runGen

likelihood :: Likelihood -> (CExpr -> CExpr)
likelihood l = case l of Likely   -> likely
                         Regular  -> id
                         Unlikely -> unlikely

genOp :: Syn.Op -> CC.Type 'Zero -> [CExpr] -> Gen v CExpr
genOp opr (CC.TPrim pt) es =
  let oprf = case opr of
               -- binary
               Plus        -> (\[e1,e2] -> downcast pt $ CBinOp C.Add  (upcast pt e1) (upcast pt e2))
               Minus       -> (\[e1,e2] -> downcast pt $ CBinOp C.Sub  (upcast pt e1) (upcast pt e2))
               Divide      -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Div (upcast pt e1) (upcast pt e2)))
               Times       -> (\[e1,e2] -> downcast pt $ CBinOp C.Mul  (upcast pt e1) (upcast pt e2))
               Mod         -> (\[e1,e2] -> (if __cogent_fcheck_undefined then flip (CCondExpr e2) (mkConst pt 0) else id)
                                              (downcast pt $ CBinOp C.Mod (upcast pt e1) (upcast pt e2)))
               And         -> (\[e1,e2] -> mkBoolLit (CBinOp C.Land (strDot e1 boolField) (strDot e2 boolField)))
               Or          -> (\[e1,e2] -> mkBoolLit (CBinOp C.Lor  (strDot e1 boolField) (strDot e2 boolField)))
               BitAnd      -> (\[e1,e2] -> downcast pt $ CBinOp C.And  (upcast pt e1) (upcast pt e2))
               BitXor      -> (\[e1,e2] -> downcast pt $ CBinOp C.Xor  (upcast pt e1) (upcast pt e2))
               BitOr       -> (\[e1,e2] -> downcast pt $ CBinOp C.Or   (upcast pt e1) (upcast pt e2))
               LShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Lsh (upcast pt e1) (upcast pt e2)))
               RShift      -> (\[e1,e2] -> (if __cogent_fcheck_undefined
                                              then CCondExpr (CBinOp C.Ge e2 (mkConst pt $ width pt)) (mkConst pt 0) else id)
                                             (downcast pt $ CBinOp C.Rsh (upcast pt e1) (upcast pt e2)))
               Gt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Gt e1 e2)
               Lt          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Lt e1 e2)
               Ge          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Ge e1 e2)
               Le          -> (\[e1,e2] -> mkBoolLit $ CBinOp C.Le e1 e2)
               Syn.Eq      -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Eq (strDot e1 boolField) (strDot e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Eq e1 e2))
               Syn.NEq     -> (\[e1,e2] -> case pt of
                                Boolean -> mkBoolLit (CBinOp C.Ne (strDot e1 boolField) (strDot e2 boolField))
                                _       -> mkBoolLit (CBinOp C.Ne e1 e2))
               -- unary
               Syn.Not        -> (\[e1] -> mkBoolLit (CUnOp C.Lnot (strDot e1 boolField)))
               Syn.Complement -> (\[e1] -> downcast pt $ CUnOp C.Not (upcast pt e1))
   in return $ oprf es
  where width = \case U8 -> 8; U16 -> 16; U32 -> 32; U64 -> 64; Boolean -> 8
        -- vvv FIXME: I don't remember why we did it this way. Is it for verification or performance? / zilinc
        upcast, downcast :: PrimInt -> CExpr -> CExpr
        upcast   pt e = if pt `elem` [U8, U16] then CTypeCast u32 e else e
        downcast pt e = if pt `elem` [U8, U16] then CTypeCast (CogentPrim pt) e else e
genOp _ _ _ = __impossible "genOp"

genExpr_ :: TypedExpr 'Zero v VarName -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
genExpr_ = genExpr Nothing


-- The first argument is the return value on one level up
-- Returns: (expr, decls, stmts, reusable_var_pool)
genExpr
  :: Maybe CId
     -- ^
     -- If @Just v@, then
     --
     -- 1. A C statement is added to the list of
     --    generated C statements which assigns the
     --    C expression which evaluates to the same value
     --    as the cogent expression to the variable
     --    whose name is the identifier 'v'.
     --
     -- 2. The generated expression is the variable 'v'
     --
     -- Otherwise, the generated C expression
     -- is returned directly.

  -> TypedExpr 'Zero v VarName
     -- ^ The cogent expression to generate C code for.

  -> Gen v (CExpr, [CBlockItem], [CBlockItem], VarPool)
     -- ^
     -- The parts of the returned tuple are:
     --
     -- [@CExpr@]
     --   A C expression which evaluates to the same result as the cogent expression
     --   provided this C expression is evaluated after all the returned declarations
     --   and statements.
     --
     -- [@[CBlockItem\]@]
     --   All the generated declarations.
     --
     -- [@[CBlockItem\]@]
     --   All the generated statements


genExpr _ (TE t (Op opr [])) = __impossible "genExpr"

genExpr mv (TE t (Op opr es@(e1:_))) = do
  (es',decls,stms,ps) <- L.unzip4 <$> mapM genExpr_ es
  e' <- genOp opr (exprType e1) es'
  t' <- genType t
  (v,adecl,astm,vp) <- maybeAssign t' mv e' (mergePools ps)
  return (v, concat decls ++ adecl, concat stms ++ astm, vp)

genExpr mv (TE t (ILit n pt)) = do
  t' <- genType t
  maybeAssign t' mv (mkConst pt n) M.empty

genExpr mv (TE t (SLit s)) = do
  t' <- genType t
  maybeAssign t' mv (CConst $ CStringConst s) M.empty
#ifdef BUILTIN_ARRAYS
genExpr mv (TE t (ALit es)) = do
  blob <- mapM genExpr_ es
  let TArray telt _ _ _ = t
  t' <- genType t
  telt' <- genType telt
  (v,vdecl,vstm) <- maybeDecl mv t'
  blob' <- flip3 zipWithM [0..] blob $ \(e,edecl,estm,ep) idx -> do
    (adecl,astm) <- assign telt' (mkArrIdx (variable v) idx) e
    return (edecl++adecl, estm++astm, M.empty)  -- FIXME: varpool - meaningless placeholder now / zilinc
  let (vdecls,vstms,vps) = L.unzip3 blob'
  return (variable v, vdecl ++ concat vdecls, vstm ++ concat vstms, M.empty)

genExpr mv (TE t (ArrayIndex e i)) = do  -- FIXME: varpool - as above
  (e',edecl,estm,ep) <- genExpr_ e
  (i',idecl,istm,ep) <- genExpr_ i
  t' <- genType t
  (v,adecl,astm,vp) <- maybeAssign t' mv (CArrayDeref e' i') ep
  return (v, edecl++idecl++adecl, estm++istm++astm, vp)

genExpr mv (TE t (ArrayMap2 (_,f) (e1,e2))) = do  -- FIXME: varpool - as above
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,vdecl,vstm) <- maybeDecl mv t'
  (i,idecl,istm) <- declareInit u32 (mkConst U32 0) M.empty
  let tarr1@(TArray telt1 l1 s1 _) = exprType e1
      tarr2@(TArray telt2 l2 s2 _) = exprType e2
      l1' = mkConst U32 l1
      l2' = mkConst U32 l2
      min = CCondExpr (CBinOp C.Lt l1' l2') l1' l2'
  tarr1' <- genType tarr1
  tarr2' <- genType tarr2
  telt1' <- genType telt1
  telt2' <- genType telt2
  (f',fdecl,fstm,fp) <- withBindings (Cons (CArrayDeref e2' (variable i))
                                           (Cons (CArrayDeref e1' (variable i)) Nil)) $
                                     genExpr_ f
  (a1decl,a1stm) <- assign telt1' (CArrayDeref e1' (variable i)) (strDot f' p1)
  (a2decl,a2stm) <- assign telt1' (CArrayDeref e2' (variable i)) (strDot f' p2)
  (incdecl,incstm) <- assign u32 (variable i) (CBinOp C.Add (variable i) (mkConst U32 1))  -- i++
  let lbody = fdecl++a1decl++a2decl++incdecl++
              fstm++a1stm++a2stm++incstm
      loop = CWhile (CBinOp C.Lt (variable i) min) $ CBlock lbody
  (v1decl,v1stm) <- assign tarr1' (strDot' v p1) e1'
  (v2decl,v2stm) <- assign tarr2' (strDot' v p2) e2'
  -- vvv ASSUME: e1 and e2 are updated in-place.
  return (variable v, vdecl++e1decl++e2decl++idecl++v1decl++v2decl,
          vstm++e1stm++e2stm++istm++[CBIStmt loop]++v1stm++v2stm, M.empty)

genExpr mv (TE t (Pop _ e1 e2)) = do  -- FIXME: varpool - as above
  -- Idea:
  --   v :@ vs = e1 in e2 ~~> v1 = e1[0]; t v2[l-1]; v2 = e1[1]; e2
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  let t1@(TArray telt l s tkns) = exprType e1
  (v1,v1decl,v1stm,v1p) <- flip3 aNewVar e1p (mkArrIdx e1' 0) =<< genType telt
  let trest = TArray telt (l-1) s $ behead tkns
  trest' <- genTypeP trest
  (v2,v2decl,v2stm) <- declare trest'
  -- recycleVars v1p
  (adecl,astm) <- assign trest' (variable v2) (CBinOp C.Add e1' (mkConst U32 1))
  (e2',e2decl,e2stm,e2p) <- withBindings (fromJust $ cvtFromList (SSuc $ SSuc SZero) [v1, variable v2]) $ genExpr mv e2
  return (e2', e1decl ++ v1decl ++ v2decl ++ adecl ++ e2decl,
          e1stm ++ v1stm ++ v2stm ++ astm ++ e2stm, e2p)

genExpr mv (TE t (Singleton e)) = do
  (e',edecl,estm,ep) <- genExpr_ e
  t' <- genType t
  (v,adecl,astm,vp) <- flip (maybeAssign t' mv) ep $ mkArrIdx e' 0
  return (v, edecl++adecl, estm++astm, vp)

genExpr mv (TE t (ArrayPut arr i e)) = do
  (arr',arrdecl,arrstm,arrp) <- genExpr_ arr
  (i',idecl,istm,ip) <- genExpr_ i
  (e',edecl,estm,ep) <- genExpr_ e
  t' <- genType t
  let (TArray telt _ _ _) = t
  telt' <- genType telt
  (assdecl,assstm) <- assign telt' (CArrayDeref arr' i') e'
  (v,vdecl,vstm,vp) <- maybeAssign t' mv arr' M.empty
  return (v, arrdecl++idecl++edecl++assdecl++vdecl, arrstm++istm++estm++assstm++vstm, M.empty)
#endif

genExpr mv (TE t (Unit)) = do
  t' <- genType t
  let e' = CCompLit t' [([CDesignFld dummyField], CInitE (CConst $ CNumConst 0 (CInt True CIntT) DEC))]
  maybeAssign t' mv e' M.empty

genExpr mv (TE t (Variable v)) = do  -- NOTE: this `v' could be a higher-order function
  e' <- ((`at` fst v) <$> ask)
  -- --------------------------------------------------------------------------
  -- XXX | NOTE: We need to establish C scope in order to determine the life time of linear C variables.
  -- XXX |       Thus --fshare-linear-vars is not working due to it. It now does a weaker modification,
  -- XXX |       which moves all variable declarations to the beginning of a function / zilinc
  t' <- genType t
  p <- whenM __cogent_fshare_linear_vars $ do
    whenM (isTypeLinear t) $ case e' of
      CVar v _ -> return $ M.singleton t' [v]
      _ -> return mempty
  -- --------------------------------------------------------------------------
  maybeAssign t' mv e' p

genExpr mv (TE t (Fun f _ _)) = do  -- it is a function identifier
  t' <- genType t
  maybeAssign t' mv (variable $ funEnum (unCoreFunName f)) M.empty

genExpr mv (TE t (App e1@(TE _ (Fun f _ MacroCall)) e2)) | __cogent_ffncall_as_macro = do  -- first-order function application
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,vdecl,vstm) <- maybeDecl mv t'
  let call = [CBIStmt $ CAssignFnCall Nothing (variable $ funMacro (unCoreFunName f)) [variable v, e2']]
  recycleVars e2p
  return (variable v, e2decl ++ vdecl, e2stm ++ vstm ++ call, M.empty)

genExpr mv (TE t (App e1@(TE _ (Fun f _ _)) e2)) = do  -- first-order function application
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,adecl,astm,vp) <- maybeAssign t' mv (CEFnCall (variable (unCoreFunName f)) [e2']) e2p
  return (v, e2decl++adecl, e2stm++astm, vp)

genExpr mv (TE t (App e1 e2)) | __cogent_ffncall_as_macro = do
  enumt <- typeCId $ exprType e1
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  let fname = funDispatch enumt
  t' <- genType t
  (v,vdecl,vstm) <- maybeDecl mv t'
  let call = [CBIStmt $ CAssignFnCall Nothing (variable $ funDispMacro fname) [variable v, e1', e2']]
  recycleVars (mergePools [e1p,e2p])
  return (variable v, e1decl ++ e2decl ++ vdecl, e1stm ++ e2stm ++ vstm ++ call, M.empty)

genExpr mv (TE t (App e1 e2)) = do   -- change `e1' to its dispatch function, with `e1' being the first argument
  enumt <- typeCId $ exprType e1
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  let fname = variable $ funDispatch enumt
  (v',adecl,astm,vp) <- maybeAssign t' mv (CEFnCall fname [e1',e2']) (mergePools [e1p,e2p])
  return (v', e1decl ++ e2decl ++ adecl, e1stm ++ e2stm ++ astm, vp)

genExpr mv (TE t (Take _ rec fld e)) = do
  -- NOTE: New `rec' and old `rec' CAN be the same at this point, as long as they get copied while being
  --       updated. Similarly, the field can be `rec.f' instead of a new one / zilinc

  -- 1. Generate the C expression `rec'` corresponding to the cogent expression for the record
  --    and the C declarations `recdecl` and statements `recstm` this C expression depends on
  (rec',recdecl,recstm,recp) <- genExpr_ rec

  -- 2. Declare a new C local variable `rec''` with the C type `rect` of the record,
  --    initialsed to the C expression `rec'`
  let rect = exprType rec
      TRecord fs s = rect

  cachedTypes <- use cTypeDefs
  (rec'',recdecl',recstm',recp') <- flip3 aNewVar recp rec' =<< genType rect

  -- 3. * If __cogent_fintermediate_vars is True, then
  --       1. Declares a new local variable and assigns it the value of the field being taken
  --       2. @f'@ is a C expression which evaluates to the value of the new local variable
  --    * If __cogent_fintermediate_vars is False, then
  --       @f'@ directly evaluates to the value of the field being taken
  let fieldName = fst $ fs !! fld
  fieldExpr <- case s of
    Unboxed -> return $ strDot rec'' fieldName
    Boxed _ CLayout -> return $ strArrow rec'' fieldName
    Boxed _ _ -> do
      fieldGetter <- genBoxedGetSetField rect fieldName Get
      return $ CEFnCall fieldGetter [rec'']

  ft <- genType . fst . snd $ fs !! fld
  (f', fdecl, fstm, fp) <-
    if __cogent_fintermediate_vars
    then do
      (return . (extTup3r M.empty) . (first3 variable) <=< flip (declareInit ft) M.empty) $ fieldExpr
    else
      return (fieldExpr, [], [], M.empty)

  -- 4. Declare a new C local variable and initialise it to the value of the taken field
  (f'',fdecl',fstm',fp') <- aNewVar ft f' fp

  -- 5. Add the taken field and the new record for the context
  (e',edecl,estm,ep) <- withBindings (Cons f'' (Cons rec'' Nil)) $ genExpr mv e
  return (e', recdecl ++ recdecl' ++ fdecl ++ fdecl' ++ edecl,
          recstm ++ recstm' ++ fstm ++ fstm' ++ estm, mergePools [fp',recp',ep])

genExpr mv (TE t (Put rec fld val)) = do
  t' <- genType t
  fldt <- genType (exprType val)
  -- NOTE: always copy a new record and leave rec unchanged. This prevents the following problem:
  -- > let x' = x {f = fv}  -- x is an unboxed record
  -- >  in (x', x)
  -- >  -- x shouldn't change its field f to fv
  let TRecord fs s = exprType rec
  (rec',recdecl,recstm,recp) <- genExpr_ rec
  (rec'',recdecl',recstm') <- declareInit t' rec' recp
  (val',valdecl,valstm,valp) <- genExpr_ val

  let fieldName = fst $ fs!!fld
  (fdecl,fstm) <- case s of
    Unboxed -> assign fldt (strDot (variable rec'') fieldName) val'
    Boxed _ CLayout -> assign fldt (strArrow (variable rec'') fieldName) val'
    Boxed _ (Layout l) -> do
      let recordType = exprType rec
      fieldSetter <- genBoxedGetSetField recordType fieldName Set
      return $ ([], [CBIStmt $ CAssignFnCall Nothing fieldSetter [variable rec'', val']])

  recycleVars valp
  (v,adecl,astm,vp) <- maybeAssign t' mv (variable rec'') M.empty
  return (v, recdecl ++ recdecl' ++ valdecl ++ fdecl ++ adecl,
          recstm ++ recstm' ++ valstm ++ fstm ++ astm, vp)

genExpr mv (TE t (Let _ e1 e2))
  | not __cogent_flet_in_if || isAtom (untypeE e1) = do
    t1' <- genType $ exprType e1
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    (v,vdecl,vstm) <- declareInit t1' e1' e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', e1decl ++ vdecl ++ e2decl, e1stm ++ vstm ++ e2stm, e2p)
  | otherwise = do
    t1' <- genType $ exprType e1
    (v,vdecl,vstm) <- declare t1'
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    (adecl,astm) <- assign t1' (variable v) e1'
    let binding = [CBIStmt $ CIfStmt (variable letTrue) (CBlock $ e1stm ++ astm) CEmptyStmt]
    recycleVars e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', vdecl ++ e1decl ++ adecl ++ e2decl, vstm ++ binding ++ e2stm, e2p)

genExpr mv (TE t (LetBang vs v e1 e2)) | not __cogent_fletbang_in_if = genExpr mv (TE t (Let v e1 e2))
                                       | otherwise = do
    t1' <- genType $ exprType e1
    (v,vdecl,vstm) <- declare t1'
    (e1',e1decl,e1stm,e1p) <- genExpr_ e1
    (adecl,astm) <- assign t1' (variable v) e1'
    let binding = [CBIStmt $ CIfStmt (variable letbangTrue) (CBlock $ e1stm ++ astm) CEmptyStmt]
    recycleVars e1p
    (e2',e2decl,e2stm,e2p) <- withBindings (Cons (variable v) Nil) $ genExpr mv e2
    return (e2', vdecl ++ e1decl ++ adecl ++ e2decl, vstm ++ binding ++ e2stm, e2p)

genExpr mv (TE t (Tuple e1 e2)) = do
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  (e2',e2decl,e2stm,e2p) <- genExpr_ e2
  t' <- genType t
  (v,vdecl,vstm) <- maybeDecl mv t'
  t1' <- genType (exprType e1)
  t2' <- genType (exprType e2)
  (a1decl,a1stm) <- assign t1' (strDot' v p1) e1'
  (a2decl,a2stm) <- assign t2' (strDot' v p2) e2'
  return (variable v, e1decl ++ e2decl ++ vdecl ++ a1decl ++ a2decl,
          e1stm ++ e2stm ++ vstm ++ a2stm ++ a2stm, mergePools [e1p,e2p])

genExpr mv (TE t (Struct fs)) = do
  let (ns,es) = P.unzip fs
  (es',decls,stms,eps) <- L.unzip4 <$> mapM genExpr_ es
  t' <- genType t
  ts' <- mapM (genType . exprType) es
  -- See note: compound initialisers below
#ifdef BUILTIN_ARRAYS
  (v,vdecl,vstm) <- maybeDecl mv t'
  blob <- forM (zip3 ns ts' es') $ \(n,t',e') -> assign t' (strDot' v n) e'
  let (adecls, astms) = P.unzip blob
  return (variable v, concat decls ++ vdecl ++ concat adecls,
          concat stms ++ vstm ++ concat astms, mergePools eps)
#else
  let cinit = CCompLit t' $ zipWith (\n e -> ([CDesignFld n], CInitE e)) ns es'

  let p = mergePools eps
  (v,vdecl,vstm,p') <- case mv of
    Nothing -> return (cinit, [], [], p)
    Just v -> maybeAssign t' (Just v) cinit p
  return (v, concat decls ++ vdecl,
          concat stms ++ vstm, p')
#endif

genExpr mv (TE t (Con tag e tau)) = do  -- `tau' and `t' should be compatible
  (e',edecl,estm,ep) <- genExpr_ e
  te' <- genType (exprType e)
  t'  <- genType t
  (v,vdecl,vstm) <- maybeDecl mv t'
  -- Note: compound initialisers
  -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~
  -- The C correspondence tactic requires the C to be generated in a very specific way.
  -- For Cons, this means we need to use a compound initialiser, because it sets all unspecified fields to 0.
  -- However, the compound initialisers apparently conflict with code generation for arrays in some way.
  -- Arrays aren't verified at the moment, so we can use compound initialisers without arrays, and just field sets with arrays
#ifdef BUILTIN_ARRAYS
  (a1decl,a1stm) <- assign (CIdent tagsT) (strDot' v fieldTag) (variable $ tagEnum tag)
  (a2decl,a2stm) <- assign te' (strDot' v tag) e'
#else
  (a1decl,a1stm) <- assign t' (variable v) (CCompLit t' [([CDesignFld fieldTag], CInitE $ variable $ tagEnum tag), ([CDesignFld tag], CInitE e')])
  let (a2decl, a2stm) = ([], [])
#endif
  return (variable v, edecl ++ vdecl ++ a1decl ++ a2decl, estm ++ vstm ++ a1stm ++ a2stm, ep)

genExpr mv (TE t (Member rec fld)) = do
  let TRecord fs s = exprType rec
  (rec',recdecl,recstm,recp) <- genExpr_ rec

  let fieldName = fst $ fs !! fld
  e' <- case s of
    Unboxed -> return $ strDot rec' fieldName
    Boxed _ CLayout -> return $ strArrow rec' fieldName
    Boxed _ (Layout l) -> do
      fieldGetter <- genBoxedGetSetField (exprType rec) fieldName Get
      return $ CEFnCall fieldGetter [rec']

  t' <- genType t
  (v',adecl,astm,vp) <- maybeAssign t' mv e' recp
  return (v', recdecl++adecl, recstm++astm, vp)

genExpr mv (TE t (If c e1 e2)) = do
  (v,vdecl,vstm) <- case mv of
    Nothing -> declare =<< genType t
    Just v  -> return (v,[],[])
  (c',cdecl,cstm,cp) <- genExpr_ c
  pool0 <- use varPool
  (e1',e1decl,e1stm,e1p) <- genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e1
  pool1 <- use varPool
  varPool .= pool0
  (e2',e2decl,e2stm,e2p) <- genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e2
  pool2 <- use varPool
  varPool .= intersectPools pool1 pool2  -- it seems that pool_final = (e1p & e2p) + (pool1 & pool2)
  t1 <- genType (exprType e1)
  t2 <- genType (exprType e2)
  (a1decl,a1stm) <- assign t1 (variable v) e1'
  (a2decl,a2stm) <- assign t2 (variable v) e2'
  let ifstm = if __cogent_fintermediate_vars
                then CBIStmt $ CIfStmt (strDot c' boolField) (CBlock $ e1stm ++ a1stm)
                                                             (CBlock $ e2stm ++ a2stm)
                else CBIStmt $ CIfStmt (strDot c' boolField) (CBlock e1stm) (CBlock e2stm)
  recycleVars (mergePools [cp, intersectPools e1p e2p])
  return (variable v, vdecl ++ cdecl ++ e1decl ++ e2decl ++ a1decl ++ a2decl,
          vstm ++ cstm ++ [ifstm], M.empty)

genExpr mv (TE t (Case e tag (l1,_,e1) (_,_,e2))) = do  -- NOTE: likelihood `l2' unused because it has become binary / zilinc
  (v,vdecl,vstm) <- case mv of
    Nothing -> (declare =<< genType t)
    Just v  -> return (v,[],[])
  (e',edecl,estm,ep) <- genExpr_ e
  let et@(TSum altys) = exprType e
  (e'',edecl',estm',ep') <- flip3 aNewVar ep e' =<< genType et
  let cnd = CBinOp C.Eq (strDot e'' fieldTag) (variable $ tagEnum tag)
      (alty1,False) = fromJust $ L.lookup tag altys
  pool0 <- use varPool
  (v1,v1decl,v1stm,v1p) <- flip3 aNewVar M.empty (strDot e'' tag) =<< genType alty1
  (e1',e1decl,e1stm,e1p) <- withBindings (Cons v1 Nil) $
                              genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e1
  pool1 <- use varPool
  varPool .= pool0
  (e2',e2decl,e2stm,e2p) <- withBindings (Cons e'' Nil) $
                              genExpr (if __cogent_fintermediate_vars then Nothing else Just v) e2
  pool2 <- use varPool
  varPool .= intersectPools pool1 pool2
  t1 <- genType (exprType e1)
  t2 <- genType (exprType e2)
  (a1decl,a1stm) <- assign t1 (variable v) e1'
  (a2decl,a2stm) <- assign t2 (variable v) e2'
  let macro1 = likelihood l1
      -- XXX | macro2 = likelihood l2
      ifstm = if __cogent_fintermediate_vars
                then CBIStmt $ CIfStmt (macro1 cnd) (CBlock $ v1stm ++ e1stm ++ a1stm)
                                                    (CBlock $ e2stm ++ a2stm)
                else CBIStmt $ CIfStmt (macro1 cnd) (CBlock $ v1stm ++ e1stm) (CBlock e2stm)
  recycleVars (mergePools [ep', intersectPools (mergePools [v1p,e1p]) e2p])
  return (variable v, vdecl ++ edecl ++ edecl' ++ v1decl ++ e1decl ++ e2decl ++ a1decl ++ a2decl,
          vstm ++ estm ++ estm' ++ [ifstm], M.empty)

genExpr mv (TE t (Esac e)) = do
  (e',edecl,estm,ep) <- genExpr_ e
  let TSum alts = exprType e
      [(tag,(_,False))] = filter (not . snd . snd) alts
  t' <- genType t
  (v,adecl,astm,vp) <- flip (maybeAssign t' mv) ep $ strDot e' tag
  return (v, edecl++adecl, estm++astm, vp)

genExpr mv (TE t (Split _ e1 e2)) = do
  (e1',e1decl,e1stm,e1p) <- genExpr_ e1
  let e1t@(TProduct t1 t2) = exprType e1
  (e1'',e1decl',e1stm',e1p') <- flip3 aNewVar e1p e1' =<< genType e1t
  t1' <- genType t1
  t2' <- genType t2
  (v1,v1decl,v1stm) <- declareInit t1' (strDot e1'' p1) M.empty
  (v2,v2decl,v2stm) <- declareInit t2' (strDot e1'' p2) M.empty
  recycleVars e1p'
  (e2',e2decl,e2stm,e2p) <- withBindings (fromJust $ cvtFromList Nat.s2 [variable v1, variable v2]) $
                              genExpr mv e2
  return (e2', e1decl ++ e1decl' ++ v1decl ++ v2decl ++ e2decl,
          e1stm ++ e1stm' ++ v1stm ++ v2stm ++ e2stm, e2p)
  -- NOTE: It's commented out because split shoule behave like let / zilinc
  -- XXX | NOTE: It's an optimisation here, we no more generate new variables / zilinc
  -- XXX | (e2',e2stm) <- withBindings (fromJust $ cvtFromList Nat.s2 [strDot e1' p1, strDot e1' p2]) $ genExpr mv e2
  -- XXX | return (e2', e1stm ++ e2stm)

genExpr mv (TE t (Promote _ e)) = genExpr mv e

genExpr mv (TE t (Cast _ e)) = do   -- int promotion
  (e',edecl,estm,ep) <- genExpr_ e
  t' <- genType t
  (v,adecl,astm,vp) <- flip (maybeAssign t' mv) ep $ CTypeCast t' e'
  return (v, edecl++adecl, estm++astm, vp)


insertSetMap :: Ord a => a -> Maybe (S.Set a) -> Maybe (S.Set a)
insertSetMap x Nothing  = Just $ S.singleton x
insertSetMap x (Just y) = Just $ S.insert x y

fnSpecStaticInline (FnSpec st tq ats) = FnSpec (STStatic:st) (TQInline:tq) ats
fnSpecAttr attr = (if __cogent_fstatic_inline || inlineDef attr then fnSpecStaticInline else id)
fnSpecKind ti to = (if | isTypeHasKind ti k2 && isTypeHasKind to k2 -> fnSpecAttrConst
                       | isTypeInKinds ti [k0,k2] && isTypeInKinds to [k0,k2] -> fnSpecAttrPure
                       | otherwise -> id)
fnSpecAttrConst (FnSpec st tq ats) = FnSpec st tq (GccAttrs [GccAttr "const" []]:ats)
fnSpecAttrPure  (FnSpec st tq ats) = FnSpec st tq (GccAttrs [GccAttr "pure"  []]:ats)

-- | This function generates an FFI function for a Cogent function if it's input
--   or output type is not marshallable. See [Haskell2010 Standard](https://www.haskell.org/onlinereport/haskell2010/haskellch8.html#x15-1570008.4.2)
--   for a description of marshallable types.
genFfiFunc :: CType                 -- ^ return type of a function
           -> CId                   -- ^ function name
           -> [CType]               -- ^ function argument types
           -> Gen 'Zero [CExtDecl]  -- ^ generate a list of function prototypes and definitions
genFfiFunc rt fn [t]
    | [rtm,tm] <- map isPotentiallyUnmarshallable [rt,t], or [rtm,tm] = do
        arg <- freshLocalCId 'a'
        ret <- freshLocalCId 'r'
        let body = [ CBIDecl $ CVarDecl (ref rt) ret True Nothing
                   , if rtm then CBIStmt $ CAssignFnCall (Just $ variable ret) (variable "malloc") [CSizeofTy rt]
                            else CBIStmt CEmptyStmt -- if output needs indirection
                   , CBIStmt $ CAssignFnCall (Just $ if rtm then CDeref (variable ret) else variable ret)
                                             (variable fn)
                                             [if tm then CDeref (variable arg) else variable arg]
                   , CBIStmt $ CReturn (Just $ variable ret)
                   ]
        ffiFuncs %= (M.insert fn (ref t, ref rt))
        return [ CDecl $ CExtFnDecl (ref rt) ("ffi_" ++ fn) [(ref t,Nothing)] noFnSpec
               , CFnDefn (ref rt, "ffi_" ++ fn) [(ref t,arg)] body noFnSpec
               ]
    | otherwise = return []
  where isPotentiallyUnmarshallable (CStruct {}) = True
        isPotentiallyUnmarshallable (CIdent  {}) = True
        isPotentiallyUnmarshallable _            = False
        ref t | isPotentiallyUnmarshallable t = CPtr t
              | otherwise = t
genFfiFunc _ _ _ = __impossible "genFfiFunc: generated C functions should always have 1 argument"

 -- NOTE: This function excessively uses `unsafeCoerce' because of existentials / zilinc
genDefinition :: Definition TypedExpr VarName -> Gen 'Zero [CExtDecl]
genDefinition (FunDef attr fn Nil t rt e) = do
  localOracle .= 0
  varPool .= M.empty
  arg <- freshLocalCId 'a'
  t' <- addSynonym genTypeA (unsafeCoerce t :: CC.Type 'Zero) (argOf fn)
  (e',edecl,estm,_) <- withBindings (Cons (variable arg & if __cogent_funboxed_arg_by_ref then CDeref else id) Nil)
                         (genExpr Nothing (unsafeCoerce e :: TypedExpr 'Zero ('Suc 'Zero) VarName))
  rt' <- addSynonym genTypeP (unsafeCoerce rt :: CC.Type 'Zero) (retOf fn)
  funClasses %= M.alter (insertSetMap (fn,attr)) (Function t' rt')
  body <- case __cogent_fintermediate_vars of
    True  -> do (rv,rvdecl,rvstm) <- declareInit rt' e' M.empty
                return $ edecl ++ rvdecl ++ estm ++ rvstm ++ [CBIStmt $ CReturn $ Just (variable rv)]
    False -> return $ edecl ++ estm ++ [CBIStmt $ CReturn $ Just e']
  ffifunc <- if __cogent_fffi_c_functions then genFfiFunc rt' fn [t'] else return []
  let fnspec = ((if __cogent_ffunc_purity_attr then fnSpecKind t rt else id) $ fnSpecAttr attr noFnSpec)
  return $ ffifunc ++ [ CDecl $ CExtFnDecl rt' fn [(t',Nothing)] fnspec
                      , CFnDefn (rt',fn) [(t',arg)] body fnspec ]
genDefinition (AbsDecl attr fn Nil t rt)
  = do t'  <- addSynonym genTypeA (unsafeCoerce t  :: CC.Type 'Zero) (argOf fn)
       rt' <- addSynonym genTypeP (unsafeCoerce rt :: CC.Type 'Zero) (retOf fn)
       funClasses %= M.alter (insertSetMap (fn,attr)) (Function t' rt')
       ffifunc <- if __cogent_fffi_c_functions then genFfiFunc rt' fn [t'] else return []
       return $ ffifunc ++ [CDecl $ CExtFnDecl rt' fn [(t',Nothing)] (fnSpecAttr attr noFnSpec)]
-- NOTE: An ad hoc treatment to concrete non-parametric type synonyms / zilinc
genDefinition (TypeDef tn ins (Just (unsafeCoerce -> ty :: CC.Type 'Zero)))
  -- NOTE: We need to make sure that ty doesn't consist of any function type with no function members / zilinc
  -- NOTE: If the RHS of this (the structural definition) is used at all, we generate the synonym / zilinc (26/08/15)
  | not (isTFun ty) = lookupTypeCId ty >>= mapM_ (const $ genRealSyn ty tn) >> return []
  where
    -- This function generates a type synonym to a datatype, not to a pointer
    genRealSyn :: CC.Type 'Zero -> TypeName -> Gen v ()
    genRealSyn ty n = typeCId ty >>= \t -> typeSynonyms %= M.insert n (CIdent t)
genDefinition _ = return []
-- genDefinition (TypeDef tn ins _) = __impossible "genDefinition"

-- ----------------------------------------------------------------------------
-- These function are not in the front-end, they directly go to target code from extra info given by earlier phase

-- XXX | cFunMacro :: (FunName, M.Map Instance Int) -> [C.Definition]
-- XXX | cFunMacro (fn, m) = concat $ flip map (M.toList m) $ \(ts, idx) ->
-- XXX |                       let stableName = fn ++ "_" ++ L.intercalate "_" (map mangleName ts)
-- XXX |                           unstableName = fn ++ "_" ++ show idx
-- XXX |                       in [ C.EscDef ("#define " ++ stableName ++ "() " ++ unstableName ++ "()") noLoc
-- XXX |                          , C.EscDef ("#define " ++ funEnum stableName ++ " " ++ funEnum unstableName) noLoc ]
-- XXX |
-- XXX | cDispatchMacro :: (CC.Type Zero, CId) -> Maybe C.Definition
-- XXX | cDispatchMacro (t@(TFun t1 t2), cname) = Just $ C.EscDef ("#define " ++ funDispatch (mangleName t) ++ " " ++ funDispatch cname) noLoc
-- XXX | cDispatchMacro _ = Nothing


-- ----------------------------------------------------------------------------
-- * top-level function

compile :: [Definition TypedExpr VarName]
        -> [(Type 'Zero, String)]
        -> ( [CExtDecl]  -- enum definitions
           , [CExtDecl]  -- type definitions
           , [CExtDecl]  -- function declarations
           , [CExtDecl]  -- dispatchers
           , [CExtDecl]  -- type synonym definitions
           , [CExtDecl]  -- function definitions
           , [(TypeName, S.Set [CId])]
           , [TableCTypes]
           , [TypeName]
           , GenState
           )
compile defs ctygen =
  let (tdefs, fdefs) = L.partition isTypeDef defs
      (extDecls, st, ()) = runRWS (runGen $
        concat <$> mapM genDefinition (fdefs ++ tdefs)  -- `fdefs' will collect the types that are used in the program, and `tdefs' can generate synonyms
        ) Nil (GenState { _cTypeDefs    = []
                        , _cTypeDefMap  = M.empty
                        , _typeSynonyms = M.empty
                        , _typeCorres   = DList.empty
                        , _absTypes     = M.empty
                        , _custTypeGen  = M.fromList $ P.map (second $ (,CTGI)) ctygen
                        , _funClasses   = M.empty
                        , _localOracle  = 0
                        , _globalOracle = 0
                        , _varPool      = M.empty
                        , _ffiFuncs     = M.empty
                        , _boxedRecordSetters = M.empty
                        , _boxedRecordGetters = M.empty
                        , _boxedSettersAndGetters = []
                        })
      (enum, st', _) = runRWS (runGen $ (mappend <$> genLetTrueEnum <*> genEnum)) Nil st  -- `LET_TRUE', `LETBANG_TRUE' & `_tag' enums
      ((funclasses,tns), st'', _) = runRWS (runGen genFunClasses) Nil st'  -- fun_enums & dispatch functions
      (dispfs, fenums) = L.partition isFnDefn funclasses where isFnDefn (CFnDefn {}) = True; isFnDefn _ = False
      (fndefns,fndecls) = L.partition isFnDefn extDecls where isFnDefn (CFnDefn {}) = True; isFnDefn _ = False  -- there are no types
      tdefs' = reverse $ st ^. cTypeDefs
      tsyns' = M.toList $ st ^. typeSynonyms
      absts' = M.toList $ st ^. absTypes
      tycorr = reverse $ DList.toList $ st ^. typeCorres
      tdefs'' = concat (map (flip genTyDecl tns) tdefs')
      boxedSettersAndGetters' = reverse $ st ^. boxedSettersAndGetters
  in ( enum ++ fenums
     , tdefs''  -- type definitions
     , fndecls  -- Ext function decl's (generated by CodeGen monad)
     , dispfs
     , map genTySynDecl tsyns'  -- type synonyms
     , boxedSettersAndGetters' ++ fndefns
     , absts'  -- table of abstract types
     , map TableCTypes tycorr  -- table of Cogent types |-> C types
     , tns  -- list of funclass typenames (for HscGen)
     , st''
     )


-- ----------------------------------------------------------------------------
-- * Table of Abstract types

printATM :: [(TypeName, S.Set [CId])] -> String
printATM = L.concat . L.map (\(tn,S.toList -> ls) -> tn ++ "\n" ++
             if ls == [[]] then "    *\n" else unlines (L.map (\l -> "    " ++ unwords l) ls))


-- ----------------------------------------------------------------------------
-- * Table generator

newtype TableCTypes = TableCTypes (CId, CC.Type 'Zero)

table :: TableCTypes -> PP.Doc
table (TableCTypes entry) = PP.pretty entry

printCTable :: Handle -> (PP.Doc -> PP.Doc) -> [TableCTypes] -> String -> IO ()
printCTable h m ts log = mapM_ ((>> hPutChar h '\n') . PP.displayIO h . PP.renderPretty 0 80 . m) $
                           L.map (PP.string . ("-- " ++)) (lines log) ++ PP.line : L.map table ts

#if __GLASGOW_HASKELL__ < 709
instance PP.Pretty (CId, CC.Type 'Zero) where
#else
instance {-# OVERLAPPING #-} PP.Pretty (CId, CC.Type 'Zero) where
#endif
  pretty (n,t) = PP.pretty (deepType id (M.empty, 0) t) PP.<+> PP.string ":=:" PP.<+> PP.pretty n


-- ////////////////////////////////////////////////////////////////////////////
-- * misc.

kindcheck = runIdentity . kindcheck_ (const $ __impossible "kindcheck")

-- kindcheck :: Type 'Zero -> Kind
-- kindcheck (TVar v)         = __impossible "kindcheck"
-- kindcheck (TVarBang v)     = __impossible "kindcheck"
-- kindcheck (TCon n vs)      = mempty
-- kindcheck (TFun ti to)     = mempty
-- kindcheck (TPrim i)        = mempty
-- kindcheck (TString)        = mempty
-- kindcheck (TSum ts)        = mconcat $ L.map (kindcheck . fst . snd) ts
-- kindcheck (TProduct t1 t2) = kindcheck t1 <> kindcheck t2
-- kindcheck (TRecord ts)     = mconcat $ L.map (kindcheck . fst . snd) (filter (not . snd .snd) ts)
-- kindcheck (TUnit)          = mempty
-- kindcheck (TArray e _)     = kindcheck e

isTypeLinear :: Type 'Zero -> Bool
isTypeLinear = flip isTypeHasKind k1

isTypeInKinds :: Type 'Zero -> [Kind] -> Bool
isTypeInKinds t ks = kindcheck t `elem` ks

isTypeHasKind :: Type 'Zero -> Kind -> Bool
isTypeHasKind t k = isTypeInKinds t [k]
