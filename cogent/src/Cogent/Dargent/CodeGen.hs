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

{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}

module Cogent.Dargent.CodeGen where

import Cogent.C.Monad
import Cogent.C.Type (genType, typeCId, simplifyType)
import Cogent.C.Syntax
import Cogent.Common.Syntax (FieldName, FunName, funNameToCoreFunName, GetOrSet(..), VarName, Size)
import Cogent.Common.Types (Sigil(..))
import Cogent.Compiler
  ( __fixme
  , __impossible
  , __todo
  , __assert_
  , Architecture (..)
  , __cogent_arch
  )
import Cogent.Core (Definition (..), findFuncById, Type (..), TypedExpr)
import Cogent.Dargent.Allocation
import Cogent.Dargent.Surface (Endianness(..))
import Cogent.Dargent.Core
  ( DataLayout' (..)
  , DataLayout (..)
  , alignLayout'
  , alignLayoutToBytes'
  , dataLayoutSizeInBytes'
  )
import Cogent.Dargent.Util
import Data.Nat
import qualified Data.OMap as OMap
import Data.Char

import Control.Monad (forM, when)
import Control.Monad.Writer.Class (tell)
import Data.List as L (foldl', lookup, scanl')
import Data.Map as M
  ( Map
  , (!)
  , fromList
  , empty
  , insert
  , lookup
  , toList
  )
import Data.Maybe (catMaybes, fromJust, fromMaybe)
import Lens.Micro
  ( (^.)
  , at
  , (&)
  )
import Lens.Micro.GHC  -- orphan instances for 'Micro.Lens.at'
import Lens.Micro.Mtl
  ( (%=)
  , (?=)
  , use
  )
import Debug.Trace

-- * Getter/setter generation

-- | Returns a getter/setter function name for a field of a boxed record.
-- 
-- It will check the store to see if such a function has been previously generated.
-- If not, it will call 'genGS' to generate one, store it in the state, and
-- return its function name.
genGSRecord
  :: Type 'Zero VarName  -- ^ Cogent type of a boxed record.
  -> FieldName           -- ^ Name of field in the boxed record to extract.
  -> GetOrSet            -- ^ The type of function to generate (i.e. the mode).
  -> Gen v FunName       -- ^ The name of the getter/setter function for the field of the record.
genGSRecord t fld m = do
  let glens = case m of Get -> boxedRecordGetters; Set -> boxedRecordSetters
      slens = case m of Get -> boxedRecordGetters; Set -> boxedRecordSetters
  entry <- use (glens . at (StrlCogentType t))
  let entry' = fromMaybe M.empty entry
  case M.lookup fld entry' of
    Just fn -> return fn
    Nothing -> case t of
      TRecord _ fts (Boxed _ (Layout (RecordLayout fls))) -> do
        let ft = fst $ fromList fts ! fld
            fl = alignLayout' $ fls ! fld
        t' <- genType t
        cid <- typeCId t
        fn <- genGS True t' ft fl [fld] m
        (slens . at (StrlCogentType t)) ?= M.insert fld fn entry'
        let updGS Get f (Nothing, s) = (Just f, s)
            updGS Get f (Just g , s) = __assert_ (f == g) "genGSRecord: different getter for the same field" (Just g, s)
            updGS Set f (g, Nothing) = (g, Just f)
            updGS Set f (g, Just s ) = __assert_ (f == s) "genGSRecord: different setter for the same field" (g, Just s)
            updSort (SRecord ss (Just as)) = SRecord ss $ Just $ OMap.adjust (updGS m fn) fld as  -- it only updates the functions
        typeCorres' %= OMap.adjust updSort cid
        return fn
      TRecord _ _ (Boxed _ CLayout) -> __impossible "genGSRecord: tried to gen a getter/setter for a C type"


#ifdef BUILTIN_ARRAYS
-- | Returns a getter/setter function name for an element of a boxed array.
--   Used in array element access like @take, @put, @idx, etc.
-- 
-- We want all layout definition aligned to bytes and we don't want padding bytes between elements,
-- thus we use byte array here.
genGSArray
  :: Type 'Zero VarName
     -- ^
     -- Cogent type for the array.
  -> GetOrSet
     -- ^
     -- The type of function to generate.
  -> Gen v FunName
     -- ^
     -- The 'FunName' is the name of the getter/setter function
     -- for the field of the record.

genGSArray t m = do
  mf <- use ((case m of Get -> boxedArrayGetters; Set -> boxedArraySetters) . at t)
  case mf of
    Just f  -> return f
    Nothing ->
      case t of
        -- NOTE: do we need to check layout within elt here?
        TArray elt _ (Boxed _ (Layout (ArrayLayout ell _))) _ -> do
          let sz = dataLayoutSizeInBytes' ell
              ell' = alignLayoutToBytes' ell
              -- we get rid of unused info here, e.g. array length, hole location
          fn <- genGSName [] m
          t' <- genType t
          elt' <- genType elt
          elGs <- genGS False (CPtr charCTy) elt ell' [] m
          tell [arrayGetterSetter t' elt' sz fn elGs m]
          ((case m of Get -> boxedArrayGetters; Set -> boxedArraySetters) . at (simplifyType t)) ?= fn
          return fn
        _ -> __impossible $ "genGSArray: this function should only be called with boxed array with boxed types " ++
                            "with layout provided, check caller."
#endif




-- | Returns a getter/setter function name for a part of a boxed record.
--
-- Depending on the part's type, it recurses down the data structure in question to
-- generate a collection of accessors for the parts and aggregates them (via dispatching
-- to different worker functions depending on the type) to generate an accessor for the
-- part in question. 
genGS :: IsStruct  -- ^ Whether the C type of the box is of struct or of byte-array
      -> CType     -- ^ The 'CType' for the root boxed type which contains the embedded value that we would like to extract.
      -> Type 'Zero VarName  -- ^ The Cogent type of the embedded value that we would like to extract
      -> DataLayout' [AlignedBitRange]  -- ^ The part of the root boxed type's 'DataLayout\'' corresponding to
                                        --   the embedded value that we would like to extract.
      -> [String]  -- ^ Path in structure to value being get or set, to create readable function name
      -> GetOrSet  -- ^ Whether to generate a getter or a setter
      -> Gen v FunName  -- ^ The 'FunName' is the name of the generated getter function
                        --   for the field of the record.

-- vvv FIXME(?): This is the cause of the problem when generating a getter/setter for
-- an unboxed abstract type with layout. What we want to do is to ask the users to provide
-- their own getters and setters. / zilinc
genGS s root t@(TCon _ _ Unboxed) (PrimLayout br ω) path m = do
  -- genGSName path m
  t' <- genType t
  genGSBlock s br ω root t' path m

genGS s root t@(TCon _ _ Boxed {}) (PrimLayout br ω) path m = do
  t' <- genType t
  genGSBlock s br ω root t' path m

genGS s root t@(TPrim _) (PrimLayout br ω) path m = do
  t' <- genType t
  genGSBlock s br ω root t' path m

genGS s root t@(TFun {}) (PrimLayout br ω) path m = do
  t' <- genType t
  genGSBlock s br ω root t' path m

genGS s root t@(TRecord _ _ Boxed {}) (PrimLayout br ω) path m = do
  t' <- genType t
  genGSBlock s br ω root t' path m

genGS s root t@(TSum alts) (SumLayout tagl als) path m = do
  t' <- genType t
  fn <- genGSName path m
  tagGsetter <- genGSBlock s tagl ME root uintCTy (path ++ ["tag"]) m
  altGsetters <- forM alts $ \(c, (at, _)) -> do
    let (tagv, al) = als ! c
    gsetter <- genGS s root at al (path ++ [c]) m
    return (c, tagv, gsetter)
  tell [mkGsDeclVariant tagGsetter altGsetters root t' fn m]
  return fn

genGS s root t@(TRecord _ fts Unboxed) (RecordLayout fls) path m = do
  t' <- genType t
  fn <- genGSName path m
  gsetters <- forM fts $ \(f, (ft, _)) -> do
    let fl = fls ! f
    gsetter <- genGS s root ft fl (path ++ [f]) m
    return (f, gsetter)
  tell [mkGsDeclRecord gsetters root t' fn m]
  return fn

genGS s root TUnit UnitLayout path m = do
  fn <- genGSName path m
  tell [mkGsDeclUnit root fn m]
  return fn

#ifdef BUILTIN_ARRAYS
genGS s root t@(TArray elt l (Boxed {}) _) (PrimLayout br ω) path m = do
  t' <- genType t
  genGSBlock s br ω root t' path m

-- vvv FIXME!!!
genGS s root t@(TArray telt l Unboxed _) (ArrayLayout lelt l') path m = do
  fn <- genGSName path m
  tarr' <- genType t
  telt' <- genType telt
  eltGsName <- genGS s root telt lelt (path ++ ["arr"]) m
  tell [mkGSDeclUArray root tarr' telt' fn eltGsName m]
  return fn
  
#endif

genGS s root t l _ _ = __impossible $ "genGS"



-- | Declares in the 'Gen' state a C function which gets/sets the contents
-- of a list of aligned bit ranges in a boxed value which concatenate to
-- a value of the given embedded type.
--
-- Calls the function `mkGsDeclBlock` to generate the function.
genGSBlock
  :: IsStruct
  -> [AlignedBitRange]
  -> Endianness
  -> CType
  -> CType
  -> [String]
  -> GetOrSet
  -> Gen v FunName
genGSBlock s brs ω root t path m = do
  fn <- genGSName path m
  gsetters <- forM (zip brs [0..]) $ \(br,idx) -> do
                gsetter <- genGSName (path ++ ["part" ++ show idx]) m
                tell [mkGsDeclABR s root br gsetter m]
                return gsetter
  tell [mkGsDeclBlock (zip brs gsetters) ω root t fn m]
  return fn


-- | Generates a unique function name for the getter or setter which is also readable.
genGSName :: [String]   -- ^ Path in structure to value being get or set
          -> GetOrSet   -- ^ Whether to generate a getter or setter function
          -> Gen v CId  -- ^ The 'CId' for the function, which is guaranteed to be unique
genGSName path m =
  let path' = concatMap ('_' :) path
      m'    = case m of Get -> "_get" ; Set -> "_set"
   in (++ m' ++ path') <$> freshGlobalCId 'd'


-- * Getter/setter function declarations


-- | Calling @mkGsDeclRecord [(f0,g0), ...] root t fn Get@
-- will return the C Syntax for the following function.
-- 
-- @
-- static inline t fn (root p) {
--   return (t)
--     { .f0 = g0 (p)
--     , .f1 = g0 (p)
--     , ...
--     };
-- }
-- @
-- 
-- Calling @mkGsDeclRecord [(f0,s0), ...] root t fn Set@
-- will return the C Syntax for the following function.
-- 
-- @
-- static inline void fn (root p, t v) {
--   s0 (p, v.f0);
--   s1 (p, v.f1);
--   ...
-- }
-- @
mkGsDeclRecord
  :: [(CId, FunName)]  -- ^ pairs of field name and accessor for that field
  -> CType             -- ^ The C type of the box.
  -> CType             -- ^ The C type of the embedded data.
  -> CId               -- ^ The name to give the generated getter/setter function
  -> GetOrSet          -- ^ Whether to generate getter or setter
  -> CExtDecl          -- ^ The C syntax tree for a function which puts/extracts the embedded data from the box.
mkGsDeclRecord fs root t fn m =
  let stmts = case m of
        Get -> [CBIStmt $ CReturn $ Just $ CCompLit t $ 
                 fmap (\(f,g) -> ([CDesignFld f], CInitE $ CEFnCall (variable g) [boxVar])) fs]
        Set -> fmap (\(f,s) -> CBIStmt $ CAssignFnCall Nothing (variable s) [boxVar, CStructDot valueVar f]) fs
   in mkGsDecl root t fn stmts m


-- | Calling @mkGsDeclVariant tagFn [(c0,v0,g0), ...] root t fn Get@
-- will return the C Syntax for the following function.
-- 
-- @
-- static inline t fn (root p) {
--   return
--     (tagFn (p) == v0)
--     ? (t)
--         { .tag = TAG_ENUM_c0
--         , .c0 = g0 (p);
--         }
--     : (tagFn (p) == v1)
--       ? (t)
--           { .tag = TAG_ENUM_c1
--           , .c1 = g1 (p);
--           }
--       : ...
-- }
-- @
-- 
-- Calling @mkGsDeclVariant tagFn [(c0,v0,s0), ...] root t fn Set@
-- will return the C Syntax for the following function.
-- 
-- @
-- static inline void fn (root p, t v) {
--   if (v.tag == TAG_ENUM_c0) {
--     tagFn (p, v0);
--     s0 (p, v.c0);
--   } else if (v.tag == TAG_ENUM_c1) {
--     tagFn (p, v1);
--     s1 (p, v.c1);
--   } else if
--     ...
--   }
-- }
-- @
mkGsDeclVariant
  :: FunName  -- Name of the setter/getter function for the tag
  -> [(CId, Integer, FunName)]  -- ^ list of @(tag_name, tag_value, accessor)@
  -> CType  -- ^ The C type of the box.
  -> CType  -- ^ The C type of the embedded data.
  -> CId    -- ^ The name to give the generated getter function
  -> GetOrSet  -- ^ Whether to generate a getter or setter
  -> CExtDecl  -- ^ The C syntax tree for a function which extracts the embedded data from the box.
mkGsDeclVariant tagFn ((c0,v0,gs0):alts) root t fn m =
  let stmts = case m of
        Get -> [CBIStmt $ CReturn $ Just $
                 foldl' (\acc (c,v,g) -> CCondExpr (CBinOp Eq (CEFnCall (variable tagFn) [boxVar]) (uint v))
                                                   (getUnboxedAlt c g) acc)
                        (getUnboxedAlt c0 gs0) alts]

        Set | [] <- alts -> setUnboxedAlt c0 v0 gs0
        Set -> [CBIStmt $
                 foldl' (\acc (c,v,s) -> CIfStmt (CBinOp Eq (CStructDot valueVar fieldTag)
                                                            (variable $ tagEnum c))
                                                 (CBlock $ setUnboxedAlt c v s) acc)
                        (CBlock $ setUnboxedAlt c0 v0 gs0) alts]
   in mkGsDecl root t fn stmts m
  where
    getUnboxedAlt :: CId -> FunName -> CExpr
    getUnboxedAlt altName altGetter =
      CCompLit t
      [ ([CDesignFld fieldTag], CInitE $ variable (tagEnum altName))
      , ([CDesignFld altName] , CInitE $ CEFnCall (variable altGetter) [boxVar])
      ]

    setUnboxedAlt :: CId -> Integer -> FunName -> [CBlockItem]
    setUnboxedAlt altName tagValue altSetter = fmap CBIStmt
      [ CAssignFnCall Nothing (variable tagFn)     [boxVar, uint tagValue]
      , CAssignFnCall Nothing (variable altSetter) [boxVar, CStructDot valueVar altName]
      ]


mkGsDeclUnit :: CType     -- ^ The C type of the box.
             -> CId       -- ^ The name to give the generated getter/setter function
             -> GetOrSet  -- ^ Whether to generate getter or setter
             -> CExtDecl  -- ^ The C syntax tree for a function which puts/extracts the embedded data from the box.
mkGsDeclUnit root fn m =
  let stmts = case m of
        Get -> [CBIStmt $ CReturn $ Just $ CCompLit unitCTy [([CDesignFld dummyField], CInitE $ sint 0)]]
        Set -> []  -- Intentionally empty 
        -- Not sure if need to initialise field of unit values to a given number
   in mkGsDecl root unitCTy fn stmts m


-- | Creates a C function which either:
-- 
-- * gets the contents of a list of aligned bit ranges (ABR)
--   out of a boxed value and concatenates the retrieved values
--   to produce a value of the given embedded value type.
-- * sets the contents of a list of aligned bit ranges
--   in a boxed value from the pieces of a value of the given embedded value type.
-- 
-- @mkGsDeclBlock ((br0,g0):brrest) root t fn Get@
-- will return the C syntax for the C function
-- 
-- @
-- static inline t fn (root p) {
--   return (t) (
--     (((t)g0(p)) << 0) |
--     (((t)g1(p)) << 0 + `bitSizeABR` br0) |
--     (((t)g2(p)) << 0 + `bitSizeABR` br0 + `bitSizeABR` br1) |
--     ...);
-- }
-- @
-- 
-- @mkGsDeclBlock brs@((br0,s0):...) root t fn Set@
-- will return the C syntax for the C function
-- 
-- @
-- static inline void fn (root b, t v) {
--   s0 (b, (v >> 0) & `bitSizeABR` br0);
--   s1 (b, (v >> 0 + `bitSizeABR` br0) & `bitSizeABR` br1);
--   s2 (b, (v >> 0 + `bitSizeABR` br0 + `bitSizeABR` br1) & `bitSizeABR` br2);
--   ...
-- }
-- @
--
-- /Note:/ the total bits shifted must be smaller than the size of a word, which means that this doesn't
-- work for unboxed abstract types larger than the size of a word.
mkGsDeclBlock
  :: [(AlignedBitRange, FunName)]  -- ^ List of @(ABR, accessor_name)@
  -> Endianness  -- ^ The endianness of the embedded data.
  -> CType       -- ^ The C type of the box.
  -> CType       -- ^ The C type of the embedded data.
  -> CId         -- ^ The name to give the generated getter/setter function
  -> GetOrSet    -- ^ Whether to generate a getter or setter
  -> CExtDecl    -- ^ The C syntax tree for a function which extracts/puts the embedded data from/in the box.

mkGsDeclBlock brs@((br0,gs0):brrest) ω root t fn m
  = let stmts = case m of
          Get -> [CBIStmt $ CReturn $ Just $ fromIntValue t $ snd $
                   foldl' (\(accBoff, accExpr) (r,g) -> (accBoff + bitSizeABR r, CBinOp Or accExpr (getPart g accBoff)))
                     (bitSizeABR br0, getPart gs0 0) brrest]
          Set -> fmap (\((r,s), offset) -> CBIStmt (setPart s offset (bitSizeABR r)))
                   $ zip brs
                   $ scanl' (+) 0
                   $ fmap (bitSizeABR . fst) brs
     in mkGsDecl root t fn stmts m
  where

    -- If called, `ω` should not be `ME`, as no conversion functions are defined for machine endianness
    convEndian :: FunName
    convEndian = case intTypeForType t of
      (CIdent cid) -> map toLower $ show ω ++ "_" ++ cid ++ "_swap"
      (CInt _ _)   -> map toLower $ show ω ++ "_" ++ "u8" ++ "_swap"
      _            -> __impossible "convEndian: called with invalid embedded type"

    getPart :: FunName -> Integer -> CExpr
    getPart g offset =
      let e = CBinOp Lsh (CTypeCast (intTypeForType t) (CEFnCall (variable g) [boxVar])) (uint offset)
       in case ω of
            ME -> e
            _  -> CEFnCall (variable convEndian) [e]
    
    setPart :: FunName -> Integer -> Integer -> CStmt
    setPart s offset sz =
      let -- If @t@ is a boxed type, we cast @valueVar@ to the integer type of the correct size
          -- If it is a boolean type, we extract the boolean value
          e  = toIntValue t valueVar
          e' = case ω of
                ME -> e
                _  -> CEFnCall (variable convEndian) [e]
       in CAssignFnCall Nothing (variable s)
                        [boxVar, CTypeCast uintCTy (CBinOp And (CBinOp Rsh e' (uint offset)) (uint(sizeToMask sz)))]

mkGsDeclBlock _ _ _ _ _ _ = __impossible $ "mkGsDeclBlock should never be called on an empty list of ranges!"


-- | Creates a C function to extract/set the contents of an
-- AlignedBitRange from/in a Cogent boxed type.
-- 
-- @mkGsDeclABR b root (AlignedBitRange sz boff woff) fn Get@
-- should be the C function
-- 
-- @
-- // b == True
-- static inline unsigned int get_fn (root p) {
--   return (p.data[woff] >> boff) & `sizeToMask` sz;
-- }
-- @
-- 
-- or
--
-- @
-- // b == False
-- static inline unsigned int get_fn (char *p) {
--   return (p[woff * 4] >> boff) & `sizeToMask` sz;
-- }
-- @
-- 
-- @mkGsDeclABR b root (AlignedBitRange sz boff woff) fn Set@
-- should be the C function
-- 
-- @
-- // b == True
-- static inline void set_fn (root p, unsigned int v) {
--   p->data[woff] = p->data[woff]
--                   & ~(`sizeToMask` sz << boff))     // clear the bits
--                   | ((`sizeToMask` sz & v) << boff);  // set the bits
-- }
-- @
--
-- or
--
-- @
-- // b == False
-- static inline void set_fn (char *p, unsigned int v) {
--   p[woff * 4] = p[woff * 4]
--                 & ~(`sizeToMask` sz << boff)
--                 | ((`sizeToMask` sz & v) << boff);
-- }
-- @
mkGsDeclABR :: IsStruct -> CType -> AlignedBitRange -> CId -> GetOrSet -> CExtDecl
mkGsDeclABR b root (AlignedBitRange sz boff woff) fn m =
  let stmts = case m of
        Get -> [CBIStmt $ CReturn $ Just (CBinOp And (CBinOp Rsh expr boff') mask)]
        Set -> [CBIStmt $ CAssign expr (CBinOp Or (CBinOp And expr (CUnOp Not (CBinOp Lsh mask boff')))
                                                  (CBinOp Lsh (CBinOp And mask valueVar) boff'))]
   in mkGsDecl root uintCTy fn stmts m
  where
    boff' = uint boff
    mask  = CConst $ CNumConst (sizeToMask sz) uintCTy HEX
    expr = case b of
             True  -> CArrayDeref (CStructDot (CDeref boxVar) boxFieldName) (uint woff)
             False -> CArrayDeref boxVar (uint woff)


mkGSDeclUArray :: CType -> CType -> CType -> CId -> FunName -> GetOrSet -> CExtDecl
mkGSDeclUArray root tarr telt fn eltGsName m =
  let stmts = [CBIStmt $ CComment "// FIXME: Don't use it! Define your own getter/setter using the GETTER or SETTER pragmas." CEmptyStmt]
   in mkGsDecl root tarr fn stmts m

arrayGetterSetter :: CType -> CType -> Size -> CId -> FunName -> GetOrSet -> CExtDecl
arrayGetterSetter arrType elemType elemSize functionName elemGetterSetter Get =
  ( CFnDefn
    ( elemType, functionName )  -- (return type, function name)
    -- [(param type, param name)]
    [ ( arrType, arrId)
    , ( uintCTy, idxId) -- NOTE: type unverified
    ]
    [ CBIStmt $ CReturn $ Just
      ( CEFnCall (variable elemGetterSetter)
        [( CBinOp Add
          ( CTypeCast ( CPtr charCTy ) arrVar )
          ( CBinOp Mul idxVar ( uint elemSize ) )
        )]
      )
    ]
    staticInlineFnSpec
  )
arrayGetterSetter arrType elemType elemSize functionName elemGetterSetter Set =
  ( CFnDefn
    ( CVoid, functionName ) -- (return type, function name)
    -- [(param type, param name)]
    [(arrType, arrId), (uintCTy, idxId), (elemType, valueId)]
    [ CBIStmt $ CReturn $ Just
      ( CEFnCall (variable elemGetterSetter)
        [ ( CBinOp Add
            ( CTypeCast ( CPtr charCTy ) arrVar )
            ( CBinOp Mul idxVar ( uint elemSize ) )
          )
        , valueVar
        ]
      )
    ]
    staticInlineFnSpec
  )


-- | Returns a getter/setter function declaration
mkGsDecl :: CType -> CType -> CId -> [CBlockItem] -> GetOrSet -> CExtDecl
mkGsDecl root t f stmts Get = CFnDefn (t    , f) [(root, boxId)]               stmts staticInlineFnSpec
mkGsDecl root t f stmts Set = CFnDefn (CVoid, f) [(root, boxId), (t, valueId)] stmts staticInlineFnSpec

-- | Generates the function declarations for the top-level getters/setters.
genGSFuncDecls :: Type 'Zero VarName -> M.Map FieldName FunName -> GetOrSet -> [Definition TypedExpr VarName VarName] -> Gen v ()
genGSFuncDecls t (M.toList -> l) mode defs = do
  mdecls <- forM l $ \(fld, fn) -> do
    case findFuncById (funNameToCoreFunName fn) defs of
      Just _  -> return Nothing  -- If such a function is defined, then we don't need to generate anything.
                                 -- The code gen will take care of it.
      Nothing -> do
        let TRecord _ fts _ = t
            τ = fst . fromJust $ L.lookup fld fts  -- field type
        t' <- genType t
        τ' <- genType τ      
        case mode of
          Get -> return $ Just $ CDecl (CExtFnDecl τ' fn [(t', Nothing)] staticInlineFnSpec)
          Set -> return $ Just $ CDecl (CExtFnDecl CVoid fn [(t', Nothing), (τ', Nothing)] staticInlineFnSpec)
  tell $ catMaybes mdecls

-- * Auxilliary functions, definitions and constants


-- | @sizeToMask n@ is an integer whose binary representation has
-- exactly @n@ 1s in the @2^0@ to @2^(n-1)@ places
sizeToMask :: Integer -> Integer
sizeToMask n
  | 0 <= n && n <= wordSizeBits = 2^n - 1
  | otherwise = __impossible $ "Dargent.CodeGen.sizeToMask " ++ show n ++ ": n not in range [0, " ++ show wordSizeBits ++ "] after alignment"

boxFieldName :: CId
boxFieldName = "data"

-- | The first parameter to all setters/getters
boxId  = "b"
boxVar = variable boxId

-- | The second parameter to setters
valueId  = "v"
valueVar = variable valueId

-- | Below for array related operations
arrId  = "a"
arrVar = variable arrId
idxId  = "i"
idxVar = variable idxId


toIntValue :: CType -> CExpr -> CExpr
toIntValue (CInt _ _) cexpr               = cexpr
toIntValue (CIdent t) cexpr
  | t == boolT                            = CStructDot cexpr boolField
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
toIntValue _          cexpr               = CTypeCast archCTy cexpr

fromIntValue :: CType -> CExpr -> CExpr
fromIntValue (CInt _ _)     cexpr         = cexpr
fromIntValue (CIdent t)     cexpr
  | t == boolT                            = CCompLit boolCTy [([CDesignFld boolField], CInitE cexpr)]
  | t `elem` ["u8", "u16", "u32", "u64"]  = cexpr
fromIntValue ctype          cexpr         = CTypeCast ctype cexpr

-- | Given the 'CType' of an embedded value (leaf of composite type tree) to extract,
-- returns the corresponding integer type it should be extracted as before casting.
intTypeForType :: CType -> CType
intTypeForType ctype@(CInt {})            = ctype
intTypeForType (CIdent t)
  | t == boolT                            = charCTy  -- embedded boolean
  | t == tagsT                            = uintCTy
  | t `elem` ["u8", "u16", "u32", "u64"]  = CIdent t
intTypeForType _                          = archCTy  -- embedded boxed abstract type/record

type IsStruct = Bool
