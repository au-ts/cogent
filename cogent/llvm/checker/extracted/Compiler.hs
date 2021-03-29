{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module ExtractedCoq.Compiler where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

data Nat =
   O
 | S Nat

fst :: ((,) a1 a2) -> a1
fst p =
  case p of {
   (,) x _ -> x}

snd :: ((,) a1 a2) -> a2
snd p =
  case p of {
   (,) _ y -> y}

app :: (([]) a1) -> (([]) a1) -> ([]) a1
app l m =
  case l of {
   ([]) -> m;
   (:) a l1 -> (:) a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

data N =
   N0
 | Npos Prelude.Integer

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

divmod :: Nat -> Nat -> Nat -> Nat -> (,) Nat Nat
divmod x y q u =
  case x of {
   O -> (,) q u;
   S x' -> case u of {
            O -> divmod x' y (S q) y;
            S u' -> divmod x' y q u'}}

div :: Nat -> Nat -> Nat
div x y =
  case y of {
   O -> y;
   S y' -> fst (divmod x y' O y')}

modulo :: Nat -> Nat -> Nat
modulo x y =
  case y of {
   O -> y;
   S y' -> sub y' (snd (divmod x y' O y'))}

nth_error :: (([]) a1) -> Nat -> Prelude.Maybe a1
nth_error l n =
  case n of {
   O -> case l of {
         ([]) -> Prelude.Nothing;
         (:) x _ -> Prelude.Just x};
   S n0 -> case l of {
            ([]) -> Prelude.Nothing;
            (:) _ l0 -> nth_error l0 n0}}

map :: (a1 -> a2) -> (([]) a1) -> ([]) a2
map f l =
  case l of {
   ([]) -> ([]);
   (:) a t -> (:) (f a) (map f t)}

append :: Prelude.String -> Prelude.String -> Prelude.String
append s1 s2 =
  case s1 of {
   ([]) -> s2;
   (:) c s1' -> (:) c (append s1' s2)}

type Functor f =
  () -> () -> (Any -> Any) -> f -> f
  -- singleton inductive, whose constructor was Build_Functor
  
fmap :: (Functor a1) -> (a2 -> a3) -> a1 -> a1
fmap functor x x0 =
  unsafeCoerce functor __ __ x x0

data Monad m =
   Build_Monad (() -> Any -> m) (() -> () -> m -> (Any -> m) -> m)

ret :: (Monad a1) -> a2 -> a1
ret monad x =
  case monad of {
   Build_Monad ret0 _ -> unsafeCoerce ret0 __ x}

bind :: (Monad a1) -> a1 -> (a2 -> a1) -> a1
bind monad x x0 =
  case monad of {
   Build_Monad _ bind0 -> unsafeCoerce bind0 __ __ x x0}

liftM :: (Monad a1) -> (a2 -> a3) -> a1 -> a1
liftM m f x =
  bind m x (\x0 -> ret m (f x0))

functor_Monad :: (Monad a1) -> Functor a1
functor_Monad m _ _ =
  liftM m

data MonadState t m =
   Build_MonadState m (t -> m)

get :: (MonadState a1 a2) -> a2
get monadState =
  case monadState of {
   Build_MonadState get0 _ -> get0}

put :: (MonadState a1 a2) -> a1 -> a2
put monadState =
  case monadState of {
   Build_MonadState _ put0 -> put0}

data MonadExc e m =
   Build_MonadExc (() -> e -> m) (() -> m -> (e -> m) -> m)

raise :: (MonadExc a1 a2) -> a1 -> a2
raise monadExc x =
  case monadExc of {
   Build_MonadExc raise0 _ -> raise0 __ x}

data Binary_float =
   B754_zero Prelude.Bool
 | B754_infinity Prelude.Bool
 | B754_nan Prelude.Bool Prelude.Integer
 | B754_finite Prelude.Bool Prelude.Integer Prelude.Integer

type Binary32 = Binary_float

type Binary64 = Binary_float

type Float = Binary64

type Float32 = Binary32

monad_either :: Monad (Prelude.Either a1 Any)
monad_either =
  Build_Monad (\_ v -> Prelude.Right v) (\_ _ c1 c2 ->
    case c1 of {
     Prelude.Left v -> Prelude.Left v;
     Prelude.Right v -> c2 v})

exception_either :: MonadExc a1 (Prelude.Either a1 Any)
exception_either =
  Build_MonadExc (\_ v -> Prelude.Left v) (\_ c h ->
    case c of {
     Prelude.Left v -> h v;
     Prelude.Right _ -> c})

type StateT s m a = s -> m

functor_stateT :: (Functor a1) -> Functor (StateT a2 a1 Any)
functor_stateT fm _ _ f run s =
  fmap fm (\sa -> (,) (fst sa) (f (snd sa))) (run s)

get_last_digit :: Nat -> Prelude.String
get_last_digit n =
  case modulo n (S (S (S (S (S (S (S (S (S (S O)))))))))) of {
   O -> "0";
   S n0 ->
    case n0 of {
     O -> "1";
     S n1 ->
      case n1 of {
       O -> "2";
       S n2 ->
        case n2 of {
         O -> "3";
         S n3 ->
          case n3 of {
           O -> "4";
           S n4 ->
            case n4 of {
             O -> "5";
             S n5 ->
              case n5 of {
               O -> "6";
               S n6 ->
                case n6 of {
                 O -> "7";
                 S n7 -> case n7 of {
                          O -> "8";
                          S _ -> "9"}}}}}}}}}

string_of_nat_aux :: Prelude.String -> Nat -> Prelude.String
string_of_nat_aux acc n =
  case div n (S (S (S (S (S (S (S (S (S (S O)))))))))) of {
   O -> append (get_last_digit n) acc;
   S n0 ->
    sig_rec (\rec_res _ -> rec_res)
      (string_of_nat_aux (append (get_last_digit n) acc) (S n0))}

string_of_nat :: Nat -> Prelude.String
string_of_nat =
  string_of_nat_aux ""

map_monad :: (Monad a1) -> (a2 -> a1) -> (([]) a2) -> a1
map_monad h f l =
  case l of {
   ([]) -> ret h ([]);
   (:) a l' ->
    bind h (f a) (\b -> bind h (map_monad h f l') (\bs -> ret h ((:) b bs)))}

type Int = Prelude.Integer

type Float0 = Float

type Float1 = Float32

data Linkage =
   LINKAGE_Private
 | LINKAGE_Internal
 | LINKAGE_Available_externally
 | LINKAGE_Linkonce
 | LINKAGE_Weak
 | LINKAGE_Common
 | LINKAGE_Appending
 | LINKAGE_Extern_weak
 | LINKAGE_Linkonce_odr
 | LINKAGE_Weak_odr
 | LINKAGE_External

data Dll_storage =
   DLLSTORAGE_Dllimport
 | DLLSTORAGE_Dllexport

data Visibility =
   VISIBILITY_Default
 | VISIBILITY_Hidden
 | VISIBILITY_Protected

data Cconv =
   CC_Ccc
 | CC_Fastcc
 | CC_Coldcc
 | CC_Cc Int

data Param_attr =
   PARAMATTR_Zeroext
 | PARAMATTR_Signext
 | PARAMATTR_Inreg
 | PARAMATTR_Byval
 | PARAMATTR_Inalloca
 | PARAMATTR_Sret
 | PARAMATTR_Align Int
 | PARAMATTR_Noalias
 | PARAMATTR_Nocapture
 | PARAMATTR_Readonly
 | PARAMATTR_Nest
 | PARAMATTR_Returned
 | PARAMATTR_Nonnull
 | PARAMATTR_Dereferenceable Int
 | PARAMATTR_Immarg
 | PARAMATTR_Noundef
 | PARAMATTR_Nofree

data Fn_attr =
   FNATTR_Alignstack Int
 | FNATTR_Allocsize (([]) Int)
 | FNATTR_Alwaysinline
 | FNATTR_Builtin
 | FNATTR_Cold
 | FNATTR_Convergent
 | FNATTR_Hot
 | FNATTR_Inaccessiblememonly
 | FNATTR_Inaccessiblemem_or_argmemonly
 | FNATTR_Inlinehint
 | FNATTR_Jumptable
 | FNATTR_Minsize
 | FNATTR_Naked
 | FNATTR_No_jump_tables
 | FNATTR_Nobuiltin
 | FNATTR_Noduplicate
 | FNATTR_Nofree
 | FNATTR_Noimplicitfloat
 | FNATTR_Noinline
 | FNATTR_Nomerge
 | FNATTR_Nonlazybind
 | FNATTR_Noredzone
 | FNATTR_Indirect_tls_seg_refs
 | FNATTR_Noreturn
 | FNATTR_Norecurse
 | FNATTR_Willreturn
 | FNATTR_Nosync
 | FNATTR_Nounwind
 | FNATTR_Null_pointer_is_valid
 | FNATTR_Optforfuzzing
 | FNATTR_Optnone
 | FNATTR_Optsize
 | FNATTR_Readnone
 | FNATTR_Readonly
 | FNATTR_Writeonly
 | FNATTR_Argmemonly
 | FNATTR_Returns_twice
 | FNATTR_Safestack
 | FNATTR_Sanitize_address
 | FNATTR_Sanitize_memory
 | FNATTR_Sanitize_thread
 | FNATTR_Sanitize_hwaddress
 | FNATTR_Sanitize_memtag
 | FNATTR_Speculative_load_hardening
 | FNATTR_Speculatable
 | FNATTR_Ssp
 | FNATTR_Sspreq
 | FNATTR_Sspstrong
 | FNATTR_Strictfp
 | FNATTR_Uwtable
 | FNATTR_Nocf_check
 | FNATTR_Shadowcallstack
 | FNATTR_Mustprogress
 | FNATTR_String Prelude.String
 | FNATTR_Key_value ((,) Prelude.String Prelude.String)
 | FNATTR_Attr_grp Int

data Thread_local_storage =
   TLS_Localdynamic
 | TLS_Initialexec
 | TLS_Localexec

data Raw_id =
   Name Prelude.String
 | Anon Int
 | Raw Int

data Ident =
   ID_Global Raw_id
 | ID_Local Raw_id

type Local_id = Raw_id

type Global_id = Raw_id

type Block_id = Raw_id

type Function_id = Global_id

data Typ =
   TYPE_I N
 | TYPE_Pointer Typ
 | TYPE_Void
 | TYPE_Half
 | TYPE_Float
 | TYPE_Double
 | TYPE_X86_fp80
 | TYPE_Fp128
 | TYPE_Ppc_fp128
 | TYPE_Metadata
 | TYPE_X86_mmx
 | TYPE_Array N Typ
 | TYPE_Function Typ (([]) Typ)
 | TYPE_Struct (([]) Typ)
 | TYPE_Packed_struct (([]) Typ)
 | TYPE_Opaque
 | TYPE_Vector N Typ
 | TYPE_Identified Ident

data Icmp =
   Eq
 | Ne
 | Ugt
 | Uge
 | Ult
 | Ule
 | Sgt
 | Sge
 | Slt
 | Sle

data Fcmp =
   FFalse
 | FOeq
 | FOgt
 | FOge
 | FOlt
 | FOle
 | FOne
 | FOrd
 | FUno
 | FUeq
 | FUgt
 | FUge
 | FUlt
 | FUle
 | FUne
 | FTrue

data Ibinop =
   Add Prelude.Bool Prelude.Bool
 | Sub Prelude.Bool Prelude.Bool
 | Mul Prelude.Bool Prelude.Bool
 | Shl Prelude.Bool Prelude.Bool
 | UDiv Prelude.Bool
 | SDiv Prelude.Bool
 | LShr Prelude.Bool
 | AShr Prelude.Bool
 | URem
 | SRem
 | And
 | Or
 | Xor

data Fbinop =
   FAdd
 | FSub
 | FMul
 | FDiv
 | FRem

data Fast_math =
   Nnan
 | Ninf
 | Nsz
 | Arcp
 | Fast

data Conversion_type =
   Trunc
 | Zext
 | Sext
 | Fptrunc
 | Fpext
 | Uitofp
 | Sitofp
 | Fptoui
 | Fptosi
 | Inttoptr
 | Ptrtoint
 | Bitcast

type Tident t = (,) t Ident

data Exp t =
   EXP_Ident Ident
 | EXP_Integer Int
 | EXP_Float Float1
 | EXP_Double Float0
 | EXP_Hex Float0
 | EXP_Bool Prelude.Bool
 | EXP_Null
 | EXP_Zero_initializer
 | EXP_Cstring (([]) ((,) t (Exp t)))
 | EXP_Undef
 | EXP_Struct (([]) ((,) t (Exp t)))
 | EXP_Packed_struct (([]) ((,) t (Exp t)))
 | EXP_Array (([]) ((,) t (Exp t)))
 | EXP_Vector (([]) ((,) t (Exp t)))
 | OP_IBinop Ibinop t (Exp t) (Exp t)
 | OP_ICmp Icmp t (Exp t) (Exp t)
 | OP_FBinop Fbinop (([]) Fast_math) t (Exp t) (Exp t)
 | OP_FCmp Fcmp t (Exp t) (Exp t)
 | OP_Conversion Conversion_type t (Exp t) t
 | OP_GetElementPtr t ((,) t (Exp t)) (([]) ((,) t (Exp t)))
 | OP_ExtractElement ((,) t (Exp t)) ((,) t (Exp t))
 | OP_InsertElement ((,) t (Exp t)) ((,) t (Exp t)) ((,) t (Exp t))
 | OP_ShuffleVector ((,) t (Exp t)) ((,) t (Exp t)) ((,) t (Exp t))
 | OP_ExtractValue ((,) t (Exp t)) (([]) Int)
 | OP_InsertValue ((,) t (Exp t)) ((,) t (Exp t)) (([]) Int)
 | OP_Select ((,) t (Exp t)) ((,) t (Exp t)) ((,) t (Exp t))
 | OP_Freeze ((,) t (Exp t))

type Texp t = (,) t (Exp t)

data Tint_literal =
   TInt_Literal N Int

data Instr_id =
   IId Raw_id
 | IVoid Int

data Phi0 t =
   Phi t (([]) ((,) Block_id (Exp t)))

data Instr t =
   INSTR_Comment Prelude.String
 | INSTR_Op (Exp t)
 | INSTR_Call (Texp t) (([]) (Texp t))
 | INSTR_Alloca t (Prelude.Maybe (Texp t)) (Prelude.Maybe Int)
 | INSTR_Load Prelude.Bool t (Texp t) (Prelude.Maybe Int)
 | INSTR_Store Prelude.Bool (Texp t) (Texp t) (Prelude.Maybe Int)
 | INSTR_Fence
 | INSTR_AtomicCmpXchg
 | INSTR_AtomicRMW
 | INSTR_VAArg
 | INSTR_LandingPad

data Terminator t =
   TERM_Ret (Texp t)
 | TERM_Ret_void
 | TERM_Br (Texp t) Block_id Block_id
 | TERM_Br_1 Block_id
 | TERM_Switch (Texp t) Block_id (([]) ((,) Tint_literal Block_id))
 | TERM_IndirectBr (Texp t) (([]) Block_id)
 | TERM_Resume (Texp t)
 | TERM_Invoke (Tident t) (([]) (Texp t)) Block_id Block_id
 | TERM_Unreachable

data Global t =
   Mk_global Global_id t Prelude.Bool (Prelude.Maybe (Exp t)) (Prelude.Maybe
                                                              Linkage) 
 (Prelude.Maybe Visibility) (Prelude.Maybe Dll_storage) (Prelude.Maybe
                                                        Thread_local_storage) 
 Prelude.Bool (Prelude.Maybe Int) Prelude.Bool (Prelude.Maybe Prelude.String) 
 (Prelude.Maybe Int)

data Declaration t =
   Mk_declaration Function_id t ((,) (([]) Param_attr)
                                (([]) (([]) Param_attr))) (Prelude.Maybe
                                                          Linkage) (Prelude.Maybe
                                                                   Visibility) 
 (Prelude.Maybe Dll_storage) (Prelude.Maybe Cconv) (([]) Fn_attr) (Prelude.Maybe
                                                                  Prelude.String) 
 (Prelude.Maybe Int) (Prelude.Maybe Prelude.String)

type Code t = ([]) ((,) Instr_id (Instr t))

data Block t =
   Mk_block Block_id (([]) ((,) Local_id (Phi0 t))) (Code t) (Terminator t) 
 (Prelude.Maybe (([]) Prelude.String))

data Definition t fnBody =
   Mk_definition (Declaration t) (([]) Local_id) fnBody

data Metadata t =
   METADATA_Const (Texp t)
 | METADATA_Null
 | METADATA_Id Raw_id
 | METADATA_String Prelude.String
 | METADATA_Named (([]) Prelude.String)
 | METADATA_Node (([]) (Metadata t))

data Toplevel_entity t fnBody =
   TLE_Comment Prelude.String
 | TLE_Target Prelude.String
 | TLE_Datalayout Prelude.String
 | TLE_Declaration (Declaration t)
 | TLE_Definition (Definition t fnBody)
 | TLE_Type_decl Ident t
 | TLE_Source_filename Prelude.String
 | TLE_Global (Global t)
 | TLE_Metadata Raw_id (Metadata t)
 | TLE_Attribute_group Int (([]) Fn_attr)

type Toplevel_entities t fnBody = ([]) (Toplevel_entity t fnBody)

monad_err :: Monad (Prelude.Either Prelude.String Any)
monad_err =
  monad_either

exception_err :: MonadExc Prelude.String (Prelude.Either Prelude.String Any)
exception_err =
  exception_either

type ErrS st a = st -> Prelude.Either Prelude.String ((,) st a)

monad_errS :: Monad (ErrS a1 Any)
monad_errS =
  Build_Monad (\_ x s -> Prelude.Right ((,) s x)) (\_ _ m f s ->
    case m s of {
     Prelude.Left v -> Prelude.Left v;
     Prelude.Right p -> case p of {
                         (,) s' x -> f x s'}})

exception_errS :: MonadExc Prelude.String (ErrS a1 Any)
exception_errS =
  Build_MonadExc (\_ v _ -> Prelude.Left v) (\_ c h s ->
    case c s of {
     Prelude.Left v -> h v s;
     Prelude.Right x -> Prelude.Right x})

state_errS :: MonadState a1 (ErrS a1 Any)
state_errS =
  Build_MonadState (\s -> Prelude.Right ((,) s (unsafeCoerce s))) (\t _ ->
    Prelude.Right ((,) t (unsafeCoerce ())))

evalErrS :: (ErrS a1 a2) -> a1 -> Prelude.Either Prelude.String a2
evalErrS c initial =
  case c initial of {
   Prelude.Left msg -> raise (unsafeCoerce exception_err) msg;
   Prelude.Right p -> case p of {
                       (,) _ v -> ret (unsafeCoerce monad_err) v}}

err2errS :: (Prelude.Either Prelude.String a2) -> ErrS a1 a2
err2errS e =
  case e of {
   Prelude.Left msg -> raise (unsafeCoerce exception_errS) msg;
   Prelude.Right v -> ret (unsafeCoerce monad_errS) v}

option2errS :: Prelude.String -> (Prelude.Maybe a2) -> ErrS a1 a2
option2errS msg o =
  case o of {
   Prelude.Just v -> ret (unsafeCoerce monad_errS) v;
   Prelude.Nothing -> raise (unsafeCoerce exception_errS) msg}

data IRState =
   MkIRState Nat Nat Nat (([]) (Texp Typ))

block_count :: IRState -> Nat
block_count i =
  case i of {
   MkIRState block_count0 _ _ _ -> block_count0}

local_count :: IRState -> Nat
local_count i =
  case i of {
   MkIRState _ local_count0 _ _ -> local_count0}

void_count :: IRState -> Nat
void_count i =
  case i of {
   MkIRState _ _ void_count0 _ -> void_count0}

_UU0393_ :: IRState -> ([]) (Texp Typ)
_UU0393_ i =
  case i of {
   MkIRState _ _ _ _UU0393_0 -> _UU0393_0}

newState :: (Texp Typ) -> IRState
newState arg =
  MkIRState O O O ((:) arg ([]))

type Cerr a = ErrS IRState a

getStateVar :: Prelude.String -> Nat -> Cerr (Texp Typ)
getStateVar msg n =
  bind (unsafeCoerce monad_errS) (get (unsafeCoerce state_errS)) (\st ->
    option2errS msg (nth_error (_UU0393_ st) n))

incBlockNamed :: Prelude.String -> Cerr Block_id
incBlockNamed prefix =
  bind (unsafeCoerce monad_errS) (get (unsafeCoerce state_errS)) (\st ->
    bind (unsafeCoerce monad_errS)
      (put (unsafeCoerce state_errS) (MkIRState (S (block_count st))
        (local_count st) (void_count st) (_UU0393_ st))) (\_ ->
      ret (unsafeCoerce monad_errS) (Name
        (append prefix (string_of_nat (block_count st))))))

incLocalNamed :: Prelude.String -> Cerr Raw_id
incLocalNamed prefix =
  bind (unsafeCoerce monad_errS) (get (unsafeCoerce state_errS)) (\st ->
    bind (unsafeCoerce monad_errS)
      (put (unsafeCoerce state_errS) (MkIRState (block_count st) (S
        (local_count st)) (void_count st) (_UU0393_ st))) (\_ ->
      ret (unsafeCoerce monad_errS) (Name
        (append prefix (string_of_nat (local_count st))))))

incLocal :: Cerr Raw_id
incLocal =
  incLocalNamed "l"

addVars :: (([]) (Texp Typ)) -> Cerr ()
addVars newvars =
  bind (unsafeCoerce monad_errS) (get (unsafeCoerce state_errS)) (\st ->
    put (unsafeCoerce state_errS) (MkIRState (block_count st)
      (local_count st) (void_count st) (app newvars (_UU0393_ st))))

drop_err :: Nat -> (([]) a1) -> Prelude.Either Prelude.String (([]) a1)
drop_err n lst =
  case n of {
   O -> ret (unsafeCoerce monad_err) lst;
   S n' ->
    case lst of {
     ([]) -> raise (unsafeCoerce exception_err) "drop on empty list";
     (:) _ xs -> drop_err n' xs}}

dropVars :: Nat -> Cerr ()
dropVars n =
  bind (unsafeCoerce monad_errS) (get (unsafeCoerce state_errS)) (\st ->
    bind (unsafeCoerce monad_errS)
      (err2errS (unsafeCoerce drop_err n (_UU0393_ st))) (\_UU0393_' ->
      put (unsafeCoerce state_errS) (MkIRState (block_count st)
        (local_count st) (void_count st) _UU0393_')))

type Segment = (,) ((,) (Texp Typ) Block_id) (([]) (Block Typ))

body_non_empty_cast :: (([]) (Block Typ)) -> Cerr
                       ((,) (Block Typ) (([]) (Block Typ)))
body_non_empty_cast body =
  case body of {
   ([]) ->
    raise (unsafeCoerce exception_errS)
      "Attempting to generate a function containing no block";
   (:) b body0 -> ret (unsafeCoerce monad_errS) ((,) b body0)}

type Name0 = Prelude.String

type Index = Nat

data Num_type =
   U8
 | U32
 | U64

data Prim_type =
   Num Num_type
 | Bool
 | String

data Prim_op =
   Plus Num_type
 | Minus Num_type
 | Times Num_type
 | Divide Num_type
 | Mod Num_type

data Sigil =
   Boxed
 | Unboxed

data Record_state =
   Taken
 | Present

data Type =
   TFun Type Type
 | TPrim Prim_type
 | TRecord (([]) ((,) Name0 ((,) Type Record_state))) Sigil
 | TUnit

data Lit =
   LBool Prelude.Bool
 | LU8 Prelude.Integer
 | LU32 Prelude.Integer
 | LU64 Prelude.Integer

data Expr =
   Unit
 | Lit0 Lit
 | Var Index
 | Let Expr Expr
 | BPrim Prim_op Expr Expr
 | If Expr Expr Expr

data Def =
   FunDef Name0 Type Type Expr

type Cogent_prog = ([]) Def

convert_num_type :: Num_type -> Typ
convert_num_type t =
  TYPE_I
    (case t of {
      U8 -> Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
       ((\x -> 2 Prelude.* x) 1)));
      U32 -> Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
       ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
       1)))));
      U64 -> Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
       ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
       ((\x -> 2 Prelude.* x) 1))))))})

type Im = Texp Typ

int_n :: N -> Int -> Im
int_n sz n =
  (,) (TYPE_I sz) (EXP_Integer n)

int1 :: Int -> Im
int1 =
  int_n (Npos 1)

int8 :: Int -> Im
int8 =
  int_n (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))))

int32 :: Int -> Im
int32 =
  int_n (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    1))))))

int64 :: Int -> Im
int64 =
  int_n (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1)))))))

compile_lit :: Lit -> Im
compile_lit l =
  case l of {
   LBool b ->
    int1 (case b of {
           Prelude.True -> (\x -> x) 1;
           Prelude.False -> 0});
   LU8 w -> int8 w;
   LU32 w -> int32 w;
   LU64 w -> int64 w}

compile_prim_op :: Prim_op -> (,) ((Exp Typ) -> (Exp Typ) -> Exp Typ) Typ
compile_prim_op o =
  case o of {
   Plus t -> (,) (\x x0 -> OP_IBinop (Add Prelude.False Prelude.False)
    (convert_num_type t) x x0) (convert_num_type t);
   Minus t -> (,) (\x x0 -> OP_IBinop (Sub Prelude.False Prelude.False)
    (convert_num_type t) x x0) (convert_num_type t);
   Times t -> (,) (\x x0 -> OP_IBinop (Mul Prelude.False Prelude.False)
    (convert_num_type t) x x0) (convert_num_type t);
   Divide t -> (,) (\x x0 -> OP_IBinop (UDiv Prelude.False)
    (convert_num_type t) x x0) (convert_num_type t);
   Mod t -> (,) (\x x0 -> OP_IBinop URem (convert_num_type t) x x0)
    (convert_num_type t)}

compile_type :: Type -> Typ
compile_type t =
  case t of {
   TFun t0 rt -> TYPE_Pointer (TYPE_Function (compile_type rt) ((:)
    (compile_type t0) ([])));
   TPrim p ->
    case p of {
     Num n -> convert_num_type n;
     Bool -> TYPE_I (Npos 1);
     String -> TYPE_Pointer (TYPE_I (Npos ((\x -> 2 Prelude.* x)
      ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x) 1)))))};
   TRecord ts s ->
    let {
     t' = TYPE_Struct
      (map (\pat ->
        case pat of {
         (,) _ y0 -> case y0 of {
                      (,) f _ -> compile_type f}}) ts)}
    in
    case s of {
     Boxed -> TYPE_Pointer t';
     Unboxed -> t'};
   TUnit -> TYPE_I (Npos ((\x -> 2 Prelude.* x) ((\x -> 2 Prelude.* x)
    ((\x -> 2 Prelude.* x) 1))))}

code_block :: Block_id -> Block_id -> (Code Typ) -> ([]) (Block Typ)
code_block bid next_bid c =
  (:) (Mk_block bid ([]) c (TERM_Br_1 next_bid) Prelude.Nothing) ([])

nop_block :: Block_id -> Block_id -> ([]) (Block Typ)
nop_block bid next_bid =
  code_block bid next_bid ([])

cond_block :: Block_id -> Block_id -> Block_id -> Im -> ([]) (Block Typ)
cond_block bid true_bid false_bid c =
  (:) (Mk_block bid ([]) ([]) (TERM_Br c true_bid false_bid) Prelude.Nothing)
    ([])

phi_block :: Block_id -> Block_id -> (([]) ((,) Local_id (Phi0 Typ))) -> ([])
             (Block Typ)
phi_block bid next_bid p =
  (:) (Mk_block bid p ([]) (TERM_Br_1 next_bid) Prelude.Nothing) ([])

compile_expr :: Expr -> Block_id -> Cerr Segment
compile_expr e next_bid =
  case e of {
   Unit -> ret (unsafeCoerce monad_errS) ((,) ((,) (int8 0) next_bid) ([]));
   Lit0 l ->
    ret (unsafeCoerce monad_errS) ((,) ((,) (compile_lit l) next_bid) ([]));
   Var i ->
    bind (unsafeCoerce monad_errS)
      (unsafeCoerce getStateVar "unknown variable" i) (\v ->
      ret (unsafeCoerce monad_errS) ((,) ((,) v next_bid) ([])));
   Let e0 b ->
    bind (unsafeCoerce monad_errS) (unsafeCoerce incBlockNamed "Let")
      (\let_bid ->
      bind (unsafeCoerce monad_errS) (compile_expr e0 let_bid) (\x ->
        case x of {
         (,) p e_blks ->
          case p of {
           (,) e' e_bid ->
            bind (unsafeCoerce monad_errS)
              (unsafeCoerce addVars ((:) e' ([]))) (\_ ->
              bind (unsafeCoerce monad_errS) (compile_expr b next_bid)
                (\x0 ->
                case x0 of {
                 (,) p0 b_blks ->
                  case p0 of {
                   (,) b' b_bid ->
                    bind (unsafeCoerce monad_errS)
                      (unsafeCoerce dropVars (S O)) (\_ ->
                      ret (unsafeCoerce monad_errS) ((,) ((,) b' e_bid)
                        (app e_blks (app (nop_block let_bid b_bid) b_blks))))}}))}}));
   BPrim op a b ->
    case compile_prim_op op of {
     (,) op' rt ->
      bind (unsafeCoerce monad_errS) (unsafeCoerce incBlockNamed "Prim")
        (\prim_bid ->
        bind (unsafeCoerce monad_errS) (compile_expr b prim_bid) (\x ->
          case x of {
           (,) p b_blks ->
            case p of {
             (,) b' b_bid ->
              bind (unsafeCoerce monad_errS) (compile_expr a b_bid) (\x0 ->
                case x0 of {
                 (,) p0 a_blks ->
                  case p0 of {
                   (,) a' a_bid ->
                    bind (unsafeCoerce monad_errS) (unsafeCoerce incLocal)
                      (\new_local ->
                      let {
                       prim_blks = code_block prim_bid next_bid ((:) ((,)
                                     (IId new_local) (INSTR_Op
                                     (op' (snd a') (snd b')))) ([]))}
                      in
                      ret (unsafeCoerce monad_errS) ((,) ((,) ((,) rt
                        (EXP_Ident (ID_Local new_local))) a_bid)
                        (app a_blks (app b_blks prim_blks))))}})}}))};
   If c t e0 ->
    bind (unsafeCoerce monad_errS) (unsafeCoerce incBlockNamed "If")
      (\if_bid ->
      bind (unsafeCoerce monad_errS) (compile_expr c if_bid) (\x ->
        case x of {
         (,) p c_blks ->
          case p of {
           (,) c' c_bid ->
            bind (unsafeCoerce monad_errS)
              (unsafeCoerce incBlockNamed "Then_Post") (\tp_bid ->
              bind (unsafeCoerce monad_errS) (compile_expr t tp_bid) (\x0 ->
                case x0 of {
                 (,) p0 t_blks ->
                  case p0 of {
                   (,) t' t_bid ->
                    bind (unsafeCoerce monad_errS)
                      (unsafeCoerce incBlockNamed "Else_Post") (\ep_bid ->
                      bind (unsafeCoerce monad_errS) (compile_expr e0 ep_bid)
                        (\x1 ->
                        case x1 of {
                         (,) p1 e_blks ->
                          case p1 of {
                           (,) e' e_bid ->
                            bind (unsafeCoerce monad_errS)
                              (unsafeCoerce incBlockNamed "Fi") (\fi_bid ->
                              let {
                               post_blks = app (nop_block tp_bid fi_bid)
                                             (nop_block ep_bid fi_bid)}
                              in
                              let {
                               if_blks = cond_block if_bid t_bid e_bid c'}
                              in
                              bind (unsafeCoerce monad_errS)
                                (unsafeCoerce incLocal) (\new_local ->
                                let {
                                 fi_blks = phi_block fi_bid next_bid ((:)
                                             ((,) new_local (Phi (fst t')
                                             ((:) ((,) tp_bid (snd t')) ((:)
                                             ((,) ep_bid (snd e')) ([])))))
                                             ([]))}
                                in
                                ret (unsafeCoerce monad_errS) ((,) ((,) ((,)
                                  (fst t') (EXP_Ident (ID_Local new_local)))
                                  c_bid)
                                  (app c_blks
                                    (app if_blks
                                      (app t_blks
                                        (app e_blks (app post_blks fi_blks))))))))}}))}}))}}))}

compile_fun :: Prelude.String -> Type -> Type -> Expr -> Cerr
               (Definition Typ ((,) (Block Typ) (([]) (Block Typ))))
compile_fun n t rt b =
  bind (unsafeCoerce monad_errS) (unsafeCoerce incBlockNamed "Return")
    (\rid ->
    bind (unsafeCoerce monad_errS) (unsafeCoerce compile_expr b rid) (\x ->
      case x of {
       (,) p body ->
        case p of {
         (,) res _ ->
          let {
           retblock = Mk_block rid ([]) ([]) (TERM_Ret res) Prelude.Nothing}
          in
          bind (unsafeCoerce monad_errS)
            (unsafeCoerce body_non_empty_cast (app body ((:) retblock ([]))))
            (\body' ->
            ret (unsafeCoerce monad_errS) (Mk_definition (Mk_declaration
              (Name n) (TYPE_Function (compile_type rt) ((:) (compile_type t)
              ([]))) ((,) ([]) ([])) Prelude.Nothing Prelude.Nothing
              Prelude.Nothing Prelude.Nothing ([]) Prelude.Nothing
              Prelude.Nothing Prelude.Nothing) ((:) (Name "a0") ([])) body'))}}))

compile_def :: Def -> Prelude.Either Prelude.String
               (Toplevel_entity Typ ((,) (Block Typ) (([]) (Block Typ))))
compile_def d =
  case d of {
   FunDef n t rt b ->
    evalErrS
      (fmap (functor_stateT (functor_Monad (unsafeCoerce monad_err))) (\x ->
        TLE_Definition x) (unsafeCoerce compile_fun n t rt b))
      (newState ((,) (compile_type t) (EXP_Ident (ID_Local (Name "a0")))))}

type Vellvm_prog = Toplevel_entities Typ ((,) (Block Typ) (([]) (Block Typ)))

compile_cogent :: Cogent_prog -> Prelude.Either Prelude.String Vellvm_prog
compile_cogent =
  map_monad (unsafeCoerce monad_err) (unsafeCoerce compile_def)

