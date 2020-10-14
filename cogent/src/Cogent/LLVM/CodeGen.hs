{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings #-}

module Cogent.LLVM.CodeGen where

import Control.Monad.State
import Data.ByteString.Short.Internal (ShortByteString)
import Data.Function (on)
import Data.List (sortBy)
import qualified Data.Map as Map
import Data.String
import LLVM.AST
import LLVM.AST.Global

type Names = Map.Map ShortByteString Int

newName :: ShortByteString -> Names -> (ShortByteString, Names)
newName name scope =
    case Map.lookup name scope of
        Nothing -> (name, Map.insert name 1 scope)
        Just i -> (name <> fromString (show i), Map.insert name (i + 1) scope)

type Binding = [(ShortByteString, Operand)]

data BlockState = BlockState
    { idx :: Int
    , instrs :: [Named Instruction]
    , term :: Maybe (Named Terminator)
    }
    deriving (Show)

data CodegenState = CodegenState
    { currentBlock :: Name
    , blocks :: Map.Map Name BlockState
    , binding :: Binding
    , blockCount :: Int
    , unnamedCount :: Word
    , names :: Names
    , indexing :: [Operand]
    }
    deriving (Show)

newtype Codegen a = Codegen {cg :: State CodegenState a}
    deriving (Functor, Applicative, Monad, MonadState CodegenState)

genBlocks :: CodegenState -> [BasicBlock]
genBlocks m =
    map
        mkBlock
        ( sortBy
            (compare `on` (idx . snd))
            (Map.toList (blocks m))
        )

mkBlock :: (Name, BlockState) -> BasicBlock
mkBlock (name, BlockState _ instrs term) =
    let t =
            ( case term of
                Just t -> t
                Nothing -> error (show name ++ " has no terminator")
            )
     in BasicBlock name instrs t

newBlock :: Int -> BlockState
newBlock i = BlockState i [] Nothing

cgInit :: CodegenState
cgInit = CodegenState (Name "entry") Map.empty [] 1 0 Map.empty []

execCodegen :: Codegen a -> CodegenState
execCodegen m = execState (cg m) cgInit

fresh :: Codegen Word
fresh = do
    i <- gets unnamedCount
    modify (\s -> s {unnamedCount = i + 1})
    return (i + 1)

instr :: Type -> Instruction -> Codegen Operand
instr ty ins = do
    n <- fresh
    let localRef = UnName n
    blk <- current
    let i = instrs blk
    modifyBlock (blk {instrs = i ++ [localRef := ins]})
    return (LocalReference ty localRef)

unnamedInstr :: Instruction -> Codegen ()
unnamedInstr ins = do
    blk <- current
    let i = instrs blk
    modifyBlock (blk {instrs = i ++ [Do ins]})

terminator :: Named Terminator -> Codegen (Named Terminator)
terminator term = do
    blk <- current
    modifyBlock (blk {term = Just term})
    return term

entry :: Codegen Name
entry = gets currentBlock

current :: Codegen BlockState
current = do
    c <- gets currentBlock
    blks <- gets blocks
    case Map.lookup c blks of
        Just x -> return x
        Nothing -> error ("Cannot find block: " ++ show c)

modifyBlock :: BlockState -> Codegen ()
modifyBlock newBlk = do
    current <- gets currentBlock
    modify (\s -> s {blocks = Map.insert current newBlk (blocks s)})

addBlock :: ShortByteString -> Codegen Name
addBlock blkName = do
    bs <- gets blocks
    ix <- gets blockCount
    ns <- gets names
    let new = newBlock ix
        (name, newNames) = newName blkName ns
    modify
        ( \s ->
            s
                { blocks = Map.insert (Name name) new bs
                , blockCount = ix + 1
                , names = newNames
                }
        )
    return (Name name)

setBlock :: Name -> Codegen Name
setBlock blkName = do
    modify (\s -> s {currentBlock = blkName})
    return blkName

def ::
    String ->
    [Parameter] ->
    Type ->
    Codegen (Either Operand (Named Terminator)) ->
    Definition
def dName args retTy body =
    let bodyBlock =
            genBlocks
                ( execCodegen
                    ( do
                        enter <- addBlock "entry"
                        setBlock enter
                        body_exp <- body
                        case body_exp of
                            Right trm -> terminator trm
                            Left val -> terminator (Do (Ret (Just val) []))
                    )
                )
     in GlobalDefinition
            ( functionDefaults
                { name = mkName dName
                , parameters = (args, False)
                , returnType = retTy
                , basicBlocks = bodyBlock
                }
            )
