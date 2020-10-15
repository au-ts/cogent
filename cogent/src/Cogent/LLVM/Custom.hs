module Cogent.LLVM.Custom where

import Control.Monad (forM)
import LLVM.AST
import LLVM.AST.Attribute (ParameterAttribute)
import qualified LLVM.AST.Constant as C
import LLVM.AST.Global
import LLVM.AST.Type (ptr)
import LLVM.IRBuilder
import LLVM.IRBuilder.Module (MonadModuleBuilder)

-- Modified version of https://hackage.haskell.org/package/llvm-hs-pure-9.0.0/docs/src/LLVM.IRBuilder.Module.html#function
function ::
    MonadModuleBuilder m =>
    Name ->
    [(Type, [ParameterAttribute], ParameterName)] ->
    Type ->
    ([Operand] -> IRBuilderT m ()) ->
    m Operand
function label argtys retty body = do
    let tys = (\(ty, _, _) -> ty) <$> argtys
    (paramNames, blocks) <- runIRBuilderT emptyIRBuilder $ do
        paramNames <- forM argtys $ \(_, _, paramName) -> case paramName of
            NoParameterName -> fresh
            ParameterName p -> fresh `named` p
        body $ zipWith LocalReference tys paramNames
        return paramNames
    let def =
            GlobalDefinition
                functionDefaults
                    { name = label
                    , parameters = (zipWith (\(ty, a, _) nm -> Parameter ty nm a) argtys paramNames, False)
                    , returnType = retty
                    , basicBlocks = blocks
                    }
        funty = ptr $ FunctionType retty ((\(ty, _, _) -> ty) <$> argtys) False
    emitDefn def
    pure $ ConstantOperand $ C.GlobalReference funty label
