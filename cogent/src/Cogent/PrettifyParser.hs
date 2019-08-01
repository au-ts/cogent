{-# LANGUAGE RecursiveDo #-}
module Cogent.PrettifyParser where

import Text.Earley
import Cogent.PrettifySyntax
import qualified Cogent.PrettifyLexer as L
import Cogent.PrettifyLexer(Token, SourcePos)
import Control.Applicative

token' :: Token -> Prod r String (Token, SourcePos) (Token, SourcePos)
token' t = satisfy ((== t) .fst)

debugTy input = print $ fullParses (parser ty) $ L.lexDebug input
ty :: Grammar r (Prod r String (Token, SourcePos) Type)
ty = mdo
    x <- rule $ terminal typeName
             <|> terminal typeVar
             <|> unit <$> token' L.LParen <*> token' L.RParen 
             <|> parens <$> token' L.LParen <*> x <*> token' L.RParen 
             <|> bang <$> x <*> token' L.Bang
             <|> unbox <$> token' L.Hash <*> x
             <|> tyApp <$> x <*> x
             <|> fun <$> x <*> token' L.Arrow <*> x
            -- <|> tuple <$> token' L.LParen <*> some ((,) <$> x <*> token' L.Comma) <*> x <*> token' L.RParen


    pure x

  where
    unit t1 t2 = T (PrimType Unit) [t1,t2]
    parens t1 x t2 = T (Parens x) [t1,t2]
    bang x t = T (Bang x) [t]
    unbox t x = T (Unbox x) [t]
    tyApp x1 x2 = T (TyApp x1 x2) []
    fun x1 t x2 = T (Fun x1 x2) [t]
    -- tuple

    typeName :: (Token, SourcePos) -> Maybe Type
    typeName (tok, pos) = do
        L.UpperIdent n <- pure tok
        let ty' = case n of 
             "U8"   -> PrimType U8
             "U16"  -> PrimType U16
             "U32"  -> PrimType U32
             "U64"  -> PrimType U64
             "Bool" -> PrimType Bool
             _      -> Abstract n
        pure (T ty' [(tok,pos)])

    typeVar :: (Token, SourcePos) -> Maybe Type
    typeVar (tok, pos) = do
        L.LowerIdent n <- pure tok
        pure (T (TypeVar n) [(tok,pos)])
    
