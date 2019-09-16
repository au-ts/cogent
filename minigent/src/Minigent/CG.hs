module Minigent.CG(cg) where
import Minigent.Syntax
import Minigent.Environment
import Minigent.Syntax.Utils(operators)
import Data.List (intersperse)
import Data.Char (isDigit)
import Text.Read (readMaybe)
import qualified Data.Map as M
format :: String -> [String] -> String
format a xs = foldr replace a (zip [0..] xs)
  where
    replace (i, n) [] = []
    replace (i, n) (x:xs) 
       | x == '$'
       , (body, rest) <- span isDigit xs
       , Just v <- readMaybe body
       , v == i = n ++ replace (i,n) rest
       | otherwise = x : replace (i,n) xs



jsOperators :: [(Op, String)]
jsOperators = (NotEqual, "!=")
            : filter ((`notElem` [Not, NotEqual]) . fst) 
                     (map (\(x,y)->(y,x)) operators)

cg :: GlobalEnvironments -> String
cg envs = let ds = M.toList (defns envs)
           in "var C = require('./minigent.js');\n" 
              ++ "var A = require('./abstract.js');\n"
              ++ genDefs ds
              ++ "\n" ++ case lookup "main" ds of
                           Just _ -> "main(null);\n"
                           _ -> ""
  where
    genExpr :: Expr -> String
    genExpr (PrimOp Not [e]) = format "!($0)" [genExpr e]
    genExpr (PrimOp o [e1,e2]) 
      | Just x <- lookup o jsOperators
      = format "($0 $1 $2)" [genExpr e1, x, genExpr e2]
    genExpr (Literal (BoolV True)) = "true"
    genExpr (Literal (BoolV False)) = "false"
    genExpr (Literal (IntV i)) = show i
    genExpr (Literal UnitV) = "null"
    genExpr (Var v) = v
    genExpr (Con c e) = format "({tag:$0, val:$1})" [show c, genExpr e]
    genExpr (TypeApp f ts) = if M.member f (defns envs) then f else "A." ++ f
    genExpr (Sig e t) = genExpr e
    genExpr (Apply a b) = format "$0($1)" [genExpr a, genExpr b]
    genExpr (Struct fs) = format "({$0})" [ concat (intersperse ", " (map genField fs)) ] 
      where genField (f,e) = format "$0: $1" [f, genExpr e]
    genExpr (If e1 e2 e3) = format "($0 ? $1 : $2)" (map genExpr [e1,e2,e3])
    genExpr (Let v e1 e2) = format "C.Let($1,$0=>$2)" [v, genExpr e1, genExpr e2]
    genExpr (LetBang vs v e1 e2) = genExpr (Let v e1 e2)
    genExpr (Take v f vf e1 e2) = format "C.Let($3, $0=> C.Let(($3).$1, $2=> $4))"
                                         [v,f,vf,genExpr e1, genExpr e2]
    genExpr (Put e1 f e2) = case e1 of
       Sig e1' (Record _ Unboxed) 
         -> format "C.UPut($0,{$1:$2})"          [genExpr e1', f, genExpr e2]
       _ -> format "Object.assign($0,{$1:$2})" [genExpr e1 , f, genExpr e2]
    
    genExpr (Member e1 f) = format "($0).$1" [genExpr e1, f]
    genExpr (Case e c v1 e1 v2 e2) = format "C.Case($0, $1, $2=>$3,$4=>$5)" 
                                     [genExpr e, show c, v1, genExpr e1, v2, genExpr e2]
    genExpr (Esac e c v1 e1) = format "C.Let(($0).val, $1=>$2)"
                               [genExpr e, v1, genExpr e1]
    
    genDef :: (FunName, (VarName, Expr)) -> String
    genDef (f,(v,e)) = format "function $0 ($1) { return $2; };" [f, v, genExpr e]
    
    genDefs :: [(FunName, (VarName, Expr))] -> String
    genDefs = unlines . map genDef
  
