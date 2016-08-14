{-# LANGUAGE QuasiQuotes, OverloadedStrings, TemplateHaskell #-}
module COGENT.DocGent where
import Text.Blaze.Html.Renderer.String
import Text.Parsec
import Text.Hamlet
import Control.Monad.State as S
import COGENT.PrettyPrint
import COGENT.Surface
import COGENT.Common.Syntax
import COGENT.Common.Types
import Text.PrettyPrint.ANSI.Leijen (SimpleDoc(..), pretty)
import System.Console.ANSI
import Text.Blaze
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as HA
import qualified Data.Map as M
import Data.String
import Control.Lens
import Text.Markdown
import qualified Data.Text.Lazy as T
import Data.List (intersperse)
import qualified Data.Foldable as F
data SGRState = SGRState { _intensity :: ConsoleIntensity, _fg :: (ColorIntensity, Color), _bg :: (ColorIntensity, Color), _italics :: Bool, _underline :: Underlining }
makeLenses ''SGRState

currentSpan :: String -> S.State SGRState Html
currentSpan s = do
  let showColor (a,b) = show a ++ "-" ++ show b
  i <- show <$> use intensity
  f <- ("fg-" ++ ). showColor <$> use fg
  b <- ("bg-" ++ ). showColor <$> use bg
  t <- use italics >>= \x -> return $ if x then "Italics" else ""
  u <- show <$> use underline
  return $ H.span H.! HA.class_ (fromString $ unwords [i,f,b,t,u]) $ H.string s
defaultState = SGRState NormalIntensity (Dull, White) (Dull, Black) False NoUnderline

prettyFieldNames :: Maybe [String] -> Html
prettyFieldNames Nothing = [shamlet|(<span class='fg-Dull-Magenta'>..)|]
prettyFieldNames (Just fs)= let f x = [shamlet|<span class='fg-Dull-Magenta'>x</span>|]
                                fs' = mconcat $ intersperse [shamlet|, |] (map f fs)
                             in [shamlet|(#{fs'})|]

containsDocumentation :: LocType -> Bool
containsDocumentation (Documentation {}) = True
containsDocumentation (LocType _ t) = any containsDocumentation $ F.toList t

listTypes :: [LocType] -> Html
listTypes [x] = prettyType x Nothing
listTypes ts = let row x = let t = prettyType x Nothing in [shamlet|<tr><td>#{t}</td>|]
                   rows = map row ts
                in [shamlet|<table>#{rows}<td></td>|]

prettyPT :: Polytype LocType -> Html
prettyPT (PT [] t) = prettyType t Nothing
prettyPT (PT vs t) = let top = fst $ runState (displayHTML (prettyPrint id [renderPolytypeHeader vs])) defaultState
                         bottom = prettyType t Nothing
                      in [shamlet| <table><tr><td>#{top}</td><td></td></tr><tr><td>#{bottom}</td></tr>|]
prettyType :: LocType -> Maybe Html -> Html
prettyType x y | not (containsDocumentation x)  =  case y of 
                      (Just y) -> fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState) `mappend` y
                      Nothing -> fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState)
prettyType (LocType _ (TPut fs t)) x = let rest = foldMap id x
                                           fs' = prettyFieldNames fs
                                        in prettyType t (Just [shamlet|<span> <span class='fg-Vivid-Cyan'>put</span> #{fs'} #{rest}|] )
prettyType (LocType _ (TTake fs t)) x = let rest = foldMap id x
                                            fs' = prettyFieldNames fs
                                        in prettyType t (Just [shamlet|<span> <span class='fg-Vivid-Cyan'>take</span> #{fs'} #{rest}|] )
prettyType (LocType _ (TBang t)) x = let rest = foldMap id x in prettyType t (Just [shamlet|<span> <span class='fg-Vivid-Cyan'>!</span> #{rest}|] )
prettyType (LocType _ (TUnbox t)) x = let rest = prettyType t x in [shamlet|<table><tr><td class='fg-Vivid-Cyan'>#</td><td>#{rest}</td></tr>|]
prettyType (Documentation d t) (Just x) = let it = prettyType (Documentation d t) Nothing
                                           in [shamlet|<table><tr><td>(</td><td>#{it} </td><td></td> </tr><tr><td>)</td><td>#{x}</td></tr>|]
prettyType (Documentation d t) Nothing = let doc = markdown def (T.pack d)
                                          in prettyType t (Just [shamlet|
                                                                        <div .invisibledoc>#{doc}
                                                                        <div .inlinedoc>#{doc} |])
prettyType (LocType _ (TFun a b)) Nothing = let a' = prettyType a Nothing; b' = prettyType b Nothing
                                             in [shamlet|<table><tr><td> </td><td class='spaced'>#{a'}</td><td></td></tr><tr><td class='fg-Vivid-Cyan'>-></td><td class='spaced'>#{b'}</td></tr>|]
prettyType (LocType p (TFun a b)) (Just x) = let it = prettyType (LocType p (TFun a b)) Nothing
                                              in [shamlet|<table><tr><td>(</td><td>#{it} </td><td></td> </tr><tr><td>)</td><td>#{x}</td></tr>|]
prettyType (LocType _ (TTuple ts)) x       = let rest = foldMap id x
                                                 row t s = let t' = prettyType t Nothing in [shamlet|<tr><td>#{s}</td><td class='spaced'>#{t'}</td>|]
                                                 rows = zipWith row ts $ '(' : repeat ','
                                              in [shamlet|<table>#{rows}<tr><td>)</td><td>#{rest}</td><td></td></tr>|]
prettyType (LocType p (TCon t ts Unboxed))  x = if t `elem` primTypeCons then prettyType (LocType p (TCon t ts Writable)) x
                                                                         else prettyType (LocType p (TUnbox (LocType p (TCon t ts Writable)))) x
prettyType (LocType p (TCon t ts ReadOnly)) x = prettyType (LocType p (TBang (LocType p (TCon t ts Writable)))) x
prettyType (LocType p (TCon t ts Writable)) x | not $ null ts = let rest = foldMap id x
                                                                    row t = let t' = prettyType t Nothing in [shamlet|<tr><td></td><td class='spaced'>#{t'}</td>|]
                                                                    rows = map row ts
                                                                in [shamlet|<table><tr><td class='fg-Vivid-Blue BoldIntensity'>#{t}</td><td></td><td></td></tr>#{rows}<tr><td></td><td>#{rest}</td></tr>|]
prettyType (LocType _ (TVariant ts)) x     = let rest = foldMap id x
                                                 row (g,ts) s = let t' = listTypes ts in [shamlet|<tr><td>#{s}</td><td class='fg-Dull-Magenta spaced'>#{g}</td><td class='spaced'>#{t'}</td>|]
                                                 rows = zipWith row (M.toList ts) $ '<' : repeat '|'
                                              in [shamlet|<table>#{rows}<tr><td>></td><td class='spaced' colspan=2>#{rest}</td><td></td></tr>|]
prettyType (LocType p (TRecord ts Unboxed))  x = prettyType (LocType p (TUnbox (LocType p (TRecord ts Writable)))) x
prettyType (LocType p (TRecord ts ReadOnly)) x = prettyType (LocType p (TBang (LocType p (TRecord ts Writable)))) x
prettyType (LocType p (TRecord ts Writable)) x | ls <- map fst (filter (snd . snd) ts)
                                               , not (null ls) = prettyType (LocType p (TTake (Just ls) (LocType p (TRecord ts Writable)))) x
                                               | otherwise = let rest = foldMap id x
                                                                 row (g,(t,_)) s = let t' = prettyType t Nothing in [shamlet|<tr><td>#{s}</td><td class='spaced fg-Vivid-Magenta'>#{g}</td><td class='spaced'>:</td><td class='spaced'>#{t'}</td>|]
                                                                 rows = zipWith row ts $ '{' : repeat ','
                                                              in [shamlet|<table>#{rows}<tr><td>}</td><td class='spaced' colspan=3>#{rest}</td><td></td></tr>|]
prettyType x (Just y) = fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState) `mappend` y
prettyType x Nothing = fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState)

{- 
data Type t =
            -- They are in WHNF
            | TRecord [(FieldName, (t, Taken))] Sigil
            | TVariant (M.Map TagName [t])
            -- They will be elimiated at some point / zilinc
            deriving (Show, Functor, Eq, Foldable, Traversable)
-}
adjustSGRs :: SGR -> S.State SGRState ()
adjustSGRs Reset = put defaultState
adjustSGRs (SetConsoleIntensity   c) = intensity .= c
adjustSGRs (SetItalicized         c) = italics   .= c
adjustSGRs (SetUnderlining        c) = underline .= c
adjustSGRs (SetBlinkSpeed         _) = return ()
adjustSGRs (SetVisible            _) = return ()
adjustSGRs (SetColor Foreground i c) = fg .= (i, c)
adjustSGRs (SetColor Background i c) = bg .= (i, c)
adjustSGRs (SetSwapForegroundBackground _) = return ()
displayHTML :: SimpleDoc -> S.State SGRState Html
displayHTML (SFail) = error ""
displayHTML (SEmpty) = return mempty
displayHTML (SChar c d) = mappend <$> currentSpan [c] <*> displayHTML d
displayHTML (SText _ s d) = mappend <$> currentSpan s <*> displayHTML d
displayHTML (SLine i d) = mappend (preEscapedString ('\n':replicate (abs i) ' ') ) <$> displayHTML d
displayHTML (SSGR sgrs d) = mapM_ adjustSGRs sgrs >> displayHTML d
makeHtml :: Html -> Html
makeHtml content = [shamlet| <pre class="source bg-Dull-Black">#{content}|]

genDoc :: (SourcePos, DocString, TopLevel LocType VarName LocExpr) -> Html
genDoc (p,s,x@(TypeDec n ts t)) = let header = runState (displayHTML (prettyPrint id $ return $ renderTypeDecHeader n ts)) defaultState
                                      df     = prettyType t Nothing
                                      block  = [shamlet|<table><td>#{fst header}</td><td class='spaced'>#{df}</td>|]
                                      md     = markdown def (T.pack s)
                                   in [shamlet|
                                           <div class="block bg-Dull-Black header">
                                             #{block}
                                           <div class="docstring footerds">
                                             #{md} |]
genDoc (p,s,x@(FunDef n pt as)) = let n' x = [shamlet|<table><td class='fg-Vivid-Green'><b>#{n}</b> </td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
                                      pt' = prettyPT pt
                                      md     = markdown def (T.pack s)
                                      str = runState (displayHTML (prettyPrint id $ return $ prettyFunDef False n pt $ fmap (fmap stripLocE) as) ) defaultState
                                      source = makeHtml $ fst str
                               in
                                   [shamlet|
                                          <div class="block bg-Dull-Black header">
                                            #{n' pt'}
                                          <div class="docstring">
                                            #{md}
                                          <div .shbutton .bg-Dull-Black .footer>
                                            <a id="hide#{n}" .hide href="#hide#{n}" >(show source)</a>
                                            <a id="show#{n}" .show href="#show#{n}" >(hide source)</a>
                                            <div class="answer">
                                              #{source} |]
genDoc (p,s,x@(AbsDec n pt))     = let n' x = [shamlet|<table><td class='fg-Vivid-Green'><b>#{n}</b> </td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
                                       pt' = prettyPT pt
                                       md  = markdown def (T.pack s)
                                   in [shamlet|
                                           <div class="block bg-Dull-Black header">
                                             #{n' pt'}
                                           <div class="docstring footerds">
                                             #{md} |]
genDoc (p,s,(ConstDef n t as)) = let n' x = [shamlet|<table><td class='fg-Vivid-Green'><b>#{n}</b> </td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
                                     pt' = prettyPT (PT [] t)
                                     md     = markdown def (T.pack s)
                                     str = runState (displayHTML (prettyPrint id $ return $ prettyConstDef False n t $ stripLocE as) ) defaultState
                                     source = makeHtml $ fst str
                             in [shamlet|
                                         <div class="block bg-Dull-Black header">
                                           #{n' pt'}
                                         <div class="docstring">
                                           #{md}
                                         <div .shbutton .bg-Dull-Black .footer>
                                           <a id="hide#{n}" .hide href="#hide#{n}" >(show source)</a>
                                           <a id="show#{n}" .show href="#show#{n}" >(hide source)</a>
                                           <div class="answer">
                                             #{source} |]
genDoc (p,s,x) = let x' = stripAllLoc x
                     str = runState (displayHTML (prettyPrint id $ return x') ) defaultState
                     md     = markdown def (T.pack s)
                  in [shamlet|
                             <div class="block bg-Dull-Black header">
                                #{fst str}
                             <div class="docstring footerds">
                                #{md}|]

template body = [shamlet|
<html>
  <head>
    <style>
      .block {
       margin-top: 0px; font-family: PragmataPro, Iosevka, monospace;
       padding-right: 100px !important;
       position:relative;
       display:inline-block;
      }
      table {
      border-spacing: 0px;
      }
      .block td {
             vertical-align: top;
             margin: 0px;
             padding: 0px 0px 0px 0px;
             white-space:nowrap;

      }
      .spaced {
         padding-left: 5px !important;
      }
      .invisibledoc p {
         display:inherit;
         margin: 0px;
      }
      .show {
        font-size:11px;
        color:white;
        text-decoration: none;
      }
      .hide {
        font-size: 11px;
        color:white;
        text-decoration: none;
      }
      .answer,
      .show,
      .hide:target {
          display: none;
      }
      .hide:target + .show,
      .hide:target ~ .answer {
          display: inline;
      }
      .invisibledoc {
      -webkit-user-select: none; /* Chrome/Safari */        
      -moz-user-select: none; /* Firefox */
      -ms-user-select: none; /* IE10+ */
       /* Rules below not implemented in browsers yet */
       -o-user-select: none;
       user-select: none;
         margin-top:0px;
         margin-bottom:0px;
         margin-left: 5px;
         display: inline-block;
         font-family: sans-serif;
         color: #2e3436;
      }
      .inlinedoc p {
         display:inherit;
         margin: 0px;
      }
      .inlinedoc {
         display: inline-block;
         font-family: sans-serif;
         color: #eeeecc;
         position:absolute;
         right: 10px;
      }
      body { background: #192021; color: #eeeeec; }
      .header {
      border-radius: 5px 5px 0px 0px;
      padding:5px;
      margin-top: 5px;
      }
      .footer {
      border-radius: 0px 0px 5px 5px;
      padding: 5px;
      margin-bottom: 5px;
      }
      .footerds {
      border-radius: 0px 5px 5px 5px !important;
      padding: 5px;
      margin-bottom: 5px;
      }
      .docstring { background: #555753; padding: 5px; font-family: sans-serif; border-radius: 0px 5px 0px 0px; }
      .docstring p { margin: 0px; }
      .shbutton { margin-top: 0px; font-family: PragmataPro, Iosevka, monospace; padding: 5px }
      .source { margin-top: 0px; font-family: PragmataPro, Iosevka, monospace; padding: 5px }
      .BoldIntensity { font-weight: bold }
      .fg-Dull-Black { color: #2e3436;}
      .fg-Dull-Red { color: #cc0000;}
      .fg-Dull-Green { color: #4e9a06;}
      .fg-Dull-Yellow { color: #c4a000;}
      .fg-Dull-Blue { color: #3465a4;}
      .fg-Dull-Magenta { color: #75507b;}
      .fg-Vivid-Magenta { color: #06989a;}
      .fg-Dull-White { color: #d3d7cf;}
      .fg-Vivid-Black { color: #555753;}
      .fg-Vivid-Red { color: #ef2929;}
      .fg-Vivid-Green { color: #8ae234;}
      .fg-Vivid-Yellow { color: #fce94f;}
      .fg-Vivid-Blue { color: #729fcf;}
      .fg-Vivid-Cyan { color: #ad7fa8;}
      .fg-Vivid-Magenta { color: #34e2e2;}
      .fg-Vivid-White { color: #eeeeec;}
      .bg-Dull-Black { background: #2e3436;}
      .bg-Dull-Red { background: #cc0000;}
      .bg-Dull-Green { background: #4e9a06;}
      .bg-Dull-Yellow { background: #c4a000;}
      .bg-Dull-Blue { background: #3465a4;}
      .bg-Dull-Magenta { background: #75507b;}
      .bg-Dull-Cyan { background: #06989a;}
      .bg-Dull-White { background: #d3d7cf;}
      .bg-Vivid-Black { background: #555753;}
      .bg-Vivid-Red { background: #ef2929;}
      .bg-Vivid-Green { background: #8ae234;}
      .bg-Vivid-Yellow { background: #fce94f;}
      .bg-Vivid-Blue { background: #729fcf;}
      .bg-Vivid-Cyan { background: #ad7fa8;}
      .bg-Vivid-Magenta { background: #34e2e2;}
      .bg-Vivid-White { background: #eeeeec;}
  <body>
    #{body}
|]
docGent :: [(SourcePos, DocString, TopLevel LocType VarName LocExpr)] -> IO ()
docGent input = let html = mconcat $ map genDoc input
                in  putStrLn $ renderHtml $ template html
