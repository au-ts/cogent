--
-- Copyright 2017, NICTA
--
-- This software may be distributed and modified according to the terms of
-- the GNU General Public License version 2. Note that NO WARRANTY is provided.
-- See "LICENSE_GPLv2.txt" for details.
--
-- @TAG(NICTA_GPL)
--

{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}

module Cogent.DocGent where

import Cogent.Common.Syntax
import Cogent.Common.Types
import Cogent.Compiler (__impossible, __todo, __fixme)
import Cogent.PrettyPrint
import Cogent.Surface
import Cogent.Util
import Paths_cogent

import Lens.Micro.Mtl ((.=), use)
import Lens.Micro.TH
import Control.Monad.State as S
import Data.Char (isLower, toUpper)
import Data.Default
import qualified Data.Foldable as F
import Data.Function (on)
import Data.List (intersperse, sortBy, groupBy)
import qualified Data.Map as M
import Data.Maybe
import Data.Ord (comparing)
#if MIN_VERSION_pandoc(2,0,0)
import Data.Text (pack)
#else
#endif
import Data.String
import System.Console.ANSI
import System.Directory
import System.FilePath
import Text.Blaze
import Text.Blaze.Html.Renderer.String
import qualified Text.Blaze.Html5 as H
import qualified Text.Blaze.Html5.Attributes as HA
import Text.Hamlet
import qualified Text.Pandoc as T
import qualified Text.Pandoc.Walk as T
import Text.Parsec
import Text.PrettyPrint.ANSI.Leijen (SimpleDoc(..), Pretty(..))
import qualified Text.PrettyPrint.ANSI.Leijen as P

data SGRState = SGRState { _intensity :: ConsoleIntensity
                         , _fg :: (ColorIntensity, Color)
                         , _bg :: (ColorIntensity, Color)
                         , _italics :: Bool
                         , _underline :: Underlining
                         }

makeLenses ''SGRState

markdown :: (?knowns :: [(String, SourcePos)]) => String -> Html
#if MIN_VERSION_pandoc(2,0,0)
markdown s = case T.runPure (T.readMarkdown def (pack s) >>= \md -> T.writeHtml5 def (T.walk handleInline md)) of
               Left e -> fromString $ show e
               Right html -> html
#else
markdown s = case T.readMarkdown def s of
               Left e -> fromString $ show e
               Right md -> T.writeHtml def $ T.walk handleInline md
#endif

handleInline :: (?knowns :: [(String, SourcePos)]) => T.Inline -> T.Inline
handleInline x@(T.Code a str) | Just p <- lookup str ?knowns = T.Link ("", classesFor str, []) [x] (fileNameFor p ++ "#" ++ str,str)
handleInline x = x

classesFor :: String -> [String]
classesFor (x:xs) | isLower x = pure "fg-Vivid-Green"
classesFor _ = pure "fg-Vivid-Blue"

currentSpan :: (?knowns :: [(String, SourcePos)]) => String -> S.State SGRState Html
currentSpan s = do
  let showColor (a,b) = show a ++ "-" ++ show b
  i <- show <$> use intensity
  f <- ("fg-" ++ ). showColor <$> use fg
  b <- ("bg-" ++ ). showColor <$> use bg
  t <- use italics >>= \x -> return $ if x then "Italics" else ""
  u <- show <$> use underline
  if (f == "fg-Vivid-Blue") then
      case lookup s ?knowns of
        Nothing -> 
          return $ H.span H.! HA.class_ (fromString $ unwords [i,f,b,t,u]) $ H.string s
        Just p ->
          return $ H.a H.! HA.class_ (fromString $ unwords [i,f,b,t,u])
                       H.! HA.href (fromString $ fileNameFor p ++ "#" ++ s)
                 $ H.string s
    else
      if (f == "fg-Vivid-Green" && u == "SingleUnderline") then
        case lookup s ?knowns of
          Nothing ->
            return $ H.span H.! HA.class_ (fromString $ unwords [i,f,b,t,u]) $ H.string s
          Just p ->
            return $ H.a H.! HA.class_ (fromString $ unwords [i,f,b,t,u])
                         H.! HA.href (fromString $ fileNameFor p ++ "#" ++ s)
                   $ H.string s
      else
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

listTypes :: (?knowns :: [(String, SourcePos)]) => [LocType] -> Html
listTypes [x] = prettyType x Nothing
listTypes ts = let row x = let t = prettyType x Nothing in [shamlet|<tr><td>#{t}</td>|]
                   rows = map row ts
                in [shamlet|<table>#{rows}<td></td>|]

prettyPT :: (?knowns :: [(String, SourcePos)]) => Polytype LocType -> Html
prettyPT (PT [] t) = prettyType t Nothing
prettyPT (PT vs t) = let top = fst $ runState (displayHTML (prettyPrint id [renderPolytypeHeader vs])) defaultState
                         bottom = prettyType t Nothing
                      in [shamlet| <table><tr><td>#{top}</td><td></td></tr><tr><td>#{bottom}</td></tr>|]

prettyType :: (?knowns :: [(String, SourcePos)]) => LocType -> Maybe Html -> Html
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
prettyType (Documentation d t) Nothing = let doc = markdown d
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
prettyType (LocType p (TCon t ts Unboxed)) x 
  = if t `elem` primTypeCons then prettyType (LocType p (TCon t ts $ __fixme(Unboxed) {- was originally Boxed False noRepE, not sure what is right-})) x
                             else prettyType (LocType p (TUnbox (LocType p (TCon t ts $ Boxed False Nothing)))) x
prettyType (LocType p (TCon t ts (Boxed True (Just l)))) x
  = prettyType (LocType p (TBang (LocType p (TCon t ts $ __fixme(Boxed False Nothing) {- Should be (Just l), fix when docGen layouts implemented-})))) x
prettyType (LocType p (TCon t ts (Boxed False (Just l)))) x 
  | not $ null ts = let rest = foldMap id x
                        row t = let t' = prettyType t Nothing in [shamlet|<tr><td></td><td class='spaced'>#{t'}</td>|]
                        rows = map row ts
                        t' = withLinking ?knowns t
                     in [shamlet|<table><tr><td class='fg-Vivid-Blue BoldIntensity'>#{t'}</td><td></td><td></td></tr>#{rows}<tr><td></td><td>#{rest}</td></tr>|]
prettyType (LocType p (TVariant ts)) x | any snd $ (F.toList ts)
                                       , ls <- map fst $ filter (snd . snd) (M.toList ts)
                                       , ts' <- fmap (fmap (const False)) ts
                                           = prettyType (LocType p (TTake (Just ls) (LocType p (TVariant ts' )))) x
                                       | otherwise
                                           = let rest = foldMap id x
                                                 row (g,ts) s = let t' = listTypes ts in [shamlet|<tr><td>#{s}</td><td class='fg-Dull-Magenta spaced'>#{g}</td><td class='spaced'>#{t'}</td>|]
                                                 rows = zipWith row (M.toList $ fmap fst ts) $ '<' : repeat '|'
                                              in [shamlet|<table>#{rows}<tr><td>></td><td class='spaced' colspan=2>#{rest}</td><td></td></tr>|]
prettyType (LocType p (TRecord ts Unboxed))  x
  = prettyType (LocType p (TUnbox (LocType p (TRecord ts $ Boxed False Nothing)))) x
prettyType (LocType p (TRecord ts (Boxed True (Just l)))) x
  = prettyType (LocType p (TBang (LocType p (TRecord ts $ __fixme(Boxed False Nothing) {- Should be (Just l), fix when docGen layouts implemented -})))) x
prettyType (LocType p (TRecord ts (Boxed False (Just l)))) x
  | ls <- map fst (filter (snd . snd) ts)
  , not (null ls) = prettyType (LocType p (TTake (Just ls) (LocType p (TRecord ts $ __fixme(Boxed False Nothing) {- Should be (Just l), fix when docGen layouts implemented-})))) x
  | otherwise = let rest = foldMap id x
                    row (g,(t,_)) s = let t' = prettyType t Nothing in [shamlet|<tr><td>#{s}</td><td class='spaced fg-Vivid-Magenta'>#{g}</td><td class='spaced'>:</td><td class='spaced'>#{t'}</td>|]
                    rows = zipWith row ts $ '{' : repeat ','
                 in [shamlet|<table>#{rows}<tr><td>}</td><td class='spaced' colspan=3>#{rest}</td><td></td></tr>|]
prettyType x (Just y) = fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState) `mappend` y
prettyType x Nothing = fst (runState (displayHTML (prettyPrint id [pretty x])) defaultState)

withLinking :: [(String, SourcePos)] -> String -> Html
withLinking s t = case lookup t s of
                     Just p -> [shamlet|<a href="#{file p}##{t}">#{t} |]
                     Nothing -> H.toHtml t
  where file p = fileNameFor p

data DocExpr = DE { unDE :: Expr RawType RawPatn RawIrrefPatn DocExpr }
             | DocFnCall FunName [Maybe RawType] Inline deriving Show

instance ExprType DocExpr where
  isVar (DE e) s = isVar e s
  isVar _ _ = False

instance Prec DocExpr where
  prec (DE e) = prec e
  prec _ = 100

instance Pretty DocExpr where
  pretty (DE e) = pretty e
  pretty (DocFnCall x [] note) = pretty note P.<> funname' x
  pretty (DocFnCall x ts note) = pretty note P.<> funname' x P.<> typeargs (map pretty ts)

resolveNamesA :: [String] -> Alt RawPatn RawExpr -> Alt RawPatn DocExpr
resolveNamesA lcls (Alt p l e) = Alt p l $ resolveNames (lcls ++ fvP p) e

resolveNames :: [String] -> RawExpr -> DocExpr
resolveNames lcls (RE (TypeApp v ts i)) | v `notElem` lcls = DocFnCall v ts i
                                        | otherwise        = DE (TypeApp v ts i)
resolveNames lcls (RE (Var v)) | v `notElem` lcls = DocFnCall v [] NoInline
                               | otherwise = DE (Var v)
resolveNames lcls (RE (Match e t alts)) = DE (Match (resolveNames lcls e) t (map (resolveNamesA lcls) alts))
resolveNames lcls (RE (Let bs e)) = let (lcls', bs') = resolveBinders lcls bs in DE (Let bs' $ resolveNames lcls' e)
resolveNames lcls (RE e) = DE (fmap (resolveNames lcls) e)

resolveBinders :: [String]
               -> [Binding RawType RawPatn RawIrrefPatn RawExpr]
               -> ([String], [Binding RawType RawPatn RawIrrefPatn DocExpr])
resolveBinders lcls [] = (lcls, [])
resolveBinders lcls (x:xs) = let (lcls',x') = resolveBinder lcls x
                                 (lcls'', xs') = resolveBinders lcls' xs
                              in (lcls'',x':xs')

resolveBinder :: [String]
              -> Binding RawType RawPatn RawIrrefPatn RawExpr
              -> ([String], Binding RawType RawPatn RawIrrefPatn DocExpr)
resolveBinder lcls (Binding ip t e bs) = (lcls ++ fvIP ip, Binding ip t (resolveNames lcls e) bs)
resolveBinder lcls (BindingAlts p t e bs alts) =
  ( lcls ++ fvP p ++ foldMap fvA alts
  , BindingAlts p t (resolveNames lcls e) bs (map (resolveNamesA lcls) alts)
  )

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
adjustSGRs (SetRGBColor _ _) = __todo "not implemented"

displayHTML :: (?knowns :: [(String, SourcePos)]) => SimpleDoc -> S.State SGRState Html
displayHTML (SFail) = error ""
displayHTML (SEmpty) = return mempty
displayHTML (SChar c d) = mappend <$> currentSpan [c] <*> displayHTML d
displayHTML (SText _ s d) = mappend <$> currentSpan s <*> displayHTML d
displayHTML (SLine i d) = mappend (preEscapedString ('\n':replicate (abs i) ' ') ) <$> displayHTML d
displayHTML (SSGR sgrs d) = mapM_ adjustSGRs sgrs >> displayHTML d

makeHtml :: Html -> Html
makeHtml content = [shamlet| <pre class="source bg-Dull-Black">#{content}|]


genDoc :: (?knowns :: [(String, SourcePos)]) => (SourcePos, DocString, TopLevel LocType LocPatn LocExpr) -> Html
genDoc (p,s,x@(Include    {})) = __impossible "genDoc"
genDoc (p,s,x@(IncludeStd {})) = __impossible "genDoc"

genDoc (p,s,x@(TypeDec n ts t)) =
    let header = let ?knowns = [] in runState (displayHTML (prettyPrint id $ return $ renderTypeDecHeader n ts)) defaultState
        df     = prettyType t Nothing
        block  = [shamlet|<table><td><a name='#{n}'>#{fst header}</a></td><td class='spaced'>#{df}</td>|]
        md     = markdown s
     in [shamlet|
                 #{sourcePosDiv p}
                 <div class="block bg-Dull-Black header">
                    #{block}
                 <div class="docstring footerds">
                    #{md} |]
genDoc (p,s,x@(FunDef n pt as)) =
    let n' x = [shamlet|<table><td class='fg-Vivid-Green'><a name='#{n}'><b>#{n}</b></a></td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
        pt' = prettyPT pt
        md  = markdown s
        str = flip runState defaultState $ 
                displayHTML (prettyPrint id $ return $ prettyFunDef False n pt $ map (resolveNamesA [] . fmap stripLocE . ffmap stripLocP) as)
        source = makeHtml $ fst str
     in
        [shamlet|
               #{sourcePosDiv p}
               <div class="block bg-Dull-Black header">
                 #{n' pt'}
               <div class="docstring">
                 #{md}
               <div .shbutton .bg-Dull-Black .footer>
                 <a id="hide#{n}" .hide href="#hide#{n}" >(show source)</a>
                 <a id="show#{n}" .show href="#show#{n}" >(hide source)</a>
                 <div class="answer">
                   #{source} |]
genDoc (p,s,x@(AbsDec n pt)) = do
     let n' x = [shamlet|<table><td class='fg-Vivid-Green'><a name='#{n}'><b>#{n}</b></a> </td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
         pt' = prettyPT pt
         md  = markdown s
      in [shamlet|
              #{sourcePosDiv p}
              <div class="block bg-Dull-Black header">
                #{n' pt'}
              <div class="docstring footerds">
                #{md} |]
genDoc (p,s,(ConstDef n t as)) =
     let n' x = [shamlet|<table><td class='fg-Vivid-Green'><a name='#{n}'><b>#{n}</b></a> </td><td class='spaced'>:</td><td class='spaced'>#{x}</td> |]
         pt' = prettyPT (PT [] t)
         md     = markdown s
         str = runState (displayHTML (prettyPrint id $ return $ prettyConstDef False n t $ resolveNames [] $ stripLocE as) ) defaultState
         source = makeHtml $ fst str
      in [shamlet|
                  #{sourcePosDiv p}
                  <div class="block bg-Dull-Black header">
                    #{n' pt'}
                  <div class="docstring">
                    #{md}
                  <div .shbutton .bg-Dull-Black .footer>
                    <a id="hide-#{n}" .hide href="#hide-#{n}" >(show source)</a>
                    <a id="show-#{n}" .show href="#show-#{n}" >(hide source)</a>
                    <div class="answer">
                      #{source} |]
genDoc (p,_,DocBlock s) =
                 let md = markdown s
                 in [shamlet| <div .docblock>#{md} |]
genDoc (p,s,x@(AbsTypeDec n _ _)) =
                 let x' = stripAllLoc x
                     str = let ?knowns = [] in runState (displayHTML (prettyPrint id $ return x') ) defaultState
                     md     = markdown s
                  in [shamlet|
                             #{sourcePosDiv p}
                             <div class="block bg-Dull-Black header">
                                <a name=#{n}> #{fst str}
                             <div class="docstring footerds">
                                #{md}|]


template :: String -> String -> Html -> Html
template "" title body = [shamlet|
<html>
  <head>
    <script type="text/javascript" src="jquery.min.js">
    <script type="text/javascript" src="toc.min.js">
    <title>
      #{title}
    <script>
        jQuery(function() {
          jQuery('#toc').toc();
        });
    <link rel="stylesheet" href="style.css" />
  <body>
    <div #topmatter>
      <div .links>
        <a href="index.html">Contents
        <a href="binding_index.html">Index
      <img src="logo.png">
      <span .pagetitle>#{title}
      <div #toc>
    <div #main>
      #{body}
|]
template raw title body = [shamlet|
<html>
  <head>
    <script type="text/javascript" src="jquery.min.js">
    <script type="text/javascript" src="toc.min.js">
    <title>
      #{title}
    <script>
        jQuery(function() {
          jQuery('#toc').toc();
        });
    <link rel="stylesheet" href="style.css" />
  <body>
    <div #topmatter>
      <div .links>
        <a href="index.html">Contents
        <a href="binding_index.html">Index
        <a href="#{raw}">Raw
      <img src="logo.png">
      <span .pagetitle>#{title}
      <div #toc>
    <div #main>
      #{body}
|]

rawTemplate :: Html -> Html
rawTemplate body = [shamlet|
<html>
  <head>
    <style>
      pre {
        font-family: PragmataPro, Iosevka, monospace;
      }
  <body>
    <pre>
      #{body}
|]


foreach ::  (?knowns :: [(String,SourcePos)]) => (SourcePos, DocString, TopLevel LocType LocPatn LocExpr) -> (SourcePos, Html)
foreach (p, d, t) = (p,  genDoc (p,d,t))

titleFor :: SourcePos -> IO String
titleFor pos = do
  x <- canonicalizePath $ sourceName pos
  x' <- makeRelativeToCurrentDirectory x
  return x'

fileNameFor pos = (++".html") $ concat $ intersperse "." $ words $ map (\x -> if x `elem` ("./\\" :: String) then ' ' else x) $ sourceName pos
rawFileNameFor pos = (++".raw.html") $ concat $ intersperse "." $ words $ map (\x -> if x `elem` ("./\\" :: String) then ' ' else x) $ sourceName pos

commonPrefix :: (Eq e) => [e] -> [e] -> [e]
commonPrefix _ [] = []
commonPrefix [] _ = []
commonPrefix (x:xs) (y:ys)
  | x == y    = x : commonPrefix xs ys
  | otherwise = []

commonPrefix' :: FilePath -> FilePath -> FilePath
commonPrefix' p1 p2 = joinPath (commonPrefix (splitDirectories p1) (splitDirectories p2))

commonOfAll :: [FilePath] -> FilePath
commonOfAll [x] = takeDirectory x
commonOfAll []  = "."
commonOfAll rest = foldr1 commonPrefix' rest

sourcePosDiv p = do
  let f = takeFileName (sourceName p)
      c = show $ sourceLine p
      raw = rawFileNameFor p
   in [shamlet|<div .sourcepos><a href='#{raw}##{c}'>#{f}:#{c}</a>|]

docGent :: [(SourcePos, DocString, TopLevel LocType LocPatn LocExpr)] -> IO ()
docGent input = let
                    ?knowns = mapMaybe toKnown input
                in let
                    items = map foreach input
                    items' = sortBy (comparing fst) items
                    items'' = groupBy ((==) `on` (sourceName . fst) ) items'
                in do createDirectoryIfMissing True "docgent"
                      jq  <- getDataFileName "static/jquery.min.js"
                      toc <- getDataFileName "static/toc.min.js"
                      sty <- getDataFileName "static/style.css"
                      log <- getDataFileName "static/logo.png"
                      copyFile jq "docgent/jquery.min.js"
                      copyFile toc "docgent/toc.min.js"
                      copyFile sty "docgent/style.css"
                      copyFile log "docgent/logo.png"
                      titles <- mapM (titleFor . fst . head) items''
                      let titles' = map (drop (length (commonOfAll titles))) titles
                      flip mapM_ (zip titles' items'') $ \(title, xs@((pos, _):_)) -> do
                        let n = ("docgent/"++) $ fileNameFor pos
                            rn = ("docgent/"++) $ rawFileNameFor pos
                        let content = renderHtml $ template (rawFileNameFor pos) title (mconcat $ map snd xs)
                        rawContent <- readFile (sourceName pos)
                        let rawContent' = mconcat $ zipWith (\l a -> [shamlet|<a name=#{a}>#{l}|]) (lines rawContent) ([1..] :: [Int])
                            rawContent'' = renderHtml $ rawTemplate rawContent'
                        writeFile n content
                        writeFile rn rawContent''
                      generateIndex ?knowns
                      generateContents $ zip titles' (map (fst . head) items'')
  where toKnown (p, _, Include {})        = Nothing
        toKnown (p, _, IncludeStd {})     = Nothing
        toKnown (p, _, TypeDec tn _ _)    = Just (tn, p)
        toKnown (p, _, AbsTypeDec tn _ _) = Just (tn, p)
        toKnown (p, _, AbsDec tn _)       = Just (tn, p)
        toKnown (p, _, FunDef tn _ _)     = Just (tn, p)
        toKnown (p, _, ConstDef tn _ _)   = Just (tn, p)
        toKnown (p, _, DocBlock s) = Nothing

generateContents :: [(String, SourcePos)] -> IO ()
generateContents dat = do
  let content = sortBy (comparing fst) dat
      groups  = groupBy ((==) `on` takeDirectory . fst) content
      eachGroup is@((fp,_):_) | d <- takeDirectory fp =
                                   [shamlet|
                                           <h1 .contentsh1>#{d}
                                           #{thiscontent is}|]
      eachGroup _ = error "impossible"
      thiscontent is = mconcat $ map eachItem is
      eachItem (s,p) = let
        link = fileNameFor p
        in [shamlet|
           <div .contentsitem><a href='#{link}'>#{takeFileName s}</a> |]
      content' = mconcat (map eachGroup groups)
      final = template "" "Contents" content'
   in writeFile "docgent/index.html" (renderHtml final)

generateIndex :: [(String, SourcePos)] -> IO ()
generateIndex dat = do
  let content = sortBy (comparing (map toUpper . fst)) dat
      groups  = groupBy ((==) `on` toUpper . head . fst) content
      eachGroup is@((c:_,_):_) | c' <- [toUpper c] =
                                   [shamlet|
                                           <h1>#{c'}
                                           #{thiscontent}|]
        where thiscontent = mconcat $ map eachItem is
      eachGroup _ = error "impossible"
      eachItem (s,p) = let
          link = fileNameFor p  ++ "#" ++ s
        in [shamlet|
           <div .indexitem><a href='#{link}' class='#{concat (classesFor s)}'>#{s}</a>
             #{sourcePosDiv p}|]
      content' = mconcat (map eachGroup groups)
      final = template "" "Index" content'
   in writeFile "docgent/binding_index.html" (renderHtml final)

-- XXX | eqTopLevelId x (Include {}) = False
-- XXX | eqTopLevelId x (IncludeStd {}) = False
-- XXX | eqTopLevelId x (TypeDec tn _ _) = x == tn
-- XXX | eqTopLevelId x (AbsTypeDec tn _) = x == tn
-- XXX | eqTopLevelId x (AbsDec fn _) = x == fn
-- XXX | eqTopLevelId x (FunDef fn _ _) = x == fn
-- XXX | eqTopLevelId x (ConstDef vn _ _) = x == vn  -- should not matter

