{- |
Module      :  ./Common/PrintLaTeX.hs
Description :  functions for LaTeX pretty printing
Copyright   :  (c) Klaus Luettich, Christian Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Functions for LaTeX pretty printing

-}

module Common.PrintLaTeX
    ( renderLatex
    , latexHeader
    , latexFooter
    )
    where

import Data.Char (isSpace, isDigit)
import Common.Lib.State
import Data.List (isPrefixOf, isSuffixOf)
import Data.Maybe (fromMaybe)

import Common.Lib.Pretty
import Common.LaTeX_funs

-- the header of the LaTeX-file that will be processed by pdflatex
latexHeader :: String
latexHeader = unlines
  [ "\\documentclass{article}"
  , "\\usepackage{hetcasl}"
  , "\\usepackage{textcomp}"
  , "\\usepackage[T1]{fontenc}"
  , "\\begin{document}" ]

-- the ending document string
latexFooter :: String
latexFooter = "\n\\end{document}\n"

-- a style for formatting (Standard is Style PageMode 50 1.19)
latexStyle :: Style
latexStyle = style
  { ribbonsPerLine = 1.1
  , lineLength = calcLineLen 345 }
  -- for svmono you need 336.0pt

{- a LatexRenderingState
   field indentTabs : for the number of tab
     stops set those need to be rendererd after every newline.
   field recentlySet : number of setTab makros indentTabs is only
      increased if recentlySet is 0 -}
data LRState = LRS
  { indentTabs :: ![Int]
  , recentlySet
  , totalTabStops
  , setTabsThisLine
  , indentTabsWritten :: !Int
  , onlyTabs :: !Bool
  , isSetLine :: !Bool
  , collSpaceIndents :: ![Int]
  , insideAnno :: Bool
  } deriving Show

-- the initial state for using the state based rendering via LRState
initialLRState :: LRState
initialLRState = LRS
  { indentTabs = []
  , recentlySet = 0
  , totalTabStops = 0
  , setTabsThisLine = 0
  , indentTabsWritten = 0
  , onlyTabs = False
  , isSetLine = False
  , collSpaceIndents = []
  , insideAnno = False
  }

showTextDetails :: TextDetails -> String
showTextDetails t = case t of
  Chr c -> [c]
  Str s -> s
  PStr s -> s

maxTabs :: Int
maxTabs = 12

-- a function that knows how to print LaTeX TextDetails
latexTxt :: TextDetails -> State LRState ShowS -> State LRState ShowS
latexTxt td cont = let s1 = showTextDetails td in case s1 of
  "" -> cont
  "\n" -> do
      annoBrace <- endOfLine
      indent <- getIndent
      s <- cont
      return $ annoBrace . showString "\\\\\n" . indent . s
  _ | all isSpace s1 -> do
      s2 <- cont
      return $ showChar ' ' . s2
    | s1 == startTab -> do
      indent <- addTabStop
      s2 <- cont
      return $ indent . s2
    | s1 == endTab -> do
      subTabStop
      cont
    | s1 == setTab -> do
      s <- get
      setTabStop
      s2 <- cont
      let (eAn, sAn) = if insideAnno s
            then (showChar '}', showString startAnno)
            else (id, id)
      return $ eAn
        . (if indentTabsWritten s
           + setTabsThisLine s > maxTabs
           || onlyTabs s then id else showString s1)
        . sAn . s2
    | setTabWSp
      `isPrefixOf`
      s1 -> do
      addTabWithSpaces s1
      cont
    | s1 == startAnno -> do
      setInsideAnno True
      s2 <- cont
      return $ showString s1 . s2
    | s1 == endAnno -> do
      setInsideAnno False
      s2 <- cont
      return $ showChar '}' . s2
    | "\\kill\n"
      `isSuffixOf`
      s1 -> do
      indent <- getIndent
      s2 <- cont
      return $ showString s1 . indent . s2
  _ -> do
      setOnlyTabs False
      s2 <- cont
      return $ showString s1 . s2

setOnlyTabs :: Bool -> State LRState ()
setOnlyTabs b = modify $ \ s -> s { onlyTabs = b }

setInsideAnno :: Bool -> State LRState ()
setInsideAnno b = modify $ \ s -> s { insideAnno = b }

-- a function to produce a String containing the actual tab stops in use
getIndent :: State LRState ShowS
getIndent = do
  s <- get
  let indentTabsSum = min (succ maxTabs) $ sum $ indentTabs s
      collSpcInds = collSpaceIndents s
  put $ s
    { indentTabsWritten = indentTabsSum
    , collSpaceIndents = []
    , onlyTabs = True
    , totalTabStops = max (totalTabStops s)
        $ indentTabsSum + length collSpcInds }
  let indent_fun = tabIndent indentTabsSum
      space_format sf1 i = sf1 . showString (replicate i '~')
        . showString "\\="
      new_tab_line = foldl space_format id (collSpaceIndents s)
        . showString "\\kill\n"
      sAnno = if insideAnno s then showString startAnno else id
  return $ (if null collSpcInds then indent_fun else
            indent_fun . new_tab_line . indent_fun) . sAnno

tabIndent :: Int -> ShowS
tabIndent n = foldl (.) id $ replicate n $ showString "\\>"

endOfLine :: State LRState ShowS
endOfLine = do
  s <- get
  put s
    { isSetLine = False
    , setTabsThisLine = 0 }
  return $ if insideAnno s then showChar '}' else id

setTabStop :: State LRState ()
setTabStop = modify $ \ s ->
    let new_setTabsThisLine = succ $ setTabsThisLine s
    in if onlyTabs s then s { isSetLine = True } else s
      { recentlySet = succ $ recentlySet s
      , setTabsThisLine = new_setTabsThisLine
      , totalTabStops = max (totalTabStops s)
          (new_setTabsThisLine + indentTabsWritten s)
      , isSetLine = True }

addTabWithSpaces :: String -> State LRState ()
addTabWithSpaces str = let
    delay :: Int
    delay = read . reverse . takeWhile isDigit . tail $ reverse str
  in modify $ \ s ->
  s { collSpaceIndents = collSpaceIndents s ++ [delay] }

-- increase the indentTabs in the state by 1
addTabStop :: State LRState ShowS
addTabStop = state $ \ s ->
  let lineSet = isSetLine s
      recent = recentlySet s
      newTabs = if lineSet then recent else 1
      new_indentTabs =
          let iTabs = indentTabs s
          in if newTabs + sum iTabs > totalTabStops s
          then iTabs
          else iTabs ++ [newTabs]
      new_recentlySet =
          if lineSet
          then 0
          else recent
      inTabs = tabIndent newTabs
      (indent_fun, new_indentTabsWritten) =
          let writtenTabs = indentTabsWritten s
          in if sum new_indentTabs > writtenTabs
            && not lineSet && onlyTabs s
          then (inTabs, newTabs + writtenTabs)
          else (id, writtenTabs)
  in (indent_fun, s
    { recentlySet = new_recentlySet
    , indentTabs = new_indentTabs
    , indentTabsWritten = new_indentTabsWritten })

-- decrease the indentTabs in the state by 1
subTabStop :: State LRState ()
subTabStop = modify $ \ s -> s
  { indentTabs = case indentTabs s of
      [] -> []
      itabs -> init itabs }

-- functions for producing IO printable Strings

renderLatexCore :: Style -> Doc -> ShowS
renderLatexCore latexStyle' d =
    evalState (fullRender
               (mode latexStyle')
               (lineLength latexStyle')
               (ribbonsPerLine latexStyle')
               latexTxt (return id) d) initialLRState

renderLatex :: Maybe Int -> Doc -> String
renderLatex mi d = showString "\\begin{hetcasl}\n"
  $ renderLatexCore latexStyle' d "\n\\end{hetcasl}\n"
    where latexStyle' = latexStyle
            { lineLength = fromMaybe (lineLength latexStyle) mi }
