{- |
Module      :  $Header$
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
    , debugRenderLatex
    , renderLatexVerb
    , renderInternalLatex
    , setTabWithSpaces
    , latexHeader
    , latexFooter
    )
    where

import Data.Char (isSpace, isDigit)
import Common.Lib.State (State(..),evalState,get,put)
import Data.List (isPrefixOf,isSuffixOf)

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

----------------------------------------------------------------------
-- a style for formatting (Standard is Style PageMode 50 1.19)

latexStyle :: Style
latexStyle = style { ribbonsPerLine = 1.1
                   , lineLength = calc_line_length "345.0pt"}
                    -- for svmono you need 336.0pt

-- a LatexRenderingState
-- field indentTabs : for the number of tab
--                stops set those need to be rendererd after every newline.
-- field recentlySet : number of setTab makros indentTabs is only
--                 increased if recentlySet is 0
data LRState = LRS { indentTabs  :: ![Int]
                   , recentlySet
                   , totalTabStops
                   , setTabsThisLine
                   , indentTabsWritten :: !Int
                   , onlyTabs :: !Bool
                   , isSetLine :: !Bool
                   , collSpaceIndents :: ![Int]
                   , insideAnno :: Bool
                   }
             deriving (Show)

-- the initial state for using the state based rendering via LRState
initialLRState :: LRState
initialLRState = LRS { indentTabs         = []
                     , recentlySet        = 0
                     , totalTabStops      = 0
                     , setTabsThisLine    = 0
                     , indentTabsWritten  = 0
                     , onlyTabs           = False
                     , isSetLine          = False
                     , collSpaceIndents = []
                     , insideAnno = False
                     }

-- a function that knows how to print LaTeX TextDetails
latexTxt :: TextDetails -> State LRState ShowS -> State LRState ShowS
latexTxt (Chr c)   cont
    | c == '\n' = do annoBrace <- endOfLine
                     indent <- getIndent
                     s <- cont
                     return (annoBrace . showString "\\\\".
                             showChar c . indent . s)
    | otherwise = do s <- cont
                     return (showChar c . s)
latexTxt (Str s1)  cont
    | null s1        = cont
    | all isSpace s1 = do s2 <- cont
                          return (showChar ' ' . s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (showString s1 . s2)
latexTxt (PStr s1) cont
    | s1 == startTab = do indent <- addTabStop
                          s2 <- cont
                          return (indent . s2)
    | s1 == endTab   = do subTabStop
                          cont
    | s1 == setTab   = do state <- get
                          setTabStop
                          s2 <- cont
                          let (eAn,sAn) = if insideAnno state
                                          then (showChar '}',
                                                showString startAnno)
                                          else (id,id)
                          return (eAn. (if indentTabsWritten state
                                           + setTabsThisLine state > 12 ||
                                           onlyTabs state then
                                           id else showString s1) . sAn. s2)
    | setTabWSp
      `isPrefixOf`
      s1             = do addTabWithSpaces s1
                          cont
    | s1== startAnno = do setInsideAnno True
                          s2 <- cont
                          return (showString s1 . s2)
    | s1 == endAnno  = do setInsideAnno False
                          s2 <- cont
                          return (showChar '}' . s2)
    | s1 == "\n"     = do annoBrace <- endOfLine
                          indent <- getIndent
                          s2 <- cont
                          return (annoBrace . showString "\\\\\n" .
                                  indent . s2)
    | "\\kill\n"
      `isSuffixOf`
      s1             = do indent <- getIndent
                          s2 <- cont
                          return (showString s1 .
                                  indent . s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (showString s1 . s2)

-- a function that knows how to print LaTeX TextDetails
debugLatexTxt :: TextDetails -> State LRState String -> State LRState String
debugLatexTxt (Chr c) cont
    | c == '\n' = do state <- get
                     annoBrace <- endOfLine
                     indent <- getIndent
                     s <- cont
                     return (annoBrace "\\\\%" ++ show (state::LRState)
                             ++ c : indent s)
    | otherwise = fmap (c :) cont
debugLatexTxt (Str s1)  cont
    | null s1        = cont
    | all isSpace s1 = do s2 <- cont
                          return ( ' ':s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (s1 ++ s2)
debugLatexTxt (PStr s1) cont
    | s1 == startTab = do indent <- addTabStop
                          s2 <- cont
                          return (s1 ++ indent s2)
    | s1 == endTab   = do subTabStop
                          s2 <- cont
                          return (s1 ++ s2)
    | s1 == setTab   = do state <- get
                          setTabStop
                          s2 <- cont
                          let (eAn,sAn) = if insideAnno state
                                          then (showChar '}',
                                                showString startAnno)
                                          else (id,id)
                          return (eAn s1 ++ sAn s2)
    | setTabWSp
      `isPrefixOf`
      s1             = do addTabWithSpaces s1
                          s2 <- cont
                          return (s1 ++ s2)
    | s1== startAnno = do setInsideAnno True
                          s2 <- cont
                          return (s1 ++ s2)
    | s1 == endAnno  = do setInsideAnno False
                          s2 <- cont
                          return ('}' : s2)
    | s1 == "\n"     = do state <- get
                          annoBrace <- endOfLine
                          indent <- getIndent
                          s2 <- cont
                          return (annoBrace "\\\\%"++show (state::LRState)
                                  ++s1++indent s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (s1 ++ s2)


setOnlyTabs :: Bool -> State LRState ()
setOnlyTabs b = do state <- get
                   put $ state {onlyTabs = b}

setInsideAnno :: Bool -> State LRState ()
setInsideAnno b = do state <- get
                     put $ state {insideAnno = b}

-- a function to produce a String containing the actual tab stops in use
getIndent :: State LRState ShowS
getIndent = do state <- get
               let indentTabsSum = sum (indentTabs state)
               put $ state { indentTabsWritten = indentTabsSum
                           , collSpaceIndents  = []
                           , onlyTabs = True
                           , totalTabStops = max (totalTabStops state)
                                                 (indentTabsSum +
                                                  length
                                                     (collSpaceIndents state))
                           }
               let indent_fun = foldl (.) id (replicate indentTabsSum
                                                        (showString "\\>"))
                   new_tab_line = foldl space_format id
                                          (collSpaceIndents state)
                                          . showString "\\kill\n"
                   sAnno = (if insideAnno state
                            then showString startAnno
                            else id)
               return ( (if null (collSpaceIndents state) then
                            indent_fun
                         else
                            indent_fun . new_tab_line . indent_fun)
                         . sAnno)
    where space_format :: (ShowS) -> Int -> ShowS
          space_format sf1 i = sf1 . showString (replicate i '~')
                               . showString "\\="

endOfLine :: State LRState ShowS
endOfLine = do state <- get
               put $ state { isSetLine = False
                           , setTabsThisLine = 0
                           }
               return (if insideAnno state then showChar '}' else id)

setTabStop :: State LRState ()
setTabStop = State (\state -> ( ()
                              , let new_setTabsThisLine =
                                       succ $ setTabsThisLine state
                                in if onlyTabs state then state
                                   { isSetLine = True }
                                   else
                                       state
                                    {
                                     recentlySet = succ $ recentlySet state
                                    , setTabsThisLine = new_setTabsThisLine
                                      , totalTabStops =
                                               max (totalTabStops state)
                                                   (new_setTabsThisLine +
                                                    indentTabsWritten state)
                                      , isSetLine = True}
                              ))

addTabWithSpaces :: String -> State LRState ()
addTabWithSpaces s = let delayed_indent :: Int
                         delayed_indent =
                             (read . reverse . fst
                                      . span isDigit . tail . reverse) s
                     in State (\state -> ( ()
                                         , state { collSpaceIndents =
                                                      collSpaceIndents state
                                                        ++ [delayed_indent]
                                                 }
                                         ))

-- increase the indentTabs in the state by 1
addTabStop :: State LRState ShowS
addTabStop = State (\state -> let (new_indentTabs,newTabs) =
                                     let nT = if isSetLine state
                                              then recentlySet state
                                              else 1
                                     in (condAdd_indentTabs nT, nT)
                                  indentTabsSum = sum
                                  condAdd_indentTabs i =
                                         if   i + indentTabsSum
                                                   (indentTabs state)
                                            >
                                              totalTabStops state
                                         then indentTabs state
                                         else indentTabs state ++ [i]
                                  new_recentlySet =
                                     if isSetLine state
                                     then 0
                                     else recentlySet state
                                  inTabs nT = foldl (.) id
                                        (replicate nT $ showString "\\>")
                                  (indent_fun,
                                   new_indentTabsWritten) =
                                                if   indentTabsSum
                                                            new_indentTabs
                                                    >
                                                      indentTabsWritten state
                                                  && not (isSetLine state)
                                                  && onlyTabs state
                                                then (inTabs newTabs,
                                                      newTabs +
                                                       indentTabsWritten state)
                                                else (id,
                                                      indentTabsWritten state)
                              in (indent_fun
                                 ,state { recentlySet = new_recentlySet
                                        , indentTabs  = new_indentTabs
                                        , indentTabsWritten =
                                             new_indentTabsWritten
                                        })

                              )

-- decrease the indentTabs in the state by 1
subTabStop :: State LRState ()
subTabStop = do state <- get
                let l_itabs = last itabs
                    itabs = indentTabs state
                    indentTabs' = if null $ indentTabs state
                                  then []
                                  else if l_itabs == 1
                                       then init itabs
                                       else init itabs -- ++ [l_itabs -1]
                put (state {indentTabs = indentTabs'})

-- | function to set up a space based indentation macro
setTabWithSpaces :: Int -> String
setTabWithSpaces i = (showString setTabWSp . shows i) "}"

-- functions for producing IO printable Strings

renderInternalLatex :: Doc -> String
renderInternalLatex d = renderLatexCore latexStyle d ""

renderLatexCore :: Style -> Doc -> ShowS
renderLatexCore latexStyle' d =
    evalState (fullRender
               (mode           latexStyle')
               (lineLength     latexStyle')
               (ribbonsPerLine latexStyle')
               latexTxt (return id) d) initialLRState

renderLatex, renderLatexVerb :: Maybe Int -> Doc -> String

renderLatex mi d = showString "\\begin{hetcasl}\n" $
                    renderLatexCore latexStyle' d "\n\\end{hetcasl}\n"
    where latexStyle' = latexStyle {lineLength =
                                     (case mi of
                                      Nothing -> lineLength latexStyle
                                      Just l  -> l) }

debugRenderLatex :: Maybe Int -> Doc -> String
debugRenderLatex mi d = evalState (fullRender (mode           latexStyle')
                                              (lineLength     latexStyle')
                                              (ribbonsPerLine latexStyle')
                                              debugLatexTxt
                                              (return "")
                                              d')
                                  initialLRState
    where d' = ptext "\\begin{hetcasl}" $+$ d $+$ ptext "\\end{hetcasl}"
          latexStyle' = latexStyle {lineLength =
                                     (case mi of
                                      Nothing -> lineLength latexStyle
                                      Just l  -> l) }

-- this lacks some environment starting and closing LaTeX commands

renderLatexVerb mi d = renderStyle textStyle' d'
    where d' = text "\\begin{verbatim}" $+$ d $+$ text "\\end{verbatim}"
          textStyle' = style {lineLength =
                                     (case mi of
                                      Nothing -> lineLength style
                                      Just l  -> l) }
