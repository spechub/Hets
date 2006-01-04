{- |
   Module      :  $Header$
   Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003 
   License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

   Maintainer  :  luettich@tzi.de
   Stability   :  provisional
   Portability :  portable

This class needs to be instantiated for every datastructure in AS_*
   for LaTeX pretty printing. 
-}

module Common.PrintLaTeX 
    ( renderLatex
    , debugRenderLatex
    , PrintLaTeX(..)
    , renderLatexVerb
    , startTab, endTab, setTab
    , setTabWithSpaces
    , printToken_latex
    , printDisplayToken_latex
    , printId
    ) 
    where

import Data.Char (isSpace,isAlphaNum,isDigit)
import Common.Lib.State (State(..),evalState,get,put)
import Data.List (isPrefixOf,isSuffixOf)

import Common.Id
import Common.Lib.Pretty
import Common.PrettyPrint
import Common.PPUtils (printToks)
import Common.GlobalAnnotations
import Common.LaTeX_funs

----------------------------------------------------------------------
-- two Styles for Formatting (Standard is Style PageMode 100 1.5)

latexStyle :: Style
latexStyle = textStyle { ribbonsPerLine = 1.1
                       , lineLength = calc_line_length "336.0pt"}

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
latex_txt :: TextDetails -> State LRState ShowS -> State LRState ShowS
latex_txt (Chr c)   cont  
    | c == '\n' = do annoBrace <- endOfLine
                     indent <- getIndent
                     s <- cont
                     return (annoBrace . showString "\\\\". 
                             showChar c . indent . s)
    | otherwise = do s <- cont
                     return (showChar c . s)
latex_txt (Str s1)  cont
    | null s1        = cont
    | all isSpace s1 = do s2 <- cont
                          return (showChar ' ' . s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (showString s1 . s2)
latex_txt (PStr s1) cont
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
                          return (eAn. showString s1 . sAn. s2)
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
debug_latex_txt :: TextDetails -> State LRState String -> State LRState String
debug_latex_txt (Chr c)   cont  
    | c == '\n' = do state <- get
                     annoBrace <- endOfLine
                     indent <- getIndent
                     s <- cont
                     return (annoBrace "\\\\%"++show (state::LRState)
                             ++c:(indent s))
    | otherwise = do s <- cont
                     return (c:s)
debug_latex_txt (Str s1)  cont
    | null s1        = cont
    | all isSpace s1 = do s2 <- cont
                          return ( ' ':s2)
    | otherwise      = do setOnlyTabs False
                          s2 <- cont
                          return (s1 ++ s2)
debug_latex_txt (PStr s1) cont
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
               let indentTabsSum = foldl (+) 0 (indentTabs state)
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
                                in state 
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
                                  indentTabsSum = foldl (+) 0 
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

-- |
-- a constant String for starting a LaTeX indentation with tab stop
startTab :: String
startTab = "\\@begT@"

-- |
-- a constant String for releasing a LaTeX indentation with tab stop
endTab :: String
endTab = "\\@endT@"

-- |
-- a constant String to set a tab stop and enable it
setTab :: String
setTab = "\\="

-- | a constant String indicating the start of a space based indentation
setTabWSp :: String
setTabWSp = "\\@setTS@{"

-- | function to set up a space based indentation macro
setTabWithSpaces :: Int -> String
setTabWithSpaces i = (showString setTabWSp . shows i) "}"

-- functions for producing IO printable Strings
renderLatex, renderLatexVerb :: Maybe Int -> Doc -> String

renderLatex mi d = ((showString "\\begin{hetcasl}\n") .
                    (evalState (fullRender (mode           latexStyle')
                                           (lineLength     latexStyle')
                                           (ribbonsPerLine latexStyle')
                                           latex_txt
                                           (return id)
                                           d)
                               initialLRState)) "\n\\end{hetcasl}\n"
    where -- d' = ptext "\\begin{hetcasl}" $+$ d $+$ ptext "\\end{hetcasl}"
          latexStyle' = latexStyle {lineLength = 
                                     (case mi of
                                      Nothing -> lineLength latexStyle
                                      Just l  -> l) }

debugRenderLatex :: Maybe Int -> Doc -> String
debugRenderLatex mi d = evalState (fullRender (mode           latexStyle')
                                              (lineLength     latexStyle')
                                              (ribbonsPerLine latexStyle')
                                              debug_latex_txt
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
          textStyle' = textStyle {lineLength = 
                                     (case mi of
                                      Nothing -> lineLength textStyle
                                      Just l  -> l) }

-- moved instance from Id.hs (to avoid cyclic imports via GlobalAnnotations)
instance PrintLaTeX Token where
    printLatex0 ga t = printToken_latex casl_axiom_latex t'
        where i = Id [t] [] nullRange
              t' = maybe t (\ ts -> if isMixfix (Id ts [] nullRange) 
                                    then t 
                                    else head ts) 
                         (lookupDisplay ga DF_LATEX i) 

-- | print latex identifier
printId :: (GlobalAnnos -> Token -> Doc) -- ^ function to print a Token
           -> GlobalAnnos -> (Maybe Display_format) 
           -> ([Token] -> Doc)    -- ^ function to join translated tokens
           -> Id -> Doc
printId pf ga mdf f i =
    let glue_tok pf' = hcat . map pf'
        print_ (Id tops_p ids_p _) = 
            if null ids_p then glue_tok (pf ga) tops_p 
            else let (toks, places) = splitMixToken tops_p
                     comp = pf ga (mkSimpleId "[") <> 
                            fcat (punctuate comma_latex
                                            $ map (printId pf ga mdf f) ids_p)
                            <> pf ga (mkSimpleId "]")
                 in fcat [glue_tok (pf ga) toks, comp, 
                          glue_tok (pf ga) places]
        in maybe (print_ i) 
           ( \ df -> maybe (print_ i) f
             $ lookupDisplay ga df i) mdf

printToken_latex :: (String -> Doc) -> Token -> Doc
printToken_latex strConvDoc_fun t =
    let s = tokStr t
        esc = escape_latex s
    in if s `elem` map (:[]) "[](),;" 
       then strConvDoc_fun s 
       else if isPlace t || s `elem` map (:[]) "{}" 
            then strConvDoc_fun esc
            else if  all isAlphaNum s  
                     || ('\\' `elem` esc && not ('\\' `elem` s) 
                         && not ('~' `elem` s))
                     || isChar t
                 then (\x -> latex_macro "\\Id{"<>x<>latex_macro "}") 
                         $ strConvDoc_fun esc
                 else (\x -> latex_macro "\\Ax{"<>x<>latex_macro "}") 
                         $ strConvDoc_fun s

printDisplayToken_latex :: (String -> Doc) -> Token -> Doc
printDisplayToken_latex strConvDoc_fun t =
    if not (isPlace t)
       then latex_macro "\\Ax{"<>strConvDoc_fun str<>latex_macro "}"
       else printToken_latex strConvDoc_fun t
    where str = tokStr t

instance PrintLaTeX Id where
    printLatex0 ga i = printId printLatex0 ga (Just DF_LATEX)
       (fcat . printToks i (printDisplayToken_latex casl_axiom_latex)) i

