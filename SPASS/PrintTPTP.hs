{- |
Module      :  $Header$
Description :  Pretty printing for SPASS signatures in TPTP syntax.
Copyright   :  (c) Rene Wagner, Rainer Grabbe, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rainer25@tzi.de
Stability   :  provisional
Portability :  unknown

Pretty printing for SPASS signatures in TPTP syntax.
   Refer to <http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
   for the TPTP syntax documentation.

-}

{- todo:

  all these fomulas are named declaration and will be numbered
   - output typing for operations as sentences with name 
     * a conjunction of sorted variables for each parameter 
       forms the premise of an implication if there are any parameters
     * the sorted function application is the conclusion or the sentence is 
       just the sorted constant 
    examples:
     1. 
       DFG: forall([a(x1),list_A(x2)],list_A(cons(x1,x2))).

       TPTP: fof(ax4,declaration0,(! [U,V] : ((a(U) &
                          list_A(V)) => list_A(cons(U,V))))).

     2.
      DFG: list_A(nil).
      TPTP: fof(ax7,declaration1,(list_A(nil))).
   - output subsorting information as implication
       sortSymA => sortSymB
-}
module SPASS.PrintTPTP where

import Maybe

import Common.AS_Annotation
import Common.Lib.Pretty

import Control.Exception

import SPASS.Sign
import SPASS.Conversions


-- | This type class allows pretty printing in TPTP syntax of instantiated data types
class PrintTPTP a where
    printTPTP :: a -> Doc

{- |
  Helper function. Generates a '.' as a Doc.
-}
dot :: Doc
dot = char '.'

{- |
  Helper function. Generates a separating comment line.
-}
separator :: String
separator = "%-----------------------------------------------------------------"
            ++ "---------"

{- |
  Helper function. Generates a comma separated list of SPASS Terms as a Doc.
-}
printCommaSeparated :: [SPTerm] -> Doc
printCommaSeparated = foldl (\vl v -> if isEmpty vl then printTPTP v
                                      else vl <> comma <> printTPTP v) empty


instance PrintTPTP Sign where
    printTPTP = printTPTP . signToSPLogicalPart

{- |
  Creates a Doc from a SPASS Problem.
-}
instance PrintTPTP SPProblem where
    printTPTP p = text separator
      $$ text "% Problem" <+> colon <+> text (identifier p)
      $$ printTPTP (description p)
      $$ text separator
      $$ printTPTP (logicalPart p)

{- |
  Creates a Doc from a SPASS Logical Part.
-}
instance PrintTPTP SPLogicalPart where
    printTPTP lp =
      (if not $ null $ formulaLists lp
        then foldl (\d x-> d $$ printTPTP x) empty $ formulaLists lp
        else empty)

{- |
  Creates a Doc from a SPASS Formula List
-}
instance PrintTPTP SPFormulaList where
    printTPTP l = foldl (\fl x-> fl $$ printFormula (originType l) x)
                        empty $ formulae l

{- |
  Creates a Doc from a SPASS Origin Type
-}
instance PrintTPTP SPOriginType where
    printTPTP t = case t of
        SPOriginAxioms      -> text "axiom"
        SPOriginConjectures -> text "conjecture"

{- |
  Creates a Doc from a SPASS Formula. Needed since SPFormula is just a
  'type SPFormula = Named SPTerm' and thus instanciating PrintTPTP is not
  possible.
-}
printFormula :: SPOriginType -> SPFormula -> Doc
printFormula ot f =
    text "fof" <> parens (text (senName f) <> comma <> printTPTP ot <> comma <>
                          parens (printTPTP (sentence f))) <> dot

{- |
  Creates a Doc from a SPASS Term.
-}
instance PrintTPTP SPTerm where
    printTPTP t = case t of
      SPQuantTerm{quantSym= qsym, variableList= tlist, qFormula= tt}
        -> printTPTP qsym
           <+> brackets (printCommaSeparated $ getVariables tlist)
           <+> colon
           -- either all variables are simple terms
           <+> if (filter isSimpleTerm tlist == tlist) then printTPTP tt
               -- or there are none simple terms
               else assert (null $ filter isSimpleTerm tlist)
               -- construct premiss for implication out of variableList
                           printTermList SPImplies [SPComplexTerm{
                                                      symbol=SPAnd,
                                                      arguments=tlist}, tt]
      SPSimpleTerm stsym -> printTPTP stsym
      SPComplexTerm{symbol= ctsym, arguments= args}
        -> if null args
           then printTPTP ctsym
           else printTermList ctsym args
      where
        isSimpleTerm tm = case tm of 
            SPSimpleTerm _ -> True
            _              -> False

        -- check that every list entry is simple term
        getSimpleVars = foldr (\v vl -> assert (isSimpleTerm v) $ v:vl) []
        getVariables tl = if null $ filter isSimpleTerm tl
                          then foldr (\co col -> (getSimpleVars $
                                                  arguments co)++col)
                                     [] tl
                          else getSimpleVars tl

{- |
  Creates a Doc from a list of SPASS Terms connected by a SPASS Symbol.
-}
printTermList :: SPSymbol -> [SPTerm] -> Doc
printTermList symb terms = case symb of
    SPEqual            -> assert (length terms == 2) $ associate SPEqual
    SPTrue             -> assert (length terms == 0) $ associate SPTrue
    SPFalse            -> assert (length terms == 0) $ associate SPFalse
    -- variable number of terms for or/and
    SPOr               -> assert (length terms >= 0) $ associate SPOr
    SPAnd              -> assert (length terms >= 0) $ associate SPAnd
    -- only one term can be negated
    SPNot              -> assert (length terms == 1) $ applicate SPNot
    SPImplies          -> assert (length terms == 2) $ associate SPImplies
    SPImplied          -> assert (length terms == 2) $ associate SPImplied
    SPEquiv            -> assert (length terms == 2) $ associate SPEquiv   
    SPCustomSymbol cst -> applicate $ SPCustomSymbol cst
    where
      associate sb = case terms of
        []  -> empty
        [x] -> printTPTP x
        _   -> parens (foldl (\tl x -> if isEmpty tl then printTPTP x
                                       else tl <+> printTPTP sb $$ printTPTP x)
                             empty terms)
      applicate sb =
        if null terms then printTPTP sb
        else printTPTP sb <> parens (printCommaSeparated terms)

{- |
  Creates a Doc from a SPASS Quantifier Symbol.
-}
instance PrintTPTP SPQuantSym where
    printTPTP qs = case qs of
        SPForall             -> char '!'
        SPExists             -> char '?'
        SPCustomQuantSym cst -> text cst

{- |
  Creates a Doc from a SPASS Symbol.
-}
instance PrintTPTP SPSymbol where
    printTPTP s = case s of
        SPEqual            -> char '='
        SPTrue             -> text "$true"
        SPFalse            -> text "$false"
        SPOr               -> char '|'
        SPAnd              -> char '&'
        SPNot              -> char '~'
        SPImplies          -> text "=>"
        SPImplied          -> text "<="
        SPEquiv            -> text "<=>"
        SPCustomSymbol cst -> text cst

{- |
  Creates a Doc from a SPASS description.
-}
instance PrintTPTP SPDescription where
    printTPTP d = spCommentText "Name   " (name d)
      $$ spCommentText "Author " (author d)
      $$ maybe empty (spCommentText "Version") (version d)
      $$ maybe empty (spCommentText "Logic  ") (logic d)
      $$ text "% Status " <+> colon <+> printTPTP (status d)
      $$ spCommentText "Desc   " (desc d)
      $$ maybe empty (spCommentText "Date   ") (date d)

{- |
  Helper function. Creates a formatted comment output for a description field.
  On left side will be displayed the field's name, on right side its content.
-}
spCommentText :: String -> String -> Doc
spCommentText fieldName fieldDesc = hsep [char '%', text fieldName, colon, text fieldDesc]

{- |
  Creates a Doc from an 'SPLogState'.
-}
instance PrintTPTP SPLogState where
    printTPTP s = case s of
      SPStateSatisfiable   -> text "satisfiable"
      SPStateUnsatisfiable -> text "unsatisfiable"
      SPStateUnknown       -> text "unknown"
