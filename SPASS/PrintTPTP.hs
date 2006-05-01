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

module PrintTPTP where

import Maybe

import Common.AS_Annotation
import Common.Lib.Pretty

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

implies :: Doc
implies = text "=>"

endOfListS :: String
endOfListS = "end_of_list."

{- |
  Helper function. Generates a separating comment line.
-}
separator :: String
separator = "%-----------------------------------------------------------------"
            ++ "---------"

instance PrintTPTP Sign where
    printTPTP = printTPTP . signToSPLogicalPart

{- |
  Creates a Doc from a SPASS Problem.
-}
instance PrintTPTP SPProblem where
    printTPTP p = text separator
      $$ text "Problem" <+> colon <+> text (identifier p)
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
  Creates a Common.Lib.Pretty.Doc from a SPASS Formula List
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
    text "fof" <> parens (quotes (text (senName f)) <> comma <> printTPTP ot <> comma <>
                          parens (empty $$ printTPTP (sentence f))) <> dot

{- |
  Creates a Doc from a SPASS Term.
-}
instance PrintTPTP SPTerm where
    printTPTP t = case t of
      SPQuantTerm{quantSym= qsym, termTermList= tlist, termTerm= tt}
        -> printTPTP qsym
           <+> brackets (printVariableList tlist)
           <+> colon
           <+> parens (printTermList SPAnd tlist
                       <+> implies $$ printTPTP tt)
      SPSimpleTerm stsym -> space <> printTPTP stsym
      SPComplexTerm{symbol= ctsym, arguments= args}
        -> if null args
           then (space <> printTPTP ctsym)
           else (space <> printTermList ctsym args)
      where
-- !! wir kriegen hier entweder SPSimpleTerm oder SPComplexTerm. Das müssen wir solange
--    durchfiltern, bis nur noch alle SPSimpleTerm übrigbleiben. Diese werden anschließend
--    in eine Menge gesteckt (also nur je einmal vorhanden). Geht das? Wie?
-- !! here the difficult part: how to get the variable names out of the tList??
--    this does something, but it won't be the filtered variable names only
        printVariableList = foldl (\ tl v -> if isEmpty tl then printTPTP v
                                             else tl <> comma <> printTPTP v) empty
      
      
{- |
  Creates a Doc from a list of SPASS Terms connected by a SPASS Symbol.
-}
printTermList :: SPSymbol -> [SPTerm] -> Doc
printTermList symb terms = case symb of
-- !! maybe use terms always as last parameter?
-- !! what about unary connectors? has to be defined with SPCustomSymbol!

    SPEqual            -> connectTerms (char '=') terms
    -- true and false ignore term list
    SPTrue             -> text "$true"
    SPFalse            -> text "$false"
    SPOr               -> connectTerms (char '|') terms
    SPAnd              -> connectTerms (char '&') terms
    -- only one term can be negated
    SPNot              -> (char '~') <> parens (printTPTP $ head terms)
    SPImplies          -> connectTerms implies terms
    SPImplied          -> connectTerms (text "<=") terms
    SPEquiv            -> connectTerms (text "<=>") terms
    SPCustomSymbol cst -> connectTerms (text cst) terms
    where
      connectTerms sb t =
        parens (foldl (\ tl x -> if isEmpty tl then printTPTP x
                                 else tl <+> sb $$ space <> printTPTP x)
                      empty t)

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
-- !! maybe this doesn't work properly in all cases (if any)
    printTPTP s = case s of
     SPEqual            -> char '='
     SPTrue             -> text "$true"
     SPFalse            -> text "$false"
     SPOr               -> char '|'
     SPAnd              -> char '&'
     SPNot              -> char '~'
     SPImplies          -> implies
     SPImplied          -> text "<="
     SPEquiv            -> text "<=>"
     SPCustomSymbol cst -> text cst

{- |
  Creates a Doc from a SPASS description.
-}
instance PrintTPTP SPDescription where
    printTPTP d = spText "Name   " (name d)
      $$ spText "Author " (author d)
      $$ maybe empty (spText "Version") (version d)
      $$ maybe empty (spText "Logic  ") (logic d)
      $$ text "Status " <+> colon <+> printTPTP (status d)
      $$ spText "Desc   " (desc d)
      $$ maybe empty (spText "Date   ") (date d)

{- |
  Helper function. Creates a formatted output for a description field.
  On left side will be displayed the field's name, on right side its content.
-}
spText :: String -> String -> Doc
spText sn sd = hsep [text sn, colon, text sd]

{- |
  Creates a Doc from an 'SPLogState'.
-}
instance PrintTPTP SPLogState where
    printTPTP s = case s of
      SPStateSatisfiable   -> text "satisfiable"
      SPStateUnsatisfiable -> text "unsatisfiable"
      SPStateUnknown       -> text "unknown"
