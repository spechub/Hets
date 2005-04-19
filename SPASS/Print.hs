{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  unknown

   Pretty printing for SPASS signatures.
   Refer to <http://spass.mpi-sb.mpg.de/webspass/help/syntax/dfgsyntax.html>
   for the SPASS syntax documentation.

-}

module SPASS.Print where

import Maybe

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Lib.Pretty
import Common.PrettyPrint

import SPASS.Sign

{- |
  Helper function. Generates a '.' as a Doc.
-}
dot :: Doc
dot = char '.'

{- |
  Creates a Doc from a SPASS Problem.
-}
printProblem :: SPProblem-> Doc
printProblem p = text "begin_problem" <> parens (text (identifier p)) <> dot
  $$ printDescription (description p)
  $$ printLogicalPart (logicalPart p)
  $$ text "end_problem."

{- |
  Creates a Doc from a SPASS Logical Part.
-}
printLogicalPart :: SPLogicalPart-> Doc
printLogicalPart lp =
  (if isJust (symbolList lp) then printSymbolList (fromJust (symbolList lp)) else empty)
  $$ (if not $ null (declarationList lp) then printDeclarationList (declarationList lp) else empty)
  $$ (if not $ null (formulaLists lp) then printFormulaLists (formulaLists lp) else empty)
  where
    printDeclarationList xs = text "list_of_declarations."
      $$ foldl (\d x-> d $$ printDeclaration x) empty xs
      $$ text "end_of_list."
    printFormulaLists = foldl (\d x-> d $$ printFormulaList x) empty

{- |
  Creates a Doc from a SPASS Symbol List.
-}
printSymbolList :: SPSymbolList-> Doc
printSymbolList sl = text "list_of_symbols."
  $$ printSignSymList "functions" (functions sl)
  $$ printSignSymList "predicates" (predicates sl)
  $$ printSignSymList "sorts" (sorts sl)
  $$ printSignSymList "operators" (operators sl)
  $$ printSignSymList "quantifiers" (quantifiers sl)
  $$ text "end_of_list."
  where 
    printSignSymList name list =
      if not $ null list
        then text name <> brackets (foldl (\d x-> if isEmpty d then printSignSym x else d <> comma $$ printSignSym x) empty list) <> dot
        else empty

{-|
  Helper function. Creates a Doc from a Signature Symbol.
-}
printSignSym :: SPSignSym-> Doc
printSignSym (SPSimpleSignSym s) = text s
printSignSym ssym = parens (text (sym ssym) <> comma <> int (arity ssym))

{- |
  Creates a Doc from a SPASS Declaration
-}
printDeclaration :: SPDeclaration-> Doc
printDeclaration _ = empty

{- |
  Creates a Common.Lib.Pretty.Doc from a SPASS Formula List
-}
printFormulaList :: SPFormulaList-> Doc
printFormulaList l = text "list_of_formulae" <> parens (printOriginType (originType l)) <> dot
  $$ printFormulae (formulae l)
  $$ text "end_of_list."
  where
    printFormulae = foldl (\fl x-> fl <> printFormula x <> dot) empty

{- |
  Creates a Doc from a SPASS Origin Type
-}
printOriginType :: SPOriginType-> Doc
printOriginType t = case t of
  SPOriginAxioms      -> text "axioms"
  SPOriginConjectures -> text "conjectures"

{- |
  Creates a Doc from a SPASS Formula.
-}
printFormula :: SPFormula-> Doc
printFormula f = (text "formula") <> parens (printTerm (sentence f) <> comma <> text (senName f))

{- |
  Creates a Doc from a SPASS Term.
-}
printTerm :: SPTerm-> Doc
printTerm t = case t of
  SPQuantTerm{quantSym= qsym, termTermList= tlist, termTerm= t} -> printQuantSym qsym <> parens (brackets (printTermList tlist) <> comma <> printTerm t)
  SPSimpleTerm sym -> printText0 emptyGlobalAnnos sym
  SPComplexTerm{symbol= sym, arguments= args} -> printText0 emptyGlobalAnnos sym <> parens (printTermList args)
  where
    printTermList = foldl (\tl x-> if isEmpty tl then printTerm x else tl <> comma <> (printTerm x)) empty

{- |
  Creates a Doc from a SPASS Quantifier Symbol.
-}
printQuantSym :: SPQuantSym-> Doc
printQuantSym qs = case qs of
  SPForall             -> text "forall"
  SPExists             -> text "exists"
  SPCustomQuantSym cst -> text cst

{- |
  Creates a Doc from a SPASS Symbol.
-}
-- printSymbol :: SPSymbol-> Doc
instance PrettyPrint SPSymbol where
    printText0 ga s = case s of
     SPEqual            -> text "equal"
     SPTrue             -> text "true"
     SPFalse            -> text "false"
     SPOr               -> text "or"
     SPAnd              -> text "and"
     SPNot              -> text "not"
     SPImplies          -> text "implies"
     SPImplied          -> text "implied"
     SPEquiv            -> text "equiv"
     SPCustomSymbol cst -> text cst

{- |
  Creates a Doc from a SPASS description.
-}
printDescription :: SPDescription-> Doc
printDescription d = text "list_of_descriptions."
  $$ text "name" <> parens (spText (name d)) <> dot
  $$ text "author" <> parens (spText (author d)) <> dot
  $$ (if isJust (version d) then text "version" <> parens (spText (fromJust (version d))) <> dot else empty)
  $$ (if isJust (logic d) then text "logic" <> parens (spText (fromJust (logic d))) <> dot else empty)
  $$ text "status" <> parens (printLogState (status d)) <> dot
  $$ text "description" <> parens (spText (desc d)) <> dot
  $$ (if isJust (date d) then text "date" <> parens (text (fromJust (date d))) <> dot else empty)
  $$ text "end_of_list."

{- |
  Helper function. Wraps a String in "{*  *}" as required for some of the
  description fields.
-}
spText :: String-> Doc
spText s = text "{* " <> text s <> text " *}"

{- |
  Creates a Doc from an 'SPLogState'.
-}
printLogState :: SPLogState-> Doc
printLogState s = case s of
  SPStateSatisfiable   -> text "satisfiable"
  SPStateUnsatisfiable -> text "unsatisfiable"
  SPStateUnknown       -> text "unknown"
