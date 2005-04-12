{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  unknown

   Data structures representing SPASS signatures.
   Refer to <http://spass.mpi-sb.mpg.de/webspass/help/syntax/dfgsyntax.html>
   for the SPASS syntax documentation.

-}

module SPASS.Sign where

import Common.AS_Annotation
import Common.PrettyPrint
import Common.Lib.Pretty

{- |
  A SPASS Identifier is a String for now. Might need a checkIdentifier function
  and possibly also conversion functions.
-}
type SPIdentifier = String

{- |
  A SPASS Formula is modelled as a Named SPTerm for now. This doesn't reflect
  the fact that the SPASS syntax list both term and label as optional.
-}
type SPFormula = Named SPTerm

{- |
  There are axiom formulae and conjecture formulae.
-}
data SPOriginType =
        SPOriginAxioms
      | SPOriginConjectures
      deriving (Eq, Show)

{- |
  A SPASS Term.
-}
data SPTerm = 
        SPQuantTerm { quantSym :: SPQuantSym,
                      termList :: [SPTerm],
                      term     :: SPTerm }
      | SPSimpleTerm SPSymbol
      | SPComplexTerm { symbol    :: SPSymbol,
                        arguments :: [SPTerm]}
      deriving (Eq, Show)

{- |
  SPASS Quantifier Symbols.
-}
data SPQuantSym =
        SPForall
      | SPExists
      | SPCustomQuantSym SPIdentifier
      deriving (Eq, Show)

{- |
  SPASS Symbols.
-}
data SPSymbol =
        SPEqual
      | SPTrue 
      | SPFalse 
      | SPOr 
      | SPAnd
      | SPNot
      | SPImplies
      | SPImplied
      | SPEquiv
      | SPCustomSymbol SPIdentifier
      deriving (Eq, Show)

{- |
  Creates a Common.Lib.Pretty.Doc from a SPASS Formula.
-}
printFormula :: SPFormula-> Doc
printFormula f = (text "formula") <> parens (printTerm (sentence f) <> comma <> text (senName f))

{- |
  Creates a Doc from a SPASS Term.
-}
printTerm :: SPTerm-> Doc
printTerm t = case t of
  SPQuantTerm{quantSym= qsym, termList= tlist, term= t} -> printQuantSym qsym <> parens (brackets (printTermList tlist) <> comma <> printTerm t)
  SPSimpleTerm sym -> printSymbol sym
  SPComplexTerm{symbol= sym, arguments= args} -> printSymbol sym <> parens (printTermList args)
  where
    printTermList = foldr (\x tl-> if isEmpty tl then printTerm x else tl <> comma <> (printTerm x)) empty

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
printSymbol :: SPSymbol-> Doc
printSymbol s = case s of
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
