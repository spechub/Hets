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

import Maybe
import Char

import Common.AS_Annotation
import Common.PrettyPrint
import Common.Lib.Pretty

{- |
  A SPASS Identifier is a String for now. See also 'checkIdentifier' function
  below. Might need conversion functions as well.
-}
type SPIdentifier = String

{- |
  SPASS Identifiers may contain letters, digits, and underscores only.
-}
checkIdentifier :: String-> Bool
checkIdentifier "" = False
checkIdentifier xs = and (map checkChar xs)
  where
    checkChar c = isAlphaNum c || '_' == c

{- |
  A SPASS problem consists of a description and a logical part. The optional
  settings part hasn't been implemented yet.
-}
data SPProblem =
        SPProblem { identifier  :: SPIdentifier,
                    description :: SPDescription,
                    logicalPart :: SPLogicalPart --,
--                    settings    :: [SPSetting],
                    }
      deriving (Eq, Show)

{- |
  A SPASS logical part consists of a symbol list, a declaration list, and a
  set of formula lists. Support for clause lists and proof lists hasn't
  been implemented yet.
-}
data SPLogicalPart =
        SPLogicalPart { symbolList      :: Maybe SPSymbolList,
                        declarationList :: [SPDeclaration],
                        formulaLists    :: [SPFormulaList] --,
--                        clauseLists :: [SPClauseList],
--                        proofLists :: [SPProofList]
                        }
      deriving (Eq, Show)

{- |
  All non-predefined signature symbols must be declared as part of a SPASS
  symbol list. 
-}
data SPSymbolList =
        SPSymbolList { functions   :: [SPSignSym],
                       predicates  :: [SPSignSym],
                       sorts       :: [SPSignSym],
                       operators   :: [SPSignSym],
                       quantifiers :: [SPSignSym] }
      deriving (Eq, Show)

{- |
  A common data type used for all signature symbols.
-}
data SPSignSym =
        SPSignSym { sym    :: SPIdentifier,
                    arity  :: Int }
      | SPSimpleSignSym SPIdentifier
      deriving (Eq, Show)

--DOCUMENTME
data SPDeclaration =
        SPSubsortDecl { sortSymA :: SPIdentifier,
                        sortSymB :: SPIdentifier }
      | SPTermDecl { termDeclTermList :: [SPTerm],
                     termDeclTerm     :: SPTerm }
      | SPSimpleTermDecl SPTerm
      | SPPredDecl { predSym  :: SPIdentifier,
                     sortSyms :: [SPIdentifier] }
      | SPGenDecl { sortSym  :: SPIdentifier,
                    funcList :: [SPIdentifier]}
      deriving (Eq, Show)

{- |
  SPASS Formula List
-}
data SPFormulaList = 
        SPFormulaList { originType :: SPOriginType,
                        formulae   :: [SPFormula] }
      deriving (Eq, Show)

{- |
  There are axiom formulae and conjecture formulae.
-}
data SPOriginType =
        SPOriginAxioms
      | SPOriginConjectures
      deriving (Eq, Show)

{- |
  A SPASS Formula is modelled as a Named SPTerm for now. This doesn't reflect
  the fact that the SPASS syntax lists both term and label as optional.
-}
type SPFormula = Named SPTerm

{- |
  A SPASS Term.
-}
data SPTerm = 
        SPQuantTerm { quantSym     :: SPQuantSym,
                      termTermList :: [SPTerm],
                      termTerm     :: SPTerm }
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
  A description is mandatory for a SPASS problem. It has to specify at least
  a 'name', the name of the 'author', the 'status' (see also 'SPLogState' below),
  and a (verbose) description.
-}
data SPDescription =
        SPDescription { name    :: String,
                        author  :: String,
                        version :: Maybe String,
                        logic   :: Maybe String,
                        status  :: SPLogState,
                        desc    :: String,
                        date    :: Maybe String}
      deriving (Eq, Show)

{- |
  The state of a SPASS problem can be satisfiable, unsatisfiable, or unknown.
-}
data SPLogState =
        SPStateSatisfiable
      | SPStateUnsatisfiable
      | SPStateUnknown
      deriving (Eq, Show)

{- |
  Helper function. Generates a "." as a Doc.
-}
dot :: Doc
dot = text "."

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
      $$ foldr (\x d-> d $$ printDeclaration x) empty xs
      $$ text "end_of_list."
    printFormulaLists = foldr (\x d-> d $$ printFormulaList x) empty

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
        then text name <> brackets (foldr (\x d-> if isEmpty d then printSignSym x else d <> comma $$ printSignSym x) empty list) <> dot
        else empty

{-|
  Helper function. Creates a Doc from a Signature Symbol.
-}
printSignSym :: SPSignSym-> Doc
printSignSym (SPSimpleSignSym s) = text s
printSignSym ssym = parens (text (sym ssym) <> comma <> int (arity ssym))

-- FIXME
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
    printFormulae = foldr (\x fl-> fl <> printFormula x <> dot) empty

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
