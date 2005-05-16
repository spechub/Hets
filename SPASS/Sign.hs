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

import Char

import Common.AS_Annotation

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

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

{- |
  SPASS Declarations allow the introduction of sorts.
-}
data SPDeclaration =
        SPSubsortDecl { sortSymA :: SPIdentifier,
                        sortSymB :: SPIdentifier }
      | SPTermDecl { termDeclTermList :: [SPTerm],
                     termDeclTerm     :: SPTerm }
      | SPSimpleTermDecl SPTerm
      | SPPredDecl { predSym  :: SPIdentifier,
                     sortSyms :: [SPIdentifier] }
      | SPGenDecl { sortSym         :: SPIdentifier,
                    freelyGenerated :: Bool,
                    funcList        :: [SPIdentifier]}
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
