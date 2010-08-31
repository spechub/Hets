{- |
Module      :  $Header$
Description :  To be replaced by SoftFOL.Sign
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.SPASS.Sign where

type SPIdentifier = String

data SPProblem =
        SPProblem { identifier  :: SPIdentifier,
                    description :: SPDescription,
                    logicalPart :: SPLogicalPart,
                    settings    :: [SPSetting]
                    }
      deriving (Eq, Ord, Show)

-- ** SPASS Logical Parts

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
      deriving (Eq, Ord, Show)

-- *** Symbol Lists

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
      deriving (Eq, Ord, Show)

{- |
  Creates an empty SPASS Symbol List.
-}
emptySymbolList :: SPSymbolList
emptySymbolList =
        SPSymbolList { functions   = [],
                       predicates  = [],
                       sorts       = [],
                       operators   = [],
                       quantifiers = [] }

{- |
  A common data type used for all signature symbols.
-}
data SPSignSym =
        SPSignSym { sym    :: SPIdentifier,
                    arity  :: Int }
      | SPSimpleSignSym SPIdentifier
      deriving (Eq, Ord, Show)

-- *** Declarations

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
      deriving (Eq, Ord, Show)

-- *** Formula List

{- |
  SPASS Formula List
-}
data SPFormulaList =
        SPFormulaList { originType :: SPOriginType,
                        formulae   :: [SPFormula] }
      deriving (Eq, Ord, Show)

{- |
  There are axiom formulae and conjecture formulae.
-}
data SPOriginType =
        SPOriginAxioms
      | SPOriginConjectures
      deriving (Eq, Ord, Show)

-- *** Formulae And Terms

{- |
  A SPASS Formula is modelled as a Named SPTerm for now. This doesn't reflect
  the fact that the SPASS syntax lists both term and label as optional.
-}

data Named s = NamedSen
    { senName  :: String
    , isAxiom :: Bool
    , isDef :: Bool
    , sentence :: s } deriving (Eq, Ord, Show)

type SPFormula = Named SPTerm


{- |
  A SPASS Term.
-}
data SPTerm =
        SPQuantTerm { quantSym     :: SPQuantSym,
                      variableList :: [SPTerm],
                      qFormula     :: SPTerm }
      | SPSimpleTerm SPSymbol
      | SPComplexTerm { symbol    :: SPSymbol,
                        arguments :: [SPTerm]}
      deriving (Eq, Ord, Show)

{- |
  SPASS Quantifier Symbols.
-}
data SPQuantSym =
        SPForall
      | SPExists
      | SPCustomQuantSym SPIdentifier
      deriving (Eq, Ord, Show)

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
      | SPXor -- eigene Erweiterung
      | SPCustomSymbol SPIdentifier
      deriving (Eq, Ord, Show)

-- ** SPASS Desciptions

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
      deriving (Eq, Ord, Show)

{- |
  The state of a SPASS problem can be satisfiable, unsatisfiable, or unknown.
-}
data SPLogState =
        SPStateSatisfiable
      | SPStateUnsatisfiable
      | SPStateUnknown
      deriving (Eq, Ord, Show)

-- ** SPASS Settings

{- |
  We only support one of the three types mentioned here:
  <http://spass.mpi-sb.mpg.de/webspass/help/options.html>
-}

data SPSetting = SPFlag String String
     deriving (Eq,Ord,Show)

-- ** SoftFOL proof tree

{- |
  Datatype for storing of the proof tree. The Show class is instantiated.
-}
data ProofTree = ProofTree String
       deriving (Eq, Ord)

instance Show ProofTree where
  show (ProofTree st) = st
