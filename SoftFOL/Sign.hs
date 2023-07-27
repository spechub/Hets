{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./SoftFOL/Sign.hs
Description :  Data structures representing SPASS signatures.
Copyright   :  (c) Rene Wagner, Heng Jiang, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Data structures representing SPASS signatures.
   Refer to <http://spass.mpi-sb.mpg.de/webspass/help/syntax/dfgsyntax.html>
   for the SPASS syntax documentation.
-}

module SoftFOL.Sign where

import Data.Data
import Data.Char
import Data.Maybe (isNothing)
import qualified Data.Map as Map
import qualified Data.Set as Set

import qualified Common.Lib.Rel as Rel
import Common.AS_Annotation hiding (Name)
import Common.Id
import Common.DefaultMorphism
import qualified Control.Monad.Fail as Fail

-- * Externally used data structures

{- |
  We use the DefaultMorphism for SPASS.
-}
type SoftFOLMorphism = DefaultMorphism Sign

type SortMap = Map.Map SPIdentifier (Maybe Generated)

type FuncMap = Map.Map SPIdentifier (Set.Set ([SPIdentifier], SPIdentifier))

type PredMap = Map.Map SPIdentifier (Set.Set [SPIdentifier])

{- |
  This Signature data type will be translated to the SoftFOL data types
  internally.

  sortRel contains the sorts relation. For each sort we need to know
  if it is a generated sort and if so by which functions it is
  possibly freely generated (sortMap).

  For each function the types of all arguments and the return type
  must be known (funcMap). The same goes for the arguments of a predicate
  (predMap).
-}
data Sign = Sign { sortRel :: Rel.Rel SPIdentifier
                 , sortMap :: SortMap
                 , funcMap :: FuncMap
                 , predMap :: PredMap
                 , singleSorted :: Bool
                 } deriving (Show, Eq, Ord, Typeable, Data)

{- |
  Sorts can be (freely) generated by a set of functions.
-}
data Generated = Generated { freely :: Bool
                           , byFunctions :: [SPIdentifier]
                           } deriving (Show, Eq, Ord, Typeable, Data)

{- |
  Creates an empty Signature.
-}
emptySign :: Sign
emptySign = Sign { sortRel = Rel.empty
                 , sortMap = Map.empty
                 , funcMap = Map.empty
                 , predMap = Map.empty
                 , singleSorted = True
                 }

{- |
  A Sentence is a SoftFOL Term.
-}
type Sentence = SPTerm

{- |
  A SPASS Identifier is a String for now.
-}
type SPIdentifier = Token


{- |
  Check a Sign if it is single sorted (and the sort is non-generated).
-}
singleSortNotGen :: Sign -> Bool
singleSortNotGen spSig = singleSorted spSig &&
                  isNothing (head . Map.elems $ sortMap spSig)

-- ** Symbol related datatypes

{- |
   Symbols of SoftFOL.
-}
data SFSymbol = SFSymbol { sym_ident :: SPIdentifier
                         , sym_type :: SFSymbType}
              deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange SFSymbol

{- |
   Symbol types of SoftFOL. (not related to CASL)
-}

data SFSymbType = SFOpType [SPIdentifier] SPIdentifier
              | SFPredType [SPIdentifier]
              | SFSortType
                deriving (Show, Eq, Ord, Typeable, Data)

sfSymbKind :: SFSymbType -> String
sfSymbKind t = case t of
  SFOpType {} -> "function"
  SFPredType {} -> "predicate"
  SFSortType -> "sort"

-- * Internal data structures

-- ** SPASS Problems

{- |
  A SPASS problem consists of a description and a logical part. The optional
  settings part hasn't been implemented yet.
-}
data SPProblem =
        SPProblem { identifier :: String,
                    description :: SPDescription,
                    logicalPart :: SPLogicalPart,
                    settings :: [SPSetting]
                    }
      deriving (Show, Eq, Ord, Typeable, Data)

-- ** SPASS Logical Parts

{- |
  A SPASS logical part consists of a symbol list, a declaration list, and a
  set of formula lists. Support for clause lists and proof lists hasn't
  been implemented yet.
-}
data SPLogicalPart =
        SPLogicalPart { symbolList :: Maybe SPSymbolList,
                        declarationList :: Maybe [SPDeclaration],
                        formulaLists :: [SPFormulaList],
                        clauseLists :: [SPClauseList],
                        proofLists :: [SPProofList]
                        }
      deriving (Show, Eq, Ord, Typeable, Data)

emptySPLogicalPart :: SPLogicalPart
emptySPLogicalPart = SPLogicalPart { symbolList = Nothing,
                                     declarationList = Nothing,
                                     formulaLists = [],
                                     clauseLists = [],
                                     proofLists = []
                                   }

-- *** Symbol Lists

{- |
  All non-predefined signature symbols must be declared as part of a SPASS
  symbol list.
-}
data SPSymbolList =
        SPSymbolList { functions :: [SPSignSym],
                       predicates :: [SPSignSym],
                       sorts :: [SPSignSym]}
      deriving (Show, Eq, Ord, Typeable, Data)

{- |
  Creates an empty SPASS Symbol List.
-}
emptySymbolList :: SPSymbolList
emptySymbolList =
        SPSymbolList { functions = [],
                       predicates = [],
                       sorts = []}


{- |
  A common data type used for all signature symbols.
-}
data SPSignSym =
        SPSignSym { sym :: SPIdentifier,
                    arity :: Int }
      | SPSimpleSignSym SPIdentifier
      deriving (Show, Eq, Ord, Typeable, Data)

data SPSortSym = SPSortSym SPIdentifier
      deriving (Show, Eq, Ord, Typeable, Data)

-- *** Declarations

{- |
  SPASS Declarations allow the introduction of sorts.
-}
data SPDeclaration =
        SPSubsortDecl { sortSymA :: SPIdentifier,
                        sortSymB :: SPIdentifier }
      | SPTermDecl { termDeclTermList :: [SPTerm],
                     termDeclTerm :: SPTerm }
      | SPSimpleTermDecl SPTerm
      | SPPredDecl { predSym :: SPIdentifier,
                     sortSyms :: [SPIdentifier] }
      | SPGenDecl { sortSym :: SPIdentifier,
                    freelyGenerated :: Bool,
                    funcList :: [SPIdentifier]}
      deriving (Show, Eq, Ord, Typeable, Data)

-- *** Formula List

{- |
  SPASS Formula List
-}
data SPFormulaList =
        SPFormulaList { originType :: SPOriginType,
                        formulae :: [SPFormula] }
      deriving (Show, Eq, Ord, Typeable, Data)

-- | test the origin type of the formula list
isAxiomFormula :: SPFormulaList -> Bool
isAxiomFormula fl =
    case originType fl of
      SPOriginAxioms -> True
      _ -> False

-- *** Clause List

-- | SPASS Clause List
data SPClauseList =
        SPClauseList { coriginType :: SPOriginType,
                        clauseType :: SPClauseType,
                        clauses :: [SPClause] }
      deriving (Show, Eq, Ord, Typeable, Data)


{- |
  There are axiom formulae and conjecture formulae.
-}
data SPOriginType =
        SPOriginAxioms
      | SPOriginConjectures
      deriving (Show, Eq, Ord, Typeable, Data)

{- |
   Formulae can be in cnf or dnf
-}
data SPClauseType = SPCNF
                  | SPDNF
    deriving (Show, Eq, Ord, Typeable, Data)

type SPClause = Named NSPClause

data NSPClause = QuanClause [SPTerm] NSPClauseBody
               | SimpleClause NSPClauseBody
               | BriefClause TermWsList TermWsList TermWsList
                 deriving (Show, Eq, Ord, Typeable, Data)

-- | a true boolean indicates the cnf
data NSPClauseBody = NSPClauseBody SPClauseType [SPLiteral]
                     deriving (Show, Eq, Ord, Typeable, Data)

data TermWsList = TWL [SPTerm] Bool    -- maybe plus.
                  deriving (Show, Eq, Ord, Typeable, Data)

{- |
  A SPASS Term.
-}
data SPTerm =
        SPQuantTerm { quantSym :: SPQuantSym,
                      variableList :: [SPTerm],
                      qFormula :: SPTerm }
      | SPComplexTerm { symbol :: SPSymbol,
                        arguments :: [SPTerm]}
      deriving (Show, Eq, Ord, Typeable, Data)

instance GetRange SPTerm

data FileName = FileName String deriving (Show, Typeable, Data)

data FormKind = FofKind | CnfKind | FotKind deriving (Typeable, Data)

instance Show FormKind where
    show k = case k of
        FofKind -> "fof"
        CnfKind -> "cnf"
        FotKind -> "fot"

data Role =
    Axiom
  | Hypothesis
  | Definition
  | Assumption
  | Lemma
  | Theorem
  | Conjecture
  | Negated_conjecture
  | Plain
  | Fi_domain
  | Fi_functors
  | Fi_predicates
  | Type
  | Unknown
    deriving (Show, Typeable, Data)

data Name = Name String deriving (Show, Typeable, Data)

data Annos = Annos Source (Maybe Info) deriving (Show, Typeable, Data)

data Source = Source GenTerm deriving (Show, Typeable, Data)

data AWord = AWord String deriving (Show, Typeable, Data)

data GenTerm =
    GenTerm GenData (Maybe GenTerm)
  | GenTermList [GenTerm]
    deriving (Show, Typeable, Data)

data GenData =
    GenData AWord [GenTerm]
  | OtherGenData String  -- variable, number, distinct_object
  | GenFormData FormData
    deriving (Show, Typeable, Data)

data FormData = FormData FormKind SPTerm deriving (Show, Typeable, Data)

data Info = Info [GenTerm] deriving (Show, Typeable, Data)

data TPTP =
    FormAnno FormKind Name Role SPTerm (Maybe Annos)
  | Include FileName [Name]
  | CommentLine String  -- collect top-level comment lines
  | EmptyLine -- and blank lines
    deriving (Show, Typeable, Data)

instance GetRange TPTP

-- | Literals for SPASS CNF and DNF (the boolean indicates a negated literal).
data SPLiteral = SPLiteral Bool SPSymbol
  deriving (Show, Eq, Ord, Typeable, Data)

toLiteral :: (Fail.MonadFail m) => SPTerm -> m SPLiteral
toLiteral t = case t of
      SPComplexTerm SPNot [SPComplexTerm arg []] ->
          return $ SPLiteral False arg
      SPComplexTerm arg [] -> return $ SPLiteral True arg
      _ -> Fail.fail "expected literal"

{- |
  SPASS Quantifier Symbols.
-}
data SPQuantSym =
        SPForall
      | SPExists
      | SPCustomQuantSym SPIdentifier
      deriving (Show, Eq, Ord, Typeable, Data)

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
      | SPID
      | SPDiv
      | SPComp
      | SPSum
      | SPConv
      | SPCustomSymbol SPIdentifier
      deriving (Show, Eq, Ord, Typeable, Data)

mkSPCustomSymbol :: String -> SPSymbol
mkSPCustomSymbol = SPCustomSymbol . mkSimpleId

showSPSymbol :: SPSymbol -> String
showSPSymbol s = case s of
        SPCustomSymbol cst -> tokStr cst
        _ -> map toLower $ drop 2 $ show s

-- *** Proof List

-- | SPASS Proof List
data SPProofList =
        SPProofList {proofType :: Maybe SPProofType,
                     plAssocList :: SPAssocList,
                     step :: [SPProofStep]}
        deriving (Show, Eq, Ord, Typeable, Data)

type SPProofType = SPIdentifier

data SPProofStep = SPProofStep { reference :: SPReference,
                                 result :: SPResult,
                                 ruleAppl :: SPRuleAppl,
                                 parentList :: [SPParent],
                                 stepAssocList :: SPAssocList}
                   deriving (Show, Eq, Ord, Typeable, Data)

data SPReference = PRefTerm SPTerm deriving (Show, Eq, Ord, Typeable, Data)

data SPResult = PResTerm SPTerm
                deriving (Show, Eq, Ord, Typeable, Data)

data SPRuleAppl = PRuleTerm SPTerm
                | PRuleUser SPUserRuleAppl
                  deriving (Show, Eq, Ord, Typeable, Data)

data SPUserRuleAppl = GeR | SpL | SpR | EqF | Rew | Obv | EmS | SoR | EqR
                    | Mpm | SPm | OPm | SHy | OHy | URR | Fac | Spt | Inp
                    | Con | RRE | SSi | ClR | UnC | Ter
                      deriving (Show, Eq, Ord, Typeable, Data)

data SPParent = PParTerm SPTerm deriving (Show, Eq, Ord, Typeable, Data)

type SPAssocList = Map.Map SPKey SPValue

data SPKey = PKeyTerm SPTerm deriving (Show, Eq, Ord, Typeable, Data)

data SPValue = PValTerm SPTerm deriving (Show, Eq, Ord, Typeable, Data)

-- *** Formulae And Terms

{- |
  A SPASS Formula is modelled as a Named SPTerm for now. This doesn't reflect
  the fact that the SPASS syntax lists both term and label as optional.
-}
type SPFormula = Named SPTerm

-- ** helpers for generating SoftFOL formulas

typedVarTerm :: SPIdentifier -- ^ Variable symbol: v
             -> SPIdentifier -- ^ Sort symbol: s
             -> SPTerm -- ^ Term: s(v)
typedVarTerm spVar spSort = compTerm (spSym spSort) [simpTerm (spSym spVar)]

spTerms :: [SPIdentifier] -> [SPTerm]
spTerms = map (simpTerm . spSym)

spSym :: SPIdentifier -> SPSymbol
spSym = SPCustomSymbol

compTerm :: SPSymbol -> [SPTerm] -> SPTerm
compTerm = SPComplexTerm

simpTerm :: SPSymbol -> SPTerm
simpTerm s = compTerm s []

mkConj :: SPTerm -> SPTerm -> SPTerm
mkConj t1 t2 = compTerm SPAnd [t1, t2]

mkDisj :: SPTerm -> SPTerm -> SPTerm
mkDisj t1 t2 = compTerm SPOr [t1, t2]

mkEq :: SPTerm -> SPTerm -> SPTerm
mkEq t1 t2 = compTerm SPEqual [t1, t2]

-- ** SPASS Desciptions

{- | A description is mandatory for a SPASS problem. It has to specify
  at least a 'name', the name of the 'author', the 'status' (see also
  'SPLogState' below), and a (verbose) description. -}
data SPDescription =
        SPDescription { name :: String,
                        author :: String,
                        version :: Maybe String,
                        logic :: Maybe String,
                        status :: SPLogState,
                        desc :: String,
                        date :: Maybe String}
      deriving (Show, Eq, Ord, Typeable, Data)

{- |
  The state of a SPASS problem can be satisfiable, unsatisfiable, or unknown.
-}
data SPLogState =
        SPStateSatisfiable
      | SPStateUnsatisfiable
      | SPStateUnknown
      deriving (Show, Eq, Ord, Typeable, Data)

-- ** SPASS Settings

{- |
   New impelmentation of Settings. See spass input syntax Version 1.5.
-}
data SPSetting = SPGeneralSettings {entries :: [SPHypothesis]}
               | SPSettings {settingName :: SPSettingLabel,
                             settingBody :: [SPSettingBody]}
                 deriving (Show, Eq, Ord, Typeable, Data)

data SPSettingBody = SPClauseRelation [SPCRBIND]   -- clauseFormulaRelation
                   | SPFlag String [String]  -- set_pred(x,y,...)
                     deriving (Show, Eq, Ord, Typeable, Data)

data SPHypothesis = SPHypothesis [SPIdentifier]
                    deriving (Show, Eq, Ord, Typeable, Data)

data SPSettingLabel = KIV | LEM | OTTER | PROTEIN | SATURATE
                    | ThreeTAP | SETHEO | SPASS
                      deriving (Show, Eq, Ord, Typeable, Data)

showSettingLabel :: SPSettingLabel -> String
showSettingLabel l = case l of
    ThreeTAP -> "3TAP"
    _ -> show l

{- |
  A Tupel of the Clause Relation
-}
data SPCRBIND = SPCRBIND {clauseSPR :: String, formulaSPR :: String}
                deriving (Show, Eq, Ord, Typeable, Data)


-- | negate a sentence
negateSentence :: SPTerm -> Maybe SPTerm
negateSentence x =
  Just $ SPComplexTerm SPNot [x]
