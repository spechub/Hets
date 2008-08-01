{- |
Module      :  $Header$
Description :  OMDoc-related functions for conversion (in\/out)
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable

Definitions for reading\/writing omdoc
-}
module OMDoc.OMDocDefs where

import CASL.Sign
import CASL.AS_Basic_CASL
import qualified Common.Id as Id
import qualified CASL.AS_Basic_CASL as ABC

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map

import Data.List (find)

import qualified OMDoc.HetsDefs as Hets

import OMDoc.XmlHandling
import OMDoc.KeyDebug

debugEnv::forall a . DbgKey -> String -> a -> a
debugEnv = OMDoc.KeyDebug.debugEnv

-- Global-Options (for debugging currently)

data GlobalOptions =
  GOpts
    {
        dbgInf :: DbgInf
      , hetsOpts :: Hets.HetcatsOpts
      , processingConstraint :: Bool
    }
  deriving Show

debugGO::forall a . GlobalOptions->DbgKey->String->a->a
debugGO go = debug (dbgInf go)

debugGOIO::GlobalOptions->DbgKey->String->IO ()
debugGOIO go = debugIO (dbgInf go)

emptyGlobalOptions::GlobalOptions
emptyGlobalOptions =
  GOpts
    {
        dbgInf = (simpleDebug [])
      , hetsOpts = Hets.dho
      , processingConstraint  = False
    }

-- OMDoc definitions

omdocNameXMLNS
  ,omdocNameXMLAttr :: String
omdocNameXMLNS = "xml"
omdocNameXMLAttr = "id"

theoryNameXMLNS
  ,theoryNameXMLAttr :: String
theoryNameXMLNS = "xml"
theoryNameXMLAttr = "id"

axiomNameXMLNS
  ,axiomNameXMLAttr :: String
axiomNameXMLNS = "xml"
axiomNameXMLAttr = "id"

sortNameXMLNS
  ,sortNameXMLAttr :: String
sortNameXMLNS = ""
sortNameXMLAttr = "name"

symbolTypeXMLNS
  ,symbolTypeXMLAttr :: String

symbolTypeXMLNS = ""
symbolTypeXMLAttr = "role"

predNameXMLNS
  ,predNameXMLAttr :: String
predNameXMLNS = ""
predNameXMLAttr = "name"

opNameXMLNS
  ,opNameXMLAttr :: String
opNameXMLNS = ""
opNameXMLAttr = "name"

--caslQuantificationS
caslConjunctionS
  ,caslDisjunctionS
  ,caslImplicationS
  ,caslImplication2S
  ,caslEquivalenceS
  ,caslEquivalence2S
  ,caslNegationS
  ,caslPredicationS
  ,caslDefinednessS
  ,caslExistl_equationS
  ,caslStrong_equationS
  ,caslMembershipS
  ,caslSort_gen_axS :: String

caslSymbolQuantUniversalS
  ,caslSymbolQuantExistentialS
  ,caslSymbolQuantUnique_existentialS
  ,caslSymbolAtomFalseS
  ,caslSymbolAtomTrueS :: String


unsupportedS :: String

typeS :: String
caslS :: String

axiomInclusionS
  ,theoryInclusionS :: String

--caslQuantificationS = "quantification"
caslConjunctionS = "conjunction"
caslDisjunctionS = "disjunction"
caslImplicationS = "implication"
caslImplication2S = "implies"
caslEquivalenceS = "equivalence"
caslEquivalence2S = "equal"
caslNegationS = "neg"
caslPredicationS = "predication"
caslDefinednessS = "definedness"
caslExistl_equationS = "existial-equation"
caslStrong_equationS = "strong-equation"
caslMembershipS = "membership"
caslSort_gen_axS = "sort-gen-ax"

data FormulaType =
    FTConjunction
  | FTDisjunction
  | FTImplication
  | FTEquivalence
  | FTNegation
  | FTPredication
  | FTDefinedness
  | FTExistl_equation
  | FTStrong_equation
  | FTMembership
  | FTSort_gen_ax

instance Show FormulaType where
  show FTConjunction = caslConjunctionS
  show FTDisjunction = caslDisjunctionS
  show FTImplication = caslImplicationS
  show FTEquivalence = caslEquivalenceS
  show FTNegation = caslNegationS
  show FTPredication = caslPredicationS
  show FTDefinedness = caslDefinednessS
  show FTExistl_equation = caslExistl_equationS
  show FTStrong_equation = caslStrong_equationS
  show FTMembership = caslMembershipS
  show FTSort_gen_ax = caslSort_gen_axS

instance Read FormulaType where
  readsPrec _ "conjunction" = [(FTConjunction, "")]
  readsPrec _ "disjunction" = [(FTDisjunction, "")]
  readsPrec _ "implication" = [(FTImplication, "")]
  readsPrec _ "implies" = [(FTImplication, "")]
  readsPrec _ "equivalence" = [(FTEquivalence, "")]
  readsPrec _ "equal" = [(FTEquivalence, "")]
  readsPrec _ "neg" = [(FTNegation, "")]
  readsPrec _ "predication" = [(FTPredication, "")]
  readsPrec _ "definedness" = [(FTDefinedness, "")]
  readsPrec _ "existial-equation" = [(FTExistl_equation, "")]
  readsPrec _ "strong-equation" = [(FTStrong_equation, "")]
  readsPrec _ "membership" = [(FTMembership, "")]
  readsPrec _ "sort-gen-ax" = [(FTSort_gen_ax, "")]
  readsPrec _ _ = []

caslSymbolQuantUniversalS = "universal"
caslSymbolQuantExistentialS = "existential"
caslSymbolQuantUnique_existentialS = "unique-existential"

caslSymbolAtomFalseS = "false"
caslSymbolAtomTrueS = "true"

unsupportedS = "unsupported-formula"

typeS = "type"
caslS = "casl"

axiomInclusionS = "axiom-inclusion"
theoryInclusionS = "theory-inclusion"

-- | describes a value with an xml-name and an origin
type XmlNamedWO a b = XmlNamed (Hets.WithOrigin a b)
-- | describes a value with an xml-name and a Graph.Node for origin
type XmlNamedWON a = XmlNamedWO a Graph.Node

-- | a SORT with an xml-name and a Graph.Node for origin
type XmlNamedWONSORT = XmlNamedWON SORT

-- | strip origin
xnWOaToXNa::XmlNamedWO a b->XmlNamed a
xnWOaToXNa a = XmlNamed (Hets.woItem (xnItem a)) (xnName a)

-- | strip all
xnWOaToa::XmlNamedWO a b->a
xnWOaToa a = Hets.woItem (xnItem a)

-- | get origin (strip value and name)
xnWOaToO::XmlNamedWO a b->b
xnWOaToO a = Hets.woOrigin (xnItem a)

-- just an alias to complete this
-- | strip xml-name
xnWOaToWOa::XmlNamedWO a b->Hets.WithOrigin a b
xnWOaToWOa a = xnItem a

-- | a predicate with xml-name and origin
data PredTypeXNWON = PredTypeXNWON {predArgsXNWON :: [XmlNamedWONSORT]}
  deriving (Show, Eq, Ord)

-- | an operator with xml-name and origin
data OpTypeXNWON = OpTypeXNWON { opKindX :: FunKind, opArgsXNWON :: [XmlNamedWONSORT], opResXNWON :: XmlNamedWONSORT }
  deriving (Show, Eq, Ord)

-- | tries to find the 'pure' sort among named sorts
sortToXmlNamedWONSORT::[XmlNamedWONSORT]->SORT->(Maybe XmlNamedWONSORT)
sortToXmlNamedWONSORT list s = find (\i -> (Hets.idToString s) == (Hets.idToString (xnWOaToa i))) list

sortToXmlNamedWONSORTSet::Set.Set XmlNamedWONSORT->SORT->(Maybe XmlNamedWONSORT)
sortToXmlNamedWONSORTSet sortset sort =
  case Set.toList $ Set.filter (\i -> sort == (xnWOaToa i)) sortset of
    [] -> Nothing
    (i:_) -> (Just i)

aToXmlNamedWONa::(Eq a)=>[XmlNamedWON a]->a->(Maybe (XmlNamedWON a))
aToXmlNamedWONa xnlist a = find (\i -> a == (xnWOaToa i)) xnlist

aToXmlNamedWONaSet::(Eq a, Ord a)=>Set.Set (XmlNamedWON a)->a->(Maybe (XmlNamedWON a))
aToXmlNamedWONaSet xnset a =
  case Set.toList $ Set.filter (\i -> a == (xnWOaToa i)) xnset of
    [] -> Nothing
    (i:_) -> (Just i)

predTypeToPredTypeXNWON::[XmlNamedWON SORT]->PredType->PredTypeXNWON
predTypeToPredTypeXNWON xnwonsorts (PredType {predArgs = pA}) =
  let
    xnwonargs = map (\a -> case (sortToXmlNamedWONSORT xnwonsorts a) of
      Nothing -> error "Unable to find xml-named sort for predicate argument!"
      (Just xnsort) -> xnsort) pA
  in
    PredTypeXNWON xnwonargs

predTypeXNWONToPredType::PredTypeXNWON->PredType
predTypeXNWONToPredType (PredTypeXNWON xnargs) =
  PredType $ map xnWOaToa xnargs

opTypeToOpTypeXNWON::[XmlNamedWON SORT]->OpType->OpTypeXNWON
opTypeToOpTypeXNWON xnwonsorts (OpType {CASL.Sign.opKind = oK, opArgs = oA, opRes = oR}) =
  let
    xnwonargs = map (\a -> case (sortToXmlNamedWONSORT xnwonsorts a) of
      Nothing -> error "Unable to find xml-named sort for operator argument!"
      (Just xnsort) -> xnsort) oA
    xnwonres = case sortToXmlNamedWONSORT xnwonsorts oR of
      Nothing -> error "Unable to find xml-named sort for operator result!"
      (Just xnsort) -> xnsort
  in
    OpTypeXNWON oK xnwonargs xnwonres

opTypeXNWONToOpType::OpTypeXNWON->OpType
opTypeXNWONToOpType (OpTypeXNWON fk xnargs xnres) =
  OpType fk (map xnWOaToa xnargs) (xnWOaToa xnres)

type XmlNamedWONId = XmlNamedWON Id.Id

-- | A Theory (DevGraph-Node) with an xml-name
type TheoryXN = XmlNamed (Graph.Node, NodeName)

-- | Set of Theories
type TheoryXNSet = Set.Set TheoryXN

-- | name by node
getTheoryXmlName::TheoryXNSet->Graph.Node->Maybe XmlName
getTheoryXmlName ts n =
  case find (\i -> (fst (xnItem i)) == n) $ Set.toList ts of
    Nothing -> Nothing
    (Just i) -> Just (xnName i)

-- | node by name
getNodeForTheoryName::TheoryXNSet->XmlName->Maybe Graph.Node
getNodeForTheoryName xntheoryset xname =
  let
    searchname = case xname of
      ('#':r) -> r
      _ -> xname
  in
    case find (\i -> (xnName i) == searchname) $ Set.toList xntheoryset of
      Nothing -> Nothing
      (Just i) -> Just (fst (xnItem i))

type XmlTaggedDevGraph =
  Map.Map
    (XmlNamed Hets.NodeNameWO)
    (
        Set.Set XmlNamedWONSORT
      , Set.Set Hets.SORTWO
      , Rel.Rel XmlNamedWONSORT
      , [(XmlNamedWONId, PredType)]
      , [(XmlNamedWONId, OpType)]
      , [(XmlNamed Hets.SentenceWO)]
    )

type XmlTaggedLibEnv =
  Map.Map
      Hets.LIB_NAME
      XmlTaggedDevGraph
