{- |
Module      :  $Header$
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@tzi.de
Stability   :  provisional
Portability :  non-portable (depends on HXT)

  Definitions for reading/writing omdoc
-}
module OMDoc.OMDocDefs where

import CASL.Sign
import CASL.AS_Basic_CASL
import qualified Common.Id as Id
import qualified CASL.AS_Basic_CASL as ABC

import Static.DevGraph
import qualified Data.Graph.Inductive.Graph as Graph

import Driver.Options

import qualified Common.Lib.Set as Set

import Data.List (find)

import qualified OMDoc.HetsInterface as Hets

import OMDoc.XmlHandling
import OMDoc.KeyDebug

-- Global-Options (for debugging currently)

data GlobalOptions =
  GOpts
    {
       dbgInf :: DbgInf
			,hetsOpts :: HetcatsOpts
    }
                
debugGO::forall a . GlobalOptions->DbgKey->String->a->a
debugGO go = debug (dbgInf go)

debugGOIO::GlobalOptions->DbgKey->String->IO ()
debugGOIO go = debugIO (dbgInf go)
                
emptyGlobalOptions::GlobalOptions
emptyGlobalOptions =
  GOpts
    {
      dbgInf = (simpleDebug [])
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
axiomNameXMLNS = ""
axiomNameXMLAttr = "name"
                                                
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

caslSymbolQuantUniversalS = "universal"
caslSymbolQuantExistentialS = "existential"
caslSymbolQuantUnique_existentialS = "unique-existential"

caslSymbolAtomFalseS = "false"
caslSymbolAtomTrueS = "true"

unsupportedS = "unsupported-formula"

typeS = "type"
caslS = "casl"

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
data PredTypeXNWON = PredTypeXNWON {predArgsXNWON :: [XmlNamedWON SORT]}
  deriving (Show, Eq, Ord)
        
-- | an operator with xml-name and origin
data OpTypeXNWON = OpTypeXNWON { opKind :: FunKind, opArgsXNWON :: [XmlNamedWON SORT], opResXNWON :: (XmlNamedWON SORT) }
  deriving (Show, Eq, Ord)

-- | tries to find the 'pure' sort among named sorts    
sortToXmlNamedWONSORT::[XmlNamedWONSORT]->SORT->(Maybe XmlNamedWONSORT)
sortToXmlNamedWONSORT list s = find (\i -> s == (xnWOaToa i)) list

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
        
predTypeToPredTypeXNWON::Set.Set (XmlNamedWON SORT)->PredType->PredTypeXNWON
predTypeToPredTypeXNWON sortwoset (PredType {predArgs = pA}) =
  let
    xnwonsorts = Set.toList sortwoset
    xnwonargs = map (\a -> case (sortToXmlNamedWONSORT xnwonsorts a) of
      Nothing -> error "Unable to find xml-named sort for predicate argument!"
      (Just xnsort) -> xnsort) pA
  in
    PredTypeXNWON xnwonargs
                
predTypeXNWONToPredType::PredTypeXNWON->PredType
predTypeXNWONToPredType (PredTypeXNWON xnargs) =
  PredType $ map xnWOaToa xnargs
                
opTypeToOpTypeXNWON::Set.Set (XmlNamedWON SORT)->OpType->OpTypeXNWON
opTypeToOpTypeXNWON sortwoset (OpType {CASL.Sign.opKind = oK, opArgs = oA, opRes = oR}) =
  let
    xnwonsorts = Set.toList sortwoset
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
type TheoryXN = XmlNamed (Graph.Node, NODE_NAME)

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
  case find (\i -> (xnName i) == xname) $ Set.toList xntheoryset of
    Nothing -> Nothing
    (Just i) -> Just (fst (xnItem i))

cv_Op_typeToOpType::OP_TYPE->OpType
cv_Op_typeToOpType (Op_type fk args res _) = OpType fk args res

cv_OpTypeToOp_type::OpType->OP_TYPE
cv_OpTypeToOp_type (OpType fk args res) = Op_type fk args res Id.nullRange

cv_Pred_typeToPredType::PRED_TYPE->PredType
cv_Pred_typeToPredType (Pred_type args _) = PredType args

cv_PredTypeToPred_type::PredType->PRED_TYPE
cv_PredTypeToPred_type (PredType args) = Pred_type args Id.nullRange
