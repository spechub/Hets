{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/Sign.hs
Copyright   :  Heng Jiang, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

OWL 2 signature and sentences
-}

module OWL2.Sign where


import Common.IRI
import qualified OWL2.AS as AS

import qualified Data.Set as Set
import qualified Data.Map as Map

import Common.Lib.State
import Common.Result

import Control.Monad

import Data.Data

data Sign = Sign
            { concepts :: Set.Set AS.Class
              -- classes
            , datatypes :: Set.Set AS.Datatype -- datatypes
            , objectProperties :: Set.Set AS.ObjectProperty
              -- object properties
            , dataProperties :: Set.Set AS.DataProperty
              -- data properties
            , annotationRoles :: Set.Set AS.AnnotationProperty
              -- annotation properties
            , individuals :: Set.Set AS.NamedIndividual  -- named individuals
            , labelMap :: Map.Map IRI String -- labels (for better readability)
            , prefixMap :: AS.PrefixMap
            } deriving (Show, Typeable, Data)

instance Ord Sign where
  compare (Sign c1 d1 op1 dp1 ar1 iv1 _ _) (Sign c2 d2 op2 dp2 ar2 iv2 _ _)
    = compare (c1, d1, op1, dp1, ar1, iv1) (c2, d2, op2, dp2, ar2, iv2)

instance Eq Sign where
  s1 == s2 = compare s1 s2 == EQ

data SignAxiom =
    Subconcept AS.ClassExpression AS.ClassExpression   -- subclass, superclass
  | Role (DomainOrRangeOrFunc (RoleKind, RoleType)) AS.ObjectPropertyExpression
  | Data (DomainOrRangeOrFunc ()) AS.DataPropertyExpression
  | Conceptmembership AS.Individual AS.ClassExpression
    deriving (Show, Eq, Ord, Typeable, Data)

data RoleKind = FuncRole | RefRole deriving (Show, Eq, Ord, Typeable, Data)

data RoleType = IRole | DRole deriving (Show, Eq, Ord, Typeable, Data)

data DesKind = RDomain | DDomain | RIRange
  deriving (Show, Eq, Ord, Typeable, Data)

data DomainOrRangeOrFunc a =
    DomainOrRange DesKind AS.ClassExpression
  | RDRange AS.DataRange
  | FuncProp a
    deriving (Show, Eq, Ord, Typeable, Data)

emptySign :: Sign
emptySign = Sign
  { concepts = Set.empty
  , datatypes = Set.empty
  , objectProperties = Set.empty
  , dataProperties = Set.empty
  , annotationRoles = Set.empty
  , individuals = Set.empty
  , labelMap = Map.empty
  , prefixMap = Map.empty
  }

diffSig :: Sign -> Sign -> Sign
diffSig a b =
    a { concepts = concepts a `Set.difference` concepts b
      , datatypes = datatypes a `Set.difference` datatypes b
      , objectProperties = objectProperties a
            `Set.difference` objectProperties b
      , dataProperties = dataProperties a `Set.difference` dataProperties b
      , annotationRoles = annotationRoles a `Set.difference` annotationRoles b
      , individuals = individuals a `Set.difference` individuals b
      }

addSymbToSign :: Sign -> AS.Entity -> Result Sign
addSymbToSign sig ent =
 case ent of
   AS.Entity _ AS.Class eIri ->
    return sig {concepts = Set.insert eIri $ concepts sig}
   AS.Entity _ AS.ObjectProperty eIri ->
    return sig {objectProperties = Set.insert eIri $ objectProperties sig}
   AS.Entity _ AS.NamedIndividual eIri ->
    return sig {individuals = Set.insert eIri $ individuals sig}
   _ -> return sig

addSign :: Sign -> Sign -> Sign
addSign toIns totalSign =
    totalSign {
                concepts = Set.union (concepts totalSign)
                                     (concepts toIns),
                datatypes = Set.union (datatypes totalSign)
                                      (datatypes toIns),
                objectProperties = Set.union (objectProperties totalSign)
                                           (objectProperties toIns),
                dataProperties = Set.union (dataProperties totalSign)
                                            (dataProperties toIns),
                annotationRoles = Set.union (annotationRoles totalSign)
                                            (annotationRoles toIns),
                individuals = Set.union (individuals totalSign)
                                        (individuals toIns)
              }

isSubSign :: Sign -> Sign -> Bool
isSubSign a b =
    Set.isSubsetOf (concepts a) (concepts b)
       && Set.isSubsetOf (datatypes a) (datatypes b)
       && Set.isSubsetOf (objectProperties a) (objectProperties b)
       && Set.isSubsetOf (dataProperties a) (dataProperties b)
       && Set.isSubsetOf (annotationRoles a) (annotationRoles b)
       && Set.isSubsetOf (individuals a) (individuals b)

symOf :: Sign -> Set.Set AS.Entity
symOf s = Set.unions
  [ Set.map (\ ir -> AS.Entity (Map.lookup ir $ labelMap s) AS.Class ir) $ concepts s
  , Set.map (AS.mkEntity AS.Datatype) $ datatypes s
  , Set.map (AS.mkEntity AS.ObjectProperty) $ objectProperties s
  , Set.map (AS.mkEntity AS.DataProperty) $ dataProperties s
  , Set.map (AS.mkEntity AS.NamedIndividual) $ individuals s
  , Set.map (AS.mkEntity AS.AnnotationProperty) $ annotationRoles s ]

-- | takes an entity and modifies the sign according to the given function
modEntity :: (IRI -> Set.Set IRI -> Set.Set IRI) -> AS.Entity -> State Sign ()
modEntity f (AS.Entity _ ty u) = do
  s <- get
  let chg = f u
  unless (AS.isDatatypeKey u || AS.isThing u) $ put $ case ty of
    AS.Datatype -> s { datatypes = chg $ datatypes s }
    AS.Class -> s { concepts = chg $ concepts s }
    AS.ObjectProperty -> s { objectProperties = chg $ objectProperties s }
    AS.DataProperty -> s { dataProperties = chg $ dataProperties s }
    AS.NamedIndividual -> if AS.isAnonymous u then s
         else s { individuals = chg $ individuals s }
    AS.AnnotationProperty -> s {annotationRoles = chg $ annotationRoles s}

-- | adding entities to the signature
addEntity :: AS.Entity -> State Sign ()
addEntity = modEntity Set.insert
