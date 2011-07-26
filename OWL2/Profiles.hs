{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 Profiles (EL, QL, RL, DL)

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.Profiles where

import OWL2.AS
import OWL2.MS

import Data.Maybe

-- this datatype contains booleans, in this order, for EL, QL and RL
data CoreProfiles = (Bool, Bool, Bool)

{- this datatype contains booleans, in this order, for EL, QL, RL,
    EL + QL, EL + RL, QL + RL and EL + QL + RL -}
data AllProfiles = (Bool, Bool, Bool, Bool, Bool, Bool, Bool)

data Table = [AllProfiles]

computeAll :: CoreProfiles -> AllProfiles
computeAll (el, ql, rl) = (el, ql, rl, el || ql, el || rl, ql || rl, el || ql || rl)

minimalCovering :: Table -> AllProfiles
minimalCovering = zipWith3 &&


validSubClass :: ClassExpression -> Bool
validSubClass cex = case cex of
    Expression c -> ((not . isThing) c)
    ObjectJunction _ cel -> (all validSubClassRL cel)
    ObjectOneOf _ -> True
    ObjectValuesFrom qt _ ce -> case qt of
        SomeValuesFrom -> case ce of
            Expression c -> isThing c
            _ -> validSubClassRL ce
        _ -> False
    ObjectHasValue _ _ -> True
    DataHasValue _ _ -> True
    DataValuesFrom SomeValuesFrom _ dr -> validDataRangeRL dr
    _ -> False

validSuperClassRL :: ClassExpression -> Bool
validSuperClassRL cex = case cex of
    Expression c -> (not . isThing) c
    ObjectJunction IntersectionOf  cel -> all validSuperClassRL cel
    ObjectComplementOf ce -> validSubClassRL ce
    ObjectValuesFrom AllValuesFrom _ ce -> validSuperClassRL ce
    ObjectHasValue _ _ -> True
    ObjectCardinality (Cardinality MaxCardinality i _ mce) -> elem i [0, 1] &&
        (case mce of
            Nothing -> True
            Just ce -> case ce of
                Expression c -> isThing c
                _ -> validSubClassRL ce)
    DataValuesFrom AllValuesFrom _ dr -> validDataRangeRL dr
    DataHasValue _ _ -> True
    DataCardinality (Cardinality MaxCardinality i _ mdr) -> elem i [0, 1] &&
        (case mdr of
            Nothing -> True
            Just dr -> validDataRangeRL dr)
    _ -> False

validEquivClassRL :: ClassExpression -> Bool
validEquivClassRL cex = case cex of
    Expression c -> (not . isThing) c
    ObjectJunction IntersectionOf cel -> all validEquivClassRL cel
    ObjectHasValue _ _ -> True
    DataHasValue _ _ -> True
    _ -> False

validDataRangeRL :: DataRange -> Bool
validDataRangeRL dr = case dr of
    DataType _ cfl -> null cfl
    DataJunction IntersectionOf drl -> all validDataRangeRL drl
    _ -> False

validEDClassesRL :: Relation -> [ClassExpression] -> Bool
validEDClassesRL r cel = case r of
    EDRelation Equivalent -> all validEquivClassRL cel
    EDRelation Disjoint -> all validSubClassRL cel
    _ -> False

validLfbRL :: Maybe Relation -> Extended -> ListFrameBit -> Bool
validLfbRL mr ext lfb = case lfb of
    ExpressionBit anl ->
        let cel = map snd anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc _ -> validEDClassesRL r cel
            ClassEntity c -> case r of
                SubClass -> validSubClassRL c && all validSuperClassRL cel
                _ -> validEDClassesRL r cel
            _ -> all validSuperClassRL cel
    IndividualSameOrDifferent _ -> True
    ObjectCharacteristics anl ->
        let cl = map snd anl
        in notElem Reflexive cl && notElem Antisymmetric cl
    DataPropRange anl -> all validDataRangeRL $ map snd anl
    _ -> True

validAfbRL :: Extended -> AnnFrameBit -> Bool
validAfbRL ext afb = case afb of
    DatatypeBit dr -> validDataRangeRL dr
    ClassDisjointUnion _ -> False
    ClassHasKey _ _ -> case ext of
        ClassEntity ce -> validSubClassRL ce
        _ -> False
    _ -> True

validFbRL :: Extended -> FrameBit -> Bool
validFbRL ext fb = case fb of
    ListFrameBit mr lfb -> validLfbRL mr ext lfb
    AnnFrameBit _ afb -> validAfbRL ext afb

validAxiomRL :: Axiom -> Bool
validAxiomRL (PlainAxiom ext fb) = validFbRL ext fb  








