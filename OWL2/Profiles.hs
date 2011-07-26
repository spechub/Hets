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

import Common.Id

import Data.Maybe

-- this type contains booleans, in this order, for EL, QL and RL
type CoreProfiles = [Bool]

{- this type contains booleans, in this order, for EL, QL, RL,
    EL + QL, EL + RL, QL + RL and EL + QL + RL -}
type AllProfiles = [Bool]

computeAll :: CoreProfiles -> AllProfiles
computeAll cp = case cp of
    [e, q, r] -> [e, q, r, e || q, e || r, q || r, e || q || r]
    _ -> []

anaTable :: [[Bool]] -> [Bool]
anaTable ls =
    let first = all head ls
    in first : case length $ head ls of
        1 -> []
        _ -> anaTable $ map tail ls

minimalCovering :: CoreProfiles -> [AllProfiles] -> AllProfiles
minimalCovering c t = anaTable [anaTable t, computeAll c]

bottomProfile :: AllProfiles
bottomProfile = [False, False, False, False, False, False, False]

topProfile :: AllProfiles
topProfile = [True, True, True, True, True, True, True]

el :: CoreProfiles
el = [True, False, False]

ql :: CoreProfiles
ql = [False, True, False]

rl :: CoreProfiles
rl = [False, False, True]

elrl :: CoreProfiles
elrl = [True, False, True]

elql :: CoreProfiles
elql = [True, True, False]

qlrl :: CoreProfiles
qlrl = [False, True, True]

individual :: Individual -> AllProfiles
individual i = if isAnonymous i then computeAll rl else topProfile

objProp :: ObjectPropertyExpression -> AllProfiles
objProp ope = case ope of
    ObjectInverseOf _ -> computeAll qlrl
    _ -> topProfile 

subClass :: ClassExpression -> AllProfiles
subClass cex = case cex of
    Expression c -> computeAll [True, True, (not . isThing) c]
    ObjectJunction jt cel -> case jt of
        IntersectionOf -> minimalCovering elrl $ map subClass cel
        UnionOf -> minimalCovering rl $ map subClass cel
    ObjectOneOf _ -> computeAll elrl
    ObjectValuesFrom SomeValuesFrom _ ce -> case ce of
        Expression c -> if isThing c then topProfile
                         else computeAll elrl
        _ -> computeAll elrl
    ObjectHasValue _ _ -> computeAll elrl
    ObjectHasSelf _ -> computeAll el
    DataHasValue _ _ -> computeAll elrl
    DataValuesFrom SomeValuesFrom _ dr -> bottomProfile -- dataRange dr
    _ -> bottomProfile

superClass :: ClassExpression -> AllProfiles
superClass cex = case cex of
    Expression c -> computeAll [True, True, (not . isThing) c]
    ObjectJunction IntersectionOf cel -> anaTable $ map superClass cel
    ObjectComplementOf ce -> minimalCovering qlrl [subClass ce]
    ObjectOneOf _ -> computeAll el
    ObjectValuesFrom qt _ ce -> case qt of
        SomeValuesFrom -> minimalCovering elql [subClass ce]  -- !! check this
        AllValuesFrom -> minimalCovering rl [superClass ce]
    ObjectHasValue _ _ -> computeAll elrl
    ObjectCardinality (Cardinality MaxCardinality i _ mce) ->
        let tf = elem i [0, 1]
        in minimalCovering rl [[tf, tf, tf, tf, tf, tf, tf],
            (case mce of
                Nothing -> topProfile
                Just ce -> case ce of
                    Expression c -> topProfile
                    _ -> subClass ce)]
 {-   DataValuesFrom AllValuesFrom _ dr -> validDataRangeRL dr
    DataHasValue _ _ -> True
    DataCardinality (Cardinality MaxCardinality i _ mdr) -> elem i [0, 1] &&
        (case mdr of
            Nothing -> True
            Just dr -> validDataRangeRL dr)
    _ -> False
-}
{-
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
-}







