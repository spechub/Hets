{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 Profiles (EL, QL, RL and combinations)

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.Profiles where

import OWL2.AS
import OWL2.MS

import Common.Id

import Data.Maybe

data CoreProfiles = CoreProfiles {
        el0 :: Bool,
        ql0 :: Bool,
        rl0 :: Bool
    } deriving (Show, Eq, Ord)

data AllProfiles = AllProfiles {
        el :: Bool,
        ql :: Bool,
        rl :: Bool,
        elql :: Bool,
        elrl :: Bool,
        qlrl :: Bool,
        all3 :: Bool
    } deriving (Show, Eq, Ord)

bottomProfile :: AllProfiles
bottomProfile = AllProfiles False False False False False False False

topProfile :: AllProfiles
topProfile = AllProfiles True True True True True True True

noProfile :: CoreProfiles
noProfile = CoreProfiles False False False

elProfile :: CoreProfiles
elProfile = CoreProfiles True False False

qlProfile :: CoreProfiles
qlProfile = CoreProfiles False True False

rlProfile :: CoreProfiles
rlProfile = CoreProfiles False False True

elqlProfile :: CoreProfiles
elqlProfile = CoreProfiles True True False

elrlProfile :: CoreProfiles
elrlProfile = CoreProfiles True False True

qlrlProfile :: CoreProfiles
qlrlProfile = CoreProfiles False True True

all3Profile :: CoreProfiles
all3Profile = CoreProfiles True True True

extendProfile :: CoreProfiles -> AllProfiles
extendProfile cp =
    let e = el0 cp
        q = ql0 cp
        r = rl0 cp
    in bottomProfile {
            el = e,
            ql = q,
            rl = r,
            elql = e || q,
            elrl = e || r,
            qlrl = q || r,
            all3 = e || q || r
        }

andProfileList :: [AllProfiles] -> AllProfiles
andProfileList pl = bottomProfile {
        el = all el pl,
        ql = all ql pl,
        rl = all rl pl,
        elql = all elql pl,
        elrl = all elrl pl,
        qlrl = all qlrl pl,
        all3 = all all3 pl
    }

minimalCovering :: CoreProfiles -> [AllProfiles] -> AllProfiles
minimalCovering c pl = andProfileList [extendProfile c, andProfileList pl]

datatypeRequirement :: Datatype -> AllProfiles
datatypeRequirement dt = topProfile -- needs to be implemented, of course

literal :: Literal -> AllProfiles
literal l = topProfile -- needs to be implemented

individual :: Individual -> AllProfiles
individual i = if isAnonymous i then extendProfile rlProfile else topProfile

objProp :: ObjectPropertyExpression -> AllProfiles
objProp ope = case ope of
    ObjectInverseOf _ -> extendProfile qlrlProfile
    _ -> topProfile

dataRange :: DataRange -> AllProfiles
dataRange dr = case dr of
    DataType dt cfl ->
        if null cfl then datatypeRequirement dt
         else bottomProfile
    DataJunction IntersectionOf drl -> andProfileList $ map dataRange drl
    DataOneOf ll -> minimalCovering elProfile $ map literal ll
    _ -> bottomProfile

subClass :: ClassExpression -> AllProfiles
subClass cex = case cex of
    Expression c -> if isThing c then extendProfile elqlProfile else topProfile
    ObjectJunction jt cel -> case jt of
        IntersectionOf -> minimalCovering elrlProfile $ map subClass cel
        UnionOf -> minimalCovering rlProfile $ map subClass cel
    ObjectOneOf il -> minimalCovering elrlProfile $ map individual il
    ObjectValuesFrom SomeValuesFrom ope ce -> andProfileList [objProp ope,
        case ce of
            Expression c -> if isThing c then topProfile
                             else extendProfile elrlProfile
            _ -> minimalCovering elrlProfile [subClass ce]]
    ObjectHasValue ope i -> minimalCovering elrlProfile
       [objProp ope, individual i]
    ObjectHasSelf ope -> minimalCovering elProfile [objProp ope]
    DataValuesFrom SomeValuesFrom _ dr -> dataRange dr
    DataHasValue _ l -> literal l
    _ -> bottomProfile

superClass :: ClassExpression -> AllProfiles
superClass cex = case cex of
    Expression c -> if isThing c then extendProfile elqlProfile else topProfile
    ObjectJunction IntersectionOf cel -> andProfileList $ map superClass cel
    ObjectComplementOf ce -> minimalCovering qlrlProfile [subClass ce]
    ObjectOneOf il -> andProfileList $ map individual il
    ObjectValuesFrom qt ope ce -> case qt of
        SomeValuesFrom -> case ce of
            Expression c -> minimalCovering elqlProfile [objProp ope]
            _ -> andProfileList [objProp ope, extendProfile elProfile]



{-
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
-}







