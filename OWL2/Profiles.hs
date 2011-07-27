{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Contains    :  OWL2 Profiles (EL, QL and RL)

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.Profiles where

import OWL2.AS
import OWL2.MS

import Common.Id
import Data.Maybe

data Profiles = Profiles {
        el :: Bool,
        ql :: Bool,
        rl :: Bool
    } deriving (Show, Eq, Ord)

bottomProfile :: Profiles
bottomProfile = Profiles False False False

topProfile :: Profiles
topProfile = Profiles True True True

noProfile :: Profiles
noProfile = Profiles False False False

elProfile :: Profiles
elProfile = Profiles True False False

qlProfile :: Profiles
qlProfile = Profiles False True False

rlProfile :: Profiles
rlProfile = Profiles False False True

elqlProfile :: Profiles
elqlProfile = Profiles True True False

elrlProfile :: Profiles
elrlProfile = Profiles True False True

qlrlProfile :: Profiles
qlrlProfile = Profiles False True True

all3Profile :: Profiles
all3Profile = Profiles True True True

andProfileList :: [Profiles] -> Profiles
andProfileList pl = bottomProfile {
        el = all el pl,
        ql = all ql pl,
        rl = all rl pl
    }

minimalCovering :: Profiles -> [Profiles] -> Profiles
minimalCovering c pl = andProfileList [c, andProfileList pl]

datatypeRequirement :: Datatype -> Profiles
datatypeRequirement dt = topProfile -- needs to be implemented, of course

literal :: Literal -> Profiles
literal l = topProfile -- needs to be implemented

individual :: Individual -> Profiles
individual i = if isAnonymous i then rlProfile else topProfile

objProp :: ObjectPropertyExpression -> Profiles
objProp ope = case ope of
    ObjectInverseOf _ -> qlrlProfile
    _ -> topProfile

dataRange :: DataRange -> Profiles
dataRange dr = case dr of
    DataType dt cfl ->
        if null cfl then datatypeRequirement dt
         else bottomProfile
    DataJunction IntersectionOf drl -> andProfileList $ map dataRange drl
    DataOneOf ll -> minimalCovering elProfile $ map literal ll
    _ -> bottomProfile

subClass :: ClassExpression -> Profiles
subClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else topProfile
    ObjectJunction jt cel -> minimalCovering (case jt of
        IntersectionOf -> elrlProfile
        UnionOf -> rlProfile) $ map subClass cel
    ObjectOneOf il -> minimalCovering elrlProfile $ map individual il
    ObjectValuesFrom SomeValuesFrom ope ce -> andProfileList [objProp ope,
        case ce of
            Expression c -> if isThing c then topProfile
                             else elrlProfile
            _ -> minimalCovering elrlProfile [subClass ce]]
    ObjectHasValue ope i -> minimalCovering elrlProfile
       [objProp ope, individual i]
    ObjectHasSelf ope -> minimalCovering elProfile [objProp ope]
    DataValuesFrom SomeValuesFrom _ dr -> dataRange dr
    DataHasValue _ l -> literal l
    _ -> bottomProfile

superClass :: ClassExpression -> Profiles
superClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else topProfile
    ObjectJunction IntersectionOf cel -> andList superClass cel
    ObjectComplementOf ce -> minimalCovering qlrlProfile [subClass ce]
    ObjectOneOf il -> andProfileList $ map individual il
    ObjectValuesFrom qt ope ce -> case qt of
        SomeValuesFrom -> andProfileList [objProp ope, case ce of
            Expression _ -> elqlProfile
            _ -> elProfile]
        AllValuesFrom -> andProfileList [superClass ce, rlProfile]
    ObjectHasValue ope i -> andProfileList [elrlProfile, objProp ope,
        individual i]
    ObjectHasSelf ope -> andProfileList [elProfile, objProp ope]
    ObjectCardinality (Cardinality MaxCardinality i _ mce) ->
        if elem i [0, 1] then andProfileList [rlProfile, case mce of
            Nothing -> topProfile
            Just ce -> case ce of
                Expression _ -> topProfile
                _ -> subClass ce]
         else bottomProfile
    DataValuesFrom qt _ dr -> andProfileList [dataRange dr, case qt of
        SomeValuesFrom -> elqlProfile
        AllValuesFrom -> rlProfile]
    DataHasValue _ l -> andProfileList [elrlProfile, literal l]
    DataCardinality (Cardinality MaxCardinality i _ mdr) ->
        if elem i [0, 1] then andProfileList [rlProfile, case mdr of
            Nothing -> topProfile
            Just dr -> dataRange dr]
         else bottomProfile
    _ -> bottomProfile

equivClassRL :: ClassExpression -> Bool
equivClassRL cex = case cex of
    Expression c -> (not . isThing) c
    ObjectJunction IntersectionOf cel -> all equivClassRL cel
    ObjectHasValue _ i -> rl $ individual i
    DataHasValue _ l -> rl $ literal l
    _ -> False

annotation :: Annotation -> Profiles
annotation (Annotation as _ av) = andProfileList [annotations as, case av of
    AnnValLit l -> literal l
    _ -> topProfile]

annotations :: Annotations -> Profiles
annotations ans = andProfileList $ map annotation ans

andList :: (a -> Profiles) -> [a] -> Profiles
andList f cel = andProfileList (map f cel)

assertionQL :: ClassExpression -> Bool
assertionQL ce = case ce of
    Expression _ -> True
    _ -> False

char :: [Character] -> [Character] -> Bool
char charList ls = all (`elem` ls) charList

fact :: Fact -> Profiles
fact f = case f of
    ObjectPropertyFact pn ope i -> andProfileList [objProp ope, individual i,
        case pn of
            Positive -> topProfile
            Negative -> elrlProfile]
    DataPropertyFact pn _ l -> andProfileList [literal l,
        case pn of
            Positive -> topProfile
            Negative -> elrlProfile]

lFB :: Extended -> Maybe Relation -> ListFrameBit -> Profiles
lFB ext mr lfb = case lfb of
    AnnotationBit anl -> annotations $ concatMap fst anl
    ExpressionBit anl ->
        let ans = annotations $ concatMap fst anl
            cel = map snd anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno,
                bottomProfile {
                    el = el $ andList subClass cel,
                    ql = ql $ andList subClass cel,
                    rl = all equivClassRL cel
                }]
            ClassEntity c -> case r of
                SubClass -> andProfileList [ans, subClass c,
                    andList superClass cel]
                _ -> andProfileList [ans, bottomProfile {
                    el = el $ andList subClass $ c : cel,
                    ql = ql $ andList subClass $ c : cel,
                    rl = all equivClassRL $ c : cel
                }]
            ObjectEntity op -> andProfileList [ans, objProp op,
                andList superClass cel]
            SimpleEntity (Entity ty ent) -> case ty of
                DataProperty -> andProfileList [ans, andList superClass cel]
                NamedIndividual -> andProfileList [ans, individual ent,
                    bottomProfile {
                        el = el $ andList superClass cel,
                        ql = all assertionQL cel,
                        rl = rl $ andList superClass cel
                    }]
                _ -> error "invalid expression bit"
    ObjectBit anl ->
        let ans = annotations $ concatMap fst anl
            opl = andList objProp $ map snd anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, opl, case r of
                EDRelation Equivalent -> topProfile
                _ -> qlrlProfile]
            ObjectEntity op -> andProfileList [ans, opl, objProp op, case r of
                SubPropertyOf -> topProfile
                EDRelation Equivalent -> topProfile         
                _ -> qlrlProfile]
            _ -> error "invalit object bit"
    DataBit anl ->
        let ans = annotations $ concatMap fst anl
            r = fromMaybe (error "relation needed") mr
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, case r of
                EDRelation Equivalent -> topProfile
                _ -> qlrlProfile]
            _ -> andProfileList [ans, case r of
                    SubPropertyOf -> topProfile
                    EDRelation Equivalent -> topProfile         
                    _ -> qlrlProfile]
    IndividualSameOrDifferent anl ->
        let ans = annotations $ concatMap fst anl
            r = fromMaybe (error "relation needed") mr
            i = andList individual $ map snd anl
        in case ext of
            Misc anno -> andProfileList [ans, annotations anno, i, case r of
                SDRelation Different -> topProfile
                _ -> elrlProfile]
            SimpleEntity (Entity _ ind) -> andProfileList [ans, individual ind,
                i, case r of
                    SDRelation Different -> topProfile
                    _ -> elrlProfile]
            _ -> error "bad individual bit"
    ObjectCharacteristics anl ->
        let ans = annotations $ concatMap fst anl
            cl = map snd anl
        in case ext of
            ObjectEntity op -> andProfileList [ans, objProp op,
                    bottomProfile {
                        el = char cl [Reflexive, Transitive],
                        ql = char cl [Reflexive, Symmetric, Asymmetric],
                        rl = char cl [Functional, InverseFunctional,
                                Irreflexive, Symmetric, Asymmetric, Transitive]
                    }]
            _ -> error "object entity needed"
    DataPropRange anl ->
        let ans = annotations $ concatMap fst anl
            dr = andList dataRange $ map snd anl
        in andProfileList [ans, dr]
    IndividualFacts anl ->
        let ans = annotations $ concatMap fst anl
            facts = andList fact $ map snd anl
        in andProfileList [ans, facts]




{-

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







