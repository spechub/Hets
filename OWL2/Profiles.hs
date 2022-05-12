{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/Profiles.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

OWL2 Profiles (EL, QL and RL)

References  :  <http://www.w3.org/TR/owl2-profiles/>
-}

module OWL2.Profiles
    ( Profiles
    , bottomProfile
    , topProfile
    , allProfiles

    , profileMax
    , printProfile

    , axiom
    , ontologyProfiles
    ) where

import OWL2.AS

import Data.Data
import qualified Data.Set as Set

import Common.IRI(setPrefix, mkIRI)

data Profiles = Profiles
    { outsideEL :: Bool
    , outsideQL :: Bool
    , outsideRL :: Bool
    } deriving (Show, Eq, Ord, Typeable, Data)

allProfiles :: [[Profiles]]
allProfiles = [[bottomProfile]
            , [elProfile, qlProfile, rlProfile]
            , [elqlProfile, elrlProfile, qlrlProfile]
            , [topProfile]]

bottomProfile :: Profiles
bottomProfile = Profiles False False False

topProfile :: Profiles
topProfile = Profiles True True True

elProfile :: Profiles
elProfile = Profiles False True True

qlProfile :: Profiles
qlProfile = Profiles True False True

rlProfile :: Profiles
rlProfile = Profiles True True False

elqlProfile :: Profiles
elqlProfile = Profiles False False True

elrlProfile :: Profiles
elrlProfile = Profiles False True False

qlrlProfile :: Profiles
qlrlProfile = Profiles True False False

printProfile :: Profiles -> String
printProfile p@(Profiles e q r) = case p of
    (Profiles True True True) -> "NP"
    _ -> (if not e then "EL" else "")
            ++ (if not q then "QL" else "")
            ++ (if not r then "RL" else "")

profileMax :: [Profiles] -> Profiles
profileMax pl = Profiles
    { outsideEL = any outsideEL pl
    , outsideQL = any outsideQL pl
    , outsideRL = any outsideRL pl }

profileMaxWith :: (a -> Profiles) -> [a] -> Profiles
profileMaxWith f cel = profileMax (map f cel)

maximalCovering :: Profiles -> [Profiles] -> Profiles
maximalCovering c pl = profileMax [c, profileMax pl]


owlELQLForbiddenDatatypes :: Set.Set Datatype
owlELQLForbiddenDatatypes = Set.fromList . map (setPrefix "xsd" . mkIRI) $
 [ "double", "float", "nonPositiveInteger", "positiveInteger"
 , "negativeInteger", "long", "int", "short", "byte", "unsignedLong"
 , "unsignedInt", "unsignedShort", "unsignedByte", "language", "boolean"]

datatype :: Datatype -> Profiles
datatype dt = if dt `Set.member` owlELQLForbiddenDatatypes then rlProfile else bottomProfile 

literal :: Literal -> Profiles
literal l = case l of
    Literal _ (Typed dt) -> datatype dt
    NumberLit f -> datatype . setPrefix "xsd" . mkIRI . numberName $ f
    _ -> bottomProfile

individual :: Individual -> Profiles
individual i = if isAnonymous i then rlProfile else bottomProfile

objProp :: ObjectPropertyExpression -> Profiles
objProp ope = case ope of
    ObjectInverseOf _ -> qlrlProfile
    _ -> bottomProfile

-- TODO: verify
dataRange :: DataRange -> Profiles
dataRange dr = case dr of
    DataType dt cfl ->
        if null cfl then datatype dt
         else topProfile
    DataJunction IntersectionOf drl -> profileMax $ map dataRange drl
    DataOneOf ll -> topProfile {
                        outsideEL = length ll /= 1 || outsideEL (profileMaxWith literal ll)
                    }
    _ -> topProfile

subClass :: ClassExpression -> Profiles
subClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else bottomProfile
    ObjectJunction jt cel -> maximalCovering (case jt of
        IntersectionOf -> elrlProfile
        UnionOf -> rlProfile) $ map subClass cel
    ObjectOneOf il -> bottomProfile {
                    outsideEL = length il /= 1 || outsideEL (profileMaxWith individual il),
                    outsideRL = outsideRL $ profileMaxWith individual il
                }
    ObjectValuesFrom SomeValuesFrom ope ce -> profileMax [objProp ope,
        case ce of
            Expression c -> if isThing c then bottomProfile
                             else elrlProfile
            _ -> maximalCovering elrlProfile [subClass ce]]
    ObjectHasValue ope i -> maximalCovering elrlProfile
       [objProp ope, individual i]
    ObjectHasSelf ope -> maximalCovering elProfile [objProp ope]
    DataValuesFrom SomeValuesFrom _ dr -> dataRange dr
    DataHasValue _ l -> literal l
    _ -> bottomProfile

superClass :: ClassExpression -> Profiles
superClass cex = case cex of
    Expression c -> if isThing c then elqlProfile else bottomProfile
    ObjectJunction IntersectionOf cel -> profileMaxWith superClass cel
    ObjectComplementOf ce -> maximalCovering qlrlProfile [subClass ce]
    ObjectOneOf il -> bottomProfile {
                    outsideEL = length il /= 1 || outsideEL (profileMaxWith individual il),
                    outsideRL = outsideRL $ profileMaxWith individual il
                }
    ObjectValuesFrom qt ope ce -> case qt of
        SomeValuesFrom -> profileMax [objProp ope, case ce of
            Expression _ -> elqlProfile
            _ -> elProfile]
        AllValuesFrom -> profileMax [superClass ce, rlProfile]
    ObjectHasValue ope i -> profileMax [elrlProfile, objProp ope,
        individual i]
    ObjectHasSelf ope -> profileMax [elProfile, objProp ope]
    ObjectCardinality (Cardinality MaxCardinality i _ mce) ->
        if elem i [0, 1] then profileMax [rlProfile, case mce of
            Nothing -> bottomProfile
            Just ce -> case ce of
                Expression _ -> bottomProfile
                _ -> subClass ce]
         else bottomProfile
    DataValuesFrom qt _ dr -> profileMax [dataRange dr, case qt of
        SomeValuesFrom -> elqlProfile
        AllValuesFrom -> rlProfile]
    DataHasValue _ l -> profileMax [elrlProfile, literal l]
    DataCardinality (Cardinality MaxCardinality i _ mdr) ->
        if elem i [0, 1] then profileMax [rlProfile, case mdr of
            Nothing -> topProfile
            Just dr -> dataRange dr]
         else bottomProfile
    _ -> bottomProfile

equivClassRL :: ClassExpression -> Bool
equivClassRL cex = case cex of
    Expression c -> (not . isThing) c
    ObjectJunction IntersectionOf cel -> any equivClassRL cel
    ObjectHasValue _ i -> outsideRL $ individual i
    DataHasValue _ l -> outsideRL $ literal l
    _ -> False

annotation :: Annotation -> Profiles
annotation (Annotation as _ av) = profileMax [annotations as, case av of
    AnnValLit l -> literal l
    _ -> topProfile]

annotations :: [Annotation] -> Profiles
annotations = profileMax . map annotation

classAxiomClassExpressions :: [Annotation] -> [ClassExpression] -> Profiles
classAxiomClassExpressions anns clExprs = profileMax [annotations anns, bottomProfile {
                outsideEL = outsideEL $ profileMaxWith subClass $ clExprs,
                outsideQL = outsideQL $ profileMaxWith subClass $ clExprs,
                outsideRL = any equivClassRL $ clExprs
            }]

axiom :: Axiom -> Profiles
axiom ax = case ax of
    Declaration _ _ -> bottomProfile
    ClassAxiom cax -> case cax of
        SubClassOf anns sub sup -> profileMax [annotations anns, subClass sub, superClass sup]
        EquivalentClasses anns cExprs -> classAxiomClassExpressions anns cExprs
        DisjointClasses anns cExprs -> classAxiomClassExpressions anns cExprs
        DisjointUnion anns c cExprs -> classAxiomClassExpressions anns (Expression c : cExprs)
    ObjectPropertyAxiom opax -> case opax of
        SubObjectPropertyOf anns subOpExpr supOpExpr -> case subOpExpr of
            SubObjPropExpr_obj oExpr ->
                profileMax [annotations anns, profileMax $ map objProp [oExpr, supOpExpr]]
            SubObjPropExpr_exprchain oExprs -> 
                maximalCovering elrlProfile [annotations anns, profileMax $ map objProp (supOpExpr : oExprs)]
        EquivalentObjectProperties anns oExprs -> maximalCovering (annotations anns) $ map objProp oExprs
        DisjointObjectProperties anns oExprs -> maximalCovering qlrlProfile $ (annotations anns) : map objProp oExprs
        InverseObjectProperties anns o1 o2 -> maximalCovering qlrlProfile $ (annotations anns) : map objProp [o1, o2]
        ObjectPropertyDomain anns oe ce -> profileMax [annotations anns, objProp oe, superClass ce] 
        ObjectPropertyRange anns oe ce -> profileMax [annotations anns, objProp oe, superClass ce] -- previously no check on ce was deon
        FunctionalObjectProperty _ oe -> maximalCovering rlProfile [objProp oe]
        InverseFunctionalObjectProperty _ oe -> maximalCovering rlProfile [objProp oe]
        ReflexiveObjectProperty _ oe -> maximalCovering elqlProfile [objProp oe]
        IrreflexiveObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        SymmetricObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        AsymmetricObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        TransitiveObjectProperty _ oe -> maximalCovering elrlProfile [objProp oe]
    DataPropertyAxiom a -> case a of
        SubDataPropertyOf anns _ _ -> annotations anns
        EquivalentDataProperties anns _ -> annotations anns
        DisjointDataProperties anns _ -> maximalCovering qlrlProfile [annotations anns]
        DataPropertyDomain anns _ classExpr -> profileMax [annotations anns, superClass classExpr]
        DataPropertyRange anns _ dr -> profileMax [annotations anns, dataRange dr]
        FunctionalDataProperty anns _ -> maximalCovering elrlProfile [annotations anns]
    DatatypeDefinition anns dt dr -> profileMax [annotations anns, datatype dt, dataRange dr]
    HasKey anns classExpr oExprs _ -> maximalCovering elrlProfile
        [annotations anns, subClass classExpr, profileMax $ map objProp oExprs]
    Assertion a -> case a of
        SameIndividual anns inds -> maximalCovering elrlProfile
            [annotations anns, profileMax $ map individual inds]
        DifferentIndividuals anns inds -> maximalCovering elrlProfile
            [annotations anns, profileMax $ map individual inds]
        ClassAssertion anns ce ind -> profileMax [annotations anns, subClass ce, individual ind] 
        ObjectPropertyAssertion anns oExpr i1 i2 -> profileMax $
            [annotations anns, objProp oExpr] ++ map individual [i1, i2]
        NegativeObjectPropertyAssertion anns oExpr i1 i2 -> maximalCovering elrlProfile $
            [annotations anns, objProp oExpr] ++ map individual [i1, i2]
        DataPropertyAssertion anns _ ind lit -> profileMax $
            [annotations anns, individual ind, literal lit]
        NegativeDataPropertyAssertion anns _ ind lit -> maximalCovering elrlProfile $
            [annotations anns, individual ind, literal lit]
    AnnotationAxiom a -> case a of
        AnnotationAssertion anns prop _ val -> annotation $ Annotation anns prop val
        SubAnnotationPropertyOf anns _ _ -> annotations anns
        AnnotationPropertyDomain anns _ _ -> annotations anns
        AnnotationPropertyRange anns _ _ -> annotations anns
    Rule _ -> topProfile
    DGAxiom _ _ _ _ _ -> topProfile

ontologyP :: Ontology -> Profiles
ontologyP ont =
    let anns = ontologyAnnotation ont
        ax = axioms ont
    in profileMax [profileMaxWith axiom ax, profileMaxWith annotation anns]

ontologyProfiles :: OntologyDocument -> Profiles
ontologyProfiles odoc = ontologyP $ ontology odoc
