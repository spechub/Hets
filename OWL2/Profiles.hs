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

import qualified OWL2.AS as AS
import OWL2.MS

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


owlELQLForbiddenDatatypes :: Set.Set AS.Datatype
owlELQLForbiddenDatatypes = Set.fromList . map (setPrefix "xsd" . mkIRI) $
 [ "double", "float", "nonPositiveInteger", "positiveInteger"
 , "negativeInteger", "long", "int", "short", "byte", "unsignedLong"
 , "unsignedInt", "unsignedShort", "unsignedByte", "language", "boolean"]

datatype :: AS.Datatype -> Profiles
datatype dt = if dt `Set.member` owlELQLForbiddenDatatypes then rlProfile else bottomProfile 

literal :: AS.Literal -> Profiles
literal l = case l of
    AS.Literal _ (AS.Typed dt) -> datatype dt
    AS.NumberLit f -> datatype . setPrefix "xsd" . mkIRI . AS.numberName $ f
    _ -> bottomProfile

individual :: AS.Individual -> Profiles
individual i = if AS.isAnonymous i then rlProfile else bottomProfile

objProp :: AS.ObjectPropertyExpression -> Profiles
objProp ope = case ope of
    AS.ObjectInverseOf _ -> qlrlProfile
    _ -> bottomProfile

-- TODO: verify
dataRange :: AS.DataRange -> Profiles
dataRange dr = case dr of
    AS.DataType dt cfl ->
        if null cfl then datatype dt
         else topProfile
    AS.DataJunction AS.IntersectionOf drl -> profileMax $ map dataRange drl
    AS.DataOneOf ll -> topProfile {
                        outsideEL = length ll /= 1 || outsideEL (profileMaxWith literal ll)
                    }
    _ -> topProfile

subClass :: AS.ClassExpression -> Profiles
subClass cex = case cex of
    AS.Expression c -> if AS.isThing c then elqlProfile else bottomProfile
    AS.ObjectJunction jt cel -> maximalCovering (case jt of
        AS.IntersectionOf -> elrlProfile
        AS.UnionOf -> rlProfile) $ map subClass cel
    AS.ObjectOneOf il -> bottomProfile {
                    outsideEL = length il /= 1 || outsideEL (profileMaxWith individual il),
                    outsideRL = outsideRL $ profileMaxWith individual il
                }
    AS.ObjectValuesFrom AS.SomeValuesFrom ope ce -> profileMax [objProp ope,
        case ce of
            AS.Expression c -> if AS.isThing c then bottomProfile
                             else elrlProfile
            _ -> maximalCovering elrlProfile [subClass ce]]
    AS.ObjectHasValue ope i -> maximalCovering elrlProfile
       [objProp ope, individual i]
    AS.ObjectHasSelf ope -> maximalCovering elProfile [objProp ope]
    AS.DataValuesFrom AS.SomeValuesFrom _ dr -> dataRange dr
    AS.DataHasValue _ l -> literal l
    _ -> bottomProfile

superClass :: AS.ClassExpression -> Profiles
superClass cex = case cex of
    AS.Expression c -> if AS.isThing c then elqlProfile else bottomProfile
    AS.ObjectJunction AS.IntersectionOf cel -> profileMaxWith superClass cel
    AS.ObjectComplementOf ce -> maximalCovering qlrlProfile [subClass ce]
    AS.ObjectOneOf il -> bottomProfile {
                    outsideEL = length il /= 1 || outsideEL (profileMaxWith individual il),
                    outsideRL = outsideRL $ profileMaxWith individual il
                }
    AS.ObjectValuesFrom qt ope ce -> case qt of
        AS.SomeValuesFrom -> profileMax [objProp ope, case ce of
            AS.Expression _ -> elqlProfile
            _ -> elProfile]
        AS.AllValuesFrom -> profileMax [superClass ce, rlProfile]
    AS.ObjectHasValue ope i -> profileMax [elrlProfile, objProp ope,
        individual i]
    AS.ObjectHasSelf ope -> profileMax [elProfile, objProp ope]
    AS.ObjectCardinality (AS.Cardinality AS.MaxCardinality i _ mce) ->
        if elem i [0, 1] then profileMax [rlProfile, case mce of
            Nothing -> bottomProfile
            Just ce -> case ce of
                AS.Expression _ -> bottomProfile
                _ -> subClass ce]
         else bottomProfile
    AS.DataValuesFrom qt _ dr -> profileMax [dataRange dr, case qt of
        AS.SomeValuesFrom -> elqlProfile
        AS.AllValuesFrom -> rlProfile]
    AS.DataHasValue _ l -> profileMax [elrlProfile, literal l]
    AS.DataCardinality (AS.Cardinality AS.MaxCardinality i _ mdr) ->
        if elem i [0, 1] then profileMax [rlProfile, case mdr of
            Nothing -> topProfile
            Just dr -> dataRange dr]
         else bottomProfile
    _ -> bottomProfile

equivClassRL :: AS.ClassExpression -> Bool
equivClassRL cex = case cex of
    AS.Expression c -> (not . AS.isThing) c
    AS.ObjectJunction AS.IntersectionOf cel -> any equivClassRL cel
    AS.ObjectHasValue _ i -> outsideRL $ individual i
    AS.DataHasValue _ l -> outsideRL $ literal l
    _ -> False

annotation :: AS.Annotation -> Profiles
annotation (AS.Annotation as _ av) = profileMax [annotations as, case av of
    AS.AnnValLit l -> literal l
    _ -> topProfile]

annotations :: [AS.Annotation] -> Profiles
annotations = profileMax . map annotation

classAxiomClassExpressions :: [AS.Annotation] -> [AS.ClassExpression] -> Profiles
classAxiomClassExpressions anns clExprs = profileMax [annotations anns, bottomProfile {
                outsideEL = outsideEL $ profileMaxWith subClass $ clExprs,
                outsideQL = outsideQL $ profileMaxWith subClass $ clExprs,
                outsideRL = any equivClassRL $ clExprs
            }]

axiom :: AS.Axiom -> Profiles
axiom ax = case ax of
    AS.Declaration _ _ -> bottomProfile
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf anns sub sup -> profileMax [annotations anns, subClass sub, superClass sup]
        AS.EquivalentClasses anns cExprs -> classAxiomClassExpressions anns cExprs
        AS.DisjointClasses anns cExprs -> classAxiomClassExpressions anns cExprs
        AS.DisjointUnion anns c cExprs -> classAxiomClassExpressions anns (AS.Expression c : cExprs)
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf anns subOpExpr supOpExpr -> case subOpExpr of
            AS.SubObjPropExpr_obj oExpr ->
                profileMax [annotations anns, profileMax $ map objProp [oExpr, supOpExpr]]
            AS.SubObjPropExpr_exprchain oExprs -> 
                maximalCovering elrlProfile [annotations anns, profileMax $ map objProp (supOpExpr : oExprs)]
        AS.EquivalentObjectProperties anns oExprs -> maximalCovering (annotations anns) $ map objProp oExprs
        AS.DisjointObjectProperties anns oExprs -> maximalCovering qlrlProfile $ (annotations anns) : map objProp oExprs
        AS.InverseObjectProperties anns o1 o2 -> maximalCovering qlrlProfile $ (annotations anns) : map objProp [o1, o2]
        AS.ObjectPropertyDomain anns oe ce -> profileMax [annotations anns, objProp oe, superClass ce] 
        AS.ObjectPropertyRange anns oe ce -> profileMax [annotations anns, objProp oe, superClass ce] -- previously no check on ce was deon
        AS.FunctionalObjectProperty _ oe -> maximalCovering rlProfile [objProp oe]
        AS.InverseFunctionalObjectProperty _ oe -> maximalCovering rlProfile [objProp oe]
        AS.ReflexiveObjectProperty _ oe -> maximalCovering elqlProfile [objProp oe]
        AS.IrreflexiveObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        AS.SymmetricObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        AS.AsymmetricObjectProperty _ oe -> maximalCovering qlrlProfile [objProp oe]
        AS.TransitiveObjectProperty _ oe -> maximalCovering elrlProfile [objProp oe]
    AS.DataPropertyAxiom a -> case a of
        AS.SubDataPropertyOf anns _ _ -> annotations anns
        AS.EquivalentDataProperties anns _ -> annotations anns
        AS.DisjointDataProperties anns _ -> maximalCovering qlrlProfile [annotations anns]
        AS.DataPropertyDomain anns _ classExpr -> profileMax [annotations anns, superClass classExpr]
        AS.DataPropertyRange anns _ dr -> profileMax [annotations anns, dataRange dr]
        AS.FunctionalDataProperty anns _ -> maximalCovering elrlProfile [annotations anns]
    AS.DatatypeDefinition anns dt dr -> profileMax [annotations anns, datatype dt, dataRange dr]
    AS.HasKey anns classExpr oExprs _ -> maximalCovering elrlProfile
        [annotations anns, subClass classExpr, profileMax $ map objProp oExprs]
    AS.Assertion a -> case a of
        AS.SameIndividual anns inds -> maximalCovering elrlProfile
            [annotations anns, profileMax $ map individual inds]
        AS.DifferentIndividuals anns inds -> maximalCovering elrlProfile
            [annotations anns, profileMax $ map individual inds]
        AS.ClassAssertion anns ce ind -> profileMax [annotations anns, subClass ce, individual ind] 
        AS.ObjectPropertyAssertion anns oExpr i1 i2 -> profileMax $
            [annotations anns, objProp oExpr] ++ map individual [i1, i2]
        AS.NegativeObjectPropertyAssertion anns oExpr i1 i2 -> maximalCovering elrlProfile $
            [annotations anns, objProp oExpr] ++ map individual [i1, i2]
        AS.DataPropertyAssertion anns _ ind lit -> profileMax $
            [annotations anns, individual ind, literal lit]
        AS.NegativeDataPropertyAssertion anns _ ind lit -> maximalCovering elrlProfile $
            [annotations anns, individual ind, literal lit]
    AS.AnnotationAxiom a -> case a of
        AS.AnnotationAssertion anns prop _ val -> annotation $ AS.Annotation anns prop val
        AS.SubAnnotationPropertyOf anns _ _ -> annotations anns
        AS.AnnotationPropertyDomain anns _ _ -> annotations anns
        AS.AnnotationPropertyRange anns _ _ -> annotations anns
    AS.Rule _ -> topProfile
    AS.DGAxiom _ _ _ _ _ -> topProfile

ontologyP :: AS.Ontology -> Profiles
ontologyP ont =
    let anns = AS.ontologyAnnotation ont
        ax = AS.axioms ont
    in profileMax [profileMaxWith axiom ax, profileMaxWith annotation anns]

ontologyProfiles :: AS.OntologyDocument -> Profiles
ontologyProfiles odoc = ontologyP $ AS.ontology odoc
