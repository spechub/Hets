{-# LANGUAGE DeriveDataTypeable #-}
{- |
Module      :  ./OWL2/Sublogic.hs
Copyright   :  (c) Dominik Luecke, Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Complexity analysis of OWL2

-}

module OWL2.Sublogic where

import qualified OWL2.AS as AS
import OWL2.Sign
import OWL2.Morphism

import Data.List
import Data.Maybe

import Data.Data
import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
    deriving (Show, Eq, Ord, Typeable, Data)

owlDatatypes :: Set.Set AS.Datatype
owlDatatypes = AS.predefIRIs

data OWLSub = OWLSub
    { numberRestrictions :: NumberRestrictions
    , nominals :: Bool
    , inverseRoles :: Bool
    , roleTransitivity :: Bool
    , roleHierarchy :: Bool
    , complexRoleInclusions :: Bool
    , addFeatures :: Bool
    , datatype :: Set.Set AS.Datatype
    } deriving (Show, Eq, Ord, Typeable, Data)

allSublogics :: [[OWLSub]]
allSublogics = let
  t = True
  b = slBottom
  in
  [ [ b { numberRestrictions = Unqualified }
    , b { numberRestrictions = Qualified } ]
  , [b { nominals = t } ]
  , [b { inverseRoles = t } ]
  , [b { roleTransitivity = t } ]
  , [b { roleHierarchy = t } ]
  , [b { complexRoleInclusions = t } ]
  , [b { addFeatures = t } ]
  , map (\ d -> b { datatype = Set.singleton d }) $ Set.toList owlDatatypes ]

-- | sROIQ(D)
slTop :: OWLSub
slTop = OWLSub
    { numberRestrictions = Qualified
    , nominals = True
    , inverseRoles = True
    , roleTransitivity = True
    , roleHierarchy = True
    , complexRoleInclusions = True
    , addFeatures = True
    , datatype = owlDatatypes
    }

-- | ALC
slBottom :: OWLSub
slBottom = OWLSub
    { numberRestrictions = None
    , nominals = False
    , inverseRoles = False
    , roleTransitivity = False
    , roleHierarchy = False
    , complexRoleInclusions = False
    , addFeatures = False
    , datatype = Set.empty
    }


slMax :: OWLSub -> OWLSub -> OWLSub
slMax sl1 sl2 = OWLSub
    { numberRestrictions = max (numberRestrictions sl1) (numberRestrictions sl2)
    , nominals = max (nominals sl1) (nominals sl2)
    , inverseRoles = max (inverseRoles sl1) (inverseRoles sl2)
    , roleTransitivity = max (roleTransitivity sl1) (roleTransitivity sl2)
    , roleHierarchy = max (roleHierarchy sl1) (roleHierarchy sl2)
    , complexRoleInclusions = max (complexRoleInclusions sl1)
            (complexRoleInclusions sl2)
    , addFeatures = max (addFeatures sl1) (addFeatures sl2)
    , datatype = Set.union (datatype sl1) (datatype sl2)
    }

-- | Naming for Description Logics
slName :: OWLSub -> String
slName sl =
    (if complexRoleInclusions sl || addFeatures sl
       then (if addFeatures sl then "s" else "") ++ "R"
       else (if roleTransitivity sl then "S" else "ALC")
            ++ if roleHierarchy sl then "H" else "")
    ++ (if nominals sl then "O" else "")
    ++ (if inverseRoles sl then "I" else "")
    ++ (case numberRestrictions sl of
        Qualified -> "Q"
        Unqualified -> "N"
        None -> "")
    ++ let ds = datatype sl in if Set.null ds then "" else
           "-D|" ++ (if ds == owlDatatypes then "-|" else
                intercalate "|" (map AS.printDatatype $ Set.toList ds) ++ "|")

requireQualNumberRestrictions :: OWLSub -> OWLSub
requireQualNumberRestrictions sl = sl {numberRestrictions = Qualified}

requireNumberRestrictions :: OWLSub -> OWLSub
requireNumberRestrictions sl = let nr = numberRestrictions sl in
    sl {numberRestrictions = if nr /= Qualified then Unqualified else nr}

requireRoleTransitivity :: OWLSub -> OWLSub
requireRoleTransitivity sl = sl {roleTransitivity = True}

requireRoleHierarchy :: OWLSub -> OWLSub
requireRoleHierarchy sl = sl {roleHierarchy = True}

requireComplexRoleInclusions :: OWLSub -> OWLSub
requireComplexRoleInclusions sl = (requireRoleHierarchy
    $ requireRoleTransitivity sl) {complexRoleInclusions = True}

requireAddFeatures :: OWLSub -> OWLSub
requireAddFeatures sl = (requireComplexRoleInclusions sl) {addFeatures = True}

requireNominals :: OWLSub -> OWLSub
requireNominals sl = sl {nominals = True}

requireInverseRoles :: OWLSub -> OWLSub
requireInverseRoles sl = sl {inverseRoles = True}

slDatatype :: AS.Datatype -> OWLSub
slDatatype dt = slBottom {datatype = if AS.isDatatypeKey dt then
    Set.singleton $ AS.setDatatypePrefix dt else Set.empty}

slObjProp :: AS.ObjectPropertyExpression -> OWLSub
slObjProp o = case o of
    AS.ObjectProp _ -> slBottom
    AS.ObjectInverseOf _ -> requireInverseRoles slBottom

slEntity :: AS.Entity -> OWLSub
slEntity (AS.Entity _ et iri) = case et of
    AS.Datatype -> slDatatype iri
    _ -> slBottom

slDataRange :: AS.DataRange -> OWLSub
slDataRange rn = case rn of
    AS.DataType ur _ -> slDatatype ur
    AS.DataComplementOf c -> slDataRange c
    AS.DataOneOf _ -> requireNominals slBottom
    AS.DataJunction _ drl -> foldl slMax slBottom $ map slDataRange drl

slClassExpression :: AS.ClassExpression -> OWLSub
slClassExpression des = case des of
    AS.ObjectJunction _ dec -> foldl slMax slBottom $ map slClassExpression dec
    AS.ObjectComplementOf dec -> slClassExpression dec
    AS.ObjectOneOf _ -> requireNominals slBottom
    AS.ObjectValuesFrom _ o d -> slMax (slObjProp o) (slClassExpression d)
    AS.ObjectHasSelf o -> requireAddFeatures $ slObjProp o
    AS.ObjectHasValue o _ -> slObjProp o
    AS.ObjectCardinality c -> slObjCard c
    AS.DataValuesFrom _ _ dr -> slDataRange dr
    AS.DataCardinality c -> slDataCard c
    _ -> slBottom

slDataCard :: AS.Cardinality AS.DataPropertyExpression AS.DataRange -> OWLSub
slDataCard (AS.Cardinality _ _ _ x) = requireNumberRestrictions $ case x of
    Nothing -> slBottom
    Just y -> slDataRange y

slObjCard :: AS.Cardinality AS.ObjectPropertyExpression AS.ClassExpression -> OWLSub
slObjCard (AS.Cardinality _ _ op x) = requireNumberRestrictions $ case x of
    Nothing -> slObjProp op
    Just y -> slMax (slObjProp op) (slClassExpression y)

slAxiom :: AS.Axiom -> OWLSub
slAxiom ax = case ax of
    AS.Declaration _ e -> slEntity e 
    AS.ClassAxiom cax -> case cax of
        AS.SubClassOf _ sub sup -> slMax (slClassExpression sub) (slClassExpression sup)
        AS.EquivalentClasses _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
        AS.DisjointClasses _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
        AS.DisjointUnion _ _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
    AS.ObjectPropertyAxiom opax -> case opax of
        AS.SubObjectPropertyOf _ subOpExpr supOpExpr ->
            let oExprs = case subOpExpr of
                    AS.SubObjPropExpr_obj oExpr -> [oExpr]
                    AS.SubObjPropExpr_exprchain e -> e
            in requireRoleHierarchy $ foldl slMax slBottom $ map slObjProp (supOpExpr : oExprs) 
        AS.EquivalentObjectProperties _ oExprs -> foldl slMax slBottom $ map slObjProp oExprs 
        AS.DisjointObjectProperties _ oExprs -> foldl slMax (requireAddFeatures slBottom) $ map slObjProp oExprs 
        AS.InverseObjectProperties _ e1 e2 -> slMax (slObjProp e1) (slObjProp e2)
        AS.ObjectPropertyDomain _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cExpr)
        AS.ObjectPropertyRange _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cExpr)
        AS.FunctionalObjectProperty _ oExpr -> slObjProp oExpr
        AS.InverseFunctionalObjectProperty _ oExpr -> requireInverseRoles $ slObjProp oExpr
        AS.ReflexiveObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        AS.IrreflexiveObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        AS.SymmetricObjectProperty _ oExpr -> slObjProp oExpr
        AS.AsymmetricObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        AS.TransitiveObjectProperty _ oExpr -> requireRoleTransitivity (slObjProp oExpr)
    AS.DataPropertyAxiom a -> case a of -- ?
        AS.SubDataPropertyOf _ _ _ -> requireRoleHierarchy slBottom
        AS.EquivalentDataProperties _ _ -> slBottom
        AS.DisjointDataProperties _ _ -> requireAddFeatures slBottom
        AS.DataPropertyDomain _ _ _ -> slBottom
        AS.DataPropertyRange _ _ r -> slDataRange r
        AS.FunctionalDataProperty _ _ -> slBottom
    AS.DatatypeDefinition _ dt dr -> slMax (slDatatype dt) (slDataRange dr)
    AS.HasKey _ cExpr oExprs _ -> foldl slMax (slClassExpression cExpr)
        $ map slObjProp oExprs 
    AS.Assertion a -> case a of -- ?
        AS.SameIndividual _ inds -> requireNominals slBottom
        AS.DifferentIndividuals _ _ -> requireNominals slBottom -- ?
        AS.ClassAssertion _ clExpr ind -> slClassExpression clExpr -- ?
        AS.ObjectPropertyAssertion _ _ _ _ -> slBottom
        AS.NegativeObjectPropertyAssertion _ _ _ _ -> slBottom
        AS.DataPropertyAssertion _ _ _ _ -> slBottom
        AS.NegativeDataPropertyAssertion _ _ _ _ -> slBottom
    AS.AnnotationAxiom a -> case a of
        AS.AnnotationAssertion _ p s v -> slBottom -- ?
        AS.SubAnnotationPropertyOf _ _ _ -> requireRoleHierarchy slBottom
        AS.AnnotationPropertyDomain _ _ _ -> slBottom -- ?
        AS.AnnotationPropertyRange _ _ _ -> slBottom -- ?
    _ -> slBottom -- Rules? 


slODoc :: AS.OntologyDocument -> OWLSub
slODoc = foldl slMax slBottom . map slAxiom . AS.axioms . AS.ontology

slSig :: Sign -> OWLSub
slSig sig = let dts = Set.toList $ datatypes sig in
    if Set.size (dataProperties sig) == 0 && null dts
    then slBottom else foldl slMax slBottom $ map slDatatype dts

slMor :: OWLMorphism -> OWLSub
slMor mor = slMax (slSig $ osource mor) $ slSig $ otarget mor

-- projections along sublogics
prMor :: OWLSub -> OWLMorphism -> OWLMorphism
prMor s a = a
    { osource = prSig s $ osource a
    , otarget = prSig s $ otarget a }

prSig :: OWLSub -> Sign -> Sign
prSig s a = if datatype s == Set.empty
    then a {datatypes = Set.empty, dataProperties = Set.empty}
    else a

prODoc :: OWLSub -> AS.OntologyDocument -> AS.OntologyDocument
prODoc s a =
    let o = (AS.ontology a) {AS.axioms = filter ((s >=) . slAxiom) $ AS.axioms $
            AS.ontology a }
    in a {AS.ontology = o}
