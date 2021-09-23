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

import OWL2.AS
import OWL2.Sign
import OWL2.Morphism

import Data.List

import Data.Data
import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
    deriving (Show, Eq, Ord, Typeable, Data)

owlDatatypes :: Set.Set Datatype
owlDatatypes = predefIRIs

data OWLSub = OWLSub
    { numberRestrictions :: NumberRestrictions
    , nominals :: Bool
    , inverseRoles :: Bool
    , roleTransitivity :: Bool
    , roleHierarchy :: Bool
    , complexRoleInclusions :: Bool
    , addFeatures :: Bool
    , datatype :: Set.Set Datatype
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
                intercalate "|" (map printDatatype $ Set.toList ds) ++ "|")

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

slDatatype :: Datatype -> OWLSub
slDatatype dt = slBottom {datatype = if isDatatypeKey dt then
    Set.singleton $ setDatatypePrefix dt else Set.empty}

slObjProp :: ObjectPropertyExpression -> OWLSub
slObjProp o = case o of
    ObjectProp _ -> slBottom
    ObjectInverseOf _ -> requireInverseRoles slBottom

slEntity :: Entity -> OWLSub
slEntity (Entity _ et iri) = case et of
    Datatype -> slDatatype iri
    _ -> slBottom

slDataRange :: DataRange -> OWLSub
slDataRange rn = case rn of
    DataType ur _ -> slDatatype ur
    DataComplementOf c -> slDataRange c
    DataOneOf _ -> requireNominals slBottom
    DataJunction _ drl -> foldl slMax slBottom $ map slDataRange drl

slClassExpression :: ClassExpression -> OWLSub
slClassExpression des = case des of
    ObjectJunction _ dec -> foldl slMax slBottom $ map slClassExpression dec
    ObjectComplementOf dec -> slClassExpression dec
    ObjectOneOf _ -> requireNominals slBottom
    ObjectValuesFrom _ o d -> slMax (slObjProp o) (slClassExpression d)
    ObjectHasSelf o -> requireAddFeatures $ slObjProp o
    ObjectHasValue o _ -> slObjProp o
    ObjectCardinality c -> slObjCard c
    DataValuesFrom _ _ dr -> slDataRange dr
    DataCardinality c -> slDataCard c
    _ -> slBottom

slDataCard :: Cardinality DataPropertyExpression DataRange -> OWLSub
slDataCard (Cardinality _ _ _ x) = requireNumberRestrictions $ case x of
    Nothing -> slBottom
    Just y -> slDataRange y

slObjCard :: Cardinality ObjectPropertyExpression ClassExpression -> OWLSub
slObjCard (Cardinality _ _ op x) = requireNumberRestrictions $ case x of
    Nothing -> slObjProp op
    Just y -> slMax (slObjProp op) (slClassExpression y)

slAxiom :: Axiom -> OWLSub
slAxiom ax = case ax of
    Declaration _ e -> slEntity e 
    ClassAxiom cax -> case cax of
        SubClassOf _ sub sup -> slMax (slClassExpression sub) (slClassExpression sup)
        EquivalentClasses _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
        DisjointClasses _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
        DisjointUnion _ _ clExprs -> foldl slMax slBottom $ map slClassExpression clExprs 
    ObjectPropertyAxiom opax -> case opax of
        SubObjectPropertyOf _ subOpExpr supOpExpr ->
            let oExprs = case subOpExpr of
                    SubObjPropExpr_obj oExpr -> [oExpr]
                    SubObjPropExpr_exprchain e -> e
            in requireRoleHierarchy $ foldl slMax slBottom $ map slObjProp (supOpExpr : oExprs) 
        EquivalentObjectProperties _ oExprs -> foldl slMax slBottom $ map slObjProp oExprs 
        DisjointObjectProperties _ oExprs -> foldl slMax (requireAddFeatures slBottom) $ map slObjProp oExprs 
        InverseObjectProperties _ e1 e2 -> slMax (slObjProp e1) (slObjProp e2)
        ObjectPropertyDomain _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cExpr)
        ObjectPropertyRange _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cExpr)
        FunctionalObjectProperty _ oExpr -> slObjProp oExpr
        InverseFunctionalObjectProperty _ oExpr -> requireInverseRoles $ slObjProp oExpr
        ReflexiveObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        IrreflexiveObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        SymmetricObjectProperty _ oExpr -> slObjProp oExpr
        AsymmetricObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        TransitiveObjectProperty _ oExpr -> requireRoleTransitivity (slObjProp oExpr)
    DataPropertyAxiom a -> case a of
        SubDataPropertyOf _ _ _ -> requireRoleHierarchy slBottom
        EquivalentDataProperties _ _ -> slBottom
        DisjointDataProperties _ _ -> requireAddFeatures slBottom
        DataPropertyDomain _ _ _ -> slBottom
        DataPropertyRange _ _ r -> slDataRange r
        FunctionalDataProperty _ _ -> slBottom
    DatatypeDefinition _ dt dr -> slMax (slDatatype dt) (slDataRange dr)
    HasKey _ cExpr oExprs _ -> foldl slMax (slClassExpression cExpr)
        $ map slObjProp oExprs 
    Assertion a -> case a of
        SameIndividual _ _ -> requireNominals slBottom
        DifferentIndividuals _ _ -> requireNominals slBottom
        ClassAssertion _ clExpr _ -> slClassExpression clExpr
        ObjectPropertyAssertion _ _ _ _ -> slBottom
        NegativeObjectPropertyAssertion _ _ _ _ -> slBottom
        DataPropertyAssertion _ _ _ _ -> slBottom
        NegativeDataPropertyAssertion _ _ _ _ -> slBottom
    AnnotationAxiom a -> case a of
        AnnotationAssertion _ _ _ _ -> slBottom 
        SubAnnotationPropertyOf _ _ _ -> requireRoleHierarchy slBottom
        AnnotationPropertyDomain _ _ _ -> slBottom
        AnnotationPropertyRange _ _ _ -> slBottom
    _ -> slBottom


slODoc :: OntologyDocument -> OWLSub
slODoc = foldl slMax slBottom . map slAxiom . axioms . ontology

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

prODoc :: OWLSub -> OntologyDocument -> OntologyDocument
prODoc s a =
    let o = (ontology a) {axioms = filter ((s >=) . slAxiom) $ axioms $
            ontology a }
    in a {ontology = o}
