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
import Data.Graph (stronglyConnComp, SCC(..))
import Data.Data
import Data.Maybe (mapMaybe)
import qualified Data.Map as Map
import qualified Data.Set as Set

data NumberRestrictions = None | Unqualified | Qualified
    deriving (Show, Eq, Ord, Typeable, Data)

owlDatatypes :: Set.Set Datatype
owlDatatypes = predefIRIs

data OWLSub = OWLSub
    { numberRestrictions :: NumberRestrictions -- | Cardinaly restrictions the can be used
    , nominals :: Bool              -- | Enumerated classes can be used
    , inverseRoles :: Bool          -- | Inverse roles can be used
    , roleTransitivity :: Bool      -- | Roles can be transitive
    , roleHierarchy :: Bool         -- | Role hierachy (subproperties) can be used
    , complexRoleInclusions :: Bool -- | ? Complex role inclusions can be used
    , addFeatures :: Bool           -- | ?
    , datatype :: Set.Set Datatype  -- | Set of datatypes that can be used
    , rules :: Bool                 -- | SWRL Rules can be used
    , unrestrictedDL :: Bool        -- | OWL2 DL restriction can be ignored
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
  , [b { rules = t} ]
  , [b { unrestrictedDL = t} ]
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
    , rules = True
    , unrestrictedDL = True
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
    , rules = False
    , unrestrictedDL = False
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
    , rules = max (rules sl1) (rules sl2)
    , unrestrictedDL = max (unrestrictedDL sl1) (unrestrictedDL sl2) 
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
    ++ (if rules sl then "u" else "")
    ++ (if unrestrictedDL sl then "x" else "")
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

requireRules :: OWLSub -> OWLSub
requireRules sl = sl {rules = True}

requireUnrestrictedDL :: OWLSub -> OWLSub
requireUnrestrictedDL sl = sl {unrestrictedDL = True}

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

slClassExpression :: COPs -> ClassExpression -> OWLSub
slClassExpression cops des = case des of
    ObjectJunction _ dec -> foldl slMax slBottom $ map (slClassExpression cops) dec
    ObjectComplementOf dec -> slClassExpression cops dec
    ObjectOneOf _ -> requireNominals slBottom
    ObjectValuesFrom _ o d -> slMax (slObjProp o) (slClassExpression cops d)
    ObjectHasSelf o -> slSimpleObjectProp cops o $ requireAddFeatures
    ObjectHasValue o _ -> slObjProp o
    ObjectCardinality c -> slObjCard cops c
    DataValuesFrom _ _ dr -> slDataRange dr
    DataCardinality c -> slDataCard c
    _ -> slBottom

slDataCard :: Cardinality DataPropertyExpression DataRange -> OWLSub
slDataCard (Cardinality _ _ _ x) = requireNumberRestrictions $ case x of
    Nothing -> slBottom
    Just y -> slDataRange y

slObjCard :: COPs -> Cardinality ObjectPropertyExpression ClassExpression -> OWLSub
slObjCard cops (Cardinality _ _ op x) = requireNumberRestrictions $
    slSimpleObjectProp cops op $ case x of
    Nothing -> slObjProp op
        Just y -> slMax (slObjProp op) (slClassExpression cops y)

slSimpleObjectProp :: COPs -> ObjectPropertyExpression  -> OWLSub
slSimpleObjectProp cops ope = let sl = slObjProp ope
    if ope `Set.member` cops then requireUnrestrictedDL sl else sl

slAxiom :: COPs -> Axiom -> OWLSub
slAxiom cops ax = case ax of
    Declaration _ e -> slEntity e 
    ClassAxiom cax -> case cax of
        SubClassOf _ sub sup -> slMax (slClassExpression cops sub) (slClassExpression cops sup)
        EquivalentClasses _ clExprs -> foldl slMax slBottom $ map (slClassExpression cops) clExprs 
        DisjointClasses _ clExprs -> foldl slMax slBottom $ map (slClassExpression cops) clExprs 
        DisjointUnion _ _ clExprs -> foldl slMax slBottom $ map (slClassExpression cops) clExprs 
    ObjectPropertyAxiom opax -> case opax of
        SubObjectPropertyOf _ subOpExpr supOpExpr ->
            let oExprs = case subOpExpr of
                    SubObjPropExpr_obj oExpr -> [oExpr]
                    SubObjPropExpr_exprchain e -> e
            in requireRoleHierarchy $ foldl slMax slBottom $ map slObjProp (supOpExpr : oExprs) 
        EquivalentObjectProperties _ oExprs -> foldl slMax slBottom $ map slObjProp oExprs 
        DisjointObjectProperties _ oExprs -> foldl slMax (requireAddFeatures slBottom) $ map (slSimpleObjectProp cops) oExprs 
        InverseObjectProperties _ e1 e2 -> slMax (slObjProp e1) (slObjProp e2)
        ObjectPropertyDomain _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cops cExpr)
        ObjectPropertyRange _ oExpr cExpr -> slMax (slObjProp oExpr) (slClassExpression cops cExpr)
        FunctionalObjectProperty _ oExpr -> slSimpleObjectProp cops oExpr slBottom
        InverseFunctionalObjectProperty _ oExpr -> requireInverseRoles $ slSimpleObjectProp cops oExpr
        ReflexiveObjectProperty _ oExpr -> requireAddFeatures (slObjProp oExpr)
        IrreflexiveObjectProperty _ oExpr -> requireAddFeatures $ slSimpleObjectProp cops oExpr
        SymmetricObjectProperty _ oExpr -> slObjProp oExpr
        AsymmetricObjectProperty _ oExpr -> requireAddFeatures $ slSimpleObjectProp cops oExpr
        TransitiveObjectProperty _ oExpr -> requireRoleTransitivity (slObjProp oExpr)
    DataPropertyAxiom a -> case a of
        SubDataPropertyOf _ sub _ -> requireRoleHierarchy .
            (if topDataProperty == sub then requireUnrestrictedDL else id) $
            slBottom
        EquivalentDataProperties _ _ -> slBottom
        DisjointDataProperties _ _ -> requireAddFeatures slBottom
        DataPropertyDomain _ _ _ -> slBottom
        DataPropertyRange _ _ r -> slDataRange r
        FunctionalDataProperty _ _ -> slBottom
    DatatypeDefinition _ dt dr -> slMax (slDatatype dt) (slDataRange dr)
    HasKey _ cExpr oExprs _ -> foldl slMax (slClassExpression cops cExpr)
        $ map slObjProp oExprs 
    Assertion a -> case a of
        SameIndividual _ _ -> requireNominals slBottom
        DifferentIndividuals _ _ -> requireNominals slBottom
        ClassAssertion _ clExpr _ -> slClassExpression cops clExpr
        ObjectPropertyAssertion _ _ _ _ -> slBottom
        NegativeObjectPropertyAssertion _ _ _ _ -> slBottom
        DataPropertyAssertion _ _ _ _ -> slBottom
        NegativeDataPropertyAssertion _ _ _ _ -> slBottom
    AnnotationAxiom a -> case a of
        AnnotationAssertion _ _ _ _ -> slBottom 
        SubAnnotationPropertyOf _ _ _ -> requireRoleHierarchy slBottom
        AnnotationPropertyDomain _ _ _ -> slBottom
        AnnotationPropertyRange _ _ _ -> slBottom
    Rule _ -> requireRules slBottom
    _ -> slBottom


-- | Checks only for general restrictions 
slGeneralRestrictions :: [Axiom] -> OWLSub
slGeneralRestrictions axs = 
    let dts = mapMaybe (\ax -> case ax of
            DatatypeDefinition _ dt dr -> Just (dt, dr)
            _ -> Nothing) axs
    in
    slGDatatypes dts slBottom

-- | Analyses the datatypes for a circle in their definition
slGDatatypes :: [(Datatype, DataRange)] -> OWLSub -> OWLSub
slGDatatypes ax sl = if isCyclic vertices then
        requireUnrestrictedDL sl 
    else sl where
    vertices = stronglyConnComp $ map (\x -> (x, fst x, basedOn . snd $ x)) ax


isCyclic :: [SCC a] -> Bool
isCyclic = contains 1

-- | @containsCircle len ver@ Checks whether @ver@ contains a circle of min length @len@
containsCircle :: Int -> [SCC a] -> Bool
containsCircle len vertices = any cyclic vertices where
    cyclic s = case s of
        CyclicSCC circle | length circle >= len -> True
        _ -> False

type COPs = Set.Set ObjectPropertyExpression

compositeObjectProperties :: [Axiom] -> Set.Set ObjectPropertyExpression
compositeObjectProperties axs = Set.fromList $
    ObjectProp topObjectProperty :
    ObjectProp bottomObjectProperty :
    mapMaybe (\ax -> case ax of
        ObjectPropertyAxiom (SubObjectPropertyOf _ (SubObjPropExpr_exprchain c) ope)
            | length c > 1 -> Just ope
        ObjectPropertyAxiom (TransitiveObjectProperty _ ope) -> Just ope
        _ -> Nothing
        ) axs

-- | Extracts the object property hierachy as an adjacency list.
--
--   Each object property expression has an edge according to https://www.w3.org/TR/2012/REC-owl2-syntax-20121211/#Property_Hierarchy_and_Simple_Object_Property_Expressions
hierachy :: [Axiom] -> Map.Map ObjectPropertyExpression (Set.Set ObjectPropertyExpression)
hierachy = foldr (\ax m -> case ax of
        ObjectPropertyAxiom (SubObjectPropertyOf _ (SubObjPropExpr_obj o1) o2) ->
            ins o2 o1 m
        ObjectPropertyAxiom (EquivalentObjectProperties _ ops) ->
            foldr (\o2 -> insl o2 [o1 | o1 <- ops, o1 /= o2]) m ops
        ObjectPropertyAxiom (InverseObjectProperties _ o1 o2) ->
            ins (inverseOf o2) o1 $ ins o1 (inverseOf o2) m
        ObjectPropertyAxiom (SymmetricObjectProperty _ o) ->
            ins (inverseOf o) o $ ins o (inverseOf o) m
        _ -> m) Map.empty
    where
        ins k v m = insl k [k, v] m -- also add self for reflexive closure
        insl k v m = Map.insertWith (Set.union) k (Set.fromList v) $
            Map.insertWith (Set.union) (inverseOf k) (Set.fromList (inverseOf <$> v)) m
        -- also add hierachy for inverse

-- | All object properties in a set of axioms that are not simple
complexObjectProperties :: [Axiom] -> Set.Set ObjectPropertyExpression
complexObjectProperties axs = foldr cop Set.empty axs where
    compOPE = compositeObjectProperties axs
    h = hierachy axs
    -- cop :: Axiom -> Set.Set ObjectProperty -> Set.Set.ObjectProperty
    cop (ObjectPropertyAxiom (SubObjectPropertyOf _ sub super)) = case sub of
        SubObjPropExpr_obj o -- @o -> super@ holds
            | isComposite o -> Set.insert super -- If any sub property is composite
        SubObjPropExpr_exprchain ch  -- @super ->* super@ holds, super is composite
            | length ch > 1 -> Set.insert super
        _ -> id
    cop _ = id

    -- Checks if object property expression has any composite object property
    -- expression in their hierachy
    isComposite ope = ope `Set.member` compOPE || any isComposite ts where
        ts = Map.findWithDefault Set.empty ope h


slODoc :: OntologyDocument -> OWLSub
slODoc odoc =
    let axs = axioms . ontology $ odoc
        cops = complexObjectProperties axs
    in slMax
    (slGeneralRestrictions axs)
    (foldl slMax slBottom . map (slAxiom cops) $ axs)

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
