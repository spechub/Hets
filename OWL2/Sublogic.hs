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
import Data.Graph (stronglyConnComp, stronglyConnCompR, graphFromEdges, SCC(..))
import Data.Array ((!), assocs, elems)
import Data.Tree
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

-- | Checks anonymous individuals
--   Anonymous individuals are not allowed in some place in OWL2 DL
slIndividuals :: [Individual] -> OWLSub
slIndividuals is = if any isAnonymous is then requireUnrestrictedDL slBottom else slBottom

slClassExpression :: COPs -> ClassExpression -> OWLSub
slClassExpression cops des = case des of
    ObjectJunction _ dec -> foldl slMax slBottom $ map (slClassExpression cops) dec
    ObjectComplementOf dec -> slClassExpression cops dec
    ObjectOneOf is -> requireNominals $ slIndividuals is
    ObjectValuesFrom _ o d -> slMax (slObjProp o) (slClassExpression cops d)
    ObjectHasSelf o -> requireAddFeatures $ slSimpleObjectProp cops o
    ObjectHasValue o i -> (if isAnonymous i then requireUnrestrictedDL else id) $ slObjProp o
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
    case x of
        Nothing -> slSimpleObjectProp cops op
        Just y -> slMax (slSimpleObjectProp cops op) (slClassExpression cops y)

slSimpleObjectProp :: COPs -> ObjectPropertyExpression  -> OWLSub
slSimpleObjectProp cops ope = let sl = slObjProp ope in
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
        FunctionalObjectProperty _ oExpr -> slSimpleObjectProp cops oExpr
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
        SameIndividual _ is -> requireNominals $ slIndividuals is
        DifferentIndividuals _ is -> requireNominals  $ slIndividuals is
        ClassAssertion _ clExpr _ -> slClassExpression cops clExpr
        ObjectPropertyAssertion _ _ si ti -> slIndividuals [si, ti]
        NegativeObjectPropertyAssertion _ _ si ti -> slIndividuals [si, ti]
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
        is = mapMaybe (\ax -> case ax of
            Assertion (ObjectPropertyAssertion _ _ s t) -> Just (s, t)
            _ -> Nothing) axs
        es = mapMaybe (\ax -> case ax of
            Declaration _ e -> Just e
            _ -> Nothing) axs
    in
    foldl slMax slBottom $ 
        [ slGDatatypes dts
        , slGPropertyHierachy axs
        , slGAnonymousIndividuals is
        , slGTypingConstraints es]

slGTypingConstraints :: [Entity] -> OWLSub
slGTypingConstraints declared = 
    if all obeysRestriction $ Map.elems entityMap then slBottom else requireUnrestrictedDL slBottom where
    entityMap = foldl (\m (Entity _ k i) -> Map.insertWith Set.union i (Set.singleton k) m) Map.empty declared
    obeysRestriction ks = all ((>=) 1 . Set.size . Set.intersection ks) $ Set.fromList <$> [
        [ObjectProperty, DataProperty, AnnotationProperty],
        [Datatype, Class]]


-- | Analyses the datatypes for a circle in their definition
slGDatatypes :: [(Datatype, DataRange)] -> OWLSub 
slGDatatypes ax = if isCyclic comps then
        requireUnrestrictedDL slBottom
    else slBottom where
    comps = stronglyConnComp $ map (\x -> (x, fst x, basedOn . snd $ x)) ax

type Graph a = Map.Map a (Set.Set a)

-- | @connected x g@ yields all nodes connected to x with an edge in g
connected :: Ord a => a -> Graph a -> Set.Set a
connected = Map.findWithDefault Set.empty

-- | Checks whether an undirected graph is cyclic
isCyclicU :: Ord a => Graph a -> Bool
isCyclicU g = case Map.keys g of
    [] -> False
    (h:_) -> fst $ isCyclicU' g h Nothing (Map.keysSet g)

-- | @isCyclicU' g v p r@ checks if a cycle can be found in @g@ starting at vertex @v@ with parent @p@ and not visited vertices @r@
isCyclicU' :: Ord a => Graph a -> a -> Maybe a -> Set.Set a -> (Bool, Set.Set a)
isCyclicU' g v p remaining = let remaining' = Set.delete v remaining in
    foldl (\(b, r) c -> if b then (b, r) else if c `Set.member` r then 
            isCyclicU' g c (Just v) r
        else (Just c /= p, r)) (False, remaining') (Map.findWithDefault Set.empty v g)

-- | @forest g@ Given that @g@ is acyclic, transforms @g@ to a forest
forest :: Ord a => Graph a -> Forest a
forest g = case Map.keys g of
    [] -> []
    (h:_) -> let (t, g') = buildTree g h in t : forest g'

-- | @reachable r g@ returns all reachable nodes from @r@ in @g@
reachable :: Ord a => a -> Graph a -> Set.Set a
reachable r g = reachable' g (Set.singleton r) r

-- | @reachable' g visited r@ returns all reachable unvisited nodes from @r@ in @g@ 
reachable' :: Ord a => Graph a -> Set.Set a -> a -> Set.Set a
reachable' g visited r = Set.union c $ Set.unions . Set.toList $ Set.map (reachable' g (Set.union visited c)) c where
    c = (connected r g) `Set.difference` visited

-- | @components  g@ gets the components of @g@
components :: Ord a => Graph a -> [Graph a]
components graph = case Map.keys graph of
    [] -> []
    (h:_) -> let (c, g') = compsOf graph h in c : components g'
    where
    compsOf graph' r = Map.partitionWithKey (\k _ -> r == k || k `Set.member` (reachable r graph')) graph'

-- | @buildTree g r@ given that @g@ is acyclic, transforms @g@ into a tree with @r@ as root node and returns the remaining graph
buildTree :: Ord a => Graph a -> a -> (Tree a, Graph a)
buildTree graph r = (Node r f, g') where
    g = Map.delete r graph
    (f, g') = foldl (\(f', g'') v ->
        let (tree, g''') = buildTree g'' v in 
            (tree : f', g''')) ([] :: [Tree a], g) $ Set.filter (/= r) (Map.findWithDefault Set.empty r graph)

slGAnonymousIndividuals :: [(Individual, Individual)] -> OWLSub
slGAnonymousIndividuals edges = if any isCyclicU comps || not (all (\t -> any (\x -> Set.size (Set.filter (not . isAnonymous) (connected x g')) <= 1) t) f) then
        requireUnrestrictedDL slBottom
    else slBottom where
    edges' = edges ++ [(y,x) | (x,y) <- edges]
    g = foldl (\m (x,y) -> Map.insertWith Set.union x (if isAnonymous y then Set.singleton y else Set.empty) m) Map.empty (filter (\(x,y) -> isAnonymous x) edges')
    g' = foldl (\m (x,y) -> Map.insertWith Set.union x (Set.singleton y) m) Map.empty edges'
    comps = components g
    f = forest g


slGPropertyHierachy :: [Axiom] -> OWLSub
slGPropertyHierachy axs
    | containsCircle 2
        . stronglyConnComp
        . (fmap (\(k, v) -> (k, k, Set.toList v)))
        . Map.assocs
        . objectPropertyHierachy True $ axs = requireUnrestrictedDL slBottom
    | otherwise = slBottom

-- | Whether a direct graph is cyclic
isCyclic :: [SCC a] -> Bool
isCyclic = containsCircle 1

-- | @containsCircle len comps@ Checks whether @comps@ contain a circle of min length @len@
containsCircle :: Int -> [SCC a] -> Bool
containsCircle len comps = any cyclic comps where
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
objectPropertyHierachy :: Bool -> [Axiom] -> Graph ObjectPropertyExpression
objectPropertyHierachy withChains = foldr (\ax m -> case ax of
        ObjectPropertyAxiom (SubObjectPropertyOf _ (SubObjPropExpr_obj o1) o2) ->
            ins o2 o1 m
        ObjectPropertyAxiom (SubObjectPropertyOf _ (SubObjPropExpr_exprchain (ops@(o1 : _ : _))) o)
            | not withChains -> m
            | o == ObjectProp topObjectProperty -> m
            | length ops == 2 && all (== o) ops -> m
            | o == o1 -> insl o (tail ops) m
            | o == last ops -> insl o (init ops) m
            | otherwise -> insl o ops m

        ObjectPropertyAxiom (EquivalentObjectProperties _ ops) ->
            foldr (\o2 -> insl o2 [o1 | o1 <- ops, o1 /= o2]) m ops
        ObjectPropertyAxiom (InverseObjectProperties _ o1 o2) ->
            ins (inverseOf o2) o1 $ ins o1 (inverseOf o2) m
        ObjectPropertyAxiom (SymmetricObjectProperty _ o) ->
            ins (inverseOf o) o $ ins o (inverseOf o) m
        _ -> m) Map.empty
    where
        ins k v m = insl k [k, v] m -- also add self for reflexive closure
        insl k v m = Map.insertWith (Set.union) k (Set.fromList v) m -- $
            --Map.insertWith (Set.union) (inverseOf k) (Set.fromList (inverseOf <$> v)) m
        -- also add hierachy for inverse

-- | All object properties in a set of axioms that are not simple
complexObjectProperties :: [Axiom] -> Set.Set ObjectPropertyExpression
complexObjectProperties axs = foldr cop Set.empty axs where
    compOPE = compositeObjectProperties axs
    h = objectPropertyHierachy False axs
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
    in slMax (slGeneralRestrictions axs) (foldl slMax slBottom . map (slAxiom cops) $ axs)

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
    let cops = compositeObjectProperties . axioms . ontology $ a
        o = (ontology a) {axioms = filter ((s >=) . slAxiom cops) $ axioms $
            ontology a }
    in a {ontology = o}
