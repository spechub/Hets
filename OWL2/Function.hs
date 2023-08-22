{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  ./OWL2/Function.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Instances for some of the functions used in OWL 2
-}

module OWL2.Function where

import OWL2.AS
import Common.IRI
import Common.Id (stringToId)
import qualified Common.GlobalAnnotations as GA (PrefixMap)
import OWL2.Sign
import OWL2.Symbols

import Data.List (stripPrefix)
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

{- | this class contains general functions which operate on the ontology
    document, such as prefix renaming, IRI expansion or Morphism mapping -}
class Function a where
    function :: Action -> AMap -> a -> a

data Action = Rename | Expand
    deriving (Show, Eq, Ord)

type StringMap = Map.Map String String
type MorphMap = Map.Map Entity IRI

data AMap =
      StringMap StringMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

getIri :: EntityType -> IRI -> Map.Map Entity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (mkEntity ty u)

cutWith :: EntityType -> Action -> AMap -> IRI -> IRI
cutWith ty t s anIri = cutIRI $ function t s $ mkEntity ty anIri

err :: t
err = error "operation not allowed"

instance Function PrefixMap where
    function a m oldPs = case m of
        StringMap mp -> case a of
            Rename ->
                foldl (\ ns (pre, ouri) ->
                    Map.insert (Map.findWithDefault pre pre mp) ouri ns)
                    Map.empty $ Map.toList oldPs
            Expand -> oldPs
        _ -> err

instance Function GA.PrefixMap where
    function a m oldPs = case m of
        StringMap mp -> case a of
            Rename ->
                foldl (\ ns (pre, ouri) ->
                    Map.insert (Map.findWithDefault pre pre mp) ouri ns)
                    Map.empty $ Map.toList oldPs
            Expand -> oldPs
        _ -> err

instance Function IRI where
  function a m iri = case m of
    StringMap pm -> case a of
     Rename -> let pre = prefixName iri in
              iri { prefixName = Map.findWithDefault pre pre pm}
     Expand ->
      let np = prefixName iri
          lp = show $ iriPath iri
          iRi = if hasFullIRI iri then let
                  ex = np ++ ":" ++ lp
                  res = expandIRI' pm iri
                in if elem np ["http", "https"] && not (isAbbrev iri) then -- abbreviate
                        case Map.lookup "" pm of
                          Just ep | length ep > 5 -> case stripPrefix ep ex of
                            Just rl@(_ : _) -> res
                              { prefixName = ""
                              , iriPath = stringToId rl -- todo: maybe we should keep the Id structure of iriPath iri. See #1820
                              }
                            _ -> res
                          _ -> res
                      else res
               else if isBlankNode iri then iri
               else let iriMap = Map.union pm predefPrefixes
                    in expandIRI' iriMap iri
      in setReservedPrefix iRi
    _ -> iri

instance Function Sign where
   function t mp (Sign p1 p2 p3 p4 p5 p6 p7 p8) = case mp of
    StringMap _ ->
        Sign (Set.map (function t mp) p1)
            (Set.map (function t mp) p2)
            (Set.map (function t mp) p3)
            (Set.map (function t mp) p4)
            (Set.map (function t mp) p5)
            (Set.map (function t mp) p6)
            (Map.mapKeys (function t mp) p7)
            (function t mp p8)
    _ -> err

instance Function Entity where
    function t pm (Entity _ ty ent) = case pm of
        StringMap _ -> mkEntity ty $ function t pm ent
        MorphMap m -> mkEntity ty $ getIri ty ent m

instance Function Literal where
    function t pm l = case l of
        Literal lf (Typed dt) -> Literal lf $ Typed
                $ cutWith Datatype t pm dt
        _ -> l

instance Function ObjectPropertyExpression where
    function t s opr = case opr of
        ObjectProp op -> ObjectProp $ cutWith ObjectProperty t s op
        ObjectInverseOf op -> ObjectInverseOf $ function t s op

instance Function DataRange where
    function t s dra = case dra of
        DataType dt ls -> DataType (cutWith Datatype t s dt)
            $ map (\ (cf, rv) -> (function t s cf, function t s rv)) ls
        DataJunction jt drl -> DataJunction jt $ map (function t s) drl
        DataComplementOf dr -> DataComplementOf $ function t s dr
        DataOneOf ll -> DataOneOf $ map (function t s) ll

instance Function ClassExpression where
    function t s cle = case cle of
        Expression c -> Expression $ cutWith Class t s c
        ObjectJunction jt cel -> ObjectJunction jt $ map (function t s) cel
        ObjectComplementOf ce -> ObjectComplementOf $ function t s ce
        ObjectOneOf il -> ObjectOneOf $ map (cutWith NamedIndividual t s) il
        ObjectValuesFrom qt op ce ->
            ObjectValuesFrom qt (function t s op) $ function t s ce
        ObjectHasValue op i -> ObjectHasValue (function t s op)
            $ cutWith NamedIndividual t s i
        ObjectHasSelf op -> ObjectHasSelf $ function t s op
        ObjectCardinality (Cardinality ct i op mce) -> ObjectCardinality
            $ Cardinality ct i (function t s op) $ maybeDo t s mce
        DataValuesFrom qt dps dr -> DataValuesFrom qt
            (cutWith DataProperty t s <$> dps) $ function t s dr
        DataHasValue dp l -> DataHasValue (cutWith DataProperty t s dp)
            $ function t s l
        DataCardinality (Cardinality ct i dp mdr) -> DataCardinality
              $ Cardinality ct i (cutWith DataProperty t s dp) $ maybeDo t s mdr

instance Function Annotation where
    function t s (Annotation al ap av) = Annotation (map (function t s) al)
        (cutWith AnnotationProperty t s ap) $ function t s av

instance Function AnnotationValue where
    function t s av = case av of
        AnnValue anIri -> AnnValue $ function t s anIri
        AnnValLit l -> AnnValLit $ function t s l
        AnnAnInd i -> AnnAnInd $ function t s i

instance Function AnnotationSubject where
    function t s av = case av of
        AnnSubIri i -> AnnSubIri $ function t s i
        AnnSubAnInd i -> AnnSubAnInd $ function t s i


instance Function AnnotationAxiom where
    function t mp (AnnotationAssertion anno p s v) = AnnotationAssertion
        (function t mp anno)
        (function t mp p)
        (function t mp s)
        (function t mp v)
    function t mp (SubAnnotationPropertyOf anno subP supP) = SubAnnotationPropertyOf
        (function t mp anno)
        (function t mp subP)
        (function t mp supP)
    function t mp (AnnotationPropertyDomain anno p i) = AnnotationPropertyDomain
        (function t mp anno)
        (function t mp p)
        (function t mp i)
    function t mp (AnnotationPropertyRange anno p i) = AnnotationPropertyRange
        (function t mp anno)
        (function t mp p)
        (function t mp i)

instance Function Axiom where
    function t mp (Declaration anns e) = Declaration (function t mp anns)
        (function t mp e)
    function t mp (ClassAxiom c) = ClassAxiom (function t mp c)
    function t mp (ObjectPropertyAxiom opAx) =
        ObjectPropertyAxiom (function t mp opAx)
    function t mp (DataPropertyAxiom d) =
        DataPropertyAxiom (function t mp d)
    function t mp  (DatatypeDefinition anns dt dr) =
        DatatypeDefinition (function t mp anns) (function t mp dt)
            (function t mp dr)
    function t mp (HasKey anns c o d) = HasKey
        (function t mp anns)
        (function t mp c)
        (function t mp <$> o)
        (function t mp <$> d)

    function t mp (Assertion assertion) = Assertion (function t mp assertion)   
    function t mp (AnnotationAxiom a) = AnnotationAxiom (function t mp a)
    function t mp (Rule r) = Rule (function t mp r)
    function t mp (DGAxiom anns dgName dgNodes dgEdges mainClasses) =
        DGAxiom (function t mp anns) (function t mp dgName)
            (function t mp dgNodes) (function t mp dgEdges)
            (function t mp mainClasses)

instance Function ClassAxiom where
    function t mp (SubClassOf anns subClExpr supClExpr) =
        SubClassOf (function t mp anns) (function t mp subClExpr)
            (function t mp supClExpr)

    function t mp (EquivalentClasses anns clExprs) =
        EquivalentClasses (function t mp anns)
            (function t mp <$> clExprs)
    
    function t mp (DisjointClasses anns clExprs) =
        DisjointClasses (function t mp anns)
            (function t mp <$> clExprs)

    function t mp (DisjointUnion anns clIri clExprs) = 
        DisjointUnion (function t mp anns) (function t mp clIri)
            (function t mp <$> clExprs)


instance Function SubObjectPropertyExpression where
    function t mp (SubObjPropExpr_obj e) = SubObjPropExpr_obj
        (function t mp e)
    function t mp (SubObjPropExpr_exprchain e) = SubObjPropExpr_exprchain
        (function t mp e)

instance Function ObjectPropertyAxiom where
    function t mp (SubObjectPropertyOf anns subExpr supExpr) = 
        SubObjectPropertyOf (function t mp anns)
            (function t mp subExpr)
            (function t mp supExpr)
            
    function t mp (EquivalentObjectProperties anns exprs) = 
        EquivalentObjectProperties (function t mp anns)
            (function t mp <$> exprs)

    function t mp (DisjointObjectProperties anns exprs) = 
        DisjointObjectProperties (function t mp anns)
            (function t mp <$> exprs)

    function t mp (InverseObjectProperties anns expr1 expr2) = 
        InverseObjectProperties (function t mp anns)
            (function t mp expr1) (function t mp expr2)

    function t mp (ObjectPropertyDomain anns opExpr clExpr) = 
        ObjectPropertyDomain (function t mp anns)
            (function t mp opExpr) (function t mp clExpr)

    function t mp (ObjectPropertyRange anns opExpr clExpr) = 
        ObjectPropertyRange (function t mp anns)
            (function t mp opExpr) (function t mp clExpr)
            
    function t mp (FunctionalObjectProperty anns opExpr) =
        FunctionalObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (InverseFunctionalObjectProperty anns opExpr) = 
        InverseFunctionalObjectProperty (function t mp anns)
            (function t mp opExpr)
            
    function t mp (ReflexiveObjectProperty anns opExpr) =
        ReflexiveObjectProperty (function t mp anns)
            (function t mp opExpr)
            
    function t mp (IrreflexiveObjectProperty anns opExpr) =
        IrreflexiveObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (SymmetricObjectProperty anns opExpr) =
        SymmetricObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (AsymmetricObjectProperty anns opExpr) =
        AsymmetricObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (TransitiveObjectProperty anns opExpr) =
        TransitiveObjectProperty (function t mp anns)
            (function t mp opExpr)

instance Function DataPropertyAxiom where
    function t mp (SubDataPropertyOf anns subD supD) =
        SubDataPropertyOf (function t mp anns)
            (function t mp subD) (function t mp supD)
    
    function t mp (EquivalentDataProperties anns dpExprs) =
        EquivalentDataProperties (function t mp anns)
            (function t mp <$> dpExprs)
            
    function t mp (DisjointDataProperties anns dpExprs) =
        DisjointDataProperties (function t mp anns)
            (function t mp dpExprs)

    function t mp (DataPropertyDomain anns dpExpr clExpr) =
        DataPropertyDomain (function t mp anns)
            (function t mp dpExpr) (function t mp clExpr)
    
    function t mp (DataPropertyRange anns dpExpr dr) =
        DataPropertyRange (function t mp anns)
            (function t mp dpExpr) (function t mp dr)

    function t mp (FunctionalDataProperty anns dpExpr) = 
        FunctionalDataProperty (function t mp anns)
            (function t mp dpExpr)

instance Function Assertion where
    function t mp (SameIndividual anns is) = SameIndividual
        (function t mp anns)
        (function t mp <$> is)
    function t mp (DifferentIndividuals anns is) = DifferentIndividuals
        (function t mp anns)
        (function t mp <$> is)
    function t mp (ClassAssertion anns c i) = ClassAssertion
        (function t mp anns)
        (function t mp c)
        (function t mp i)
    function t mp (ObjectPropertyAssertion anns o s t_) = ObjectPropertyAssertion
        (function t mp anns)
        (function t mp o)
        (function t mp s)
        (function t mp t_)
    function t mp (NegativeObjectPropertyAssertion anns o s t_) = NegativeObjectPropertyAssertion
        (function t mp anns)
        (function t mp o)
        (function t mp s)
        (function t mp t_)
    function t mp (DataPropertyAssertion anns d s t_) = DataPropertyAssertion
        (function t mp anns)
        (function t mp d)
        (function t mp s)
        (function t mp t_)
    function t mp (NegativeDataPropertyAssertion anns d s t_) = NegativeDataPropertyAssertion
        (function t mp anns)
        (function t mp d)
        (function t mp s)
        (function t mp t_)


instance (Function a) => Function [a] where
    function t mp l = function t mp <$> l

instance (Function a) => Function (Maybe a) where
    function _ _ Nothing = Nothing
    function t mp (Just l) = Just (function t mp l)

instance Function Rule where
    function t mp (DLSafeRule anns b h) = DLSafeRule
        (function t mp anns)
        (function t mp b)
        (function t mp h)
    function t mp (DGRule anns b h) = DGRule
        (function t mp anns)
        (function t mp b)
        (function t mp h)

instance Function DataArg where
    function t mp (DArg l) = DArg (function t mp l)
    function t mp (DVar v) = DVar (function t mp v)

instance Function IndividualArg where
    function t mp (IArg i) = IArg (function t mp i)
    function t mp (IVar v) = IVar (function t mp v)

instance Function UnknownArg   where
    function t mp (IndividualArg i) = IndividualArg (function t mp i)
    function t mp (DataArg d) = DataArg (function t mp d)
    function t mp (Variable v) = Variable (function t mp v)
    
instance Function Atom where
    function t mp (ClassAtom c arg) = ClassAtom
        (function t mp c)
        (function t mp arg)
    function t mp (DataRangeAtom d arg) = DataRangeAtom
        (function t mp d)
        (function t mp arg)
    function t mp (ObjectPropertyAtom oexpr arg1 arg2) = ObjectPropertyAtom
        (function t mp oexpr)
        (function t mp arg1)
        (function t mp arg2)
    function t mp (DataPropertyAtom d arg1 arg2) = DataPropertyAtom
        (function t mp d)
        (function t mp arg1)
        (function t mp arg2)
    function t mp (BuiltInAtom i args) = BuiltInAtom
        (function t mp i)
        (function t mp <$> args)
    function t mp (SameIndividualAtom arg1 arg2) = SameIndividualAtom
        (function t mp arg1)
        (function t mp arg2)
    function t mp (DifferentIndividualsAtom arg1 arg2) = DifferentIndividualsAtom
        (function t mp arg1)
        (function t mp arg2)
    function t mp (UnknownUnaryAtom i arg) = UnknownUnaryAtom
        (function t mp i)
        (function t mp arg)
    function t mp (UnknownBinaryAtom i arg1 arg2) = UnknownBinaryAtom
        (function t mp i)
        (function t mp arg1)
        (function t mp arg2)
    

instance Function DGAtom where
    function t mp (DGClassAtom c arg) = DGClassAtom
        (function t mp c)
        (function t mp arg)
    function t mp (DGObjectPropertyAtom e a1 a2) = DGObjectPropertyAtom
        (function t mp e)
        (function t mp a1)
        (function t mp a2)

instance Function DGEdgeAssertion where
    function t mp (DGEdgeAssertion o v1 v2) = DGEdgeAssertion
        (function t mp o)
        (function t mp v1)
        (function t mp v2)

instance Function DGNodeAssertion where
    function t mp (DGNodeAssertion c node) = DGNodeAssertion
        (function t mp c)
        (function t mp node)


instance Function Ontology where
    function t mp (Ontology n version imp anns ax) = Ontology
        (function t mp n)
        (function t mp version)
        (function t mp imp)
        (function t mp anns)
        (function t mp ax)

instance Function PrefixDeclaration where
    function t mp (PrefixDeclaration n i) = PrefixDeclaration
        n
        (function t mp i)

instance Function OntologyDocument where
  function t mp (OntologyDocument m pm onto) =
      OntologyDocument m (function t mp pm) (function t mp onto)

instance Function RawSymb where
  function t mp rs = case rs of
     ASymbol e -> ASymbol $ function t mp e
     AnUri i -> AnUri $ function t mp i
     p -> p
