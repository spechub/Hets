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

import qualified OWL2.AS as AS
import Common.IRI
import Common.Id (stringToId)
import OWL2.MS
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
type MorphMap = Map.Map AS.Entity IRI

data AMap =
      StringMap StringMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

getIri :: AS.EntityType -> IRI -> Map.Map AS.Entity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (AS.mkEntity ty u)

cutWith :: AS.EntityType -> Action -> AMap -> IRI -> IRI
cutWith ty t s anIri = AS.cutIRI $ function t s $ AS.mkEntity ty anIri

err :: t
err = error "operation not allowed"

instance Function AS.PrefixMap where
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
                  res = let x = expandCurie (Map.map mkIRI pm) iri in
                         case x of
                          Just y -> y
                          Nothing -> error $ "could not expand:" ++ showIRI iri 
                in if elem np ["http", "https"] then -- abbreviate
                        case Map.lookup "" pm of
                          Just ep | length ep > 5 -> case stripPrefix ep ex of
                            Just rl@(_ : _) -> res
                              { prefixName = ""
                              , iriPath = stringToId rl -- todo: maybe we should keep the Id structure of iriPath iri. See #1820
                              }
                            _ -> res
                          _ -> res
                      else res
               else if isBlankNode iri then iri else   
                    let iriMap = foldl (\pm' (kp, vp) -> 
                                case parseIRI vp of
                                  Just i -> Map.insert kp i pm'
                                  Nothing -> if null kp then 
                                               Map.insert kp 
                                                 ((mkIRI vp)) 
                                                 pm'
                                              else pm') 
                              Map.empty $  
                              Map.toList $ Map.union pm AS.predefPrefixes
                        x = expandCurie iriMap iri 
                    in case x of
                        Just y -> y
                        Nothing -> error $ "could not expand curie:" ++ showIRI iri
      in AS.setReservedPrefix iRi
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

instance Function AS.Entity where
    function t pm (AS.Entity _ ty ent) = case pm of
        StringMap _ -> AS.mkEntity ty $ function t pm ent
        MorphMap m -> AS.mkEntity ty $ getIri ty ent m

instance Function AS.Literal where
    function t pm l = case l of
        AS.Literal lf (AS.Typed dt) -> AS.Literal lf $ AS.Typed
                $ cutWith AS.Datatype t pm dt
        _ -> l

instance Function AS.ObjectPropertyExpression where
    function t s opr = case opr of
        AS.ObjectProp op -> AS.ObjectProp $ cutWith AS.ObjectProperty t s op
        AS.ObjectInverseOf op -> AS.ObjectInverseOf $ function t s op

instance Function AS.DataRange where
    function t s dra = case dra of
        AS.DataType dt ls -> AS.DataType (cutWith AS.Datatype t s dt)
            $ map (\ (cf, rv) -> (function t s cf, function t s rv)) ls
        AS.DataJunction jt drl -> AS.DataJunction jt $ map (function t s) drl
        AS.DataComplementOf dr -> AS.DataComplementOf $ function t s dr
        AS.DataOneOf ll -> AS.DataOneOf $ map (function t s) ll

instance Function AS.ClassExpression where
    function t s cle = case cle of
        AS.Expression c -> AS.Expression $ cutWith AS.Class t s c
        AS.ObjectJunction jt cel -> AS.ObjectJunction jt $ map (function t s) cel
        AS.ObjectComplementOf ce -> AS.ObjectComplementOf $ function t s ce
        AS.ObjectOneOf il -> AS.ObjectOneOf $ map (cutWith AS.NamedIndividual t s) il
        AS.ObjectValuesFrom qt op ce ->
            AS.ObjectValuesFrom qt (function t s op) $ function t s ce
        AS.ObjectHasValue op i -> AS.ObjectHasValue (function t s op)
            $ cutWith AS.NamedIndividual t s i
        AS.ObjectHasSelf op -> AS.ObjectHasSelf $ function t s op
        AS.ObjectCardinality (AS.Cardinality ct i op mce) -> AS.ObjectCardinality
            $ AS.Cardinality ct i (function t s op) $ maybeDo t s mce
        AS.DataValuesFrom qt dp dr -> AS.DataValuesFrom qt
            [(cutWith AS.DataProperty t s (head dp))] $ function t s dr
        AS.DataHasValue dp l -> AS.DataHasValue (cutWith AS.DataProperty t s dp)
            $ function t s l
        AS.DataCardinality (AS.Cardinality ct i dp mdr) -> AS.DataCardinality
              $ AS.Cardinality ct i (cutWith AS.DataProperty t s dp) $ maybeDo t s mdr

instance Function AS.Annotation where
    function t s (AS.Annotation al ap av) = AS.Annotation (map (function t s) al)
        (cutWith AS.AnnotationProperty t s ap) $ function t s av

instance Function AS.AnnotationValue where
    function t s av = case av of
        AS.AnnValue anIri -> AS.AnnValue $ function t s anIri
        AS.AnnValLit l -> AS.AnnValLit $ function t s l

instance Function AS.AnnotationSubject where
    function t s av = case av of
        AS.AnnSubIri i -> AS.AnnSubIri $ function t s i
        AS.AnnSubAnInd i -> AS.AnnSubAnInd $ function t s i


instance Function AS.AnnotationAxiom where
    function t mp (AS.AnnotationAssertion ann p s v) = AS.AnnotationAssertion
        (function t mp ann)
        (function t mp p)
        (function t mp s)
        (function t mp v)
    function t mp (AS.SubAnnotationPropertyOf ann subP supP) = AS.SubAnnotationPropertyOf
        (function t mp ann)
        (function t mp subP)
        (function t mp supP)
    function t mp (AS.AnnotationPropertyDomain ann p i) = AS.AnnotationPropertyDomain
        (function t mp ann)
        (function t mp p)
        (function t mp i)
    function t mp (AS.AnnotationPropertyRange ann p i) = AS.AnnotationPropertyRange
        (function t mp ann)
        (function t mp p)
        (function t mp i)

instance Function AS.Axiom where
    function t mp (AS.Declaration anns e) = AS.Declaration (function t mp anns)
        (function t mp e)
    function t mp (AS.ClassAxiom c) = AS.ClassAxiom (function t mp c)
    function t mp (AS.ObjectPropertyAxiom opAx) =
        AS.ObjectPropertyAxiom (function t mp opAx)
    function t mp (AS.DataPropertyAxiom d) =
        AS.DataPropertyAxiom (function t mp d)
    function t mp  (AS.DatatypeDefinition anns dt dr) =
        AS.DatatypeDefinition (function t mp anns) (function t mp dt)
            (function t mp dr)
    function t mp (AS.HasKey anns c o d) = AS.HasKey
        (function t mp anns)
        (function t mp c)
        (function t mp <$> o)
        (function t mp <$> d)

    function t mp (AS.Assertion assertion) = AS.Assertion (function t mp assertion)   
    function t mp (AS.AnnotationAxiom a) = AS.AnnotationAxiom (function t mp a)
    function t mp (AS.Rule r) = AS.Rule (function t mp r)
    function t mp (AS.DGAxiom anns dgName dgNodes dgEdges mainClasses) =
        AS.DGAxiom (function t mp anns) (function t mp dgName)
            (function t mp dgNodes) (function t mp dgEdges)
            (function t mp mainClasses)

instance Function AS.ClassAxiom where
    function t mp (AS.SubClassOf anns subClExpr supClExpr) =
        AS.SubClassOf (function t mp anns) (function t mp subClExpr)
            (function t mp supClExpr)

    function t mp (AS.EquivalentClasses anns clExprs) =
        AS.EquivalentClasses (function t mp anns)
            (function t mp <$> clExprs)
    
    function t mp (AS.DisjointClasses anns clExprs) =
        AS.DisjointClasses (function t mp anns)
            (function t mp <$> clExprs)

    function t mp (AS.DisjointUnion anns clIri clExprs) = 
        AS.DisjointUnion (function t mp anns) (function t mp clIri)
            (function t mp <$> clExprs)


instance Function AS.SubObjectPropertyExpression where
    function t mp (AS.SubObjPropExpr_obj e) = AS.SubObjPropExpr_obj
        (function t mp e)
    function t mp (AS.SubObjPropExpr_exprchain e) = AS.SubObjPropExpr_exprchain
        (function t mp e)

instance Function AS.ObjectPropertyAxiom where
    function t mp (AS.SubObjectPropertyOf anns subExpr supExpr) = 
        AS.SubObjectPropertyOf (function t mp anns)
            (function t mp subExpr)
            (function t mp supExpr)
            
    function t mp (AS.EquivalentObjectProperties anns exprs) = 
        AS.EquivalentObjectProperties (function t mp anns)
            (function t mp <$> exprs)

    function t mp (AS.DisjointObjectProperties anns exprs) = 
        AS.DisjointObjectProperties (function t mp anns)
            (function t mp <$> exprs)

    function t mp (AS.InverseObjectProperties anns expr1 expr2) = 
        AS.InverseObjectProperties (function t mp anns)
            (function t mp expr1) (function t mp expr2)

    function t mp (AS.ObjectPropertyDomain anns opExpr clExpr) = 
        AS.ObjectPropertyDomain (function t mp anns)
            (function t mp opExpr) (function t mp clExpr)

    function t mp (AS.ObjectPropertyRange anns opExpr clExpr) = 
        AS.ObjectPropertyRange (function t mp anns)
            (function t mp opExpr) (function t mp clExpr)
            
    function t mp (AS.FunctionalObjectProperty anns opExpr) =
        AS.FunctionalObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (AS.InverseFunctionalObjectProperty anns opExpr) = 
        AS.InverseFunctionalObjectProperty (function t mp anns)
            (function t mp opExpr)
            
    function t mp (AS.ReflexiveObjectProperty anns opExpr) =
        AS.ReflexiveObjectProperty (function t mp anns)
            (function t mp opExpr)
            
    function t mp (AS.IrreflexiveObjectProperty anns opExpr) =
        AS.IrreflexiveObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (AS.SymmetricObjectProperty anns opExpr) =
        AS.SymmetricObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (AS.AsymmetricObjectProperty anns opExpr) =
        AS.AsymmetricObjectProperty (function t mp anns)
            (function t mp opExpr)

    function t mp (AS.TransitiveObjectProperty anns opExpr) =
        AS.TransitiveObjectProperty (function t mp anns)
            (function t mp opExpr)

instance Function AS.DataPropertyAxiom where
    function t mp (AS.SubDataPropertyOf anns subD supD) =
        AS.SubDataPropertyOf (function t mp anns)
            (function t mp subD) (function t mp supD)
    
    function t mp (AS.EquivalentDataProperties anns dpExprs) =
        AS.EquivalentDataProperties (function t mp anns)
            (function t mp <$> dpExprs)
            
    function t mp (AS.DisjointDataProperties anns dpExprs) =
        AS.DisjointDataProperties (function t mp anns)
            (function t mp dpExprs)

    function t mp (AS.DataPropertyDomain anns dpExpr clExpr) =
        AS.DataPropertyDomain (function t mp anns)
            (function t mp dpExpr) (function t mp clExpr)
    
    function t mp (AS.DataPropertyRange anns dpExpr dr) =
        AS.DataPropertyRange (function t mp anns)
            (function t mp dpExpr) (function t mp dr)

    function t mp (AS.FunctionalDataProperty anns dpExpr) = 
        AS.FunctionalDataProperty (function t mp anns)
            (function t mp dpExpr)

instance Function AS.Assertion where
    function t mp (AS.SameIndividual anns is) = AS.SameIndividual
        (function t mp anns)
        (function t mp <$> is)
    function t mp (AS.DifferentIndividuals anns is) = AS.DifferentIndividuals
        (function t mp anns)
        (function t mp <$> is)
    function t mp (AS.ClassAssertion anns c i) = AS.ClassAssertion
        (function t mp anns)
        (function t mp c)
        (function t mp i)
    function t mp (AS.ObjectPropertyAssertion anns o s t_) = AS.ObjectPropertyAssertion
        (function t mp anns)
        (function t mp o)
        (function t mp s)
        (function t mp t_)
    function t mp (AS.NegativeObjectPropertyAssertion anns o s t_) = AS.NegativeObjectPropertyAssertion
        (function t mp anns)
        (function t mp o)
        (function t mp s)
        (function t mp t_)
    function t mp (AS.DataPropertyAssertion anns d s t_) = AS.DataPropertyAssertion
        (function t mp anns)
        (function t mp d)
        (function t mp s)
        (function t mp t_)
    function t mp (AS.NegativeDataPropertyAssertion anns d s t_) = AS.NegativeDataPropertyAssertion
        (function t mp anns)
        (function t mp d)
        (function t mp s)
        (function t mp t_)


instance (Function a) => Function [a] where
    function t mp l = function t mp <$> l

instance (Function a) => Function (Maybe a) where
    function t mp Nothing = Nothing
    function t mp (Just l) = Just (function t mp l)

instance Function AS.Rule where
    function t mp (AS.DLSafeRule anns b h) = AS.DLSafeRule
        (function t mp anns)
        (function t mp b)
        (function t mp h)
    function t mp (AS.DGRule anns b h) = AS.DGRule
        (function t mp anns)
        (function t mp b)
        (function t mp h)

instance Function AS.DataArg where
    function t mp (AS.DArg l) = AS.DArg (function t mp l)
    function t mp (AS.DVar v) = AS.DVar (function t mp v)

instance Function AS.IndividualArg where
    function t mp (AS.IArg i) = AS.IArg (function t mp i)
    function t mp (AS.IVar v) = AS.IVar (function t mp v)

instance Function AS.UnkownArg   where
    function t mp (AS.IndividualArg i) = AS.IndividualArg (function t mp i)
    function t mp (AS.DataArg d) = AS.DataArg (function t mp d)
    function t mp (AS.Variable v) = AS.Variable (function t mp v)
    
instance Function AS.Atom where
    function t mp (AS.ClassAtom c arg) = AS.ClassAtom
        (function t mp c)
        (function t mp arg)
    function t mp (AS.DataRangeAtom d arg) = AS.DataRangeAtom
        (function t mp d)
        (function t mp arg)
    function t mp (AS.DataPropertyAtom d arg1 arg2) = AS.DataPropertyAtom
        (function t mp d)
        (function t mp arg1)
        (function t mp arg2)
    function t mp (AS.BuiltInAtom i args) = AS.BuiltInAtom
        (function t mp i)
        (function t mp <$> args)
    function t mp (AS.SameIndividualAtom arg1 arg2) = AS.SameIndividualAtom
        (function t mp arg1)
        (function t mp arg2)
    function t mp (AS.DifferentIndividualsAtom arg1 arg2) = AS.DifferentIndividualsAtom
        (function t mp arg1)
        (function t mp arg2)
    function t mp (AS.UnknownUnaryAtom i arg) = AS.UnknownUnaryAtom
        (function t mp i)
        (function t mp arg)
    function t mp (AS.UnknownBinaryAtom i arg1 arg2) = AS.UnknownBinaryAtom
        (function t mp i)
        (function t mp arg1)
        (function t mp arg2)
    

instance Function AS.DGAtom where
    function t mp (AS.DGClassAtom c arg) = AS.DGClassAtom
        (function t mp c)
        (function t mp arg)
    function t mp (AS.DGObjectPropertyAtom e a1 a2) = AS.DGObjectPropertyAtom
        (function t mp e)
        (function t mp a1)
        (function t mp a2)

instance Function AS.DGEdgeAssertion where
    function t mp (AS.DGEdgeAssertion o v1 v2) = AS.DGEdgeAssertion
        (function t mp o)
        (function t mp v1)
        (function t mp v2)

instance Function AS.DGNodeAssertion where
    function t mp (AS.DGNodeAssertion c node) = AS.DGNodeAssertion
        (function t mp c)
        (function t mp node)


instance Function AS.Ontology where
    function t mp (AS.Ontology name version imp anns ax) = AS.Ontology
        (function t mp name)
        (function t mp version)
        (function t mp imp)
        (function t mp anns)
        (function t mp ax)

instance Function AS.PrefixDeclaration where
    function t mp (AS.PrefixDeclaration n i) = AS.PrefixDeclaration
        n
        (function t mp i)

instance Function AS.OntologyDocument where
  function t mp (AS.OntologyDocument m pm onto) =
      AS.OntologyDocument m (function t mp pm) (function t mp onto)

instance Function RawSymb where
  function t mp rs = case rs of
     ASymbol e -> ASymbol $ function t mp e
     AnUri i -> AnUri $ function t mp i
     p -> p
