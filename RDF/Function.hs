{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  ./RDF/Function.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Instances for some of the functions used in RDF
-}

module RDF.Function where
import Common.IRI
import RDF.AS
-- import RDF.Sign

import qualified Data.HashMap.Strict as Map
{- import qualified Data.Set as Set
}
{- | this class contains general functions which operate on the ontology
    document, such as prefix renaming, IRI expansion or Morphism mapping -}
class Function a where
    function :: AMap -> a -> a

data Action = Rename | Expand
    deriving (Show, Eq, Ord)
-}
type StringMap = Map.HashMap String String
type MorphMap = Map.HashMap RDFEntity IRI
{- }
data AMap =
      StringMap StringMap
    | PrefixMap RDFPrefixMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)
{-}
maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp
-}

instance Function IRI where
    function m iri = case m of
        StringMap sm -> let pre = namePrefix iri in
                    iri { namePrefix = Map.findWithDefault pre pre sm}
        PrefixMap pm ->
            let np = namePrefix iri
                lp = localPart iri
            in case iriType iri of
                    NodeID -> iri {expandedIRI = np ++ ":" ++ lp}
                    Abbreviated -> let miri = Map.lookup np pm
                         in case miri of
                            Just rp -> if isAbsoluteIRI rp
                                then iri {expandedIRI = expandedIRI rp ++ lp}
                                else iri
                            Nothing -> error $ np ++ ": prefix not found"
                    _ -> iri
        _ -> iri

instance Function Predicate where
    function m (Predicate iri) = Predicate $ function m iri

instance Function Subject where
    function m sub = case sub of
        Subject iri -> Subject $ function m iri
        SubjectList ls -> SubjectList $ map (function m) ls
        SubjectCollection ls -> SubjectCollection $ map (function m) ls

instance Function Object where
    function m obj = case obj of
        Object s -> Object $ function m s
        ObjectLiteral l -> ObjectLiteral $ function m l

instance Function PredicateObjectList where
    function m (PredicateObjectList p ol) = PredicateObjectList (function m p)
        $ map (function m) ol

instance Function RDFLiteral where
    function m lit = case lit of
        RDFLiteral b lf (Typed dt) -> RDFLiteral b lf $ Typed $ function m dt
        _ -> lit

instance Function Triples where
    function m (Triples s ls) = Triples (function m s) $ map (function m) ls

instance Function Statement where
    function m s = case s of
        Statement t -> Statement $ function m t
        Base iri -> Base $ function m iri
        Prefix p iri -> case m of
            StringMap sm -> Prefix (fromJust $ Map.lookup p sm) iri
            _ -> s

instance Function RDFPrefixMap where
    function m prefMap = case m of
        StringMap sm -> Map.mapKeys
                            (\ pref -> fromJust $ Map.lookup pref sm) prefMap
        _ -> prefMap

instance Function TurtleDocument where
    function m doc = emptyTurtleDocument
                        { statements = map (function m) $ statements doc
                        , prefixMap = function m $ prefixMap doc }


getIri :: RDFEntityType -> IRI -> Map.Map RDFEntity IRI -> IRI
getIri ty u = fromMaybe u . Map.lookup (RDFEntity ty u)

instance Function Sign where
   function t mp (Sign p1 p2 p3) = case mp of
    StringMap _ ->
        Sign (Set.map (function t mp) p1)
            (Set.map (function t mp) p2)
            (Set.map (function t mp) p3)
    _ -> error "cannot perform operation"

instance Function RDFEntity where
    function t pm (RDFEntity ty ent) = case pm of
        StringMap _ -> RDFEntity ty $ function t pm ent
        MorphMap m -> RDFEntity ty $ getIri ty ent m

instance Function Literal where
    function _ _ l = l

instance Function Object where
    function t pm obj = case obj of
        Left iri -> Left $ function t pm iri
        Right lit -> Right $ function t pm lit

valueOfKey :: RDFEntityType -> IRI -> MorphMap -> IRI
valueOfKey ty iri mm =
    let ent = RDFEntity ty iri
    in fromMaybe iri $ Map.lookup ent mm

instance Function Axiom where
    function t mp (Axiom sub pre obj) = case mp of
        StringMap _ -> Axiom (function t mp sub) (function t mp pre)
            (function t mp obj)
        MorphMap mm ->
            let nsub = valueOfKey Subject sub mm
                npre = valueOfKey Predicate pre mm
            in Axiom nsub npre $ case obj of
                    Left iri -> Left $ valueOfKey Object iri mm
                    _ -> obj

instance Function RDFGraph where
  function t mp (RDFGraph l) = RDFGraph $ map (function t mp) l
  -}
