{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  $Header$
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Instances for some of the functions used in RDF
-}

module RDF.Function where

import OWL2.AS
import RDF.AS
import RDF.Sign

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
type MorphMap = Map.Map RDFEntity IRI

data AMap =
      StringMap StringMap
    | MorphMap MorphMap
    deriving (Show, Eq, Ord)

maybeDo :: (Function a) => Action -> AMap -> Maybe a -> Maybe a
maybeDo t mp = fmap $ function t mp

instance Function IRI where
  function a m qn = case m of
    StringMap pm -> case a of
        Rename -> let pre = namePrefix qn in
            qn { namePrefix = Map.findWithDefault pre pre pm}
        Expand ->
            let np = namePrefix qn
                lp = localPart qn
            in case iriType qn of
                    Abbreviated -> qn
                    _ -> qn {expandedIRI = np ++ ":" ++ lp}
    _ -> qn

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
