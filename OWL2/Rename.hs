{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

{- |
Module      :  ./OWL2/Rename.hs
Copyright   :  (c) Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Renames prefixes in OntologyDocuments, so that there are
no prefix clashes
-}

module OWL2.Rename where

import OWL2.AS
import Common.IRI
import Common.Id (stringToId)
import OWL2.MS
import OWL2.Sign
import OWL2.Function

import Data.Maybe
import Data.Char (isDigit)
import Data.List (find, nub)
import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.Result

testAndInteg :: (String, String)
     -> (PrefixMap, StringMap) -> (PrefixMap, StringMap)
testAndInteg (pre, oiri) (old, tm) = case Map.lookup pre old of
  Just anIri ->
   if oiri == anIri then (old, tm)
    else let pre' = disambiguateName pre old
         in (Map.insert pre' oiri old, Map.insert pre pre' tm)
  Nothing -> (Map.insert pre oiri old, tm)

disambiguateName :: String -> PrefixMap -> String
disambiguateName n nameMap =
  let nm = if null n then "n" else n  -- change other empty prefixes to "n..."
      newname = reverse . dropWhile isDigit $ reverse nm
      x =  find (not . flip Map.member nameMap)
           [newname ++ show (i :: Int) | i <- [1 ..]]
  in case x of
      Just y -> y
      Nothing -> error $ "could not disambiguate " ++ n ++ 
                         " using " ++ show nameMap 

uniteSign :: Sign -> Sign -> Result Sign
uniteSign s1 s2 = do
    let (pm, tm) = integPref (prefixMap s1) (prefixMap s2)
    if Map.null tm then return (addSign s1 s2) {prefixMap = pm}
      else fail "Static analysis could not unite signatures"

intersectSign :: Sign -> Sign -> Result Sign
intersectSign s1 s2 = do
   let (pm, tm) = integPref (prefixMap s1) $ prefixMap s2
   if Map.null tm then 
     return emptySign{ 
              concepts = Set.intersection (concepts s1) $ concepts s2 
            , datatypes = Set.intersection (datatypes s1) $ datatypes s2 
            , objectProperties = Set.intersection (objectProperties s1) $ objectProperties s2
            , dataProperties = Set.intersection (dataProperties s1) $ dataProperties s2
            , annotationRoles = Set.intersection (annotationRoles s1) $ annotationRoles s2
            , individuals  = Set.intersection (individuals s1) $ individuals s2
            , labelMap = Map.intersection (labelMap s1) $ labelMap s2
            , prefixMap =  pm
            }
    else fail "Static analysis could not intersect signatures"

integPref :: PrefixMap -> PrefixMap
                    -> (PrefixMap, StringMap)
integPref oldMap testMap =
   foldr testAndInteg (oldMap, Map.empty) (Map.toList testMap)

newOid :: OntologyIRI -> OntologyIRI -> OntologyIRI
newOid id1 id2 =
  let lid1 = iriPath id1
      lid2 = iriPath id2
  in if null $ show lid1 then id2
      else if (null $ show lid2) || id1 == id2 then id1
            else id1 { iriPath = stringToId (uriToName (show lid1) ++ "_" ++ uriToName (show lid2)) }
  -- todo: improve. @Till: Here we probably need to follow the same decision as for alignments.

combineDoc :: OntologyDocument -> OntologyDocument
                      -> OntologyDocument
combineDoc od1@( OntologyDocument ns1
                           ( Ontology oid1 imp1 anno1 frames1))
                      od2@( OntologyDocument ns2
                           ( Ontology oid2 imp2 anno2 frames2)) =
  if od1 == od2 then od1
   else
    let (newPref, tm) = integPref ns1 ns2
    in OntologyDocument newPref
      (Ontology (newOid oid1 oid2) (nub $ imp1 ++ map
            (function Rename $ StringMap tm) imp2)
       (nub $ anno1 ++ map (function Rename $ StringMap tm) anno2)
       (nub $ frames1 ++ map (function Rename $ StringMap tm) frames2))

uriToName :: String -> String
uriToName str = let
  str' = case str of
           '"' : _ -> read str
           _ -> str
  in takeWhile (/= '.') $ reverse $ case takeWhile (/= '/') $ reverse str' of
         '#' : r -> r
         r -> r

unifyWith1 :: OntologyDocument -> [OntologyDocument] -> [OntologyDocument]
unifyWith1 d odl = case odl of
  [] -> []
  [doc] -> [snd $ unifyTwo d doc]
  doc1 : docs ->
    let (merged, newDoc1) = unifyTwo d doc1
    in newDoc1 : unifyWith1 merged docs

{- | takes 2 docs and returns as snd the corrected first one
    and as fst the merge of the two -}
unifyTwo :: OntologyDocument -> OntologyDocument ->
              (OntologyDocument, OntologyDocument)
unifyTwo od1 od2 =
  let (_, tm) = integPref (prefixDeclaration od1) (prefixDeclaration od2)
      newod2 = function Rename (StringMap tm) od2
      alld = combineDoc od1 od2
  in (alld, newod2)

unifyDocs :: [OntologyDocument] -> [OntologyDocument]
unifyDocs = unifyWith1 emptyOntologyDoc
