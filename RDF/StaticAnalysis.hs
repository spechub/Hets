{- |
Module      :  $Header$
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Static analysis for RDF
-}

module RDF.StaticAnalysis where

import OWL2.AS
import OWL2.Parse
import RDF.AS
--import RDF.Sign
--import RDF.Function
import RDF.Print
import RDF.Parse

import Data.Maybe
import Network.URI
import qualified Data.Map as Map
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec

import Common.AS_Annotation hiding (Annotation)
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State

-- * URI Resolution

resolveFullIRI :: IRI -> IRI -> IRI
resolveFullIRI abs rel = if isAbsoluteIRI rel then rel else
    let r = fromJust $ parseURIReference $ expandedIRI rel
        a = fromJust $ parseURI $ expandedIRI abs
        resolved = (uriToString id $ fromJust $ relativeTo r a) ""
        Right new = parse uriQ "" $ "<" ++ resolved ++ ">"
    in rel {expandedIRI = expandedIRI new}
    
resolveAbbreviatedIRI :: RDFPrefixMap -> IRI -> IRI
resolveAbbreviatedIRI pm new = case Map.lookup (namePrefix new) pm of
    Nothing -> error $ namePrefix new ++ ": prefix not declared"
    Just iri -> let new2 = if null (namePrefix new)
                                        && length (localPart new) > 0
                                        && head (localPart new) == ':'
                            then new {localPart = tail $ localPart new}
                            else new
                in new2 {expandedIRI = expandedIRI iri ++ localPart new2}
                
resolveIRI :: Base -> RDFPrefixMap -> IRI -> IRI
resolveIRI (Base current) pm new = if iriType new == Full
    then resolveFullIRI current new
    else resolveAbbreviatedIRI pm new

resolveBase :: Base -> RDFPrefixMap -> Base -> Base
resolveBase b pm (Base new) = Base $ resolveIRI b pm new
    
resolvePrefix :: Base -> RDFPrefixMap -> Prefix -> (Prefix, RDFPrefixMap)
resolvePrefix b pm (Prefix s new) = let res = resolveIRI b pm new
    in (Prefix s res, Map.insert s res pm) 

resolvePredicate :: Base -> RDFPrefixMap -> Predicate -> Predicate
resolvePredicate b pm (Predicate p) =
    if null (namePrefix p) && localPart p == "a" then Predicate $
        p { expandedIRI = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
          , iriType = Full }
    else Predicate $ resolveIRI b pm p

resolveSubject :: Base -> RDFPrefixMap -> Subject -> Subject
resolveSubject b pm s = case s of
    Subject iri -> Subject $ resolveIRI b pm iri
    SubjectList ls -> SubjectList $ map (resolvePOList b pm) ls
    SubjectCollection ls -> SubjectCollection $ map (resolveObject b pm) ls
    
resolvePOList :: Base -> RDFPrefixMap -> PredicateObjectList
    -> PredicateObjectList
resolvePOList b pm (PredicateObjectList p ol) =
    PredicateObjectList (resolvePredicate b pm p) $ map (resolveObject b pm) ol
    
resolveObject :: Base -> RDFPrefixMap -> Object -> Object
resolveObject b pm o = case o of
    Object s -> Object $ resolveSubject b pm s
    ObjectLiteral lit -> case lit of
        RDFLiteral bool lf (Typed dt) ->
                ObjectLiteral $ RDFLiteral bool lf $ Typed $ resolveIRI b pm dt
        _ -> o 
       
resolveTriples :: Base -> RDFPrefixMap -> Triples -> Triples
resolveTriples b pm (Triples s ls) =
    Triples (resolveSubject b pm s) $ map (resolvePOList b pm) ls

resolveStatements :: Base -> RDFPrefixMap -> [Statement] -> [Statement]
resolveStatements b pm ls = case ls of
    [] -> []
    BaseStatement base : t -> let newBase = resolveBase b pm base
            in BaseStatement newBase : resolveStatements newBase pm t
    PrefixStatement pref : t -> let (newPref, newPrefMap) = resolvePrefix b pm pref
            in PrefixStatement newPref : resolveStatements b newPrefMap t
    Statement triples : t ->
            Statement (resolveTriples b pm triples) : resolveStatements b pm t
    
resolveDocument :: TurtleDocument -> TurtleDocument
resolveDocument doc = let newStatements = resolveStatements
                            (Base $ documentName doc) Map.empty $ statements doc
    in doc { statements = newStatements
           , prefixMap = extractPrefixMap Map.empty newStatements } 

extractPrefixMap :: RDFPrefixMap -> [Statement] -> RDFPrefixMap
extractPrefixMap pm ls = case ls of
    [] -> pm
    h : t -> case h of
        PrefixStatement (Prefix p iri) -> extractPrefixMap (Map.insert p iri pm) t
        _ -> extractPrefixMap pm t
        
-- * Axiom extraction

generateBNode :: Int -> IRI
generateBNode i = setPrefix "_" $ mkQName $ "hets_rdf_bnode_" ++ show i
{-}
decodeSubject :: Int -> Subject -> (Int, Subject, [Triples])
decodeSubject i s = case s of
    Subject _ -> (i, s, [])
    SubjectList ls -> let (j, bnode, tl) = decodePredicateObjectList i ls
                      in (j, Subject bnode, tl)
    SubjectCollection ol -> case ol of
        [] -> (i, Subject rdfNil, [])
        h : t -> let (j, bnode, tl) = decodePredicateObjectList i
            [ PredicateObjectList (Predicate rdfFirst) h
            , PredicateObjectList (Predicate rdfRest) $ SubjectCollection t ]
                 in (j, Subject bnode, tl)
                                                        
expandPOList :: Int -> PredicateObjectList -> [PredicateObjectList]
expandPOList (PredicateObjectList p objs) = if null objs
    then [PredicateObjectList p [Object $ Subject $ generateBNode i]]
    else 
    map (\ obj -> PredicateObjectList p [obj]) objs
    
decodePredicateObjectList :: Int -> Subject -> [PredicateObjectList]
    -> (Int, [Triples])
decodePredicateObjectList i subj ls = case ls of
    [] -> (i, [])
    _ -> let poList = concatMap expandPOList ls
             tripleList = map (\ po -> Triples (Subject iri) [po]) poList
             (j, triples) = decodeTriples i tripleList
         in (j, triples)
         
decodeObject :: Int -> Object -> (Int, Object, [Triples])
decodeObject i o = case o of
    Object s -> let (j, s, tl) = decodeSubject i s in (j, Object s, tl)
    _ -> (i, o, [])
    
decodeSingleTriple :: Int -> Triples -> (Int, [Triples])
decodeSingleTriple i (Triple s ls) =
    let (j, s, tl) = decodeSubject i s
    in case tl of
        Nothing -> 
    
-}

collectionToPOList :: [Object] -> [PredicateObjectList]
collectionToPOList objs = case objs of
    [] -> [PredicateObjectList (Predicate rdfNil) []]
    h : t -> [ PredicateObjectList (Predicate rdfFirst) [h]
             , PredicateObjectList (Predicate rdfRest) [Object $ if null t
                then Subject rdfNil else SubjectList $ collectionToPOList t]]
                
expandPOList1 :: Triples -> [Triples]
expandPOList1 (Triples s pols) = map (\ pol -> Triples s [pol]) pols

-- | this assumes exactly one subject and one predicate
expandPOList2 :: Triples -> [Triples]
expandPOList2 (Triples s pols) = case pols of
    [PredicateObjectList p objs] ->
        map (\ obj -> Triples s [PredicateObjectList p [obj]]) objs
    _ -> error "unexpected ; abbreviated triple"
    
expandPOList :: Triples -> [Triples]
expandPOList = concatMap expandPOList2 . expandPOList1

-- | this assumes exactly one subject, one predicate and one object
expandObject :: Int -> Triples -> [Triples]
expandObject i t@(Triples s ls) = case ls of
    [PredicateObjectList p [obj]] -> case obj of
        ObjectLiteral _ -> [t]
        Object (Subject _) -> [t]
        Object (SubjectList pol) ->
            let bnode = Subject $ generateBNode i
                newTriple = Triples s [PredicateObjectList p [Object bnode]]
                connectedTriples = Triples bnode pol
            in [newTriple, connectedTriples]
    _ -> error "unexpected , or ; abbreviated triple"

{-}
{- | this assumes the subject is only IRI and the PredicateObjectList
has only one element -}
expandForSimpleSubjPOList :: Triples -> [Axiom]
expandForSimpleSubjPOList (Triples s pol) = case (s, pol) of
    (Subject subjIri, [PredicateObjectList predIri obj]) -> case obj of
        ObjectLiteral lit -> [Axiom subjIri predIri $ Right lit]
    _ -> error $ "expanding triple with non-simple IRI subject"
    -}
{-
-- | takes an entity and modifies the sign according to the given function
modEntity :: (IRI -> Set.Set IRI -> Set.Set IRI) -> RDFEntity -> State Sign ()
modEntity f (RDFEntity ty u) = do
  s <- get
  let chg = f u
  put $ case ty of
    Subject -> s { subjects = chg $ subjects s }
    Predicate -> s { predicates = chg $ predicates s }
    Object -> s { objects = chg $ objects s }

-- | adding entities to the signature
addEntity :: RDFEntity -> State Sign ()
addEntity = modEntity Set.insert

collectEntities :: Axiom -> State Sign ()
collectEntities (Axiom sub pre obj) = do
    addEntity (RDFEntity Subject sub)
    addEntity (RDFEntity Predicate pre)
    case obj of
        Left iri -> addEntity (RDFEntity Object iri)
        _ -> return ()

-- | collects all entites from the graph
createSign :: RDFGraph -> State Sign ()
createSign (RDFGraph gr) =
    mapM_ (collectEntities . function Expand (StringMap Map.empty)) gr

-- | corrects the axioms according to the signature
createAxioms :: Sign -> RDFGraph -> Result ([Named Axiom], RDFGraph)
createAxioms _ (RDFGraph gr) = do
    let cf = map (function Expand $ StringMap Map.empty) gr
    return (map anaAxiom cf, RDFGraph cf)

-- | adding annotations for theorems
anaAxiom :: Axiom -> Named Axiom
anaAxiom ax = findImplied ax $ makeNamed "" ax

findImplied :: Axiom -> Named Axiom -> Named Axiom
findImplied ax sent =
  if prove ax then sent
         { isAxiom = False
         , isDef = False
         , wasTheorem = False }
   else sent { isAxiom = True }

prove :: Axiom -> Bool
prove _ = False

-- | static analysis of graph with incoming sign.
basicRDFAnalysis :: (RDFGraph, Sign, GlobalAnnos)
    -> Result (RDFGraph, ExtSign Sign RDFEntity, [Named Axiom])
basicRDFAnalysis (gr, inSign, _) = do
    let syms = Set.difference (symOf accSign) $ symOf inSign
        accSign = execState (createSign gr) inSign
    (axl, newgraph) <- createAxioms accSign gr
    return (newgraph, ExtSign accSign syms, axl)
-}
