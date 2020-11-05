{- |
Module      :  ./RDF/StaticAnalysis.hs
Copyright   :  Felix Gabriel Mance
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  f.mance@jacobs-university.de
Stability   :  provisional
Portability :  portable

Static analysis for RDF
-}

module RDF.StaticAnalysis where

import OWL2.AS
import Common.IRI
import OWL2.Parse
import RDF.AS
import RDF.Sign
import RDF.Parse (predefinedPrefixes)

import Data.Maybe
import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

import Text.ParserCombinators.Parsec hiding (State)

import Common.AS_Annotation hiding (Annotation)
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State

-- * URI Resolution

resolveFullIRI :: IRI -> IRI -> IRI
resolveFullIRI _absol rel = rel
 {-if isAbsoluteIRI rel then rel else
    let r = fromJust $ parseIRIReference $ fromJust $ expandCurie Map.empty rel
        a = fromJust $ parseIRI $ fromJust $ expandCurie Map.empty absol
        Just ra = IRI.relativeTo r a
        resolved = IRI.iriToStringUnsecure ra
        Right new = parse uriQ "" $ "<" ++ resolved ++ ">"
    in rel {expandedIRI = expandedIRI new}
 -}

resolveAbbreviatedIRI :: RDFPrefixMap -> IRI -> IRI
resolveAbbreviatedIRI pm new = fromJust $ expandCurie pm new
  {-case Map.lookup (namePrefix new) pm of
    Nothing -> error $ namePrefix new ++ ": prefix not declared"
    Just iri -> let new2 = if null (namePrefix new)
                                        {- FIXME: If null (localPart new)
                                                  then head will fail! -}
                                        && null (localPart new)
                                        && head (localPart new) == ':'
                            then new {localPart = tail $ localPart new}
                            else new
                in new2 {expandedIRI = expandedIRI iri ++ localPart new2}
 -}

resolveIRI :: Base -> RDFPrefixMap -> IRI -> IRI
resolveIRI (Base current) pm new 
    | hasFullIRI new = resolveFullIRI current new
    | isBlankNode new = new
    | otherwise = resolveAbbreviatedIRI pm new

resolveBase :: Base -> RDFPrefixMap -> Base -> Base
resolveBase b pm (Base new) = Base $ resolveIRI b pm new

resolvePrefix :: Base -> RDFPrefixMap -> Prefix -> (Prefix, RDFPrefixMap)
resolvePrefix b pm (PrefixR s new) = let res = resolveIRI b pm new
    in (PrefixR s res, Map.insert s res pm)

resolvePredicate :: Base -> RDFPrefixMap -> Predicate -> Predicate
resolvePredicate b pm (Predicate p) = Predicate $
    if null (prefixName p) && show (iriPath p) == "a" then
        p { iriScheme = "http:",
            iriPath = stringToId "//www.w3.org/1999/02/22-rdf-syntax-ns#type"
          }
    else resolveIRI b pm p

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

extractPrefixMap :: RDFPrefixMap -> [Statement] -> RDFPrefixMap
extractPrefixMap pm ls = case ls of
    [] -> pm
    h : t -> case h of
        PrefixStatement (PrefixR p iri) -> extractPrefixMap (Map.insert p iri pm) t
        _ -> extractPrefixMap pm t

resolveDocument :: TurtleDocument -> TurtleDocument
resolveDocument doc = let newStatements = resolveStatements
                            (Base $ documentName doc) predefinedPrefixes $ statements doc
    in doc { statements = newStatements
           , prefixMap = Map.union predefinedPrefixes $
                                extractPrefixMap Map.empty newStatements }

-- * Axiom extraction

generateBNode :: Int -> IRI
generateBNode i = nullIRI { iriPath = stringToId ("bnode" ++ show i)
                          , isAbbrev = True 
                          , isBlankNode = True}

collectionToPOList :: [Object] -> [PredicateObjectList]
collectionToPOList objs = case objs of
    [] -> []
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

-- | converts a triple to a list of triples with one predicate and one object
expandPOList :: Triples -> [Triples]
expandPOList = concatMap expandPOList2 . expandPOList1

-- | this assumes exactly one subject, one predicate and one object
expandObject1 :: Int -> Triples -> (Int, [Triples])
expandObject1 i t@(Triples s ls) = case ls of
    [PredicateObjectList p [obj]] -> case obj of
        ObjectLiteral _ -> (i, [t])
        Object (Subject _) -> (i, [t])
        Object (SubjectList pol) ->
            let bnode = Subject $ generateBNode i
                newTriple = Triples s [PredicateObjectList p [Object bnode]]
                connectedTriples = expandPOList $ Triples bnode pol
                (j, expandedTriples) = expandObject2 (i + 1) connectedTriples
            in (j, newTriple : expandedTriples)
        Object (SubjectCollection col) -> let pol = collectionToPOList col
            in if null pol then
                (i, [Triples s [PredicateObjectList p [Object $ Subject rdfNil]]])
               else expandObject1 i $ Triples s [PredicateObjectList p [Object $ SubjectList pol]]
    _ -> error "unexpected , or ; abbreviated triple"

-- | this assumes each triple has one subject, one predicate and one object
expandObject2 :: Int -> [Triples] -> (Int, [Triples])
expandObject2 i tl = case tl of
    [] -> (i, [])
    h : t -> let (j, triples1) = expandObject1 i h
                 (k, triples2) = expandObject2 j t
             in (k, triples1 ++ triples2)

expandObject :: Int -> Triples -> (Int, [Triples])
expandObject i t = expandObject2 i $ expandPOList t

expandSubject :: Int -> Triples -> (Int, [Triples])
expandSubject i t@(Triples s ls) = case s of
    Subject _ -> (i, [t])
    SubjectList pol -> let bnode = Subject $ generateBNode i
        in (i + 1, map (Triples bnode) [ls, pol])
    SubjectCollection col -> let pol = collectionToPOList col
        in if null col then (i, [Triples (Subject rdfNil) ls])
           else expandSubject i $ Triples (SubjectList pol) ls

expandTriple :: Int -> Triples -> (Int, [Triples])
expandTriple i t = let (j, sst) = expandSubject i t in case sst of
    [triple] -> expandObject j triple
    [triple, connectedTriple] ->
        let (k, tl1) = expandObject j triple
            (l, tl2) = expandObject k connectedTriple
        in (l, tl1 ++ tl2)
    _ -> error "expanding triple before expanding subject"

expandTripleList :: Int -> [Triples] -> (Int, [Triples])
expandTripleList i tl = case tl of
    [] -> (i, [])
    h : t -> let (j, tl1) = expandTriple i h
                 (k, tl2) = expandTripleList j t
             in (k, tl1 ++ tl2)

simpleTripleToAxiom :: Triples -> Axiom
simpleTripleToAxiom (Triples s pol) = case (s, pol) of
    (Subject sub, [PredicateObjectList (Predicate pr) [o]]) ->
        Axiom (SubjectTerm sub) (PredicateTerm pr) $ ObjectTerm $ case o of
            ObjectLiteral lit -> Right lit
            Object (Subject obj) -> Left obj
            _ -> error "object should be an URI"
    _ -> error "subject should be an URI or triple should not be abbreviated"

createAxioms :: TurtleDocument -> [Axiom]
createAxioms doc = map simpleTripleToAxiom $ snd $ expandTripleList 1
                                    $ triplesOfDocument $ resolveDocument doc

-- | takes an entity and modifies the sign according to the given function
modEntity :: (Term -> Set.Set Term -> Set.Set Term) -> RDFEntity -> State Sign ()
modEntity f (RDFEntity ty u) = do
  s <- get
  let chg = f u
  put $ case ty of
    SubjectEntity -> s { subjects = chg $ subjects s }
    PredicateEntity -> s { predicates = chg $ predicates s }
    ObjectEntity -> s { objects = chg $ objects s }

-- | adding entities to the signature
addEntity :: RDFEntity -> State Sign ()
addEntity = modEntity Set.insert

collectEntities :: Axiom -> State Sign ()
collectEntities (Axiom sub pre obj) = do
    addEntity (RDFEntity SubjectEntity sub)
    addEntity (RDFEntity PredicateEntity pre)
    addEntity (RDFEntity ObjectEntity obj)

-- | collects all entites from the axioms
createSign :: TurtleDocument -> State Sign ()
createSign = mapM_ collectEntities . createAxioms

anaAxiom :: Axiom -> Named Axiom
anaAxiom = makeNamed ""

-- | static analysis of document with incoming sign.
basicRDFAnalysis :: (TurtleDocument, Sign, GlobalAnnos)
    -> Result (TurtleDocument, ExtSign Sign RDFEntity, [Named Axiom])
basicRDFAnalysis (doc, inSign, _) = do
    let syms = Set.difference (symOf accSign) $ symOf inSign
        accSign = execState (createSign doc) inSign
        axioms = map anaAxiom $ createAxioms doc
    return (doc, ExtSign accSign syms, axioms)
