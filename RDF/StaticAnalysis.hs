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
import RDF.Function
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

resolveIRI :: IRI -> IRI -> IRI
resolveIRI abs rel = if isAbsoluteIRI rel || iriType rel /= Full then rel else
    let r = fromJust $ parseURIReference $ expandedIRI rel
        a = fromJust $ parseURI $ expandedIRI abs
        resolved = (uriToString id $ fromJust $ relativeTo r a) ""
        Right new = parse uriQ "" $ "<" ++ resolved ++ ">"
    in new
    
resolvePrefix :: Statement -> Statement -> Statement
resolvePrefix (Base base) (Prefix s iri) = Prefix s $ resolveIRI base iri

resolveBase :: Statement -> Statement -> Statement
resolveBase (Base base) (Base new) = if iriType new == Full
    then Base $ resolveIRI base new
    else 

resolvePredicate :: Statement -> Predicate -> Predicate
resolvePredicate (Base base) (Predicate p) = Predicate $ resolveIRI base p

resolveSubject :: Statement -> Subject -> Subject
resolveSubject b@(Base base) s = case s of
    Subject iri -> Subject $ resolveIRI base iri
    SubjectList ls -> SubjectList $ map (resolvePOList b) ls
    SubjectCollection ls -> SubjectCollection $ map (resolveObject b) ls
    
resolvePOList :: Statement -> PredicateObjectList -> PredicateObjectList
resolvePOList b (PredicateObjectList p ol) =
    PredicateObjectList (resolvePredicate b p) $ map (resolveObject b) ol
    
resolveObject :: Statement -> Object -> Object
resolveObject b@(Base base) o = case o of
    Object s -> Object $ resolveSubject b s
    ObjectLiteral lit -> case lit of
        RDFLiteral bool lf (Typed dt) ->
                ObjectLiteral $ RDFLiteral bool lf $ Typed $ resolveIRI base dt
        _ -> o 
       
resolveTriples :: Statement -> Triples -> Triples
resolveTriples b (Triples s ls) = Triples (resolveSubject b s) $ map (resolvePOList b) ls

resolveStatements :: Statement -> [Statement] -> [Statement]
resolveStatements b ls = case ls of
    [] -> []
    h@(Base _) : t -> let new = resolveBase b h in new : resolveStatements new t
    h@(Prefix _ _) : t -> resolvePrefix b h : resolveStatements b t
    h@(Statement triples) : t -> Statement (resolveTriples b triples) : resolveStatements b t
    
resolveDocument :: Statement -> TurtleDocument -> TurtleDocument
resolveDocument b doc = let newStatements = resolveStatements b $ statements doc
    in doc {statements = newStatements, prefixMap = extractPrefixMap newStatements} 
    

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
