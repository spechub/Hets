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
import RDF.AS
import RDF.Sign
import RDF.Function

import qualified Data.Map as Map
import qualified Data.Set as Set

import Common.AS_Annotation hiding (Annotation)
import Common.Result
import Common.GlobalAnnotations
import Common.ExtSign
import Common.Lib.State




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
    

resolveBases :: Statement -> Statement -> Statement
resolveBases (Base rel) (Base base) =
    let uri1 = fromJust $ parseURIReference $ expandedIRI rel
        uri2 = fromJust $ parseURIReference $ expandedIRI base
        resolved = (uriToString id $ fromJust $ relativeTo uri1 uri2) ""
        Right newIri = parse uriQ "" resolved
    in Base newIri
    
-}
