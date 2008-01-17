{- |
Module      :  Comorphisms/OWL2CASL_DL.hs
Description :  Comorphism from OWL 1.1 to CASL_Dl
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

-}

module Comorphisms.OWL2CASL_DL where

import Text.XML.HXT.DOM.XmlTreeTypes

import Logic.Logic
import Logic.Comorphism
import Common.Id
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import Common.AS_Annotation
import Data.List()
import Common.Result
import CASL_DL.PredefinedCASLAxioms()
import Common.GlobalAnnotations()

--OWL = domain
import OWL.Logic_OWL11
import OWL.AS
import qualified OWL.Sign as OS
import OWL.Sign

--CASL_DL = codomain
import CASL_DL.Logic_CASL_DL
import CASL_DL.AS_CASL_DL
import CASL_DL.Sign
import CASL_DL.StatAna -- DLSign
import CASL_DL.PredefinedSign
import CASL.AS_Basic_CASL
import CASL.Sign as CS
import CASL.Morphism

data OWL2CASL_DL = OWL2CASL_DL deriving Show

instance Language OWL2CASL_DL

instance Comorphism
    OWL2CASL_DL     -- comorphism
    OWL11           -- lid domain
    ()              -- sublogics domain
    OntologyFile    -- Basic spec domain
    Sentence        -- sentence domain
    ()              -- symbol items domain
    ()              -- symbol map items domain
    OS.Sign         -- signature domain
    OWL11_Morphism  -- morphism domain
    ()              -- symbol domain
    ()              -- rawsymbol domain
    ()              -- proof tree codomain
    CASL_DL         -- lid codomain
    ()              -- sublogics codomain
    DL_BASIC_SPEC   -- Basic spec codomain
    DLFORMULA       -- sentence codomain
    SYMB_ITEMS      -- symbol items codomain
    SYMB_MAP_ITEMS  -- symbol map items codomain
    DLSign          -- signature codomain
    DLMor           -- morphism codomain
    Symbol          -- symbol codomain
    RawSymbol       -- rawsymbol codomain
    ()              -- proof tree domain
    where 
      sourceLogic OWL2CASL_DL    = OWL11
      sourceSublogic OWL2CASL_DL = ()
      targetLogic OWL2CASL_DL    = CASL_DL
      mapSublogic OWL2CASL_DL _  = Just ()
      map_theory  OWL2CASL_DL    = trTheory
      map_morphism OWL2CASL_DL   = trMor
      map_sentence OWL2CASL_DL   = trSen

trSign :: OS.Sign -> DLSign
trSign inSig =
    (CS.emptySign emptyCASL_DLSign)
    { sortSet = trPrimCons $ primaryConcepts inSig
    , sortRel = makePrimSubs  (primaryConcepts inSig) (axioms inSig)
    , predMap = trNonPrimCons (concepts inSig) (primaryConcepts inSig) (axioms inSig)
    }


-- Translation of concepts
makePrimSubs :: Set.Set URIreference -> 
                Set.Set SignAxiom    ->
                Rel.Rel SORT
makePrimSubs inPrims inAxs = 
    let
        inAxRel = filter (\(x,y) -> Set.member x inPrims && Set.member y inPrims) $
                  Rel.toList $ makeSubconceptRel inAxs
    in
      foldl (\z (x,y)-> Rel.insert (mkId $ showURIreference x) (mkId $ showURIreference y) z)
                      Rel.empty inAxRel

trPrimCons :: Set.Set URIreference -> Set.Set SORT
trPrimCons inSet = Set.map (\x -> mkId $ showURIreference x) inSet

trNonPrimCons :: Set.Set URIreference ->               -- concepts
                 Set.Set URIreference ->               -- primary concepts
                 Set.Set SignAxiom ->                  -- axioms to generate Subconcept relation
                 Map.Map Id (Set.Set PredType)
trNonPrimCons inCons inPrims inAxs = 
    let 
        inAxRel = filter (\(x,y) -> Set.member x inCons && Set.member y inPrims) $
                  Rel.toList $ makeSubconceptRel inAxs
    in
      Set.fold (\x y -> 
                    let
                        goodRels = filter (\(z,_) -> (z == x)) inAxRel
                        outSet   = map (\(_,z) -> PredType {predArgs = [mkId $ showURIreference z]}) goodRels
                        outSetR  = case outSet of
                                     [] -> Set.fromList [PredType {predArgs = [topSort]}]
                                     _  -> Set.fromList outSet
                    in
                      Map.insert (mkId $ showURIreference x) outSetR y
                      ) Map.empty inCons
                      
showURIreference :: URIreference -> [Token]
showURIreference (QN prefix localpart u)
    | localpart == "_" = [mkSimpleId "_"]
    | null prefix = if null u then
                        [mkSimpleId localpart]
                      else [mkSimpleId u, mkSimpleId localpart]
    | otherwise = [mkSimpleId prefix, mkSimpleId localpart]

-- end translation of concepts

trTheory :: (OS.Sign, [Named Sentence]) -> Result (DLSign, [Named DLFORMULA])
trTheory (inSig, inSens) = 
    do
      return (trSign inSig, [])

trMor :: OWL11_Morphism -> Result DLMor
trMor _ = Result {
               diags = []
             ,  maybeResult = (Nothing) 
             }

trSen :: OS.Sign -> Sentence -> Result DLFORMULA
trSen _ = error "NYI"

makeSubconceptRel :: Set.Set SignAxiom -> Rel.Rel URIreference
makeSubconceptRel sigAx = 
    Rel.irreflex $ Rel.transClosure $ 
    Set.fold
           (\x y -> Rel.union
            (case x of 
               Subconcept (OWLClass d1) (OWLClass d2) -> Rel.insert d1 d2 Rel.empty
               _                                      -> Rel.empty
            ) y
           ) Rel.empty sigAx