{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./OWL2/OWLRelativisation.hs
Description :  Relativisation comorphism for OWL
Copyright   :  (c) Mihai Codescu and University of Magdeburg, 2016
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  codescu@iws.cs.ovgu.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.OWLRelativisation where

import Logic.Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import Common.Id
import qualified Data.Set as Set

-- OWL = domain
import OWL2.Logic_OWL2
import OWL2.MS
import OWL2.AS 
import OWL2.ProfilesAndSublogics
import OWL2.Morphism
import OWL2.Symbols
import qualified OWL2.Sign as OS
import Common.ProofTree

import Debug.Trace

data OWLRelativisation = OWLRelativisation deriving Show

instance Language OWLRelativisation

instance Comorphism
    OWLRelativisation        -- comorphism
    OWL2             -- lid domain
    ProfSub          -- sublogics domain
    OntologyDocument    -- Basic spec domain
    Axiom           -- sentence domain
    SymbItems       -- symbol items domain
    SymbMapItems    -- symbol map items domain
    OS.Sign         -- signature domain
    OWLMorphism     -- morphism domain
    Entity          -- symbol domain
    RawSymb         -- rawsymbol domain
    ProofTree       -- proof tree codomain
    OWL2            -- lid codomain
    ProfSub         -- sublogics codomain
    OntologyDocument   -- Basic spec codomain
    Axiom     -- sentence codomain
    SymbItems      -- symbol items codomain
    SymbMapItems  -- symbol map items codomain
    OS.Sign        -- signature codomain
    OWLMorphism         -- morphism codomain
    Entity          -- symbol codomain
    RawSymb       -- rawsymbol codomain
    ProofTree       -- proof tree domain
    where
      sourceLogic OWLRelativisation = OWL2
      sourceSublogic OWLRelativisation = topS
      targetLogic OWLRelativisation = OWL2
      mapSublogic OWLRelativisation =  Just
      map_theory OWLRelativisation = mapTheory
      map_morphism OWLRelativisation = mapMorphism
      map_symbol OWLRelativisation = mapSymbol
      isInclusionComorphism OWLRelativisation = True 
      has_model_expansion OWLRelativisation = False -- TODO: check

topC :: String -> IRI
topC s = QN "" ("top_" ++ s) Abbreviated ("top_" ++ s) nullRange

mapTheory :: Maybe String -> (OS.Sign, [Named Axiom]) -> Result (OS.Sign, [Named Axiom])
mapTheory mString (sig, nsens) = do
 let s = maybe "" id mString
     sig' = sig{OS.concepts = Set.insert (topC s) $ OS.concepts sig}
     (dds, dops, rops, nsens') = foldl (\(dps, opd, opr, sens) se -> let 
                                  (dps', opd', opr', s') = mapSentence s (dps, opd, opr) se 
                                 in (dps', opd', opr', s':sens))
                            (Set.empty, Set.empty, Set.empty, []) nsens
     csens = map (cSubTop s)  $ Set.toList $ OS.concepts sig
     isens = map (iIsTop s) $ Set.toList $ OS.individuals sig
     dsens = map (dTop s) $ Set.toList $ Set.difference (OS.objectProperties sig) dops
     rsens = map (rTop s) $ Set.toList $ Set.difference (OS.objectProperties sig) rops
     dsens' = map (dDataTop s) $ Set.toList $ Set.difference (OS.dataProperties sig) dds 
 return (sig', (reverse nsens') ++ csens ++ isens ++ dsens ++ rsens ++ dsens')

cSubTop :: String -> IRI -> Named Axiom
cSubTop s c = let 
   sen = PlainAxiom (mkExtendedEntity $ mkEntity Class c)
                   (ListFrameBit (Just SubClass) $
                           ExpressionBit [([], Expression (topC s))])
 in makeNamed "" sen

iIsTop :: String -> IRI -> Named Axiom 
iIsTop s i = let 
   sen = PlainAxiom (mkExtendedEntity $ mkEntity NamedIndividual i)
                   (ListFrameBit (Just Types) $
                           ExpressionBit [([], Expression (topC s))])
 in makeNamed "" sen

dDataTop :: String -> IRI -> Named Axiom
dDataTop s d = let
  sen = PlainAxiom (mkExtendedEntity $ mkEntity DataProperty d) 
                   (ListFrameBit (Just (DRRelation ADomain)) $ 
                       ExpressionBit [([], Expression (topC s))])
 in makeNamed "" sen

dTop :: String -> IRI -> Named Axiom
dTop s r = let
  sen = PlainAxiom (mkExtendedEntity $ mkEntity ObjectProperty r) 
                   (ListFrameBit (Just (DRRelation ADomain)) $ 
                       ExpressionBit [([], Expression (topC s))])
 in makeNamed "" sen


rTop :: String -> IRI -> Named Axiom
rTop s r = let 
  sen = PlainAxiom (mkExtendedEntity $ mkEntity ObjectProperty r) 
                   (ListFrameBit (Just (DRRelation ARange)) $ 
                       ExpressionBit [([], Expression (topC s))])
 in makeNamed "" sen

relClassExp :: String -> ClassExpression -> ClassExpression
relClassExp s ce = case ce of 
 Expression aClass -> if isThing aClass then Expression (topC s) else ce
 ObjectJunction j ces -> ObjectJunction j $ map (relClassExp s) ces
 ObjectComplementOf ce' -> ObjectJunction IntersectionOf 
       [Expression (topC s), ObjectComplementOf $ relClassExp s ce']
 ObjectValuesFrom AllValuesFrom ope ce' -> 
    ObjectJunction IntersectionOf [Expression (topC s),  
                   ObjectValuesFrom AllValuesFrom ope $ relClassExp s ce']
 _ -> ce 

relListFrameBit :: String -> ListFrameBit -> ListFrameBit
relListFrameBit s lfb = case lfb of
 ExpressionBit acel -> ExpressionBit $ map (\(x,ce) -> (x, relClassExp s ce)) acel
 -- the replacement already ensures that the domain is a subclass of top
 -- together with Class: C SubClassOf: top for every C
 _ -> lfb 

relAnnFrameBit :: String -> AnnFrameBit -> AnnFrameBit
relAnnFrameBit s afb = case afb of
  ClassDisjointUnion ces -> ClassDisjointUnion $ map (relClassExp s) ces 
  _ -> afb

mapSentence :: String -> (Set.Set IRI, Set.Set IRI, Set.Set IRI) -> Named Axiom -> 
               (Set.Set IRI, Set.Set IRI, Set.Set IRI, Named Axiom)
mapSentence s (dpd, opd, opr) ax = let
   relAxiom sen = case axiomTopic sen of 
      ClassEntity _ce -> case axiomBit sen of
        ListFrameBit mrel lfb -> 
             (dpd, opd, opr, 
              PlainAxiom (axiomTopic sen) $ 
               ListFrameBit mrel $  
                 relListFrameBit s lfb) 
        AnnFrameBit annos afb -> (dpd, opd, opr, PlainAxiom (axiomTopic sen) $ 
               AnnFrameBit annos $ relAnnFrameBit s afb) -- for disjoint unions?
      ObjectEntity (ObjectProp anIri) -> case axiomBit sen of  -- when do I have here an inverse?
         ListFrameBit (Just (DRRelation ADomain)) lfb -> 
          (dpd, Set.insert anIri opd, opr, 
                 PlainAxiom (axiomTopic sen)
                    (ListFrameBit (Just (DRRelation ADomain)) $ 
                      relListFrameBit s lfb)
                    )
         ListFrameBit (Just (DRRelation ARange)) lfb -> 
          (dpd, opd, Set.insert anIri opr, 
                 PlainAxiom (axiomTopic sen)
                    (ListFrameBit (Just (DRRelation ARange)) $ 
                      relListFrameBit s lfb)
                    )
         ListFrameBit mrel lfb -> (dpd, opd, opr, 
                 PlainAxiom (axiomTopic sen)
                    (ListFrameBit mrel $ 
                      relListFrameBit s lfb))
         AnnFrameBit annos afb -> (dpd, opd, opr, PlainAxiom (axiomTopic sen) $ 
                         AnnFrameBit annos $ relAnnFrameBit s afb)
      SimpleEntity ent -> case entityKind ent of 
         DataProperty -> case axiomBit sen of
             ListFrameBit (Just (DRRelation ADomain)) lfb -> 
               (Set.insert (cutIRI ent) dpd, opd, opr, 
                 PlainAxiom (axiomTopic sen)
                    (ListFrameBit (Just (DRRelation ADomain)) $ 
                      relListFrameBit s lfb)
                    )
             _ -> (dpd, opd, opr, sen) 
         NamedIndividual -> case axiomBit sen of
            ListFrameBit (Just Types) lfb ->
                  (dpd, opd, opr,
                   PlainAxiom (axiomTopic sen) $
                    ListFrameBit (Just Types) $ 
                     relListFrameBit s lfb) 
            _ -> (dpd, opd, opr, sen) 
         _ -> (dpd, opd, opr, sen)
      _ -> (dpd, opd, opr, sen)
   (dpd', opd', opr', axRel) = relAxiom $ sentence ax
 in (dpd', opd', opr', (flip mapNamed ax . const) axRel)

mapMorphism :: OWLMorphism -> Result OWLMorphism
mapMorphism _mor = error "nyi"

mapSymbol :: OS.Sign -> Entity -> Set.Set Entity
mapSymbol _sig sym = Set.singleton sym
