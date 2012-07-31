{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CASL to OWL2
Copyright   :  (c) C. Maeder, DFKI GmbH 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)
-}

module OWL2.CASL2OWL where

import Logic.Logic as Logic
import Logic.Comorphism
import Common.AS_Annotation
import Common.Result
import qualified Data.Set as Set
{-
import Common.Id
import Control.Monad
import Data.Char
import qualified Data.Map as Map
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

-- the DL with the initial signature for OWL
import CASL_DL.PredefinedCASLAxioms
-}

-- OWL = codomain
import OWL2.Logic_OWL2
{-
import OWL2.Keywords
import OWL2.Parse
import OWL2.Print
-}
import OWL2.MS
import OWL2.AS
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterPrint ()
import OWL2.Morphism
import OWL2.Symbols
import qualified OWL2.Sign as OS
-- CASL = domain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.Sublogic

import Common.ProofTree
{-
import Common.DocUtils

import Data.Maybe
import Text.ParserCombinators.Parsec
-}

data CASL2OWL = CASL2OWL deriving Show

instance Language CASL2OWL

instance Comorphism
    CASL2OWL        -- comorphism
    CASL            -- lid domain
    CASL_Sublogics  -- sublogics domain
    CASLBasicSpec   -- Basic spec domain
    CASLFORMULA     -- sentence domain
    SYMB_ITEMS      -- symbol items domain
    SYMB_MAP_ITEMS  -- symbol map items domain
    CASLSign        -- signature domain
    CASLMor         -- morphism domain
    Symbol          -- symbol domain
    RawSymbol       -- rawsymbol domain
    ProofTree       -- proof tree domain
    OWL2            -- lid codomain
    ProfSub         -- sublogics codomain
    OntologyDocument -- Basic spec codomain
    Axiom           -- sentence codomain
    SymbItems       -- symbol items codomain
    SymbMapItems    -- symbol map items codomain
    OS.Sign         -- signature codomain
    OWLMorphism     -- morphism codomain
    Entity          -- symbol codomain
    RawSymb         -- rawsymbol codomain
    ProofTree       -- proof tree codomain
    where
      sourceLogic CASL2OWL = CASL
      sourceSublogic CASL2OWL = caslTop
      targetLogic CASL2OWL = OWL2
      mapSublogic CASL2OWL _ = Just topS
      map_theory CASL2OWL = mapTheory
      map_morphism CASL2OWL = mapMorphism
      map_symbol CASL2OWL _ = mapSymbol
      isInclusionComorphism CASL2OWL = True
      has_model_expansion CASL2OWL = True

-- | Mapping of CASL morphisms
mapMorphism :: CASLMor -> Result OWLMorphism
mapMorphism _ = fail "CASL2OWL.mapMorphism"
{-
      cdm <- mapSign $ osource oMor
      ccd <- mapSign $ otarget oMor
      let emap = mmaps oMor
          preds = Map.foldWithKey (\ (Entity ty u1) u2 -> let
              i1 = uriToCaslId u1
              i2 = uriToCaslId u2
              in case ty of
                Class -> Map.insert (i1, conceptPred) i2
                ObjectProperty -> Map.insert (i1, objectPropPred) i2
                DataProperty -> Map.insert (i1, dataPropPred) i2
                _ -> id) Map.empty emap
          ops = Map.foldWithKey (\ (Entity ty u1) u2 -> case ty of
                NamedIndividual -> Map.insert (uriToCaslId u1, indiConst)
                  (uriToCaslId u2, Total)
                _ -> id) Map.empty emap
      return (embedMorphism () cdm ccd)
                 { op_map = ops
                 , pred_map = preds }
-}

mapSymbol :: Symbol -> Set.Set Entity
mapSymbol _ = Set.empty
{-
(Entity ty iri) = let
  syN = Set.singleton . Symbol (uriToCaslId iri)
  in case ty of
    Class -> syN $ PredAsItemType conceptPred
    ObjectProperty -> syN $ PredAsItemType objectPropPred
    DataProperty -> syN $ PredAsItemType dataPropPred
    NamedIndividual -> syN $ OpAsItemType indiConst
    AnnotationProperty -> Set.empty
    Datatype -> Set.empty
-}

mapSign :: CASLSign -> Result OS.Sign
mapSign _ = fail "CASL2OWL.mapSign"
{-
      let conc = OS.concepts sig
          cvrt = map uriToCaslId . Set.toList
          tMp k = MapSet.fromList . map (\ u -> (u, [k]))
          cPreds = thing : nothing : cvrt conc
          oPreds = cvrt $ OS.objectProperties sig
          dPreds = cvrt $ OS.dataProperties sig
          aPreds = foldr MapSet.union MapSet.empty
            [ tMp conceptPred cPreds
            , tMp objectPropPred oPreds
            , tMp dataPropPred dPreds ]
     in return $ uniteCASLSign predefSign (emptySign ())
             { predMap = aPreds
             , opMap = tMp indiConst . cvrt $ OS.individuals sig
             }
-}

mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (OS.Sign, [Named Axiom])
mapTheory _ = fail "CASL2OWL.mapSign"
{-
    cSig <- mapSign owlSig
    let pSig = loadDataInformation sl
        dTypes = (emptySign ()) {sortRel = Rel.transClosure $ Rel.fromList
                    $ map (\ d -> (uriToCaslId d, dataS))
                    $ predefIRIs ++ Set.toList (OS.datatypes owlSig)}
    (cSens, nSig) <- foldM (\ (x, y) z -> do
            (sen, sig) <- mapSentence y z
            return (sen ++ x, uniteCASLSign sig y)) ([], cSig) owlSens
    return (foldl1 uniteCASLSign [nSig, pSig, dTypes],
                predefinedAxioms ++ cSens)
-}

{-
-- | mapping of OWL to CASL_DL formulae
mapSentence :: CASLSign -> Named Axiom -> Result ([Named CASLFORMULA], CASLSign)
mapSentence cSig inSen = do
    (outAx, outSig) <- mapAxioms cSig $ sentence inSen
    return (map (flip mapNamed inSen . const) outAx, outSig)
-}
