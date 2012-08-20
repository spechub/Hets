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
import Common.DocUtils
import Common.Result
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.List
import Common.Id
import qualified Common.Lib.MapSet as MapSet

{-
import Control.Monad
import Data.Char
import qualified Data.Map as Map
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
import OWL2.Sign as OS
-- CASL = domain
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Disambiguate
import CASL.Sign
import qualified CASL.MapSentence as MapSen
import CASL.Morphism
import CASL.SimplifySen
import CASL.Sublogic
import CASL.ToDoc
import CASL.Overload

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
        { sub_features = LocFilSub }
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

mapSymbol :: Symbol -> Set.Set Entity
mapSymbol _ = Set.empty

{- names must be disambiguated as is done in CASL.Qualify or SuleCFOL2SoftFOL.
   Ops or preds in the overload relation denote the same objectProperty!
-}
idToIRI :: Id -> QName
idToIRI i = nullQName
  { localPart = show i, iriPos = rangeOfId i }

mapSign :: CASLSign -> Result (OS.Sign, [Named Axiom])
mapSign csig = let
  om = opMap csig
  keepMaxs = keepMinimals1 False csig id
  mk s i m = makeNamed (s ++ show i ++ m) . PlainAxiom
       (ObjectEntity $ ObjectProp $ idToIRI i)
  toC = Expression . idToIRI
  toEBit i = ExpressionBit [([], toC i)]
  mkDR dr = ListFrameBit (Just $ DRRelation dr) . toEBit
  toIris = Set.map idToIRI
  (cs, ncs) = MapSet.partition (null . opArgs) om
  (sos, os) = MapSet.partition isSingleArgOp ncs
  (sps, rps) = MapSet.partition (isSingle . predArgs) pm
  (bps, ps) = MapSet.partition isBinPredType rps
  pm = predMap csig
  osig = OS.emptySign
    { concepts = toIris $ Set.unions
      [ sortSet csig, MapSet.keysSet sps ]
    , objectProperties = toIris $ Set.union (MapSet.keysSet sos)
      $ MapSet.keysSet bps
    , individuals = toIris $ MapSet.keysSet cs
    }
  in do
  s1 <- Map.foldWithKey (\ i s ml ->
    case keepMinimals csig id . map opRes $ Set.toList s of
    [t] -> do
      l <- ml
      return $ makeNamed ("individual " ++ show i ++ " of class " ++ show t)
                 (PlainAxiom (SimpleEntity $ Entity NamedIndividual $ idToIRI i)
                 $ ListFrameBit (Just Types) $ toEBit t) : l
    ts -> fail $ "CASL2OWL.mapSign1: " ++ show i ++ " types: " ++ show ts)
    (return []) (MapSet.toMap cs)
  s2 <- Map.foldWithKey (\ i s ml -> do
    l <- ml
    let sl = Set.toList s
        mki = mk "plain function " i
    case (keepMaxs $ concatMap opArgs sl, keepMaxs $ map opRes sl) of
      ([a], [r]) -> return
         $ [ mki " character" $ ListFrameBit Nothing
             $ ObjectCharacteristics [([], Functional)]
           , mki " domain" $ mkDR ADomain a, mki " range" $ mkDR ARange r]
         ++ l
      (as, rs) -> fail $ "CASL2OWL.mapSignw: " ++ show i ++ " args: "
                   ++ show as ++ " resulttypes: " ++ show rs)
    (return s1) (MapSet.toMap sos)
  s3 <- Map.foldWithKey (\ i s ml -> do
    l <- ml
    let mkp = mk "binary predicate " i
    case map keepMaxs . transpose . map predArgs $ Set.toList s of
      [[a], [r]] -> return
         $ [mkp " domain" $ mkDR ADomain a, mkp " range" $ mkDR ARange r]
         ++ l
      ts -> fail $ "CASL2OWL.mapSign3: " ++ show i ++ " types: " ++ show ts)
    (return s2) (MapSet.toMap bps)
  s4 <- Map.foldWithKey (\ i s ml ->
     case keepMaxs $ concatMap predArgs $ Set.toList s of
       [r] -> do
         l <- ml
         return $ makeNamed ("plain predicate " ++ show i)
              (PlainAxiom (ClassEntity $ toC r)
              $ ListFrameBit (Just SubClass) $ toEBit i) : l
       ts -> fail $ "CASL2OWL.mapSign4: " ++ show i ++ " types: " ++ show ts)
     (return s3) (MapSet.toMap sps)
  MapSet.foldWithKey (\ i s m -> do
    m
    justWarn () $ "not translated op " ++ shows i " :" ++ showDoc s "")
    (return ()) os
  MapSet.foldWithKey (\ i s m -> do
    m
    justWarn () $ "not translated pred " ++ shows i " : " ++ showDoc s "")
    (return ()) ps
  return (osig, s4)

{- binary predicates and single argument functions should become
   objectProperties.
   Serge also turned constructors into concepts.
   How to treat multi-argument predicates and functions?
   Maybe create tuple concepts?
-}

mapTheory :: (CASLSign, [Named CASLFORMULA]) -> Result (OS.Sign, [Named Axiom])
mapTheory (sig, sens) = do
  let mor = disambigSig sig
      tar = mtarget mor
      ns = map (mapNamed $ MapSen.mapSen (const id) mor) sens
  mapM_ (justWarn () . ("not translated\n" ++) . show . printTheoryFormula
         . mapNamed (simplifyCASLSen tar)) ns
  mapSign tar
