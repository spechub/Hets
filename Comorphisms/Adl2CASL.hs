{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Coding a description language into CASL
Copyright   :  (c)  Stef Joosten, Christian Maeder DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Adl to CASL.
-}

module Comorphisms.Adl2CASL
    ( Adl2CASL (..)
    ) where

import Logic.Logic
import Logic.Comorphism

-- Adl
import Adl.Logic_Adl as A
import Adl.As
import Adl.Sign as A

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL
import CASL.Sublogic
import CASL.Sign as C
import CASL.Morphism as C

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.Id
import Common.ProofTree
import Common.Result
import qualified Common.Lib.Rel as Rel

import qualified Data.Set as Set
import qualified Data.Map as Map

-- | lid of the morphism
data Adl2CASL = Adl2CASL deriving Show

instance Language Adl2CASL -- default is ok

instance Comorphism Adl2CASL
    Adl
    ()
    Context
    Sen
    ()
    ()
    A.Sign
    A.Morphism
    A.Symbol
    A.RawSymbol
    ProofTree
    CASL
    CASL_Sublogics
    CASLBasicSpec
    CASLFORMULA
    SYMB_ITEMS
    SYMB_MAP_ITEMS
    CASLSign
    CASLMor
    C.Symbol
    C.RawSymbol
    ProofTree
    where
      sourceLogic Adl2CASL = Adl
      sourceSublogic Adl2CASL = ()
      targetLogic Adl2CASL = CASL
      mapSublogic Adl2CASL _ = Just $ caslTop
        { has_part = False
        , cons_features = NoSortGen }
      map_theory Adl2CASL = mapTheory
      map_sentence Adl2CASL _ = return . mapSen
      map_morphism Adl2CASL = mapMor
      map_symbol Adl2CASL _ = Set.singleton . mapSym
      is_model_transportable Adl2CASL = True
      has_model_expansion Adl2CASL = True
      is_weakly_amalgamable Adl2CASL = True
      isInclusionComorphism Adl2CASL = True

mapTheory :: (A.Sign, [Named Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = return (mapSign s, map (mapNamed mapSen) ns)

relTypeToPred :: RelType -> PredType
relTypeToPred (RelType c1 c2) = PredType [conceptToId c1, conceptToId c2]

mapSign :: A.Sign -> CASLSign
mapSign s = (C.emptySign ())
  { sortSet = Set.fold (\ sy -> case sy of
                 Con (C i) -> Set.insert $ simpleIdToId i
                 _ -> id) Set.empty $ A.symOf s
  , sortRel = Rel.map conceptToId $ isas s
  , predMap = Map.map (Set.map relTypeToPred) $ rels s
  }

mapSen :: Sen -> CASLFORMULA
mapSen s = case s of
  DeclProp _ p -> True_atom $ getRange p
  Assertion _ r -> True_atom $ getRange r

-- | Translation of morphisms
mapMor :: A.Morphism -> Result CASLMor
mapMor mor = return $ embedMorphism ()
    (mapSign $ domOfDefaultMorphism mor) $ mapSign $ codOfDefaultMorphism mor

mapSym :: A.Symbol -> C.Symbol
mapSym s = case s of
  Con c -> idToSortSymbol $ conceptToId c
  Rel (Sgn n t) -> idToPredSymbol (simpleIdToId n) $ relTypeToPred t
