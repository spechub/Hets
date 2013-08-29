{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Coding QVTR into CASL
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module Comorphisms.QVTR2CASL
    ( QVTR2CASL (..)
    ) where

import Logic.Logic
import Logic.Comorphism
import Common.DefaultMorphism

-- CSMOF
--import CSMOF.Logic_CSMOF as CSMOF
--import CSMOF.As as CSMOFAs
--import CSMOF.Sign as CSMOF

-- QVTR
import QVTR.Logic_QVTR as QVTR
import QVTR.As as QVTRAs
import QVTR.Sign as QVTR

-- CASL
import CASL.Logic_CASL
import CASL.AS_Basic_CASL as C
import CASL.Sublogic
import CASL.Sign as C
import CASL.Morphism as C

import Common.AS_Annotation
import Common.GlobalAnnotations
--import Common.Id
import Common.ProofTree
import Common.Result

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.MapSet as MapSet

import qualified Data.Set as Set
import qualified Data.Map as Map

-- | lid of the morphism
data QVTR2CASL = QVTR2CASL deriving Show

instance Language QVTR2CASL -- default is ok

instance Comorphism QVTR2CASL
    QVTR.QVTR
    ()
    QVTRAs.Transformation
    QVTR.Sen
    ()
    ()
    QVTR.Sign
    QVTR.Morphism
    ()
    ()
    ()
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
      sourceLogic QVTR2CASL = QVTR
      sourceSublogic QVTR2CASL = ()
      targetLogic QVTR2CASL = CASL
      mapSublogic QVTR2CASL _ = Just $ caslTop
        { has_part = False
        , sub_features = LocFilSub
        , cons_features = SortGen True True }
      map_theory QVTR2CASL = mapTheory
      map_sentence QVTR2CASL s = return . mapSen (mapSign s)
      map_morphism QVTR2CASL = mapMor
      -- map_symbol QVTR2CASL _ = Set.singleton . mapSym
      is_model_transportable QVTR2CASL = True
      has_model_expansion QVTR2CASL = True
      is_weakly_amalgamable QVTR2CASL = True
      isInclusionComorphism QVTR2CASL = True


mapTheory :: (QVTR.Sign, [Named QVTR.Sen]) -> Result (CASLSign, [Named CASLFORMULA])
mapTheory (s, ns) = let cs = mapSign s in
  return (cs, map (mapNamed $ mapSen cs) ns ++ sentences cs)


mapSign :: QVTR.Sign -> CASLSign
mapSign _ = --s = 
  let 
    sorts = Rel.empty --Rel.Rel SORT
    ops = MapSet.empty --OpMap
  in
    C.Sign
    { sortRel = sorts
    , revSortRel = Nothing 
    , emptySortSet = Set.empty
    , opMap = ops
    , assocOps = MapSet.empty
    , predMap = MapSet.empty --PredMap
    , varMap = Map.empty
    , sentences = [] --[Named (FORMULA f)]
    , declaredSymbols = Set.empty
    , envDiags = []
    , annoMap = MapSet.empty
    , globAnnos = emptyGlobalAnnos
    , extendedInfo = ()
    }


mapSen :: CASLSign -> QVTR.Sen -> CASLFORMULA
mapSen _ _ = trueForm -- sig (KeyConstr k) = trueForm
--mapSen _ _ = trueForm -- sig (QVTSen k) = trueForm


-- | Translation of morphisms
mapMor :: QVTR.Morphism -> Result CASLMor
mapMor m = return C.Morphism
  { msource = mapSign $ domOfDefaultMorphism m
  , mtarget = mapSign $ codOfDefaultMorphism m
  , sort_map = Map.empty
  , op_map = Map.empty
  , pred_map = Map.empty
  , extended_map = ()
  }


-- mapSym :: QVTR.Symbol -> C.Symbol



