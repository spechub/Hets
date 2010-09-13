{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Coding of Maude with preorder semantics into CASL
Copyright   :  (c) Adrian Riesco and Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  ariesco@fdi.ucm.es
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Maude with preorder semantics to CASL.
-}

module Comorphisms.Maude2CASL
    (
     Maude2CASL (..)
   , mapMaudeFreeness
    )
    where

import Common.ProofTree

import Logic.Logic
import Logic.Comorphism

-- Maude
import qualified Maude.Logic_Maude as MLogic
import qualified Maude.AS_Maude as MAS
import qualified Maude.Sign as MSign
import qualified Maude.Morphism as MMor
import qualified Maude.Symbol as MSymbol
import qualified Maude.Sentence as MSentence
import Maude.PreComorphism

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

import Common.Result
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id ()
import qualified Data.Map as Map

-- | lid of the morphism
data Maude2CASL = Maude2CASL deriving Show

instance Language Maude2CASL where
  language_name Maude2CASL = "Maude2CASL"

instance Comorphism Maude2CASL
    MLogic.Maude
    ()
    MAS.MaudeText
    MSentence.Sentence
    ()
    ()
    MSign.Sign
    MMor.Morphism
    MSymbol.Symbol
    MSymbol.Symbol
    ()
    CLogic.CASL
    CSL.CASL_Sublogics
    CLogic.CASLBasicSpec
    CBasic.CASLFORMULA
    CBasic.SYMB_ITEMS
    CBasic.SYMB_MAP_ITEMS
    CSign.CASLSign
    CMor.CASLMor
    CSign.Symbol
    CMor.RawSymbol
    ProofTree
    where
      sourceLogic Maude2CASL = MLogic.Maude
      sourceSublogic Maude2CASL = ()
      targetLogic Maude2CASL = CLogic.CASL
      mapSublogic Maude2CASL _ = Just CSL.caslTop
        { CSL.cons_features = CSL.emptyMapConsFeature
        , CSL.sub_features = CSL.NoSub }
      map_theory Maude2CASL = mapTheory
      is_model_transportable Maude2CASL = True
      map_symbol Maude2CASL = mapSymbol
      map_sentence Maude2CASL = mapSentence
      map_morphism Maude2CASL = mapMorphism
      has_model_expansion Maude2CASL = True
      is_weakly_amalgamable Maude2CASL = True
      isInclusionComorphism Maude2CASL = True

mapMaudeFreeness :: MMor.Morphism
                 -> Result (CSign.CASLSign, CMor.CASLMor, CMor.CASLMor)
mapMaudeFreeness morph = do
 let sMaude = MMor.source morph
     tMaude = MMor.target morph
 (sCASL, _) <- map_theory Maude2CASL (sMaude, [])
 (tCASL, _) <- map_theory Maude2CASL (tMaude, [])
 let tExt = signExtension tMaude tCASL
     (f1, f2) = morExtension morph tExt sCASL tCASL
 return (tExt, f1, f2)


signExtension :: MSign.Sign -> CSign.CASLSign -> CSign.CASLSign
signExtension sigma sigmaC =
 let
  sorts = Set.map MSymbol.toId $ MSign.sorts sigma
  subsorts = Rel.map MSymbol.toId $ MSign.subsorts sigma
  kindR = MSign.kindRel sigma
  funs = (\ (x, _, _) -> x) $ translateOps (kindMapId kindR) $ MSign.ops sigma
  funSorts = atLeastOneSort $ MSign.ops sigma
  funs' = (\ (x, _, _) -> x) $ translateOps' (kindMapId kindR) funSorts
  {- opTypeKind (CSign.OpType oK oArgs oRes) =
              CSign.OpType oK (map kindId oArgs) (kindId oRes) -}
 in sigmaC
         {CSign.sortSet = Set.union sorts $ Set.map kindId sorts,
          CSign.sortRel = Rel.union subsorts $ Rel.union
                              (Rel.map kindId subsorts)
                              $ Rel.fromSet
                              $ Set.map (\ x -> (x, kindId x)) sorts,
          CSign.opMap = CSign.addOpMapSet funs funs',
           -- Map.map (\s -> Set.union s $ Set.map opTypeKind s) funs,
          CSign.predMap = rewPredicates $ Set.union sorts
                          $ Set.map kindId sorts

          }

morExtension :: MMor.Morphism ->  -- sigma:\Sigma -> \Sigma'
                CSign.CASLSign ->  -- phi(\Sigma)
                CSign.CASLSign -> -- phi(\Sigma')
                CSign.CASLSign -> -- \Sigma'#
                (CMor.CASLMor, CMor.CASLMor)
morExtension phi tExt sCASL tCASL =
 let
   changeMap f mapF = Map.mapKeys f $
                       Map.map f mapF
   sortF = changeMap MSymbol.toId $ MMor.sortMap phi
   iotaN = CMor.embedMorphism () tCASL tExt
   genOps f = let
               f' = MSymbol.toId f
               profiles = Map.findWithDefault
                         Set.empty f' $
                         CSign.opMap sCASL
               ff = Map.findWithDefault (error "morExtension")
                     f $ MMor.opMap phi
              in Set.toList $ Set.map (\ x -> ((f', x),
                            (MSymbol.toId ff, CBasic.Partial)))
                 profiles
   phi' = CMor.Morphism {
             CMor.msource = sCASL,
             CMor.mtarget = tExt,
             CMor.sort_map = Map.union sortF $
                              changeMap kindId sortF,
             CMor.op_map = Map.fromList $
                            foldl (++) [] $
                            map genOps $ Map.keys $
                            MMor.opMap phi ,
             CMor.pred_map = Map.empty,
                -- because rew is mapped identically!
             CMor.extended_map = ()
           }
 in (iotaN, phi')
