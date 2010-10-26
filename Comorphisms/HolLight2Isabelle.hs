{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  translating from HolLight to Isabelle
Copyright   :  (c) M. Codescu, DFKI 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Mihai.Codescu@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Comorphisms.HolLight2Isabelle where

import Logic.Comorphism
import Logic.Logic

import qualified Isabelle.IsaSign as IsaSign
import Isabelle.Logic_Isabelle
import Isabelle.IsaConsts

import Common.Result
import Common.AS_Annotation

import qualified Data.Map as Map

import HolLight.Sign
import HolLight.Sentence
import HolLight.Logic_HolLight
import HolLight.Sublogic

data HolLight2Isabelle = HolLight2Isabelle deriving Show

instance Language HolLight2Isabelle

instance Comorphism HolLight2Isabelle
          HolLight
          HolLightSL                -- sublogic
          ()                        -- basic_spec
          Sentence                  -- sentence
          ()                        -- symb_items
          ()                        -- symb_map_items
          Sign                      -- sign
          HolLightMorphism          -- morphism
          ()                        -- symbol
          ()                        -- raw_symbol
          ()                        -- proof_tree
          Isabelle () () IsaSign.Sentence () ()
          IsaSign.Sign
          IsabelleMorphism () () ()  where
   sourceLogic _ = HolLight
   sourceSublogic _ = Top
   targetLogic _ = Isabelle
   mapSublogic _ _ = Just ()
   map_theory HolLight2Isabelle = mapTheory
   map_morphism = error "nyi"
   map_sentence HolLight2Isabelle = mapSentence

-- mapping sentences

mapSentence :: Sign -> Sentence -> Result IsaSign.Sentence
mapSentence _ s = return $ mapHolSen s

mapHolSen :: Sentence -> IsaSign.Sentence
mapHolSen (Sentence _n t _p) = IsaSign.Sentence{
                                  IsaSign.isSimp = False
                                 ,IsaSign.isRefuteAux = False
                                 ,IsaSign.metaTerm =
                                    IsaSign.Term $ translateTerm t
                                 , IsaSign.thmProof = Nothing
                                      }

tp2DTyp :: HolType -> IsaSign.DTyp
tp2DTyp tp = IsaSign.Hide{
                IsaSign.typ = tp2Typ tp,
                IsaSign.kon = IsaSign.TCon,
                IsaSign.arit = Nothing
              }

translateTerm :: Term -> IsaSign.Term
translateTerm (Var s _tp) = IsaSign.Free $ IsaSign.mkVName s
translateTerm (Const s tp) = IsaSign.Const (IsaSign.mkVName s)
                                $ tp2DTyp tp
translateTerm (Comb tm1 tm2) = IsaSign.App (translateTerm tm1)
                                          (translateTerm tm2)
                                          IsaSign.NotCont
translateTerm (Abs tm1 tm2) = IsaSign.Abs (translateTerm tm1)
                                          (translateTerm tm2)
                                          IsaSign.NotCont

-- mapping theories

mapTheory :: (Sign, [Named Sentence]) ->
             Result(IsaSign.Sign, [Named IsaSign.Sentence])
mapTheory (sig, n_sens) = let
  sig' = mapSign sig
  n_sens' = map mapNamedSen n_sens
                          in return (sig', n_sens')

mapSign :: Sign -> IsaSign.Sign
mapSign (Sign t o) = IsaSign.emptySign{
                       IsaSign.baseSig = IsaSign.MainHC_thy,
                       IsaSign.tsig = mapTypes t,
                       IsaSign.constTab = mapOps o
                      }

mapOps :: Map.Map String HolType -> IsaSign.ConstTab
mapOps f = Map.fromList $
            map (\(x,y) -> (IsaSign.mkVName x, tp2Typ y)) $ Map.toList f

tp2Typ :: HolType -> IsaSign.Typ
tp2Typ (TyVar s) = IsaSign.Type s holType []
tp2Typ (TyApp s tps) = IsaSign.Type s holType $ map tp2Typ tps

mapTypes :: [HolType] -> IsaSign.TypeSig
mapTypes tps = IsaSign.emptyTypeSig {
                IsaSign.arities = Map.fromList $ map extractTypeName tps}
 where
    extractTypeName t@(TyVar s) = (s, [(isaTerm, [(tp2Typ t, holType)])])
    extractTypeName t@(TyApp s _tps') = (s, [(isaTerm, [(tp2Typ t, holType)])])


mapNamedSen :: Named Sentence -> Named IsaSign.Sentence
mapNamedSen n_sen = let
 sen = sentence n_sen
 trans = mapHolSen sen
                    in
 n_sen{sentence = trans}

