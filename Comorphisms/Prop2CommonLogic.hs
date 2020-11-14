{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/Prop2CommonLogic.hs
Description :  Coding of Propositional into CommonLogic
Copyright   :  (c) Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from Propositional to CommonLogic.
-}

module Comorphisms.Prop2CommonLogic
    (
     Prop2CommonLogic (..)
    )
    where

import Common.ProofTree
import Common.Id
import Common.Result
import qualified Common.AS_Annotation as AS_Anno

import Logic.Logic
import Logic.Comorphism

import qualified Data.HashSet as Set (fromList)

-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- CommonLogic
import CommonLogic.AS_CommonLogic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSL

-- | lid of the morphism
data Prop2CommonLogic = Prop2CommonLogic deriving Show

instance Language Prop2CommonLogic where
  language_name Prop2CommonLogic = "Propositional2CommonLogic"

instance Comorphism Prop2CommonLogic
    PLogic.Propositional
    PSL.PropSL
    PBasic.BASIC_SPEC
    PBasic.FORMULA
    PBasic.SYMB_ITEMS
    PBasic.SYMB_MAP_ITEMS
    PSign.Sign
    PMor.Morphism
    PSymbol.Symbol
    PSymbol.Symbol
    ProofTree
    ClLogic.CommonLogic     -- lid domain
    ClSL.CommonLogicSL      -- sublogics codomain
    BASIC_SPEC              -- Basic spec domain
    TEXT_META               -- sentence domain
    SYMB_ITEMS              -- symb_items
    SYMB_MAP_ITEMS          -- symbol map items domain
    ClSign.Sign             -- signature domain
    ClMor.Morphism          -- morphism domain
    ClSymbol.Symbol         -- symbol domain
    ClSymbol.Symbol         -- rawsymbol domain
    ProofTree               -- proof tree codomain
    where
      sourceLogic Prop2CommonLogic = PLogic.Propositional
      sourceSublogic Prop2CommonLogic = PSL.top
      targetLogic Prop2CommonLogic = ClLogic.CommonLogic
      mapSublogic Prop2CommonLogic = Just . mapSub
      map_theory Prop2CommonLogic = mapTheory
      map_sentence Prop2CommonLogic = mapSentence
      map_morphism Prop2CommonLogic = mapMor

mapSub :: PSL.PropSL -> ClSL.CommonLogicSL
mapSub _ = ClSL.folsl

mapMor :: PMor.Morphism -> Result ClMor.Morphism
mapMor mor =
  let src = mapSign $ PMor.source mor
      tgt = mapSign $ PMor.target mor
      pmp = PMor.propMap mor
  in return $ ClMor.Morphism src tgt pmp

mapSentence :: PSign.Sign -> PBasic.FORMULA -> Result TEXT_META
mapSentence _ f = return $ translate f

mapSign :: PSign.Sign -> ClSign.Sign
mapSign sig =
  ClSign.unite (ClSign.emptySig {
      ClSign.discourseNames = PSign.items sig
    }) baseSig

baseSig :: ClSign.Sign
baseSig = ClSign.emptySig {
    ClSign.discourseNames = Set.fromList [simpleIdToId xName, simpleIdToId yName]
  }

mapTheory :: (PSign.Sign, [AS_Anno.Named PBasic.FORMULA])
             -> Result (ClSign.Sign, [AS_Anno.Named TEXT_META])
mapTheory (srcSign, srcFormulas) =
  return (mapSign srcSign,
        map (uncurry AS_Anno.makeNamed . transSnd . senAndName) srcFormulas)
  where senAndName :: AS_Anno.Named PBasic.FORMULA -> (String, PBasic.FORMULA)
        senAndName f = (AS_Anno.senAttr f, AS_Anno.sentence f)
        transSnd :: (String, PBasic.FORMULA) -> (String, TEXT_META)
        transSnd (s, f) = (s, translate f)

translate :: PBasic.FORMULA -> TEXT_META
translate f =
  emptyTextMeta {
        getText = Text [Sentence singletonUniv, Sentence $ toSen f] nullRange
  }
  where singletonUniv = Quant_sent Universal [Name xName, Name yName]
                        (Atom_sent (Equation
                                    (Name_term xName)
                                    (Name_term yName)) nullRange) nullRange

toSen :: PBasic.FORMULA -> SENTENCE
toSen x = case x of
  PBasic.False_atom _ -> Bool_sent (Negation clTrue) nullRange
  PBasic.True_atom _ -> clTrue
  PBasic.Predication n -> Atom_sent (Atom (Name_term n) []) nullRange
  PBasic.Negation f _ -> Bool_sent (Negation $ toSen f) nullRange
  PBasic.Conjunction fs _ ->
    Bool_sent (Junction Conjunction $ map toSen fs) nullRange
  PBasic.Disjunction fs _ ->
    Bool_sent (Junction Disjunction $ map toSen fs) nullRange
  PBasic.Implication f1 f2 _ ->
    Bool_sent (BinOp Implication (toSen f1) (toSen f2)) nullRange
  PBasic.Equivalence f1 f2 _ ->
    Bool_sent (BinOp Biconditional (toSen f1) (toSen f2)) nullRange

clTrue :: SENTENCE -- forall x. x=x
clTrue = Quant_sent Universal [Name xName]
         (Atom_sent (Equation (Name_term xName) (Name_term xName))
          nullRange) nullRange

xName :: NAME
xName = mkSimpleId "x"

yName :: NAME
yName = mkSimpleId "y"
