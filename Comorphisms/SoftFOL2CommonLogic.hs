{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Coding of SoftFOL into CommonLogic
Copyright   :  (c) Eugen Kuksa and Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

The translating comorphism from SoftFOL to CommonLogic.
-}

module Comorphisms.SoftFOL2CommonLogic
    (
     SoftFOL2CommonLogic (..)
    )
    where

import Common.ProofTree
import Common.Id
import Common.Result
import qualified Common.AS_Annotation as AS_Anno

import Logic.Logic
import Logic.Comorphism

import qualified Data.Set as Set

-- SoftFOL
import qualified SoftFOL.Logic_SoftFOL as FOLLogic
import qualified SoftFOL.Sign as FOLSign

-- CommonLogic
import CommonLogic.AS_CommonLogic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSL

-- | lid of the morphism
data SoftFOL2CommonLogic = SoftFOL2CommonLogic deriving Show

instance Language SoftFOL2CommonLogic where
  language_name SoftFOL2CommonLogic = "SoftFOL2CommonLogic"

instance Comorphism SoftFOL2CommonLogic
    FOLLogic.SoftFOL         -- lid domain
    ()                       -- sublogics codomain
    ()                       -- Basic spec domain
    FOLSign.Sentence         -- sentence domain
    ()                       -- symbol items domain
    ()                       -- symbol map items domain
    FOLSign.Sign             -- signature domain
    FOLSign.SoftFOLMorphism  -- morphism domain
    FOLSign.SFSymbol         -- symbol domain
    ()                       -- rawsymbol domain
    ProofTree                -- proof tree codomain
    ClLogic.CommonLogic      -- lid domain
    ClSL.CommonLogicSL       -- sublogics codomain
    BASIC_SPEC               -- Basic spec domain
    TEXT                     -- sentence domain
    NAME                     -- symbol items domain
    SYMB_MAP_ITEMS           -- symbol map items domain
    ClSign.Sign              -- signature domain
    ClMor.Morphism           -- morphism domain
    ClSymbol.Symbol          -- symbol domain
    ClSymbol.Symbol          -- rawsymbol domain
    ProofTree                -- proof tree codomain
    where
      sourceLogic SoftFOL2CommonLogic = FOLLogic.SoftFOL
      sourceSublogic SoftFOL2CommonLogic = ()
      targetLogic SoftFOL2CommonLogic = ClLogic.CommonLogic
      mapSublogic SoftFOL2CommonLogic = Just . mapSub
      map_theory SoftFOL2CommonLogic = mapTheory
      map_sentence SoftFOL2CommonLogic = mapSentence
      map_morphism SoftFOL2CommonLogic = mapMor

mapSub :: () -> ClSL.CommonLogicSL
mapSub _ = ClSL.folsl

mapMor :: FOLSign.SoftFOLMorphism -> Result ClMor.Morphism
mapMor mor = undefined {-
  let src = mapSign $ PMor.source mor
      tgt = mapSign $ PMor.target mor
      pmp = PMor.propMap mor
  in  return $ ClMor.Morphism src tgt pmp
-}
  
mapSentence :: FOLSign.Sign -> FOLSign.Sentence -> Result TEXT
mapSentence _ f = return $ translate f

mapSign :: FOLSign.Sign -> ClSign.Sign
mapSign sig = undefined
--  ClSign.unite (ClSign.Sign (PSign.items sig) (PSign.items sig)) $ baseSig

mapTheory :: (FOLSign.Sign, [AS_Anno.Named FOLSign.Sentence])
             -> Result (ClSign.Sign, [AS_Anno.Named TEXT])
mapTheory (srcSign, srcFormulas) = undefined {-
  return (mapSign srcSign,
        map ((uncurry AS_Anno.makeNamed) . elimModSnd . senAndName) srcFormulas)
  where senAndName :: AS_Anno.Named PBasic.FORMULA -> (String, PBasic.FORMULA)
        senAndName f = (AS_Anno.senAttr f, AS_Anno.sentence f)
        elimModSnd :: (String, PBasic.FORMULA) -> (String, TEXT)
        elimModSnd (s, f) = (s, translate f)
-}

translate :: FOLSign.Sentence -> TEXT
translate f = Text [Sentence $ toSen f] nullRange

toSen :: FOLSign.SPTerm -> SENTENCE
toSen t = case t of
  FOLSign.SPQuantTerm qsym vl f -> quantTerm qsym vl f
  FOLSign.SPComplexTerm sym args ->
    Atom_sent (Atom (symToTerm sym) (map sptermToTermSeq args)) nullRange

quantTerm :: FOLSign.SPQuantSym -> [FOLSign.SPTerm] -> FOLSign.SPTerm
             -> SENTENCE
quantTerm qsymm vl f =
  let trans_vl = map sptermToNameSeq vl
      trans_f = toSen f
      quantifier = case qsymm of
        FOLSign.SPForall -> Universal
        FOLSign.SPExists -> Existential
        _ -> undefined -- is caught below
  in case qsymm of 
        FOLSign.SPCustomQuantSym cq -> 
            Irregular_sent (
              Comment_sent
                (Comment "customQuantifier" nullRange)
                (undefined)
                nullRange
            ) nullRange
        _ -> Quant_sent (quantifier trans_vl trans_f) nullRange

symToSen :: FOLSign.SPSymbol -> SENTENCE
symToSen s = case s of
  FOLSign.SPEqual -> undefined   -- =
  FOLSign.SPTrue -> undefined
  FOLSign.SPFalse -> undefined
  FOLSign.SPOr -> undefined
  FOLSign.SPAnd -> undefined
  FOLSign.SPNot -> undefined
  FOLSign.SPImplies -> undefined --  =>
  FOLSign.SPImplied -> undefined -- <=
  FOLSign.SPEquiv -> undefined   -- <=>
  FOLSign.SPID -> undefined      -- ?
  FOLSign.SPDiv -> undefined     -- ?
  FOLSign.SPComp -> undefined    -- ?
  FOLSign.SPSum -> undefined     -- ?
  FOLSign.SPConv -> undefined    -- ?
  FOLSign.SPCustomSymbol i -> undefined

symToTerm :: FOLSign.SPSymbol -> TERM
symToTerm s = case s of
  FOLSign.SPEqual -> undefined   -- =
  FOLSign.SPTrue -> undefined
  FOLSign.SPFalse -> undefined
  FOLSign.SPOr -> undefined
  FOLSign.SPAnd -> undefined
  FOLSign.SPNot -> undefined
  FOLSign.SPImplies -> undefined --  =>
  FOLSign.SPImplied -> undefined -- <=
  FOLSign.SPEquiv -> undefined   -- <=>
  FOLSign.SPID -> undefined      -- ?
  FOLSign.SPDiv -> undefined     -- ?
  FOLSign.SPComp -> undefined    -- ?
  FOLSign.SPSum -> undefined     -- ?
  FOLSign.SPConv -> undefined    -- ?
  FOLSign.SPCustomSymbol i -> Name_term i

sptermToTermSeq :: FOLSign.SPTerm -> TERM_SEQ
sptermToTermSeq t = undefined

sptermToNameSeq :: FOLSign.SPTerm -> NAME_OR_SEQMARK
sptermToNameSeq t = undefined

clTrue :: SENTENCE --forall x. x=x
clTrue = Quant_sent (Universal [Name xName]
            $ Atom_sent (Equation (Name_term xName) (Name_term xName)) nullRange
          ) nullRange

clFalse :: SENTENCE
clFalse = Bool_sent (Negation clTrue) nullRange

xName :: NAME
xName = mkSimpleId "x"
