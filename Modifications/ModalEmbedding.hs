{- |
Module      :  $EmptyHeader$
Description :  <optional short description entry>
Copyright   :  (c) <Authors or Affiliations>
License     :  GPLv2 or higher

Maintainer  :  <email>
Stability   :  unstable | experimental | provisional | stable | frozen
Portability :  portable | non-portable (<reason>)

<optional description>
-}
{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances, FlexibleInstances
  , TypeSynonymInstances #-}
-- institution modification
-- CASL -------------------------id------------------> CASL
-- CASL ---CASL2Modal----> ModalCASL --Modal2CASL----> CASL

module Modifications.ModalEmbedding where

import Logic.Modification
import Logic.Logic
import Logic.Comorphism

import Comorphisms.CASL2Modal
import Comorphisms.Modal2CASL


import CASL.Logic_CASL
import CASL.Sign
import CASL.Morphism
import CASL.AS_Basic_CASL
import CASL.Sublogic as SL

import Common.ProofTree

data MODAL_EMBEDDING = MODAL_EMBEDDING deriving Show

instance Language MODAL_EMBEDDING

instance Modification MODAL_EMBEDDING (InclComorphism CASL CASL_Sublogics)
    (CompComorphism CASL2Modal Modal2CASL)
        CASL CASL_Sublogics
        CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        CASLSign
        CASLMor
        Symbol RawSymbol ProofTree
        CASL CASL_Sublogics
        CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        CASLSign
        CASLMor
        Symbol RawSymbol ProofTree
        CASL CASL_Sublogics
        CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        CASLSign
        CASLMor
        Symbol RawSymbol ProofTree
        CASL CASL_Sublogics
        CASLBasicSpec CASLFORMULA SYMB_ITEMS SYMB_MAP_ITEMS
        CASLSign
        CASLMor
        Symbol RawSymbol ProofTree
 where
  sourceComorphism MODAL_EMBEDDING = mkIdComorphism CASL (top_sublogic CASL)
  targetComorphism MODAL_EMBEDDING = CompComorphism CASL2Modal Modal2CASL
  tauSigma MODAL_EMBEDDING sigma = do
      (sigma1, _ ) <- wrapMapTheory CASL2Modal (sigma, [])
      (sigma2, _ ) <- wrapMapTheory Modal2CASL (sigma1, [])
      return (embedMorphism () sigma sigma2)
