{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Comorphism from Propositional to QBF
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

-}

module Comorphisms.Prop2QBF (Prop2QBF (..)) where

import Common.ProofTree

import Logic.Logic
import Logic.Comorphism

-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- QBF
import qualified QBF.Logic_QBF as QLogic
import qualified QBF.AS_BASIC_QBF as QBasic
import qualified QBF.Sublogic as QSL
import qualified QBF.Morphism as QMor
import qualified QBF.Symbol as QSymbol

import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Result

-- | lid of the morphism
data Prop2QBF = Prop2QBF deriving Show

instance Language Prop2QBF where
  language_name Prop2QBF = "Propositional2QBF"

instance Comorphism Prop2QBF
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
    QLogic.QBF
    QSL.QBFSL
    QBasic.BASICSPEC
    QBasic.FORMULA
    QBasic.SYMBITEMS
    QBasic.SYMBMAPITEMS
    PSign.Sign
    QMor.Morphism
    QSymbol.Symbol
    QSymbol.Symbol
    ProofTree
    where
      sourceLogic Prop2QBF = PLogic.Propositional
      sourceSublogic Prop2QBF = PSL.top
      targetLogic Prop2QBF = QLogic.QBF
      mapSublogic Prop2QBF _ = Nothing
      map_theory Prop2QBF = mapTheory
      is_model_transportable Prop2QBF = True
      map_symbol Prop2QBF _ = mapSym
      map_sentence Prop2QBF _ = trForm
      map_morphism Prop2QBF = mapMor
      has_model_expansion Prop2QBF = True
      is_weakly_amalgamable Prop2QBF = True
      isInclusionComorphism Prop2QBF = True

-- | Translation of the signature
mapSig :: PSign.Sign -> PSign.Sign
mapSig = id

-- | Translation of morphisms
mapMor :: PMor.Morphism -> Result QMor.Morphism
mapMor mor = return QMor.Morphism
  { QMor.source = PMor.source mor
  , QMor.target = PMor.target mor
  , QMor.propMap = PMor.propMap mor }

-- | Mapping of a theory
mapTheory :: (PSign.Sign, [Named PBasic.FORMULA])
  -> Result (PSign.Sign, [Named QBasic.FORMULA])
mapTheory (sig, form) = do
                          form_ <- mapM (mapNamedM trForm) form
                          return (mapSig sig, form_)

-- | Translation of symbols
mapSym :: PSymbol.Symbol -> Set.Set QSymbol.Symbol
mapSym = Set.singleton . QSymbol.idToRaw . PSymbol.getSymbolName

-- | Helper for map sentence and map theory
trForm :: PBasic.FORMULA -> Result QBasic.FORMULA
trForm = return . trForm_

trForm_ :: PBasic.FORMULA -> QBasic.FORMULA
trForm_ form = case form of
  PBasic.Negation f r -> QBasic.Negation (trForm_ f) r
  PBasic.Conjunction fs r -> QBasic.Conjunction (map trForm_ fs) r
  PBasic.Disjunction fs r -> QBasic.Disjunction (map trForm_ fs) r
  PBasic.Implication f1 f2 r -> QBasic.Implication (trForm_ f1) (trForm_ f2) r
  PBasic.Equivalence f1 f2 r -> QBasic.Equivalence (trForm_ f1) (trForm_ f2) r
  PBasic.True_atom r -> QBasic.TrueAtom r
  PBasic.False_atom r -> QBasic.FalseAtom r
  PBasic.Predication t -> QBasic.Predication t
