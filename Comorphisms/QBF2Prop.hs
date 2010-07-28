{-# LANGUAGE MultiParamTypeClasses #-}
{- |
Module      :  $Header$
Description :  Comorphism from QBF to Propositional
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

-}

module Comorphisms.QBF2Prop (QBF2Prop (..)) where

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
import QBF.Tools

import qualified Data.Set as Set
import Common.AS_Annotation
import Common.Id
import Common.Result

-- | lid of the morphism
data QBF2Prop = QBF2Prop deriving Show

instance Language QBF2Prop where
  language_name QBF2Prop = "QBF2Propositional"

instance Comorphism QBF2Prop
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
    where
      sourceLogic QBF2Prop = QLogic.QBF
      sourceSublogic QBF2Prop = QSL.top
      targetLogic QBF2Prop = PLogic.Propositional
      mapSublogic QBF2Prop _ = Nothing
      map_theory QBF2Prop = mapTheory
      is_model_transportable QBF2Prop = True
      map_symbol QBF2Prop _ = mapSym
      map_sentence QBF2Prop _ = trForm
      map_morphism QBF2Prop = mapMor
      -- has_model_expansion QBF2Prop = True
      -- is_weakly_amalgamable QBF2Prop = True
      isInclusionComorphism QBF2Prop = True

-- | Translation of the signature
mapSig :: PSign.Sign -> PSign.Sign
mapSig = id

-- | Translation of morphisms
mapMor :: QMor.Morphism -> Result PMor.Morphism
mapMor mor = return PMor.Morphism
  { PMor.source = QMor.source mor
  , PMor.target = QMor.target mor
  , PMor.propMap = QMor.propMap mor }

-- | Mapping of a theory
mapTheory :: (PSign.Sign, [Named QBasic.FORMULA])
  -> Result (PSign.Sign, [Named PBasic.FORMULA])
mapTheory (sig, form) = do
                          form_ <- mapM (mapNamedM trForm) form
                          return (mapSig sig, form_)

-- | Translation of symbols
mapSym :: QSymbol.Symbol -> Set.Set PSymbol.Symbol
mapSym = Set.singleton . PSymbol.idToRaw . QSymbol.getSymbolName

-- | Helper for map sentence and map theory
trForm :: QBasic.FORMULA -> Result PBasic.FORMULA
trForm = return . trForm_

trForm_ :: QBasic.FORMULA -> PBasic.FORMULA
trForm_ form = case form of
  QBasic.Negation f r -> PBasic.Negation (trForm_ f) r
  QBasic.Conjunction fs r -> PBasic.Conjunction (map trForm_ fs) r
  QBasic.Disjunction fs r -> PBasic.Disjunction (map trForm_ fs) r
  QBasic.Implication f1 f2 r -> PBasic.Implication (trForm_ f1) (trForm_ f2) r
  QBasic.Equivalence f1 f2 r -> PBasic.Equivalence (trForm_ f1) (trForm_ f2) r
  QBasic.TrueAtom r -> PBasic.True_atom r
  QBasic.FalseAtom r -> PBasic.False_atom r
  QBasic.Predication t -> PBasic.Predication t
  QBasic.ForAll [] f _ -> trForm_ f
  QBasic.ForAll (t : ts) f r -> PBasic.Conjunction
    (map (trForm_ . replacePred (QBasic.ForAll ts f r) t)
    [QBasic.TrueAtom r, QBasic.FalseAtom r]) r
  QBasic.Exists [] f _ -> trForm_ f
  QBasic.Exists (t : ts) f r -> PBasic.Disjunction
    (map (trForm_ . replacePred (QBasic.Exists ts f r) t)
    [QBasic.TrueAtom r, QBasic.FalseAtom r]) r

-- | Helper for trForm
replacePred :: QBasic.FORMULA -> Token -> QBasic.FORMULA -> QBasic.FORMULA
replacePred f s r = foldFormula mapRecord {
  foldPredication = \ t -> if t == s then r else
    QBasic.Predication t } f
