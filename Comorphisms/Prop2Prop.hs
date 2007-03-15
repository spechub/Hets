{- |
Module      :  $Header$
Description :  Coding of CASL into SoftFOL
Copyright   :  (c) Dominik Luecke and Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Translations from Propositional to its sublogics.
-}

module Comorphisms.Prop2Prop
    where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set

import qualified Common.AS_Annotation as AS_Anno

import qualified Common.Result as Result

import qualified Propositional.Rules as Rulez

-- Propositional
import qualified Propositional.Logic_Propositional as PLogic
import qualified Propositional.AS_BASIC_Propositional as PBasic
import qualified Propositional.Sublogic as PSL
import qualified Propositional.Sign as PSign
import qualified Propositional.Morphism as PMor
import qualified Propositional.Symbol as PSymbol

-- | lids of the morphisms

data PropIE2PropI = PropIE2PropI deriving (Show)
data PropIE2PropE = PropIE2PropE deriving (Show)
data PropIE2Prop  = PropIE2Prop deriving (Show)

instance Language PropIE2PropI
instance Language PropIE2PropE
instance Language PropIE2Prop

instance Comorphism PropIE2PropI
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
    ()
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
    ()
    where
      sourceLogic PropIE2PropI            = PLogic.Propositional
      sourceSublogic PropIE2PropI         = PSL.top
      targetLogic PropIE2PropI            = PLogic.Propositional
      mapSublogic PropIE2PropI            = mapSubPropIE2PropI
      map_symbol PropIE2PropI             = mapSymbol
      map_morphism PropIE2PropI           = mapMor
      is_model_transportable PropIE2PropI = True
      map_sentence PropIE2PropI           = mapSentence trIEtoIForm
      map_theory PropIE2PropI             = mapTheory trIEtoIForm

instance Comorphism PropIE2PropE
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
    ()
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
    ()
    where
      sourceLogic PropIE2PropE            = PLogic.Propositional
      sourceSublogic PropIE2PropE         = PSL.top
      targetLogic PropIE2PropE            = PLogic.Propositional
      mapSublogic PropIE2PropE            = mapSubPropIE2PropE
      map_symbol PropIE2PropE             = mapSymbol
      map_morphism PropIE2PropE           = mapMor
      is_model_transportable PropIE2PropE = True
      map_sentence PropIE2PropE           = mapSentence trIEtoEForm
      map_theory PropIE2PropE             = mapTheory trIEtoEForm

instance Comorphism PropIE2Prop
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
    ()
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
    ()
    where
      sourceLogic PropIE2Prop             = PLogic.Propositional
      sourceSublogic PropIE2Prop          = PSL.top
      targetLogic PropIE2Prop             = PLogic.Propositional
      mapSublogic PropIE2Prop             = mapSubPropIE2Prop
      map_symbol PropIE2Prop              = mapSymbol
      map_morphism PropIE2Prop            = mapMor
      is_model_transportable PropIE2Prop  = True
      map_sentence PropIE2Prop            = mapSentence trIEtoForm
      map_theory PropIE2Prop              = mapTheory trIEtoForm

-- | determination of target sublogic 
mapSubPropIE2PropI :: PSL.PropSL -> PSL.PropSL
mapSubPropIE2PropI sl 
    | PSL.isPropIE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = True
                        , PSL.has_equiv = False
                        }
    | PSL.isPropI sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = True
                        , PSL.has_equiv = False
                        }
    | PSL.isPropE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isProp sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isCNF sl = PSL.PropSL
                        {
                          PSL.format    = PSL.CNF
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | otherwise    = error "Impossible case"

-- | determination of target sublogic
mapSubPropIE2PropE :: PSL.PropSL -> PSL.PropSL
mapSubPropIE2PropE sl 
    | PSL.isPropIE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = True
                        }
    | PSL.isPropI sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isPropE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isProp sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isCNF sl = PSL.PropSL
                        {
                          PSL.format    = PSL.CNF
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | otherwise    = error "Impossible case"

-- | determination of target sublogic
mapSubPropIE2Prop :: PSL.PropSL -> PSL.PropSL
mapSubPropIE2Prop sl 
    | PSL.isPropIE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isPropI sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isPropE sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isProp sl = PSL.PropSL
                        {
                          PSL.format    = PSL.PlainFormula
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | PSL.isCNF sl = PSL.PropSL
                        {
                          PSL.format    = PSL.CNF
                        , PSL.has_imp   = False
                        , PSL.has_equiv = False
                        }
    | otherwise    = error "Impossible case"


-- | mapping of symbol... which is trivial in our case
mapSymbol :: PSymbol.Symbol -> Set.Set PSymbol.Symbol
mapSymbol sym = Set.singleton sym

-- | mapping of the signature
mapSig :: PSign.Sign -> PSign.Sign 
mapSig = id

-- | trivial map of morphisms
mapMor :: PMor.Morphism -> Result.Result PMor.Morphism
mapMor mor = Result.Result
             {
               Result.diags = []
             , Result.maybeResult = Just mor
             }

-- | Mapping of sentences
mapSentence :: (PBasic.FORMULA
                -> PBasic.FORMULA
               )
            -> PSign.Sign 
            -> PBasic.FORMULA 
            -> Result.Result PBasic.FORMULA
mapSentence fun _ form = Result.Result
                         {
                           Result.diags = []
                         , Result.maybeResult = Just $ fun form
                         }

-- | Mapping of a theory
mapTheory :: (PBasic.FORMULA
                -> PBasic.FORMULA
               )
          ->    (PSign.Sign, [AS_Anno.Named (PBasic.FORMULA)])
          -> Result.Result (PSign.Sign, [AS_Anno.Named (PBasic.FORMULA)])
mapTheory fun (sig, form) = Result.Result
                         {
                           Result.diags = []
                         , Result.maybeResult = Just (mapSig sig, map (trNamedForm fun) form)
                         }

--------------------------------------------------------------------------
-- Helpers                                                              --
--------------------------------------------------------------------------

trNamedForm :: (PBasic.FORMULA
               -> PBasic.FORMULA
               )
            -> AS_Anno.Named (PBasic.FORMULA) 
            -> AS_Anno.Named (PBasic.FORMULA)
trNamedForm fun form = 
    let 
        sName = AS_Anno.senName form
        isAxiom = AS_Anno.isAxiom form
        isDef = AS_Anno.isDef form
        sSen = AS_Anno.sentence form
    in 
      AS_Anno.NamedSen
                 {
                   AS_Anno.senName = sName
                 , AS_Anno.sentence = fun sSen
                 , AS_Anno.isDef = isDef
                 , AS_Anno.isAxiom = isAxiom
                 }

trIEtoIForm :: PBasic.FORMULA
               -> PBasic.FORMULA
trIEtoIForm = Rulez.matEquiv

trIEtoEForm :: PBasic.FORMULA 
            -> PBasic.FORMULA
trIEtoEForm = Rulez.matImpl

trIEtoForm :: PBasic.FORMULA
           -> PBasic.FORMULA
trIEtoForm = Rulez.matEquivImpl
