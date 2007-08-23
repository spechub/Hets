{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Inverse static analysis for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Translation of Named Sentences to basic_spec

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
-}

module Propositional.InverseAnalysis
    (
     signToBasicSpec
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import qualified Data.List as List
import qualified Data.Set as Set

{--
-- | Converts signature to formula
signSymbolsToFormula :: Sign.Sign -> [AS_Anno.Annoted AS_BASIC.FORMULA]
signSymbolsToFormula sig = Set.fold (\x y -> (
                                              AS_Anno.Annoted
                                              {   
                                                AS_Anno.item = AS_BASIC.Predication $ head $ getSimpleId x
                                              , AS_Anno.opt_pos = Id.nullRange
                                              , AS_Anno.l_annos = []
                                              , AS_Anno.r_annos = []
                                              }
                                             ):y) []
                           (Sign.items sig)

--}

-- | Converts signature to PRED_ITEM
signSymbolsToPredItems :: Sign.Sign                          -- Signature
                       -> AS_BASIC.PRED_ITEM                 -- predicated ref. to AS_BASIC
signSymbolsToPredItems sig = AS_BASIC.Pred_item 
                             (
                              Set.fold (\x y -> (head $ getSimpleId x):y) [] $ Sign.items sig
                             )
                             Id.nullRange

-- | Converts signature to BASIC_ITEMS
signSymbolsToPred_decl :: Sign.Sign                          -- Signature
                       -> AS_BASIC.BASIC_ITEMS               -- BASIC_ITEMS ref. to AS_BASIC
signSymbolsToPred_decl sign = AS_BASIC.Pred_decl (signSymbolsToPredItems sign)

-- | Converts named formulae to BASIC_ITEMS
namedFormulaToAxiomItems :: [AS_Anno.Named AS_BASIC.FORMULA] -- named formulae
                         -> AS_BASIC.BASIC_ITEMS             -- BASIC_ITEMS ref. to AS_BASIC
namedFormulaToAxiomItems forms = AS_BASIC.Axiom_items
                                 (map namedFormToAnnotedForm forms)

-- | Converts named formulae to annoted formula
namedFormToAnnotedForm :: AS_Anno.Named AS_BASIC.FORMULA     -- named Basic formula ref. to AS_BASIC
                       -> AS_Anno.Annoted AS_BASIC.FORMULA   -- annoted Basic formula ref. to AS_BASIC
namedFormToAnnotedForm f  = AS_Anno.Annoted 
                            {
                              AS_Anno.item     = nakedFormula
                            , AS_Anno.opt_pos  = Id.nullRange
                            , AS_Anno.l_annos  = []
                            , AS_Anno.r_annos  = [AS_Anno.Label [name] Id.nullRange]
                            }
    where
      nakedFormula = AS_Anno.sentence f
      name         = AS_Anno.senAttr  f

-- | gets simple Id
-- this is just a shortcut
getSimpleId :: Id.Id -> [Id.Token]
getSimpleId (Id.Id toks _ _) = toks

-- | one sided inverse of static analysis
signToBasicSpec :: Sign.Sign                           -- signature
                -> [AS_Anno.Named AS_BASIC.FORMULA]    -- list of named formulae
                -> AS_BASIC.BASIC_SPEC                 -- basic spec
signToBasicSpec sign forms = AS_BASIC.Basic_spec 
                             (
                             [
                              AS_Anno.Annoted
                              {
                                AS_Anno.item    = signSymbolsToPred_decl sign
                              , AS_Anno.opt_pos = Id.nullRange
                              , AS_Anno.l_annos = []
                              , AS_Anno.r_annos = []
                              }
                             ]
                              ++
                             [
                              AS_Anno.Annoted
                              {
                                AS_Anno.item    = namedFormulaToAxiomItems forms
                              , AS_Anno.opt_pos = Id.nullRange
                              , AS_Anno.l_annos = []
                              , AS_Anno.r_annos = []
                              }
                              ]
                             )
