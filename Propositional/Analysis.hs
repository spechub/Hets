{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  portable

Basic and static analysis for propositional logic

  Ref.
  <http://en.wikipedia.org/wiki/Propositional_logic>
-}
	
module Propositional.Analysis 
    (
     basicPropositionalAnalysis
    )
    where

import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Propositional.Sign as Sign
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.Result as Result
import qualified Common.Id as Id

-- | Retrieves the signature out of a basic spec
makeSig :: 
    AS_BASIC.BASIC_SPEC                  -- Input SPEC
    -> Sign.Sign                         -- Input Signature
    -> Sign.Sign                         -- Output Signature
makeSig (AS_BASIC.Basic_spec spec) sig = retrieveBasicItems spec sig

-- Helper for makeSig
retrieveBasicItems ::
    [AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)]      -- Input Items
    -> Sign.Sign                                  -- Input Signature
    -> Sign.Sign                                  -- OutputSignature
retrieveBasicItems [] sig = sig
retrieveBasicItems (x:xs) sig = 
    case (AS_Anno.item x) of 
      (AS_BASIC.Pred_decl pred) -> retrieveBasicItems xs $ addPred sig $ unwrapPred pred
      (AS_BASIC.Axiom_items _) -> retrieveBasicItems xs sig

unwrapPred :: AS_BASIC.PRED_ITEM -> [Id.Token]
unwrapPred (AS_BASIC.Pred_item xs _) = xs

-- adds a predicate = prop to an signature
addPred :: Sign.Sign -> [Id.Token] -> Sign.Sign
addPred sig [] = sig
addPred sig (x:xs) = addPred (Sign.addToSig sig (Id.simpleIdToId x)) xs

-- | Retrieve the formulas out of a basic spec
makeFormulas :: 
    AS_BASIC.BASIC_SPEC
    -> [AS_Anno.Named (AS_BASIC.FORMULA)]
makeFormulas (AS_BASIC.Basic_spec bspec) = retrieveFormulaItems bspec []

-- Helper for makeFormulas
retrieveFormulaItems ::
    [AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)]
    -> [AS_Anno.Named (AS_BASIC.FORMULA)]
    -> [AS_Anno.Named (AS_BASIC.FORMULA)]
retrieveFormulaItems (x:xs) axs = 
    case (AS_Anno.item x) of 
      (AS_BASIC.Pred_decl _) -> retrieveFormulaItems xs axs 
      (AS_BASIC.Axiom_items ax) -> retrieveFormulaItems xs $ recurseIntoAxioms ax axs
retrieveFormulaItems [] axs = axs

-- Recursion into the Axioms
recurseIntoAxioms :: [AS_Anno.Annoted (AS_BASIC.FORMULA)] 
                     -> [AS_Anno.Named (AS_BASIC.FORMULA)]
                     -> [AS_Anno.Named (AS_BASIC.FORMULA)]
recurseIntoAxioms [] formulae = formulae
recurseIntoAxioms (x:xs) formulae = recurseIntoAxioms xs $ addFormula x formulae

--  Add a formula to a named list of formulas
addFormula :: AS_Anno.Annoted (AS_BASIC.FORMULA) 
           -> [AS_Anno.Named (AS_BASIC.FORMULA)]
           -> [AS_Anno.Named (AS_BASIC.FORMULA)]             
addFormula f formulae = formulae ++ [AS_Anno.emptyName $ AS_Anno.item f] 

basicAnalysis :: AS_BASIC.BASIC_SPEC 
              -> Sign.Sign
              -> GlobalAnnos.GlobalAnnos
              -> Result.Result (
                                AS_BASIC.BASIC_SPEC
                               ,Sign.Sign
                               ,[AS_Anno.Named (AS_BASIC.FORMULA)]                              
                               )
basicAnalysis bs sig ga = Result.Result [] $ Just (bs, makeSig bs sig, makeFormulas bs)

-- Wrapper for the interface defined in Logic.Logic
basicPropositionalAnalysis :: (
                               AS_BASIC.BASIC_SPEC
                              , Sign.Sign
                              , GlobalAnnos.GlobalAnnos
                              )
                           -> Result.Result (
                                             AS_BASIC.BASIC_SPEC
                                            ,Sign.Sign
                                            ,[AS_Anno.Named (AS_BASIC.FORMULA)]
                                            )
basicPropositionalAnalysis (bs, sig, ga) = basicAnalysis bs sig ga
