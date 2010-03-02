{-# LINE 1 "Reduce/Analysis.hs" #-}
{- |
Module      :  $Header$
Description :  Abstract syntax for reduce
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

-}


module Propositional.Analysis
    (
     basicPropositionalAnalysis
    ,mkStatSymbItems
    ,mkStatSymbMapItem
    ,inducedFromMorphism
    ,inducedFromToMorphism
    , signatureColimit
    )
    where

import Common.ExtSign
import Common.Lib.Graph
import Common.SetColimit
import Data.Graph.Inductive.Graph
import Reduce.Sign as Sign
import qualified Common.AS_Annotation as AS_Anno
import qualified Common.GlobalAnnotations as GlobalAnnos
import qualified Common.Id as Id
import qualified Common.Result as Result
import qualified Data.List as List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Reduce.AS_BASIC_Reduce 
import Reduce.Morphism 
import Reduce.Symbol 


-- | Datatype for formulas with diagnosis data
data DIAG_FORM = DiagForm
    {
      formula :: AS_Anno.Named (CMD),
      diagnosis :: Result.Diagnosis
    }

-- | takes a signature and a formula, analyzes it and returns a formula with diagnosis
analyzeFormula :: Sign.Sign -> CMD -> DIAG_FORM
analyzeFormula sign f = DiagForm  { formula = f, diagnosis = {
                                                Result.diagKind = Result.Hint
                                              , Result.diagString = "All fine"
                                              , Result.diagPos    = AS_Anno.opt_pos nullRange
                                              }}
                        
-- | Extracts the axioms and the signature of a basic spec
splitSpec :: BASIC_SPEC -> Sign.Sign -> [Sign.Sign,DIAG_FORM]
splitSpec (Basic_spec bspec) sig =
    List.foldl (\item (sign,axs) -> 
                    case (AS_Anno.item item) of
                      (Op_decl (Op_item tokens range)) -> (addTokens sign tokens, axs)
                      (Axiom_items cmds) -> (sign, addAxioms cmds axs)
               )
            []  bspec

-- | adds the specified tokens to the signature
addTokens :: Sign.Sign -> [Token] -> Sign.Sign
addTokens sign tokens = foldl (\item res -> (addToSig res (simpleIdToId item))) sign tokens

-- | adds the cmds to the already specified axioms
addAxioms :: [DIAG_FORM] -> [CMD] -> [DIAG_FORM]
addAxioms fs cmds = foldl (\item res -> (analyzeFormula item):res) fs cmds


-- | stepwise extends an initially empty signature by the basic spec bs. The resulting spec contains analyzed axioms in it. 
-- The result contains: 1) the basic spec 2) the new signature + the added symbols 3) sentences of the spec 
-- op-> items kommen in signatur
-- axioms -> kommen in liste der sätze
basicPropositionalAnalysis (bs, sig, _) =
   Result.Result diags $ if exErrs then Nothing else
     Just (bs, ExtSign sigItems declaredSyms, formulae)
    where
      bsSig     = makeSig bs sig
      sigItems  = msign bsSig
      declaredSyms = Set.map Symbol.Symbol
        $ Set.difference (items sigItems) $ items sig
      bsForm    = makeFormulas bs sigItems
      formulae  = map formula bsForm
      diags     = map diagnosis bsForm ++ tdiagnosis bsSig
      exErrs    = Result.hasErrors diags


