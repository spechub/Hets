{- |
Module      :  $Header$
Description :  ProverState for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Prover state for propositional logic
-}

module Propositional.ProverState
    where

import qualified Common.AS_Annotation as AS_Anno
import qualified Propositional.AS_BASIC_Propositional as AS
import qualified Propositional.Sign as Sign
import qualified Propositional.Morphism as PMorphism
import qualified Common.ProofUtils as PUtil
import qualified Logic.Prover as LP

-- | Datatype for the prover state for propositional logic
data PropProverState = PropProverState
    {
      initialAxioms    :: [AS_Anno.Named AS.FORMULA]
    , initialSignature :: Sign.Sign
    , freeDefs         :: [LP.FreeDefMorphism AS.FORMULA PMorphism.Morphism]
    } deriving (Show)

-- | function to create prover state
propProverState :: Sign.Sign                  -- Input Signature
                -> [AS_Anno.Named AS.FORMULA] -- Input Formulae
                -> [LP.FreeDefMorphism AS.FORMULA PMorphism.Morphism]
                -- ^ free definitions
                -> PropProverState
propProverState sign aSens freedefs =
    let
        axioms = PUtil.prepareSenNames transSenName
                                       $ filter AS_Anno.isAxiom aSens
    in
      foldl insertSentence
      PropProverState
      {
        initialAxioms    = []
      , initialSignature = sign
      , freeDefs = freedefs
      } axioms

insertSentence :: PropProverState
               -> AS_Anno.Named AS.FORMULA
               -> PropProverState
insertSentence pState frm =
    let
        sign     = initialSignature pState
        axs      = initialAxioms    pState
        freedefs = freeDefs         pState
    in
      PropProverState
      {
        initialAxioms    = axs ++ [frm]
      , initialSignature = sign
      , freeDefs = freedefs
      }


-- | Translation of Sentence names
transSenName :: String -> String
transSenName str = str
