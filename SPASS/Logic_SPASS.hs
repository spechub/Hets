{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for SPASS.
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for SPASS.
-}


module SPASS.Logic_SPASS where

import Data.Dynamic

import Common.DynamicUtils 
import Common.DefaultMorphism

import SPASS.ATC_SPASS
import Logic.Logic

import SPASS.Sign
import SPASS.Print

#ifdef UNI_PACKAGE
import SPASS.Prove
#endif


{- |
  A dummy datatype for the LogicGraph and for identifying the right
  instances
-}
data SPASS = SPASS deriving (Show)
instance Language SPASS where
 description _ = 
  "SPASS - an automated theorem prover\n" ++
  "This logic corresponds to the logic of SPASS.\n" ++
  "See http://spass.mpi-sb.mpg.de/"

sentenceTc, signTc :: TyCon

sentenceTc      = mkTyCon "SPASS.Sign.SPTerm"
signTc          = mkTyCon "SPASS.Sign.Sign"

instance Typeable SPTerm where
    typeOf _ = mkTyConApp sentenceTc []
instance Typeable Sign where
    typeOf _ = mkTyConApp signTc []

instance Category SPASS Sign SPASSMorphism where
  dom SPASS = domOfDefaultMorphism
  cod SPASS = codOfDefaultMorphism
  ide SPASS = ideOfDefaultMorphism
  comp SPASS = compOfDefaultMorphism
  legal_obj SPASS = const True
  legal_mor SPASS = legalDefaultMorphism (legal_obj SPASS)

-- abstract syntax, parsing (and printing)

instance Logic.Logic.Syntax SPASS () () ()
    -- default implementation is fine!


instance Sentences SPASS Sentence () Sign SPASSMorphism ()  where
      map_sen SPASS _ s = return s
      print_named SPASS ga formula = 
        printFormula ga formula
-- the prover uses HTk and IO functions from uni
#ifdef UNI_PACKAGE
      provers SPASS = [spassProver] 
      cons_checkers SPASS = []
#endif
    -- other default implementations are fine

instance StaticAnalysis SPASS () Sentence ()
               () ()
               Sign 
               SPASSMorphism () ()  where
         sign_to_basic_spec SPASS _sigma _sens = ()
         empty_signature SPASS = emptySign
         inclusion SPASS = defaultInclusion (is_subsig SPASS)
         is_subsig SPASS = const $ const True -- TODO!!

instance Logic SPASS () () Sentence () ()
               Sign 
               SPASSMorphism () () () where
         stability _ = Testing
    -- again default implementations are fine
