{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for SPASS.
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for SoftFOL.
-}


module SPASS.Logic_SPASS where

import Common.DefaultMorphism

import Logic.Logic

import SPASS.ATC_SPASS ()
import SPASS.Sign
import SPASS.Print

#ifdef UNI_PACKAGE
import SPASS.Prove
#endif


{- |
  A dummy datatype for the LogicGraph and for identifying the right
  instances
-}
data SoftFOL = SoftFOL deriving (Show)

instance Language SoftFOL where
 description _ = 
  "SoftFOL - Soft typed First Order Logic for Automatic Theorem Provers\n\n" ++
  "This logic corresponds to the logic of SPASS, \n"++
  "but the generation of TPTP is also possible.\n" ++
  "See http://spass.mpi-sb.mpg.de/\n"++
  "and http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Category SoftFOL Sign SoftFOLMorphism where
  dom SoftFOL = domOfDefaultMorphism
  cod SoftFOL = codOfDefaultMorphism
  ide SoftFOL = ideOfDefaultMorphism
  comp SoftFOL = compOfDefaultMorphism
  legal_obj SoftFOL = const True
  legal_mor SoftFOL = legalDefaultMorphism (legal_obj SoftFOL)

-- abstract syntax, parsing (and printing)

instance Logic.Logic.Syntax SoftFOL () () ()
    -- default implementation is fine!


instance Sentences SoftFOL Sentence () Sign SoftFOLMorphism ()  where
      map_sen SoftFOL _ s = return s
      print_named SoftFOL ga formula = 
        printFormula ga formula
-- the prover uses HTk and IO functions from uni
#ifdef UNI_PACKAGE
      provers SoftFOL = [spassProver
                       {-insert MathServ prover here-} ] 
      cons_checkers SoftFOL = []
#endif
    -- other default implementations are fine

instance StaticAnalysis SoftFOL () Sentence ()
               () ()
               Sign 
               SoftFOLMorphism () ()  where
         sign_to_basic_spec SoftFOL _sigma _sens = ()
         empty_signature SoftFOL = emptySign
         inclusion SoftFOL = defaultInclusion (is_subsig SoftFOL)
         is_subsig SoftFOL = const $ const True -- TODO!!

instance Logic SoftFOL () () Sentence () ()
               Sign 
               SoftFOLMorphism () () () where
         stability _ = Testing
    -- again default implementations are fine
