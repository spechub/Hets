{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

   Instance of class Logic for Isabelle (including Pure, HOL etc.).
-}


module Isabelle.Logic_Isabelle where

import Data.Dynamic
import Common.DynamicUtils 

import Isabelle.IsaSign
import Isabelle.IsaPrint
#ifdef UNI_PACKAGE
import Isabelle.IsaProve
#endif

import Logic.Logic
import Common.Lib.Pretty
import Common.AS_Annotation
import Common.PrettyPrint
import ATC.IsaSign

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data Isabelle = Isabelle deriving (Show)
instance Language Isabelle where
 description _ = 
  "Isabelle - a generic theorem prover\n" ++
  "This logic corresponds to the logic of Isabelle,\n" ++
  "a weak intuitionistic type theory\n" ++
  "Also, the logics encoded in Isabelle, like FOL, HOL, HOLCF, ZF " ++ 
  "are made available\n" ++
  "See http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"

sentenceTc, signTc :: TyCon

sentenceTc      = mkTyCon "Isabelle.Sign.Sentence"
signTc          = mkTyCon "Isabelle.Sign.Sign"

instance Typeable Sentence where
    typeOf _ = mkTyConApp sentenceTc []
instance Typeable Sign where
    typeOf _ = mkTyConApp signTc []

instance Category Isabelle Sign ()  
    where
         -- ide :: id -> object -> morphism
	 ide Isabelle _ = ()
         -- comp :: id -> morphism -> morphism -> Maybe morphism
	 comp Isabelle _ _ = Just ()
         -- dom, cod :: id -> morphism -> object
	 dom Isabelle _ = emptySign
	 cod Isabelle _ = emptySign
         -- legal_obj :: id -> object -> Bool
	 legal_obj Isabelle _ = True -- ??? too simplistic
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor Isabelle _ = False

-- abstract syntax, parsing (and printing)

instance Logic.Logic.Syntax Isabelle () () ()
    -- default implementation is fine!


instance Sentences Isabelle Sentence () Sign () ()  where
      map_sen Isabelle () s = return s
      print_named Isabelle ga (NamedSen lab sen) = 
	(if null lab then empty 
	else text lab <+> colon <> space) <> printText0 ga sen
#ifdef UNI_PACKAGE
      provers Isabelle = [isabelleProver] 
#endif
    -- other default implementations are fine

instance StaticAnalysis Isabelle () Sentence ()
               () ()
               Sign 
               () () ()  where
         sign_to_basic_spec Isabelle _sigma _sens = ()
         empty_signature Isabelle = emptySign

instance Logic Isabelle () () Sentence () ()
               Sign 
               () () () ()
    -- again default implementations are fine
