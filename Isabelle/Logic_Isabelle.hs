{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   Instance of class Logic for Isabelle (including Pure, HOL etc.).
-}


module Isabelle.Logic_Isabelle where

import Isabelle.IsaSign
import Logic.Logic
import Common.Result
import Common.Id
import ATC.IsaSign

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data Isabelle = Isabelle deriving (Show)
instance Language Isabelle  -- default definition is okay

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
	 legal_obj Isabelle _ = True -- ??? to simplistic
         -- legal_mor :: id -> morphism -> Bool
	 legal_mor Isabelle _ = False


-- abstract syntax, parsing (and printing)

instance Logic.Logic.Syntax Isabelle () () ()
      where 
         parse_basic_spec Isabelle = Nothing
	 parse_symb_items Isabelle = Nothing
	 parse_symb_map_items Isabelle = Nothing

instance Sentences Isabelle Sentence () Sign () ()  where
      map_sen Isabelle _morphism s = return s
      parse_sentence Isabelle = Nothing
      provers Isabelle = [] 
      cons_checkers Isabelle = []

instance StaticAnalysis Isabelle () Sentence ()
               () ()
               Sign 
               () () ()  where
         basic_analysis Isabelle = Nothing
         stat_symb_map_items Isabelle _ = 
            fatal_error "No symbol map analysis for Isabelle" nullPos
         stat_symb_items Isabelle _ = 
            fatal_error "No symbol map analysis for Isabelle" nullPos
	 ensures_amalgamability Isabelle _ = 
            fail "ensures_amalgamability nyi" -- ???

         sign_to_basic_spec Isabelle _sigma _sens = ()

         empty_signature Isabelle = emptySign
         signature_union Isabelle sigma1 sigma2 = 
            fatal_error "No signature union for Isabelle" nullPos
         morphism_union Isabelle _ _ = 
            fatal_error "No morphism union for Isabelle" nullPos
	 final_union Isabelle _ _ = 
            fatal_error "No signature union for Isabelle" nullPos
{-
         is_subsig Isabelle = isSubSig
         inclusion Isabelle = sigInclusion
         cogenerated_sign Isabelle = cogeneratedSign
         generated_sign Isabelle = generatedSign
         induced_from_morphism Isabelle = inducedFromMorphism
         induced_from_to_morphism Isabelle = inducedFromToMorphism
-}

instance Logic Isabelle () () Sentence () ()
               Sign 
               () () () () where
         sublogic_names Isabelle _ = ["Isabelle"]
         all_sublogics Isabelle = [()]

         data_logic Isabelle = Nothing
