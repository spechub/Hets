{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Class for logical frameworks
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.LogicFram where

import Logic.Logic

import qualified LF.Sign as Sign_LF
import qualified LF.Morphism as Morph_LF
import qualified LF.Logic_LF as Logic_LF

import qualified Isabelle.Logic_Isabelle as Logic_Isa
import qualified Isabelle.IsaSign as Sign_Isa

import qualified Maude.Logic_Maude as Logic_Maude
import qualified Maude.AS_Maude as AS_Maude
import qualified Maude.Sentence as Sen_Maude
import qualified Maude.Sign as Sign_Maude
import qualified Maude.Morphism as Morph_Maude
import qualified Maude.Symbol as Symbol_Maude

class Logic lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      => LogicFram lid sublogics basic_spec sentence
            symb_items symb_map_items sign
            morphism symbol raw_symbol proof_tree
      where
      -- | the base signature
      baseSig :: lid -> sign

instance LogicFram Logic_LF.LF () () () () () 
         Sign_LF.Sign Morph_LF.Morphism () () () where
   baseSig Logic_LF.LF = baseSigLF

instance LogicFram Logic_Isa.Isabelle () () Sign_Isa.Sentence () ()
         Sign_Isa.Sign Logic_Isa.IsabelleMorphism () () () where
   baseSig Logic_Isa.Isabelle = error $
       "Instance of LogicFram not yet implemented for Isabelle."

instance LogicFram Logic_Maude.Maude () AS_Maude.MaudeText Sen_Maude.Sentence
         () () Sign_Maude.Sign Morph_Maude.Morphism Symbol_Maude.Symbol
         Symbol_Maude.Symbol () where
   baseSig Logic_Maude.Maude = error $
       "Instance of LogicFram not yet implemented for Maude."

baseSigLF :: Sign_LF.Sign
baseSigLF =  
  let b = ""
      m = "Base"
      o = Sign_LF.Symbol b m "o"
      ded = Sign_LF.Symbol b m "ded"
      in Sign_LF.Sign b m 
           [Sign_LF.Def o Sign_LF.Type Nothing, 
            Sign_LF.Def ded (Sign_LF.Func [Sign_LF.Const o] Sign_LF.Type)
                            Nothing]

