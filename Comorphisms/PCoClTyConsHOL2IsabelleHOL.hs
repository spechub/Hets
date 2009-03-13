{- |
Module      :  $Header$
Description :  translating a HasCASL subset to Isabelle
Copyright   :  (c) C. Maeder, DFKI 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL without subtypes to
Isabelle-HOL.  Partial functions yield an option or bool result in
Isabelle. Case-terms and constructor classes are not supported yet.
-}

module Comorphisms.PCoClTyConsHOL2IsabelleHOL
    (PCoClTyConsHOL2IsabelleHOL(..)) where

import Comorphisms.PPolyTyConsHOL2IsaUtils
import Logic.Logic as Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.As
import HasCASL.Le as Le

import Isabelle.IsaSign as Isa
import Isabelle.Logic_Isabelle

-- | The identity of the comorphism
data PCoClTyConsHOL2IsabelleHOL = PCoClTyConsHOL2IsabelleHOL deriving Show

instance Language PCoClTyConsHOL2IsabelleHOL where
  language_name PCoClTyConsHOL2IsabelleHOL = "HasCASL2IsabelleOption"

instance Comorphism PCoClTyConsHOL2IsabelleHOL
               HasCASL Sublogic
               BasicSpec Le.Sentence SymbItems SymbMapItems
               Env Morphism
               Symbol RawSymbol ()
               Isabelle () () Isa.Sentence () ()
               Isa.Sign
               IsabelleMorphism () () ()  where
    sourceLogic PCoClTyConsHOL2IsabelleHOL = HasCASL
    sourceSublogic PCoClTyConsHOL2IsabelleHOL = noSubtypes
    targetLogic PCoClTyConsHOL2IsabelleHOL = Isabelle
    mapSublogic cid sl = if sl `isSubElem` sourceSublogic cid
                       then Just () else Nothing
    map_theory PCoClTyConsHOL2IsabelleHOL =
        mapTheory (Old Lift2Case) simpForOption
    map_morphism = mapDefaultMorphism
    map_sentence PCoClTyConsHOL2IsabelleHOL sign phi =
        transSentence sign (typeToks sign) (Old Lift2Case) simpForOption phi
    isInclusionComorphism PCoClTyConsHOL2IsabelleHOL = True
