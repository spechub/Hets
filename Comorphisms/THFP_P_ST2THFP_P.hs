{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism removing syntactic sugar
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  J. von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Remove the syntactic sugar provided by the ShortTypes extension
-}

module Comorphisms.THFP_P_ST2THFP_P where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.ShortTypes (trans_theory)

data THFP_P_ST2THFP_P = THFP_P_ST2THFP_P deriving Show

instance Language THFP_P_ST2THFP_P

instance Comorphism THFP_P_ST2THFP_P
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP_P_ST2THFP_P = THF
    sourceSublogic THFP_P_ST2THFP_P = SL.tHFP_P_ST
    targetLogic THFP_P_ST2THFP_P = THF
    mapSublogic THFP_P_ST2THFP_P sl = Just $ sl { SL.ext_ShortTypes = False }
    map_theory THFP_P_ST2THFP_P = trans_theory
    has_model_expansion THFP_P_ST2THFP_P = True
