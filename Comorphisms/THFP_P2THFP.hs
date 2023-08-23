{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/THFP_P2THFP.hs
Description :  Comorphism from THFP_P to THFP
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  J. von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The comorphism from THFP to THF0.
-}

module Comorphisms.THFP_P2THFP where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation (Named)

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.Utils
import THF.Poly

data THFP_P2THFP = THFP_P2THFP deriving Show

instance Language THFP_P2THFP

instance Comorphism THFP_P2THFP
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP_P2THFP = THF
    sourceSublogic THFP_P2THFP = SL.tHFP_P
    targetLogic THFP_P2THFP = THF
    mapSublogic THFP_P2THFP sl = Just $ sl { SL.ext_Poly = False }
    map_theory THFP_P2THFP = trans_theory
    has_model_expansion THFP_P2THFP = True

trans_theory :: (SignTHF, [Named THFFormula])
                -> Result (SignTHF, [Named THFFormula])
trans_theory (sig, sentences1) = do
 (cs, sentences) <- infer (consts sig) sentences1
 let sig1 = sig {consts = cs}
 return (recreateSymbols sig1, sentences)
