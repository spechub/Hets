{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable

   
   The embedding comorphism from HasCASL to Haskell.

-}

module Comorphisms.HasCASL2Haskell where

import Logic.Logic
import Logic.Comorphism

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Morphism

import Haskell.Logic_Haskell
import PNT
import PropPosSyntax
import Haskell.HatParser
import Haskell.HatAna
import ToHaskell.FromHasCASL

-- | The identity of the comorphism
data HasCASL2Haskell = HasCASL2Haskell deriving Show

instance Language HasCASL2Haskell -- default definition is okay

instance Comorphism HasCASL2Haskell
               HasCASL HasCASL_Sublogics
               BasicSpec Sentence SymbItems SymbMapItems
               Env
               Morphism
               Symbol RawSymbol ()
               Haskell ()
               HsDecls (HsDeclI PNT) () ()
               Sign
               HaskellMorphism
               () () () where
    sourceLogic _ = HasCASL
    sourceSublogic _ = top
    targetLogic _ = Haskell
    targetSublogic _ = ()
    map_morphism _ mor = do
       (sig1,_) <- map_sign HasCASL2Haskell (dom HasCASL mor)
       (sig2,_) <- map_sign HasCASL2Haskell (cod HasCASL mor)
       return (sig1,sig2)
    map_sentence _ = mapSingleSentence
    --map_symbol :: cid -> symbol1 -> Set symbol2
    map_theory _ = mapTheory

