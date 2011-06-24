{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for THF.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for THF.
-}

module THF.Logic_THF where

import Logic.Logic

import ATC.ProofTree ()

import Common.ProofTree

import THF.ATC_THF ()
import THF.Cons
import THF.ParseTHF
-- import THF.StaticAnalysisTHF
-- import THF.ProveLeoII

data THF = THF deriving Show

instance Language THF where
 description _ =
  "THF is a Languag for Higher Order Logic from the TPTP standard.\n" ++
  "For further information please refer to" ++
  "http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Logic.Logic.Syntax THF BasicSpecTHF () () where
    parse_basic_spec THF = Just $ fmap BasicSpecTHF parseTHF
    -- remaining default implementations are fine!

instance Sentences THF SentenceTHF SignTHF
                           MorphismTHF SymbolTHF where
    map_sen THF _ = return
    --sym_name THF =
    --negation THF _ =
    -- other default implementations are fine

instance StaticAnalysis THF BasicSpecTHF SentenceTHF () ()
               SignTHF MorphismTHF SymbolTHF () where
         -- basic_analysis THF = Just basicAnalysis
         empty_signature THF = emptySign
         --is_subsig THF _ _ = True
         --subsig_inclusion THF = defaultInclusion

instance Logic THF () BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
         stability _ = Testing
