{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
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

import ATC.ProofTree ()

import Common.ProofTree
import Common.ProverTools

import Data.Monoid

import Logic.Logic

import THF.ATC_THF ()
import THF.Cons
import THF.StaticAnalysisTHF
import THF.ProveLeoII
import THF.Sign
import THF.Print

-- TODO implement more instance methods

data THF = THF deriving Show

instance Language THF where
    description _ =
        "THF is a language for Higher Order Logic from the TPTP standard.\n" ++
        "For further information please refer to" ++
        "http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Monoid BasicSpecTHF where
    mempty = BasicSpecTHF BSTHF0 []
    mappend (BasicSpecTHF t1 l1) (BasicSpecTHF t2 l2) =
        BasicSpecTHF (max t1 t2) $ l1 ++ l2

instance Logic.Logic.Syntax THF BasicSpecTHF () () where
    parse_basic_spec THF = Just (basicSpec BSTHF0)
    -- remaining default implementations are fine!

instance Sentences THF SentenceTHF SignTHF MorphismTHF SymbolTHF where
    map_sen THF _ = return
    print_named THF = printNamedSentenceTHF
    {- sym_name THF =
    negation THF _ =
    other default implementations are fine -}

instance StaticAnalysis THF BasicSpecTHF SentenceTHF () ()
               SignTHF MorphismTHF SymbolTHF () where
    basic_analysis THF = Just basicAnalysis
    empty_signature THF = emptySign
    signature_union THF = sigUnion
    signatureDiff THF = sigDiff
    intersection THF = sigIntersect
    -- is_subsig THF _ _ = True


{- In order to find the LeoII prover there must be an entry in the
PATH environment variable leading to the leo executable
(The executable leo.opt is not supported. In this case there should be a link
called leo, or something like that.) -}
instance Logic THF () BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    stability THF = Testing
    provers THF = [] ++ unsafeProverCheck "leo" "PATH" leoIIProver
