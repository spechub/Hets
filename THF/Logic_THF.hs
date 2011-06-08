{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for THF.
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :
Stability   :
Portability :  non-portable (imports Logic)

Instance of class Logic for THF.
-}

module THF.Logic_THF where

import Logic.Logic

import ATC.ProofTree ()

import Common.ProofTree
import Common.DefaultMorphism

import THF.ATC_THF ()
import THF.Cons
import THF.As

data THF = THF deriving Show

instance Language THF where
 description _ =
  "THF is a Languag for Higher Order Logic from the TPTP standard.\n" ++
  "For further information please refer to" ++
  "http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html"

instance Logic.Logic.Syntax THF () () ()
    -- default implementation is fine!

instance Sentences THF Sentence Sign
                           THFMorphism Symbol where
    map_sen THF _ = return
    --sym_of THF =
    --sym_name THF =
    --print_named THF =
    -- other default implementations are fine
    simplify_sen THF _ = id
    --negation THF _ =
    --print_sign THF =
    --symmap_of THF _ =

instance StaticAnalysis THF () Sentence () ()
               Sign THFMorphism Symbol () where
         empty_signature THF = emptySign
         is_subsig THF _ _ = True
         subsig_inclusion THF = defaultInclusion

instance Logic THF () () Sentence () ()
                Sign THFMorphism Symbol () ProofTree where
         stability _ = Testing
