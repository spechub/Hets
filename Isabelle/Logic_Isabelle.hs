{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Isabelle/Logic_Isabelle.hs
Description :  Isabelle instance of class Logic
Copyright   :  (c) Till Mossakowski, Uni Bremen 2002-2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic)

Instance of class Logic for Isabelle (including Pure, HOL etc.).
-}

module Isabelle.Logic_Isabelle where

import Common.DefaultMorphism
import Common.Id

import Logic.Logic

import Isabelle.ATC_Isabelle ()
import Isabelle.IsaSign
import Isabelle.IsaPrint
import Isabelle.IsaProve

type IsabelleMorphism = DefaultMorphism Sign

{- a dummy datatype for the LogicGraph and for identifying the right
instances -}
data Isabelle = Isabelle deriving Show

instance Language Isabelle where
 description _ =
  "Isabelle - a generic theorem prover\n" ++
  "This logic corresponds to the logic of Isabelle,\n" ++
  "a weak intuitionistic type theory\n" ++
  "Also, the logics encoded in Isabelle, like FOL, HOL, HOLCF, ZF " ++
  "are made available\n" ++
  "See http://www.cl.cam.ac.uk/Research/HVG/Isabelle/"

instance Logic.Logic.Syntax Isabelle () () () ()
    -- default implementation is fine!

instance GetRange Sentence

instance Sentences Isabelle Sentence Sign IsabelleMorphism () where
      map_sen Isabelle _ = return
      print_named Isabelle = printNamedSen
    -- other default implementations are fine

instance StaticAnalysis Isabelle () Sentence
               () ()
               Sign
               IsabelleMorphism () () where
         empty_signature Isabelle = emptySign
         is_subsig Isabelle = isSubSign
         subsig_inclusion Isabelle = defaultInclusion

instance Logic Isabelle () () Sentence () ()
               Sign
               IsabelleMorphism () () () where
         stability _ = Testing
    -- again default implementations are fine
         empty_proof_tree _ = ()
         provers Isabelle =
           [isabelleProver Emacs, isabelleProver JEdit, isabelleBatchProver]
         cons_checkers Isabelle = [isabelleConsChecker]

instance LogicalFramework Isabelle () () Sentence () () Sign IsabelleMorphism
  () () ()
