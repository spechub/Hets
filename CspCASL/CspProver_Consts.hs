{- |
Module      :
Description :  Isabelle Abstract syntax constants for CSP-Prover operations
Copyright   :  (c) Andy Gimblett, Liam O'Reilly and Markus Roggenbach, Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Isabelle Abstract syntax constants for CSP-Prover operations.
-}

module CspCASL.CspProver_Consts (
    cspProver_skipOp,
    cspProver_stopOp,
    cspProver_divOp,
    cspProver_runOp,
    cspProver_chaosOp,
    cspProver_act_prefixOp,
    cspProver_ext_prefix_choiceOp,
    cspProver_int_prefix_choiceOp,
    cspProver_sequenceOp,
    cspProver_external_choiceOp,
    cspProver_internal_choiceOp,
    cspProver_interleavingOp,
    cspProver_synchronousOp,
    cspProver_general_parallelOp,
    cspProver_alphabetised_parallelOp,
    cspProver_hidingOp,
    cspProver_renamingOp,
    cspProver_ifOp
) where

import Isabelle.IsaSign as IsaSign

-- Symbols for CspProver

-- SKIP primitive process symbol
cspProver_skipS :: String
cspProver_skipS = "SKIP"

-- STOP primitive process symbol
cspProver_stopS :: String
cspProver_stopS = "STOP"

-- DIV primitive process symbol
cspProver_divS :: String
cspProver_divS = "DIV"

-- RUN primitive process symbol
cspProver_runS :: String
cspProver_runS = "??? RUN ??? - NOT YET DONE"

-- CHAOS primitive process symbol
cspProver_chaosS :: String
cspProver_chaosS = "??? CHAOS ??? - NOT YET DONE"

-- Action prefix operator symbols
cspProver_act_prefixS :: String
cspProver_act_prefixS = "Act_prefix"
cspProver_act_prefixAltS :: String
cspProver_act_prefixAltS = "(_ -> _)"
cspProver_act_prefixAltArgPrios :: [Int]
cspProver_act_prefixAltArgPrios = [150,80]
cspProver_act_prefixAltOpPrio :: Int
cspProver_act_prefixAltOpPrio = 80

-- External prefix choice operator symbols
cspProver_ext_prefix_choiceS :: String
cspProver_ext_prefix_choiceS = "Ext_pre_choice"
cspProver_ext_prefix_choiceAltS :: String
cspProver_ext_prefix_choiceAltS = "(? _:_ -> _)"
cspProver_ext_prefix_choiceAltArgPrios :: [Int]
cspProver_ext_prefix_choiceAltArgPrios = [900,900,80]
cspProver_ext_prefix_choiceAltOpPrio :: Int
cspProver_ext_prefix_choiceAltOpPrio = 80

-- Internal prefix choice operator symbols
cspProver_int_prefix_choiceS :: String
cspProver_int_prefix_choiceS = "Int_pre_choice"
cspProver_int_prefix_choiceAltS :: String
cspProver_int_prefix_choiceAltS = "(! _:_ -> _)"
cspProver_int_prefix_choiceAltArgPrios :: [Int]
cspProver_int_prefix_choiceAltArgPrios = [900,900,80]
cspProver_int_prefix_choiceAltOpPrio :: Int
cspProver_int_prefix_choiceAltOpPrio = 80

-- Sequence combinator operator symbols
cspProver_sequenceS :: String
cspProver_sequenceS = "Seq_compo"
cspProver_sequenceAltS :: String
cspProver_sequenceAltS = "(_ ;; _)"
cspProver_sequenceAltArgPrios :: [Int]
cspProver_sequenceAltArgPrios = [79,78]
cspProver_sequenceAltOpPrio :: Int
cspProver_sequenceAltOpPrio = 78

-- External choice operator symbols
cspProver_external_choiceS :: String
cspProver_external_choiceS = "Ext_choice"
cspProver_external_choiceAltS :: String
cspProver_external_choiceAltS = "( _ [+] _)"
cspProver_external_choiceAltArgPrios :: [Int]
cspProver_external_choiceAltArgPrios = [72,73]
cspProver_external_choiceAltOpPrio :: Int
cspProver_external_choiceAltOpPrio = 72

-- Internal choice operator symbols
cspProver_internal_choiceS :: String
cspProver_internal_choiceS = "Int_choice"
cspProver_internal_choiceAltS :: String
cspProver_internal_choiceAltS = "(_ |~| _)"
cspProver_internal_choiceAltArgPrios :: [Int]
cspProver_internal_choiceAltArgPrios = [64,65]
cspProver_internal_choiceAltOpPrio :: Int
cspProver_internal_choiceAltOpPrio = 64

-- Interleaving parallel operator symbols
cspProver_interleavingS :: String
cspProver_interleavingS = "Interleave"
cspProver_interleavingAltS :: String
cspProver_interleavingAltS = "(_ ||| _)"
cspProver_interleavingAltArgPrios :: [Int]
cspProver_interleavingAltArgPrios = [76,77]
cspProver_interleavingAltOpPrio :: Int
cspProver_interleavingAltOpPrio = 76

-- Synchronous parallel operator symbols
cspProver_synchronousS :: String
cspProver_synchronousS = "Synchro"
cspProver_synchronousAltS :: String
cspProver_synchronousAltS = "(_ || _)"
cspProver_synchronousAltArgPrios :: [Int]
cspProver_synchronousAltArgPrios = [76,77]
cspProver_synchronousAltOpPrio :: Int
cspProver_synchronousAltOpPrio = 76

-- Generalised parallel operator symbols
cspProver_general_parallelS :: String
cspProver_general_parallelS =  "Parallel"
cspProver_general_parallelAltS :: String
cspProver_general_parallelAltS = "(_ |[_]| _)"
cspProver_general_parallelAltArgPrios :: [Int]
cspProver_general_parallelAltArgPrios = [76,0,77]
cspProver_general_parallelAltOpPrio :: Int
cspProver_general_parallelAltOpPrio = 76

-- Alphabetised parallel operator symbols
cspProver_alphabetised_parallelS :: String
cspProver_alphabetised_parallelS = "Alpha_parallel"
cspProver_alphabetised_parallelAltS :: String
cspProver_alphabetised_parallelAltS = "(_ |[_,_]| _)"
cspProver_alphabetised_parallelAltArgPrios :: [Int]
cspProver_alphabetised_parallelAltArgPrios = [76,0,0,77]
cspProver_alphabetised_parallelAltOpPrio :: Int
cspProver_alphabetised_parallelAltOpPrio = 76

-- Hiding operator symbols
cspProver_hidingS :: String
cspProver_hidingS = "Hiding"
cspProver_hidingAltS :: String
cspProver_hidingAltS = "(_ -- _)"
cspProver_hidingAltArgPrios :: [Int]
cspProver_hidingAltArgPrios = [84,85]
cspProver_hidingAltOpPrio :: Int
cspProver_hidingAltOpPrio = 85

-- Renaming operator symbols
cspProver_renamingS :: String
cspProver_renamingS = "Renaming"
cspProver_renamingAltS :: String
cspProver_renamingAltS = "(_ [[_]])"
cspProver_renamingAltArgPrios :: [Int]
cspProver_renamingAltArgPrios = [84,0]
cspProver_renamingAltOpPrio :: Int
cspProver_renamingAltOpPrio = 84

-- Conditional operator symbols
cspProver_ifS :: String
cspProver_ifS = "IF"
cspProver_ifAltS :: String
cspProver_ifAltS = "(IF _ THEN _ ELSE _)"
cspProver_ifAltArgPrios :: [Int]
cspProver_ifAltArgPrios = [900,88,88]
cspProver_ifAltArgOpPrio :: Int
cspProver_ifAltArgOpPrio = 88

-- Isabelle Terms representing the operations for CspProver

-- | SKIP primitive process operator
cspProver_skipOp :: Term
cspProver_skipOp = makeCspProverOpNoAlt cspProver_skipS

-- | STOP primitive process operator
cspProver_stopOp :: Term
cspProver_stopOp = makeCspProverOpNoAlt cspProver_stopS

-- | DIV primitive process operator
cspProver_divOp :: Term
cspProver_divOp = makeCspProverOpNoAlt cspProver_divS

-- | RUN primitive process operator
cspProver_runOp :: Term
cspProver_runOp = makeCspProverOpNoAlt cspProver_runS

-- | CHAOS primitive process operator
cspProver_chaosOp :: Term
cspProver_chaosOp = makeCspProverOpNoAlt cspProver_chaosS

-- | Action prefix operator
cspProver_act_prefixOp :: Term
cspProver_act_prefixOp =
    makeCspProverOp cspProver_act_prefixS
                    cspProver_act_prefixAltS
                    cspProver_act_prefixAltArgPrios
                    cspProver_act_prefixAltOpPrio

-- | External prefix choice operator
cspProver_ext_prefix_choiceOp :: Term
cspProver_ext_prefix_choiceOp =
    makeCspProverOp cspProver_ext_prefix_choiceS
                    cspProver_ext_prefix_choiceAltS
                    cspProver_ext_prefix_choiceAltArgPrios
                    cspProver_ext_prefix_choiceAltOpPrio

-- | Internal prefix choice operator
cspProver_int_prefix_choiceOp :: Term
cspProver_int_prefix_choiceOp =
    makeCspProverOp cspProver_int_prefix_choiceS
                    cspProver_int_prefix_choiceAltS
                    cspProver_int_prefix_choiceAltArgPrios
                    cspProver_int_prefix_choiceAltOpPrio

-- | Sequence combinator operator
cspProver_sequenceOp :: Term
cspProver_sequenceOp =
    makeCspProverOp cspProver_sequenceS
                    cspProver_sequenceAltS
                    cspProver_sequenceAltArgPrios
                    cspProver_sequenceAltOpPrio

-- | External choice operator
cspProver_external_choiceOp :: Term
cspProver_external_choiceOp =
    makeCspProverOp cspProver_external_choiceS
                    cspProver_external_choiceAltS
                    cspProver_external_choiceAltArgPrios
                    cspProver_external_choiceAltOpPrio

-- | Internal choice operator
cspProver_internal_choiceOp :: Term
cspProver_internal_choiceOp =
    makeCspProverOp cspProver_internal_choiceS
                    cspProver_internal_choiceAltS
                    cspProver_internal_choiceAltArgPrios
                    cspProver_internal_choiceAltOpPrio

-- | Interleaving parallel operator
cspProver_interleavingOp :: Term
cspProver_interleavingOp =
    makeCspProverOp cspProver_interleavingS
                    cspProver_interleavingAltS
                    cspProver_interleavingAltArgPrios
                    cspProver_interleavingAltOpPrio

-- | Synchronous parallel operator
cspProver_synchronousOp :: Term
cspProver_synchronousOp =
    makeCspProverOp cspProver_synchronousS
                    cspProver_synchronousAltS
                    cspProver_synchronousAltArgPrios
                    cspProver_synchronousAltOpPrio

-- | Generalised parallel operator
cspProver_general_parallelOp :: Term
cspProver_general_parallelOp =
    makeCspProverOp cspProver_general_parallelS
                    cspProver_general_parallelAltS
                    cspProver_general_parallelAltArgPrios
                    cspProver_general_parallelAltOpPrio

-- | Alphabetised parallel operator symbols
cspProver_alphabetised_parallelOp :: Term
cspProver_alphabetised_parallelOp =
    makeCspProverOp cspProver_alphabetised_parallelS
                    cspProver_alphabetised_parallelAltS
                    cspProver_alphabetised_parallelAltArgPrios
                    cspProver_alphabetised_parallelAltOpPrio

-- | Hiding operator
cspProver_hidingOp :: Term
cspProver_hidingOp =
    makeCspProverOp cspProver_hidingS
                    cspProver_hidingAltS
                    cspProver_hidingAltArgPrios
                    cspProver_hidingAltOpPrio

-- | Renaming operator
cspProver_renamingOp :: Term
cspProver_renamingOp =
    makeCspProverOp cspProver_renamingS
                    cspProver_renamingAltS
                    cspProver_renamingAltArgPrios
                    cspProver_renamingAltOpPrio

-- | Conditional operator
cspProver_ifOp :: Term
cspProver_ifOp  =
    makeCspProverOp cspProver_ifS
                    cspProver_ifAltS
                    cspProver_ifAltArgPrios
                    cspProver_ifAltArgOpPrio

-- Create an Isabelle Term representing a CspProver operator with alternative syntax
makeCspProverOp :: String -> String -> [Int] -> Int -> Term
makeCspProverOp opName altSyntax altArgPrios altOpPrio =
    Const {
        termName = VName {
                     new = (opName),
                     altSyn = Just (AltSyntax altSyntax altArgPrios altOpPrio)
                    },
        termType = Hide {
                     typ = Type {
                             typeId ="dummy",
                             typeSort = [IsaClass "type"],
                             typeArgs = []
                           },
                     kon = NA,
                     arit= Nothing
                   }
    }

-- Create an Isabelle Term representing a CspProver operator with no alternative syntax
makeCspProverOpNoAlt :: String -> Term
makeCspProverOpNoAlt opName =
    Const {
        termName = VName {
                     new = (opName),
                     altSyn = Nothing
                    },
        termType = Hide {
                     typ = Type {
                             typeId ="dummy",
                             typeSort = [IsaClass "type"],
                             typeArgs = []
                           },
                     kon = NA,
                     arit= Nothing
                   }
    }
