{- |
Module      :  $Header$
Description :  Isabelle Abstract syntax constants for CSP-Prover operations
Copyright   :  (c) Liam O'Reilly and Markus Roggenbach,
                   Swansea University 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  csliam@swansea.ac.uk
Stability   :  provisional
Portability :  portable

Isabelle Abstract syntax constants for CSP-Prover operations.
-}

module CspCASLProver.CspProverConsts
    ( cspProverbinEqF
    , cspProver_NamedProcOp
    , cspProver_skipOp
    , cspProver_stopOp
    , cspProver_divOp
    , cspProver_runOp
    , cspProver_chaosOp
    , cspProver_action_prefixOp
    , cspProver_external_prefix_choiceOp
    , cspProver_internal_prefix_choiceOp
    , cspProver_sequenceOp
    , cspProver_external_choiceOp
    , cspProver_internal_choiceOp
    , cspProver_interleavingOp
    , cspProver_synchronousOp
    , cspProver_general_parallelOp
    , cspProver_alphabetised_parallelOp
    , cspProver_hidingOp
    , cspProver_renamingOp
    , cspProver_conditionalOp
    , cspProver_chan_nondeterministic_sendOp
    , cspProver_chan_sendOp
    , cspProver_chan_recOp
) where

import Isabelle.IsaSign as IsaSign
import Isabelle.IsaConsts (binVNameAppl, con, termAppl)

-- Symbols for CspProver
-- These symbols and priorities have come from the CSP-Prover source code

-- | binary junctors

cspProverEqV :: VName
cspProverEqV = VName "op =F" $ Just $ AltSyntax "(_ =F/ _)" [50, 51] 50

cspProverbinEqF :: Term -> Term -> Term
cspProverbinEqF = binVNameAppl cspProverEqV

-- | Name Process symbol
cspProver_NamedProcS :: String
cspProver_NamedProcS = "Proc_name"
cspProver_NamedProcAltS :: String
cspProver_NamedProcAltS = "($ _)"
cspProver_NamedProcAltArgPrios :: [Int]
cspProver_NamedProcAltArgPrios = [900]
cspProver_NamedProcAltOpPrio :: Int
cspProver_NamedProcAltOpPrio = 90

-- | SKIP primitive process symbol
cspProver_skipS :: String
cspProver_skipS = "SKIP"

-- | STOP primitive process symbol
cspProver_stopS :: String
cspProver_stopS = "STOP"

-- | DIV primitive process symbol
cspProver_divS :: String
cspProver_divS = "DIV"

-- | RUN primitive process symbol
cspProver_runS :: String
cspProver_runS = "??? RUN ??? - NOT YET DONE"

-- | CHAOS primitive process symbol
cspProver_chaosS :: String
cspProver_chaosS = "??? CHAOS ??? - NOT YET DONE"

-- | Action prefix operator symbols
cspProver_action_prefixS :: String
cspProver_action_prefixS = "Action_prefix"
cspProver_action_prefixAltS :: String
cspProver_action_prefixAltS = "(_ -> _)"
cspProver_action_prefixAltArgPrios :: [Int]
cspProver_action_prefixAltArgPrios = [150,80]
cspProver_action_prefixAltOpPrio :: Int
cspProver_action_prefixAltOpPrio = 80

-- | External prefix choice operator symbols
cspProver_external_prefix_choiceS :: String
cspProver_external_prefix_choiceS = "External_pre_choice"
cspProver_external_prefix_choiceAltS :: String
cspProver_external_prefix_choiceAltS = "(? _:_ -> _)"
cspProver_external_prefix_choiceAltArgPrios :: [Int]
cspProver_external_prefix_choiceAltArgPrios = [900,900,80]
cspProver_external_prefix_choiceAltOpPrio :: Int
cspProver_external_prefix_choiceAltOpPrio = 80

-- | Internal prefix choice operator symbols
cspProver_internal_prefix_choiceS :: String
cspProver_internal_prefix_choiceS = "Internal_pre_choice"
cspProver_internal_prefix_choiceAltS :: String
cspProver_internal_prefix_choiceAltS = "(! _:_ -> _)"
cspProver_internal_prefix_choiceAltArgPrios :: [Int]
cspProver_internal_prefix_choiceAltArgPrios = [900,900,80]
cspProver_internal_prefix_choiceAltOpPrio :: Int
cspProver_internal_prefix_choiceAltOpPrio = 80

-- | Sequence combinator operator symbols
cspProver_sequenceS :: String
cspProver_sequenceS = "Seq_compo"
cspProver_sequenceAltS :: String
cspProver_sequenceAltS = "(_ ;; _)"
cspProver_sequenceAltArgPrios :: [Int]
cspProver_sequenceAltArgPrios = [79,78]
cspProver_sequenceAltOpPrio :: Int
cspProver_sequenceAltOpPrio = 78

-- | External choice operator symbols
cspProver_external_choiceS :: String
cspProver_external_choiceS = "Ext_choice"
cspProver_external_choiceAltS :: String
cspProver_external_choiceAltS = "( _ [+] _)"
cspProver_external_choiceAltArgPrios :: [Int]
cspProver_external_choiceAltArgPrios = [72,73]
cspProver_external_choiceAltOpPrio :: Int
cspProver_external_choiceAltOpPrio = 72

-- | Internal choice operator symbols
cspProver_internal_choiceS :: String
cspProver_internal_choiceS = "Int_choice"
cspProver_internal_choiceAltS :: String
cspProver_internal_choiceAltS = "(_ |~| _)"
cspProver_internal_choiceAltArgPrios :: [Int]
cspProver_internal_choiceAltArgPrios = [64,65]
cspProver_internal_choiceAltOpPrio :: Int
cspProver_internal_choiceAltOpPrio = 64

-- | Interleaving parallel operator symbols
cspProver_interleavingS :: String
cspProver_interleavingS = "Interleave"
cspProver_interleavingAltS :: String
cspProver_interleavingAltS = "(_ ||| _)"
cspProver_interleavingAltArgPrios :: [Int]
cspProver_interleavingAltArgPrios = [76,77]
cspProver_interleavingAltOpPrio :: Int
cspProver_interleavingAltOpPrio = 76

-- | Synchronous parallel operator symbols
cspProver_synchronousS :: String
cspProver_synchronousS = "Synchro"
cspProver_synchronousAltS :: String
cspProver_synchronousAltS = "(_ || _)"
cspProver_synchronousAltArgPrios :: [Int]
cspProver_synchronousAltArgPrios = [76,77]
cspProver_synchronousAltOpPrio :: Int
cspProver_synchronousAltOpPrio = 76

-- | Generalised parallel operator symbols
cspProver_general_parallelS :: String
cspProver_general_parallelS =  "Parallel"
cspProver_general_parallelAltS :: String
cspProver_general_parallelAltS = "(_ |[_]| _)"
cspProver_general_parallelAltArgPrios :: [Int]
cspProver_general_parallelAltArgPrios = [76,0,77]
cspProver_general_parallelAltOpPrio :: Int
cspProver_general_parallelAltOpPrio = 76

-- | Alphabetised parallel operator symbols
cspProver_alphabetised_parallelS :: String
cspProver_alphabetised_parallelS = "Alpha_parallel"
cspProver_alphabetised_parallelAltS :: String
cspProver_alphabetised_parallelAltS = "(_ |[_,_]| _)"
cspProver_alphabetised_parallelAltArgPrios :: [Int]
cspProver_alphabetised_parallelAltArgPrios = [76,0,0,77]
cspProver_alphabetised_parallelAltOpPrio :: Int
cspProver_alphabetised_parallelAltOpPrio = 76

-- | Hiding operator symbols
cspProver_hidingS :: String
cspProver_hidingS = "Hiding"
cspProver_hidingAltS :: String
cspProver_hidingAltS = "(_ -- _)"
cspProver_hidingAltArgPrios :: [Int]
cspProver_hidingAltArgPrios = [84,85]
cspProver_hidingAltOpPrio :: Int
cspProver_hidingAltOpPrio = 85

-- | Renaming operator symbols
cspProver_renamingS :: String
cspProver_renamingS = "Renaming"
cspProver_renamingAltS :: String
cspProver_renamingAltS = "(_ [[_]])"
cspProver_renamingAltArgPrios :: [Int]
cspProver_renamingAltArgPrios = [84,0]
cspProver_renamingAltOpPrio :: Int
cspProver_renamingAltOpPrio = 84

-- | Conditional operator symbols
cspProver_conditionalS :: String
cspProver_conditionalS = "IF"
cspProver_conditionalAltS :: String
cspProver_conditionalAltS = "(IF _ THEN _ ELSE _)"
cspProver_conditionalAltArgPrios :: [Int]
cspProver_conditionalAltArgPrios = [900,88,88]
cspProver_conditionalAltArgOpPrio :: Int
cspProver_conditionalAltArgOpPrio = 88

-- | Channel non-deterministic send operator symbols
cspProver_chan_nondeterministic_sendS :: String
cspProver_chan_nondeterministic_sendS = "Nondet_send_prefix"
cspProver_chan_nondeterministic_sendAltS :: String
cspProver_chan_nondeterministic_sendAltS = "(_ !? _ : _ -> _)"
cspProver_chan_nondeterministic_sendAltArgPrios :: [Int]
cspProver_chan_nondeterministic_sendAltArgPrios = [900,900,1000,80]
cspProver_chan_nondeterministic_sendAltArgOpPrio :: Int
cspProver_chan_nondeterministic_sendAltArgOpPrio = 80

-- | Channel send operator symbols
cspProver_chan_sendS :: String
cspProver_chan_sendS = "Send_prefix"
cspProver_chan_sendAltS :: String
cspProver_chan_sendAltS = "(_ ! _ -> _)"
cspProver_chan_sendAltArgPrios :: [Int]
cspProver_chan_sendAltArgPrios = [900,1000,80]
cspProver_chan_sendAltArgOpPrio :: Int
cspProver_chan_sendAltArgOpPrio = 80

-- | Channel receive operator symbols
cspProver_chan_recS :: String
cspProver_chan_recS = "Rec_prefix"
cspProver_chan_recAltS :: String
cspProver_chan_recAltS = "(_ ? _ : _ -> _)"
cspProver_chan_recAltArgPrios :: [Int]
cspProver_chan_recAltArgPrios = [900,900,1000,80]
cspProver_chan_recAltArgOpPrio :: Int
cspProver_chan_recAltArgOpPrio = 80

-- Isabelle Terms representing the operations for CspProver

-- | Name Process operator
cspProver_NamedProcOp :: Term -> Term
cspProver_NamedProcOp =
    makeUnaryCspProverOp cspProver_NamedProcS
                         cspProver_NamedProcAltS
                         cspProver_NamedProcAltArgPrios
                         cspProver_NamedProcAltOpPrio

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
cspProver_action_prefixOp :: Term -> Term -> Term
cspProver_action_prefixOp =
    makeBinCspProverOp cspProver_action_prefixS
                       cspProver_action_prefixAltS
                       cspProver_action_prefixAltArgPrios
                       cspProver_action_prefixAltOpPrio

-- | External prefix choice operator
cspProver_external_prefix_choiceOp :: Term -> Term -> Term -> Term
cspProver_external_prefix_choiceOp =
    makeTriCspProverOp cspProver_external_prefix_choiceS
                       cspProver_external_prefix_choiceAltS
                       cspProver_external_prefix_choiceAltArgPrios
                       cspProver_external_prefix_choiceAltOpPrio

-- | Internal prefix choice operator
cspProver_internal_prefix_choiceOp :: Term -> Term -> Term -> Term
cspProver_internal_prefix_choiceOp =
    makeTriCspProverOp cspProver_internal_prefix_choiceS
                       cspProver_internal_prefix_choiceAltS
                       cspProver_internal_prefix_choiceAltArgPrios
                       cspProver_internal_prefix_choiceAltOpPrio

-- | Sequence combinator operator
cspProver_sequenceOp :: Term -> Term -> Term
cspProver_sequenceOp =
    makeBinCspProverOp cspProver_sequenceS
                       cspProver_sequenceAltS
                       cspProver_sequenceAltArgPrios
                       cspProver_sequenceAltOpPrio

-- | External choice operator
cspProver_external_choiceOp :: Term -> Term -> Term
cspProver_external_choiceOp =
    makeBinCspProverOp cspProver_external_choiceS
                       cspProver_external_choiceAltS
                       cspProver_external_choiceAltArgPrios
                       cspProver_external_choiceAltOpPrio

-- | Internal choice operator
cspProver_internal_choiceOp :: Term -> Term -> Term
cspProver_internal_choiceOp =
    makeBinCspProverOp cspProver_internal_choiceS
                       cspProver_internal_choiceAltS
                       cspProver_internal_choiceAltArgPrios
                       cspProver_internal_choiceAltOpPrio

-- | Interleaving parallel operator
cspProver_interleavingOp :: Term -> Term -> Term
cspProver_interleavingOp =
    makeBinCspProverOp cspProver_interleavingS
                       cspProver_interleavingAltS
                       cspProver_interleavingAltArgPrios
                       cspProver_interleavingAltOpPrio

-- | Synchronous parallel operator
cspProver_synchronousOp :: Term -> Term -> Term
cspProver_synchronousOp =
    makeBinCspProverOp cspProver_synchronousS
                       cspProver_synchronousAltS
                       cspProver_synchronousAltArgPrios
                       cspProver_synchronousAltOpPrio

-- | Generalised parallel operator
cspProver_general_parallelOp :: Term -> Term -> Term -> Term
cspProver_general_parallelOp =
    makeTriCspProverOp cspProver_general_parallelS
                       cspProver_general_parallelAltS
                       cspProver_general_parallelAltArgPrios
                       cspProver_general_parallelAltOpPrio

-- | Alphabetised parallel operator symbols
cspProver_alphabetised_parallelOp :: Term -> Term -> Term -> Term -> Term
cspProver_alphabetised_parallelOp =
    makeQuadCspProverOp cspProver_alphabetised_parallelS
                    cspProver_alphabetised_parallelAltS
                    cspProver_alphabetised_parallelAltArgPrios
                    cspProver_alphabetised_parallelAltOpPrio

-- | Hiding operator
cspProver_hidingOp :: Term -> Term -> Term
cspProver_hidingOp =
    makeBinCspProverOp cspProver_hidingS
                       cspProver_hidingAltS
                       cspProver_hidingAltArgPrios
                       cspProver_hidingAltOpPrio

-- | Renaming operator
cspProver_renamingOp :: Term -> Term -> Term
cspProver_renamingOp =
    makeBinCspProverOp cspProver_renamingS
                       cspProver_renamingAltS
                       cspProver_renamingAltArgPrios
                       cspProver_renamingAltOpPrio

-- | Conditional operator
cspProver_conditionalOp :: Term -> Term -> Term -> Term
cspProver_conditionalOp  =
    makeTriCspProverOp cspProver_conditionalS
                       cspProver_conditionalAltS
                       cspProver_conditionalAltArgPrios
                       cspProver_conditionalAltArgOpPrio

-- | Channel non-deterministic send operator
cspProver_chan_nondeterministic_sendOp :: Term -> Term -> Term -> Term -> Term
cspProver_chan_nondeterministic_sendOp  =
    makeQuadCspProverOp cspProver_chan_nondeterministic_sendS
                        cspProver_chan_nondeterministic_sendAltS
                        cspProver_chan_nondeterministic_sendAltArgPrios
                        cspProver_chan_nondeterministic_sendAltArgOpPrio

-- | Channel send operator
cspProver_chan_sendOp :: Term -> Term -> Term -> Term
cspProver_chan_sendOp  =
    makeTriCspProverOp cspProver_chan_sendS
                       cspProver_chan_sendAltS
                       cspProver_chan_sendAltArgPrios
                       cspProver_chan_sendAltArgOpPrio

-- | Channel receive operator
cspProver_chan_recOp :: Term -> Term -> Term -> Term -> Term
cspProver_chan_recOp  =
    makeQuadCspProverOp cspProver_chan_recS
                        cspProver_chan_recAltS
                        cspProver_chan_recAltArgPrios
                        cspProver_chan_recAltArgOpPrio

-- | Create an Isabelle Term representing a (Unary) CspProver operator
--   with no alternative syntax
makeCspProverOpNoAlt :: String -> Term
makeCspProverOpNoAlt opName =
    con $ VName opName $ Nothing

-- | Create an Isabelle Term representing a CspProver operator with
--   alternative syntax for a single parameter
makeUnaryCspProverOp :: String -> String -> [Int] -> Int -> Term -> Term
makeUnaryCspProverOp opName altSyntax altArgPrios altOpPrio t1 =
    let vname = VName opName $ Just $ AltSyntax altSyntax altArgPrios altOpPrio
    in termAppl (con vname) t1

-- | Create an Isabelle Term representing a CspProver operator with
--   alternative syntax for two parameters
makeBinCspProverOp :: String -> String -> [Int] -> Int -> Term -> Term -> Term
makeBinCspProverOp opName altSyntax altArgPrios altOpPrio t1 t2 =
    let vname = VName opName $ Just $ AltSyntax altSyntax altArgPrios altOpPrio
    in binVNameAppl vname t1 t2

-- | Create an Isabelle Term representing a CspProver operator (with 3
--   parameters) with alternative syntax
makeTriCspProverOp :: String -> String -> [Int] -> Int -> Term -> Term ->
                      Term -> Term
makeTriCspProverOp opName altSyntax altArgPrios altOpPrio t1 t2 t3 =
    let vname = VName opName $ Just $ AltSyntax altSyntax altArgPrios altOpPrio
    in termAppl (binVNameAppl vname t1 t2) t3

-- | Create an Isabelle Term representing a CspProver operator (with 4
--   parameters) with alternative syntax
makeQuadCspProverOp :: String -> String -> [Int] -> Int -> Term -> Term ->
                       Term -> Term -> Term
makeQuadCspProverOp opName altSyntax altArgPrios altOpPrio t1 t2 t3 t4 =
    let vname = VName opName $ Just $ AltSyntax altSyntax altArgPrios altOpPrio
    in termAppl (termAppl (binVNameAppl vname t1 t2) t3) t4
