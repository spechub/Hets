module CspCASL.CspProver_Consts where

import Isabelle.IsaConsts as IsaConsts
import Isabelle.IsaSign as IsaSign

-- | interleaving parallel operator
cspProver_interleavingS :: String
cspProver_interleavingS = "|||"

-- | synchronous parallel operator
cspProver_synchronousS :: String
cspProver_synchronousS = "||"

-- | Open generalised parallel
cspProver_general_parallel_openS :: String
cspProver_general_parallel_openS = "|["

-- | Close generalised parallel
cspProver_general_parallel_closeS :: String
cspProver_general_parallel_closeS = "]|"

-- | Open alpabetised parallel
cspProver_alpha_parallel_openS :: String
cspProver_alpha_parallel_openS = "|["

-- | Separator in alpabetised parallel
cspProver_alpha_parallel_sepS :: String
cspProver_alpha_parallel_sepS = ","

-- | Close alpabetised parallel
cspProver_alpha_parallel_closeS :: String
cspProver_alpha_parallel_closeS = "]|"

-- | External choice
cspProver_external_choiceS :: String
cspProver_external_choiceS = "[+]"

-- | Internal choice
cspProver_internal_choiceS :: String
cspProver_internal_choiceS = "|~|"

-- | Sequences of processes
cspProver_sequenceS :: String
cspProver_sequenceS = ";;"

-- | Prefix processes
cspProver_prefixS :: String
cspProver_prefixS = "->"

-- | External prefix opener
cspProver_external_prefixS :: String
cspProver_external_prefixS = "?"

-- | Internal prefix opener
cspProver_internal_prefixS :: String
cspProver_internal_prefixS = "!"

-- | Hiding
cspProver_hidingS :: String
cspProver_hidingS = "--"

-- | Open a renaming
cspProver_renaming_openS :: String
cspProver_renaming_openS = "[["

-- | Close a renaming
cspProver_renaming_closeS :: String
cspProver_renaming_closeS = "]]"

-- Dont need the next two
-- | Open parentheses
--parens_openS :: String
--parens_openS = "("

-- | Close parentheses
--parens_closeS :: String
--parens_closeS = ")"

-- | "RUN" primitive process
cspProver_runS :: String
cspProver_runS = "??? RUN ???"

-- | "CHAOS" primitive process
cspProver_chaosS :: String
cspProver_chaosS = "??? CHAOS ???"

-- | "div" primitive process
cspProver_divS :: String
cspProver_divS = "??? DIV ???"

-- | "SKIP" primitive process
cspProver_skipS :: String
cspProver_skipS = "SKIP"

-- | "STOP" primitive process
cspProver_stopS :: String
cspProver_stopS = "STOP"

-- These are inplace of common symbols
-- | CspProver IF Symbol
cspProver_ifS :: String
cspProver_ifS = "IF"

-- | CspProver THEN Symbol
cspProver_thenS :: String
cspProver_thenS = "THEN"

-- | CspProver ELSE Symbol
cspProver_elseS :: String
cspProver_elseS = "ELSE"

-- | CspProver colon Symbol
cspProver_colonS :: String
cspProver_colonS = ":"


cspProver_sequenceOp :: Term
cspProver_sequenceOp = Const {
          termName= VName {
                      new = (cspProver_sequenceS),
                      altSyn = Just (AltSyntax ("(_ " ++ cspProver_sequenceS ++ " _)") [50,51] 50)
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

cspProver_general_parallelOp :: Term
cspProver_general_parallelOp = Const {
          termName= VName {
                      new = (cspProver_sequenceS),
                      altSyn = Just (AltSyntax ("(_ " ++ cspProver_general_parallel_openS
                                                        ++ "_"
                                                        ++ cspProver_general_parallel_closeS
                                                        ++ " _)") [76,0,77] 76)
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
