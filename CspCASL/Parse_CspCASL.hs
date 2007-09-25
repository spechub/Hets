{- |
Module      :  $Id$
Description :  Parser for CspCASL specifications
Copyright   :  (c) 
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  

Parser for CSP-CASL specifications.

-}

module CspCASL.Parse_CspCASL (
    cspBasicSpec
) where

import Text.ParserCombinators.Parsec (sepBy1, try, (<|>))

import Common.AnnoState (AParser, asKey, colonT, equalT)
import Common.Lexer (commaSep1, cParenT, oParenT)

import CspCASL.AS_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process (csp_casl_process,
                                      event_set,
                                      process_name,
                                      var)

cspBasicSpec :: AParser st CspBasicSpec
cspBasicSpec = do pp <- processPart
                  return (CspBasicSpec [] pp)

processPart :: AParser st [PROC_EQ]
processPart = do asKey processS
                 peqs <- procEqs
                 return peqs

procEqs :: AParser st [PROC_EQ]
procEqs = procEq `sepBy1` (asKey semicolonS)

procEq :: AParser st PROC_EQ
procEq = do pn <- parmProcname
            equalT
            p <- csp_casl_process
            return (ProcEq pn p)

parmProcname :: AParser st PARM_PROCNAME
parmProcname = do pn <- process_name
                  pa <- procArgs
                  return (ParmProcname pn pa)

procArgs :: AParser st [PARG_DECL]
procArgs = do try oParenT
              pa <- (procArg `sepBy1` (asKey semicolonS))
              cParenT
              return pa
           <|> return []

procArg :: AParser st PARG_DECL
procArg = do vs <- commaSep1 var
             colonT
             es <- event_set
             return (PargDecl vs es)
