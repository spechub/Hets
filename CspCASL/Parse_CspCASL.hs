{- |
Module      :  $Id$
Description :  Parser for CspCASL specifications
Copyright   :  (c) Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  portable

Parser for CSP-CASL specifications.
-}

module CspCASL.Parse_CspCASL (
    cspBasicSpec
) where

import Text.ParserCombinators.Parsec (choice, many1, try, (<|>),
                                      option, sepBy)

import Common.AnnoState (AParser, asKey, colonT, equalT, anSemi)
import Common.Id
import Common.Lexer (commaSep1, commaT, cParenT, oParenT)

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

cspBasicSpec :: AParser st CspBasicSpec
cspBasicSpec = do chans <- option [] $ chanDecls
                  items <- processItems
                  return (CspBasicSpec chans items)

chanDecls :: AParser st [CHANNEL_DECL]
chanDecls = do choice [asKey channelS, asKey channelsS]
               cds <- chanDecl `sepBy` anSemi
               -- XXX optional final semicolon how?
               return cds

chanDecl :: AParser st CHANNEL_DECL
chanDecl = do vs <- commaSep1 channel_name
              colonT
              es <- csp_casl_sort
              return (ChannelDecl vs es)

processItems :: AParser st [PROC_ITEM]
processItems = do asKey processS
                  procItems <|> fmap singleProcess csp_casl_process

-- Turn an unnamed singleton process into a declaration/equation.
singleProcess :: PROCESS -> [PROC_ITEM]
singleProcess p =
    [Proc_Decl singletonProcessName [] singletonProcessAlpha,
     Proc_Eq (ParmProcname singletonProcessName []) p]
        where singletonProcessName = mkSimpleId "P"
              singletonProcessAlpha =
                  (ProcAlphabet [mkSimpleId "singletonProcessSort"]
                                nullRange)

procItems :: AParser st [PROC_ITEM]
procItems = many1 procItem

procItem :: AParser st PROC_ITEM
procItem = try procDecl
           <|> procEq

procDecl :: AParser st PROC_ITEM
procDecl = do pn <- process_name
              parms <- option [] $ do try oParenT
                                      parms <- commaSep1 csp_casl_sort
                                      cParenT
                                      return parms
              colonT
              cts <- (comm_type `sepBy` commaT)
              anSemi
              return (Proc_Decl pn parms (ProcAlphabet cts (getRange cts)))

procEq :: AParser st PROC_ITEM
procEq = do pn <- parmProcname
            equalT
            p <- csp_casl_process
            return (Proc_Eq pn p)

parmProcname :: AParser st PARM_PROCNAME
parmProcname = do pn <- process_name
                  pv <- option [] $ do try oParenT
                                       vs <- commaSep1 var
                                       cParenT
                                       return vs
                  return (ParmProcname pn pv)
