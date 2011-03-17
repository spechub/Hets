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

import Text.ParserCombinators.Parsec
import Common.AS_Annotation (Annoted (..), emptyAnno)
import Common.AnnoState (AParser, asKey, colonT, equalT, anSemi, allAnnoParser)
import Common.Id
import Common.Lexer

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

cspBasicSpec :: AParser st CspBasicSpec
cspBasicSpec = do
  chans <- option [] chanDecls
  items <- processItems
  return (CspBasicSpec chans items)

chanDecls :: AParser st [CHANNEL_DECL]
chanDecls = do
  pluralKeyword channelS
  chanDecl `sepBy` anSemi

chanDecl :: AParser st CHANNEL_DECL
chanDecl = do
  vs <- commaSep1 channel_name
  colonT
  es <- csp_casl_sort
  return (ChannelDecl vs es)

processItems :: AParser st [Annoted PROC_ITEM]
processItems = do
  asKey processS
  procItems <|> fmap singleProcess csp_casl_process

{- Turn an unnamed singleton process into a declaration/equation.  THIS WHOLE
functions seems odd. Why would we want a fixed process "P" which communicates
over sort "singletonProcessSort". BUG? -}
singleProcess :: PROCESS -> [Annoted PROC_ITEM]
singleProcess p =
    map emptyAnno [Proc_Decl singletonProcessName [] singletonProcessAlpha,
     Proc_Eq (ParmProcname (PROCESS_NAME singletonProcessName) []) p]
        where singletonProcessName = mkSimpleId "P"
              singletonProcessAlpha =
                  ProcAlphabet [mkSimpleId "singletonProcessSort"]
                                nullRange

procItems :: AParser st [Annoted PROC_ITEM]
procItems = many1 procItem

procItem :: AParser st (Annoted PROC_ITEM)
procItem = try procDecl <|> procEq

procDecl :: AParser st (Annoted PROC_ITEM)
procDecl = do
  (pn, parms, comms) <- procNameWithParamsAndComms
  anSemi
  -- We don't currently allow annotations on declarations
  return (emptyAnno $ Proc_Decl pn parms comms)

procEq :: AParser st (Annoted PROC_ITEM)
procEq = allAnnoParser $ do
  pn <- parmProcname
  equalT
  p <- csp_casl_process
  return (Proc_Eq pn p)

parmProcname :: AParser st PARM_PROCNAME
parmProcname = do
  pn <- process_name
  pv <- option [] $ do
    try oParenT
    vs <- commaSep1 var
    cParenT
    return vs
  return (ParmProcname pn pv)
