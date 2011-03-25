{- |
Module      :  $Header$
Description :  Parser for CspCASL specifications
Copyright   :  (c) Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  a.m.gimblett@swan.ac.uk
Stability   :  experimental
Portability :  portable

Parser for CSP-CASL specifications.
-}

module CspCASL.Parse_CspCASL () where

import Text.ParserCombinators.Parsec
import Common.AnnoState
import Common.Lexer

import CspCASL.AS_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

instance AParsable CspBasicExt where
  aparser = cspBasicExt

cspBasicExt :: AParser st CspBasicExt
cspBasicExt =
  itemList cspKeywords channelS (const chanDecl) (\ l _ -> Channels l)
  <|> do
    p <- asKey processS
    auxItemList (startCspKeywords ++ startKeyword)
      [p] procItem (\ l _ -> ProcItems l)

chanDecl :: AParser st CHANNEL_DECL
chanDecl = do
  vs <- commaSep1 channel_name
  colonT
  es <- cspSortId
  return (ChannelDecl vs es)

procItem :: AParser st PROC_ITEM
procItem = try procDecl <|> procEq

procDecl :: AParser st PROC_ITEM
procDecl = do
  (pn, parms, comms) <- procNameWithParamsAndComms
  return (Proc_Decl pn parms comms)

procEq :: AParser st PROC_ITEM
procEq = do
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
