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

module CspCASL.Parse_CspCASL (cspBasicExt) where

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
  itemList cspKeywords channelS (const chanDecl) Channels
  <|> do
    p <- asKey processS
    auxItemList cspStartKeys [p] procItem ProcItems

chanDecl :: AParser st CHANNEL_DECL
chanDecl = do
  vs <- commaSep1 channel_name
  colonT
  es <- cspSortId
  return (ChannelDecl vs es)

procItem :: AParser st PROC_ITEM
procItem = do
  ep <- procDeclOrDefn
  case ep of
    Left (fpn, vs) -> do
      p <- csp_casl_process
      return $ Proc_Eq (ParmProcname fpn vs) p
    Right (pn, eas, al) -> case eas of
      Left ss -> return $ Proc_Decl pn ss al
      Right vds -> do
        p <- csp_casl_process
        return $ Proc_Defn pn vds al p
