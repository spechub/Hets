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
import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.Lexer

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

import Data.Maybe

instance AParsable CspBasicExt where
  aparser = cspBasicExt

cspBasicExt :: AParser st CspBasicExt
cspBasicExt =
  itemList cspKeywords channelS (const chanDecl) (\ l _ -> Channels l)
  <|> do
    p <- asKey processS
    auxItemList cspStartKeys [p] procItem
       (\ l _ -> ProcItems $ concatMap (\ al ->
                     map (`replaceAnnoted` al) (item al)) l)

chanDecl :: AParser st CHANNEL_DECL
chanDecl = do
  vs <- commaSep1 channel_name
  colonT
  es <- cspSortId
  return (ChannelDecl vs es)

procItem :: AParser st [PROC_ITEM]
procItem = do
  (fpn, as, mAl, isEq) <- procDeclOrEq
  let simpleFsts = all (isSimpleId . fst) as
      noColons = all (isNothing . snd) as
      eq = Proc_Eq (ParmProcname fpn $ map (idToSimpleId . fst) as)
  case mAl of
    Nothing ->
      if isEq && noColons && simpleFsts
      then do
        p <- csp_casl_process
        return [eq p]
      else fail "expected only simple vars as arguments"
    Just al -> let pal = ProcAlphabet al in case fpn of
      PROCESS_NAME spn
        | isEq && all (isJust . snd) as && simpleFsts
        -> do -- declaration and definition
          p <- csp_casl_process
          return
            [ Proc_Decl spn (map (fromJust . snd) as) pal, eq p ]
        | not isEq && noColons
        -> return [ Proc_Decl spn (map fst as) pal ]
      _ -> fail "unexpected process head"
