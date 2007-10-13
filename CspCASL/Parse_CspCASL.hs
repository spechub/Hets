{- |
Module      :  $Id$
Description :  Parser for CspCASL specifications
Copyright   :  (c) Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import CASL.AS_Basic_CASL (VAR)
import Common.AnnoState (AParser, asKey, colonT, equalT, anSemi)
import Common.Id (genName)
import Common.Lexer (commaSep1, cParenT, oParenT)

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.Core_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

cspBasicSpec :: AParser st CspBasicSpec
cspBasicSpec = do
    chans <- option [] $ do
                 choice [asKey channelS, asKey channelsS]
                 cds <- chanDecl `sepBy` anSemi
                 -- XXX how to have an _optional_ final semicolon here?
                 return cds
    items <- processItems
    let (decls, eqs) = splitProcItems items
    return (basicToCore (CspBasicSpec chans decls eqs))

chanDecl :: AParser st CHANNEL
chanDecl = do vs <- commaSep1 var
              colonT
              es <- event_set
              return (Channel vs es)

type PROC_ITEM = Either PROC_DECL PROC_EQ

processItems :: AParser st [PROC_ITEM]
processItems = do asKey processS
                  procItems <|> fmap singleProcess csp_casl_process

-- Turn an unnamed singleton process into a declaration/equation.
singleProcess :: PROCESS -> [PROC_ITEM]
singleProcess p =
    [Left (ProcDecl singletonProcessName [] FullAlphabet),
     Right (ProcEq (ParmProcname singletonProcessName []) p)]
        where singletonProcessName = genName "P"

splitProcItems :: [PROC_ITEM] -> ([PROC_DECL], [PROC_EQ])
splitProcItems i = ([x | Left x <- i], [x | Right x <- i])

procItems :: AParser st [PROC_ITEM]
procItems = many1 procItem

procItem :: AParser st PROC_ITEM
procItem = try (do pdcl <- procDecl
                   return (Left pdcl))
           <|> (do peq <- procEq
                   return (Right peq))

procDecl :: AParser st PROC_DECL
procDecl = do
    pn <- process_name
    parms <- option [] $ do
               try oParenT
               parms <- commaSep1 event_set
               cParenT
               return parms
    colonT
    es <- event_set
    return (ProcDecl pn parms es)

procEq :: AParser st PROC_EQ
procEq = do
    pn <- try (do
      pn <- parmProcname
      equalT
      return pn)
    p <- csp_casl_process
    return (ProcEq pn p)

parmProcname :: AParser st PARM_PROCNAME
parmProcname = do
    pn <- process_name
    pv <- procVars
    return (ParmProcname pn pv)

procVars :: AParser st [VAR]
procVars = do try oParenT
              vs <- commaSep1 var
              cParenT
              return vs
           <|> return []
