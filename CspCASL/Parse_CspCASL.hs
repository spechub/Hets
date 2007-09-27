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

import Text.ParserCombinators.Parsec (many1, try, (<|>), option, sepBy)

import Common.AnnoState (AParser, asKey, equalT, anSemi)
import Common.Id (genName)
import CASL.Formula

import CspCASL.AS_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process

cspBasicSpec :: AParser st CspBasicSpec
cspBasicSpec = do
    option [] $ do
      asKey "channel"
      varDecl csp_casl_keywords `sepBy` anSemi
      return []
    pp <- processPart
    return (CspBasicSpec [] pp)

processPart :: AParser st [PROC_EQ]
processPart = do
    asKey processS
    procEqs <|> fmap toDummyEq csp_casl_process
    where
      toDummyEq p = [(ProcEq dummyName p)]
      dummyName = ParmProcname singletonProcessName []
      -- Default name allocated to unnamed singleton processes.
      singletonProcessName = genName "P"

procEqs :: AParser st [PROC_EQ]
procEqs = many1 procEq

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
    pa <- procArgs
    return (ParmProcname pn pa)
