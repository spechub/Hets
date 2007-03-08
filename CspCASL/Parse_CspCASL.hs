-- Parse_CspCASL.hs
--
-- WIP parser for CSP-CASL.
-- 
-- Maintainer: Andy Gimblett <a.m.gimblett@swan.ac.uk>
--
-- Changelog:
--  2005.11.04.1239 AMG v1.0
--                      Created (new version of CSP-CASL parser).

{- Parse_CspCASL.hs -- WIP parser for CSP-CASL.

This module contains a work-in-progress parser for a subset of
CSP-CASL.

2005.11.04 AMG

-}

module CspCASL.Parse_CspCASL (
    basicCspCaslSpec, dataDefn
) where

import Text.ParserCombinators.Parsec

import CASL.Parse_AS_Basic (basicSpec)
import Common.AnnoState (AParser, asKey)
import Common.Keywords (endS)
import Common.Trace

import CspCASL.AS_CspCASL
import CspCASL.AS_CspCASL_Process
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process (csp_casl_process)

basicCspCaslSpec :: AParser st BASIC_CSP_CASL_SPEC
-- The following is horrible, since if the spec _does_ end with "end",
-- it'll be parsed twice, the first time failing.  Alas, the more
-- sensible version (afterwards, commented out), doesn't work, and I
-- don't know why not.
basicCspCaslSpec = try (do asKey dataS
                           d <- dataDefn
                           asKey processS
                           p <- csp_casl_process
                           eof
                           return (Basic_Csp_Casl_Spec d p)
                       )
                   <|> (do asKey dataS
                           d <- dataDefn
                           asKey processS
                           p <- csp_casl_process
                           (asKey endS)
                           eof
                           return (Basic_Csp_Casl_Spec d p)
                       )

bling = strace "h" "g"

-- Hmmm, well, if this is the broken version, I'm not surprised.  The
-- try should be around endS, not eof.
--
--cspCaslSpec = do asKey dataS
--                 d <- dataDefn
--                 asKey processS
--                 p <- processDefn
--                 (asKey endS)
--                 (try eof)
--                 return (Csp_Casl_Spec d p)

dataDefn :: AParser st DATA_DEFN
dataDefn = do d <- basicSpec csp_casl_keywords
              return (Spec d)

processDefn :: AParser st PROCESS
processDefn = do p <- csp_casl_process
                 return p
