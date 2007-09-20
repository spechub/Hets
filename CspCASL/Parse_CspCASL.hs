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
    basicCspCaslSpec, dataPart
) where

import Text.ParserCombinators.Parsec

import CASL.Parse_AS_Basic (basicSpec)
import Common.AnnoState (AParser, asKey)
import Common.Id (equalS)
import Common.Keywords (endS)
import Common.Token (parseId)

import CspCASL.AS_CspCASL
import CspCASL.CspCASL_Keywords
import CspCASL.Parse_CspCASL_Process (csp_casl_process)

-- Ridiculous hack here.  basicCspCaslSpec' is essentially what we
-- want, but an optional 'end' is allowed afterwards.  I can't find a
-- way just (try (asKey end)) after p <- processDef, so we use this
-- stupid hackish withEnd combinator to Make It Work; unfortunately it
-- will parse the whole spec _twice_ if the end keyword is not
-- present.  Suckage!

-- This works but is nasty.
withMaybeEnd :: AParser st a -> AParser st b -> AParser st a
withMaybeEnd x y = try (do q <- x
                           y
                           return q)
                   <|> (do q <- x
                           return q)

-- This is more like what we want, but it doesn't work.
{-
withMaybeEndFail :: AParser st a -> AParser st b -> AParser st a
withMaybeEndFail x y = do q <- x
                          (try y)
                          return q
-}

basicCspCaslSpec :: AParser st BASIC_CSP_CASL_SPEC
basicCspCaslSpec = withMaybeEnd basicCspCaslSpec' (asKey endS)

basicCspCaslSpec' :: AParser st BASIC_CSP_CASL_SPEC
basicCspCaslSpec' = do asKey ccspecS
                       n <- specName
                       asKey equalS
                       d <- dataPart
                       p <- processPart
                       return (Basic_Csp_Casl_Spec n d p)

specName :: AParser st CCSPEC_NAME
specName = do s_name <- parseId csp_casl_keywords
              return s_name

dataPart :: AParser st DATA_PART
dataPart = do asKey dataS
              d <- basicSpec csp_casl_keywords
              return (DataPart d)

processPart :: AParser st PROCESS_PART
processPart = do asKey processS
                 p <- csp_casl_process
                 return (ProcessPart p)
