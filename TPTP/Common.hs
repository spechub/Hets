{- |
Module      :  ./TPTP/Common.hs
Description :  Common functions for TPTP handling.
Copyright   :  (c) Eugen Kuksa University of Magdeburg 2017
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Eugen Kuksa <kuksa@iks.cs.ovgu.de>
Stability   :  provisional

-}

module TPTP.Common where

import Common.IRI
import Common.Id

import Data.Text (pack, replace, unpack)

-- The TPTP library uses filenames like AGT027^1.p which are not IRI compliant.
-- They need to be escaped.
-- In order to display the filename anyway, the unescaped IRI is saved as the
-- name of the spec.
-- These functions are only used for file names (in includes) and spec names.

escapeTPTPFilePath :: String -> String
escapeTPTPFilePath s = unpack $ replace (pack "^") (pack "%5E") (pack s)

unescapeTPTPFilePath :: String -> String
unescapeTPTPFilePath s = unpack $ replace (pack "%5E") (pack "^") (pack s)

unescapeTPTPFileToken :: Token -> Token
unescapeTPTPFileToken t = t { tokStr = unescapeTPTPFilePath $ tokStr t }

unescapeTPTPFileId :: Id -> Id
unescapeTPTPFileId i = i { getTokens = map unescapeTPTPFileToken $ getTokens i }

unescapeTPTPFileIRI :: IRI -> IRI
unescapeTPTPFileIRI i = i { iriPath = unescapeTPTPFileId $ iriPath i }
