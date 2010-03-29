{- |
Module      :  $Header$
Description :  Hets-to-OMDoc conversion
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

CASL implementation of the interface functions export_signToOmdoc,
export_morphismToOmdoc, export_senToOmdoc from class Logic. The actual
instantiation can be found in module CASL.Logic_CASL.
-}

module CASL.OMDocImport
    ( omdocToSym
    , omdocToSen
    ) where

import OMDoc.DataTypes
--import OMDoc.Export

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

import Common.DocUtils

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.Fold
import CASL.Quantification

import qualified Data.Map as Map
import Data.Maybe

----------------------------- TOPLEVEL Interface -----------------------------


type Env = NameMap Symbol

omdocToSym :: SigMapI Symbol -> TCElement -> String -> Result Symbol
omdocToSym _ _ _ = return $ idToSortSymbol $ mkId [mkSimpleId "dummyOmdocSym"]


omdocToSen :: SigMapI Symbol -> TCElement -> String
           -> Result (Maybe (Named (FORMULA f)))
omdocToSen _ _ _ = return Nothing


