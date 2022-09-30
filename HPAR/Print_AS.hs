
{- |
Module      :  ./HPAR/Print_AS.hs
Copyright   :  (c)R. Diaconescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  portable

printing rigid declarations
-}

module HPAR.Print_AS where

import CASL.ToDoc

import Common.Doc
import Common.Lexer
import Common.DocUtils
import Common.Keywords
import qualified Common.Lib.MapSet as MapSet

import HPAR.AS_Basic_HPAR
import HPAR.Sign
import qualified Data.Set as Set


