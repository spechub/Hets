{- |
Module      :  $Header$
Description :  Abstract syntax for COL extension of CASL
Copyright   :  (c) Till Mossakowski, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Abstract syntax for COL extension of CASL
  Only the added syntax is specified
-}

module COL.AS_COL where

import Common.Id
import Common.AS_Annotation
import CASL.AS_Basic_CASL

-- DrIFT command
{-! global: GetRange !-}

type COL_BASIC_SPEC = BASIC_SPEC () COL_SIG_ITEM ()

data COL_SIG_ITEM =
          Constructor_items [Annoted Id] Range
                 -- pos: ids
        | Observer_items [Annoted (Id, Maybe Int)] Range
                 -- pos: ids
             deriving (Eq, Show)


constructorS, constructorsS    :: String
constructorS = "constructor"
constructorsS = constructorS ++ "s"

observerS, observersS    :: String
observerS = "observer"
observersS = observerS ++ "s"

col_reserved_words :: [String]
col_reserved_words = [constructorS,constructorsS,observerS,observersS]
