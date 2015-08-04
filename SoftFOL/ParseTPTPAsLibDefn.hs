{- |
Module      :  $Header$
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

-}

module SoftFOL.ParseTPTPAsLibDefn (parseTPTP) where

import Common.Id
import Common.IRI
import Common.LibName
import Common.AS_Annotation

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.AS_Structured

import SoftFOL.Logic_SoftFOL
import SoftFOL.Sign
import SoftFOL.ParseTPTP

import Text.ParserCombinators.Parsec

createSpec :: [TPTP] -> Annoted SPEC
createSpec = makeSpec . G_basic_spec SoftFOL

parseTPTP :: String -> FilePath -> IO LIB_DEFN
parseTPTP s filename = case parse tptp filename s of
  Right b -> return $ Lib_defn
    (emptyLibName $ convertFileToLibStr filename)
    [ makeLogicItem SoftFOL
    , makeSpecItem (simpleIdToIRI $ mkSimpleId filename)
      $ createSpec b ]
    nullRange []
  Left err -> fail $ show err
