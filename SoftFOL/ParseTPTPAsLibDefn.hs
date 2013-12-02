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
import Common.IRI (simpleIdToIRI)
import Common.LibName
import Common.AS_Annotation hiding (isAxiom, isDef)

import Logic.Grothendieck

import Syntax.AS_Library
import Syntax.AS_Structured

import SoftFOL.Logic_SoftFOL
import SoftFOL.Sign
import SoftFOL.ParseTPTP

import Text.ParserCombinators.Parsec

createSpec :: [TPTP] -> Annoted SPEC
createSpec b = makeSpec $ G_basic_spec SoftFOL b

parseTPTP :: FilePath -> IO LIB_DEFN
parseTPTP filename = do
 s <- readFile filename
 case parse tptp filename s of
  Right b ->
   let lib = [makeLogicItem SoftFOL, makeSpecItem (simpleIdToIRI $ mkSimpleId $
               filename) $ createSpec b]
   in return $ Lib_defn (emptyLibName $ convertFileToLibStr filename)
                lib nullRange []
  Left err -> fail $ show err
