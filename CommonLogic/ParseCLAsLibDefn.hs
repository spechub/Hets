{- |
Module      :  $Header$
Copyright   :  Eugen Kuksa 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Analyses CommonLogic files.
-}

module CommonLogic.ParseCLAsLibDefn (parseCL_CLIF) where

import Common.Id
import Common.LibName
import Common.AS_Annotation as Anno
import Common.AnnoState

import Text.ParserCombinators.Parsec


import Logic.Grothendieck

import CommonLogic.AS_CommonLogic as CL
import CommonLogic.Logic_CommonLogic
import CommonLogic.Parse_CLIF (basicSpec)

import Syntax.AS_Library
import Syntax.AS_Structured as Struc


import System.IO

-- | call for CommonLogic CLIF-parser
parseCL_CLIF :: FilePath -> IO LIB_DEFN
parseCL_CLIF filename = do
  handle <- openFile filename ReadMode
  contents <- hGetContents handle
  maybeText <- return $ runParser basicSpec (emptyAnnos ()) "" contents
  case maybeText of
      Right bs -> return $ convertToLibDefN filename bs
      Left _ -> error $ "Error parsing CLIF-File."

convertToLibDefN :: FilePath -> BASIC_SPEC -> LIB_DEFN
convertToLibDefN filename bs = Lib_defn
  (emptyLibName $ convertFileToLibStr filename)
  [convertBS filename bs]
  nullRange
  []

convertBS :: FilePath -> BASIC_SPEC -> Anno.Annoted LIB_ITEM
convertBS filename bs = emptyAnno $ Spec_defn
  (mkSimpleId filename) --TODO: SPEC_NAME
  emptyGenericity
  (createSpec bs)
  nullRange

createSpec :: BASIC_SPEC -> Anno.Annoted SPEC
createSpec b =
  let bs = emptyAnno $ Struc.Basic_spec (G_basic_spec CommonLogic b) nullRange
  in  case getImports b of
          []  -> bs
          ns  -> emptyAnno $ Extension [
              (case ns of
                   [n] -> cnvimport n
                   _   -> emptyAnno $ Union (map cnvimport ns) nullRange)
              , bs
            ] nullRange

cnvimport :: NAME -> Annoted SPEC
cnvimport n = emptyAnno $ Spec_inst n [] nullRange

getImports :: BASIC_SPEC -> [NAME]
getImports (CL.Basic_spec items) = 
  concatMap getImports_text $ concatMap textsFromBasicItems items

textsFromBasicItems :: Anno.Annoted (BASIC_ITEMS) -> [TEXT]
textsFromBasicItems abi = case Anno.item abi of
                              Axiom_items annoTexts -> map Anno.item annoTexts

getImports_text :: TEXT -> [NAME]
getImports_text (Text ps _) = map impToName $ filter isImportation ps
getImports_text (Named_text _ t _) = getImports_text t

isImportation :: PHRASE -> Bool
isImportation (Importation _) = True
isImportation _ = False

impToName :: PHRASE -> NAME
impToName (Importation (Imp_name n)) = n
impToName _ = undefined -- not necessary because filtered out
