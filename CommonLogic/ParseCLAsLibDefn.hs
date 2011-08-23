{- |
Module      :  $Header$
Copyright   :  Eugen Kuksa 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Analyses CommonLogic files.
-}

module CommonLogic.ParseCLAsLibDefn where --(parseCL_CLIF) where

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
import System.FilePath.Windows (splitFileName)

-- | call for CommonLogic CLIF-parser
parseCL_CLIF :: FilePath -> IO LIB_DEFN
parseCL_CLIF filename = do
  handle <- openFile filename ReadMode
  contents <- hGetContents handle
  maybeText <- return $ runParser (many basicSpec) (emptyAnnos ()) "" contents
  case maybeText of
      Right bs -> return $ convertToLibDefN filename $ reverse bs
      Left _ -> error $ "Error parsing CLIF-File."

convertToLibDefN :: FilePath -> [BASIC_SPEC] -> LIB_DEFN
convertToLibDefN filename bs = Lib_defn
  (emptyLibName $ convertFileToLibStr filename)
  (snd $ foldl (
      \(i,r) b -> (i+1, convertBS i (convertFileToLibStr filename) b : r)
    ) (0,[]) bs
  )
  nullRange
  []

convertBS :: Int -> String -> BASIC_SPEC -> Anno.Annoted LIB_ITEM
convertBS i filename b = emptyAnno $ Spec_defn
  (specName i b filename)
  emptyGenericity
  (createSpec b)
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
getImports (CL.Basic_spec items) =  getImports_text $ textsFromBasicItems items

textsFromBasicItems :: Anno.Annoted (BASIC_ITEMS) -> TEXT
textsFromBasicItems abi = case Anno.item abi of
                              Axiom_items annoText -> Anno.item annoText

getImports_text :: TEXT -> [NAME]
getImports_text (Text ps _) = map impToName $ filter isImportation ps
getImports_text (Named_text _ t _) = getImports_text t

isImportation :: PHRASE -> Bool
isImportation (Importation _) = True
isImportation _ = False

impToName :: PHRASE -> NAME
impToName (Importation (Imp_name n)) = n
impToName _ = undefined -- not necessary because filtered out

specName :: Int -> CL.BASIC_SPEC -> String -> NAME
specName i (CL.Basic_spec items) def =
  case Anno.item items of
       Axiom_items ax ->
          case Anno.item ax of
               Text _ _ -> mkSimpleId (def ++ "_" ++ show i)
               Named_text n _ _ -> mkSimpleId n


