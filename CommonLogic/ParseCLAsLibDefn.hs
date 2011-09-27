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
  maybeText <- return $ runParser (many basicSpec) (emptyAnnos ()) "" contents
  case maybeText of
      Right bs -> return $ convertToLibDefN filename $ reverse bs
      Left x -> error $ "Error parsing CLIF-File." ++ show x

-- maps imports in basic spec to global definition links (extensions) in
-- development graph
convertToLibDefN :: FilePath -> [BASIC_SPEC] -> LIB_DEFN
convertToLibDefN filename bs =
  let fn = convertFileToLibStr filename
      knownSpecs = map (\(i,b) -> specName i b fn) $ zip [0..] bs
  in  Lib_defn
        (emptyLibName fn)
        (concat $ foldl (
            \r bn -> (convertBS knownSpecs bn : r)
          ) [] $ zip bs knownSpecs
        )
        nullRange
        []

-- Creates Nodes in the Logic Graph.
-- Also gives each non-named text a unique name in the graph.
convertBS :: [NAME] -> (BASIC_SPEC, NAME) -> [Anno.Annoted LIB_ITEM]
convertBS knownSpecs (b,n) =
  let imports = getImports b
      missingTexts = filter (\i -> not $ elem i knownSpecs) imports
  in  map (\m -> emptyAnno $ Download_items
                  (emptyLibName $ tokStr m)
                  [Item_name $ m]
                  nullRange
            ) missingTexts
        ++ [emptyAnno $ Spec_defn
          n
          emptyGenericity
          (createSpec imports b)
          nullRange]

-- one importation is an extension
-- many importations are an extension of a union
createSpec :: [NAME] -> BASIC_SPEC -> Anno.Annoted SPEC
createSpec imports b =
  let bs = emptyAnno $ Struc.Basic_spec (G_basic_spec CommonLogic b) nullRange
  in  case imports of
          [] -> bs
          _  -> emptyAnno $ Extension [
              (case imports of
                   [n] -> cnvimport n
                   _   -> emptyAnno $ Union (map cnvimport imports) nullRange)
              , bs
            ] nullRange

-- converts an imporation name to a SPEC
cnvimport :: NAME -> Annoted SPEC
cnvimport n = emptyAnno $ Spec_inst n [] nullRange

-- retrieves all importations from the text
getImports :: BASIC_SPEC -> [NAME]
getImports (CL.Basic_spec items) =
  concatMap getImports_textMrs $ map textFromBasicItems items

textFromBasicItems :: Anno.Annoted (BASIC_ITEMS) -> TEXT_MRS
textFromBasicItems abi = case Anno.item abi of
                              Axiom_items annoText -> Anno.item annoText

getImports_textMrs :: TEXT_MRS -> [NAME]
getImports_textMrs (t,_) = getImports_text t

getImports_text :: TEXT -> [NAME]
getImports_text (Text ps _) = map impToName $ filter isImportation ps
getImports_text (Named_text _ t _) = getImports_text t

isImportation :: PHRASE -> Bool
isImportation (Importation _) = True
isImportation _ = False

impToName :: PHRASE -> NAME
impToName (Importation (Imp_name n)) = n
impToName _ = undefined -- not necessary because filtered out

-- returns a unique name for a node
specName :: Int -> CL.BASIC_SPEC -> String -> NAME
specName i (CL.Basic_spec []) def = mkSimpleId $ def ++ "_" ++ show i
specName i (CL.Basic_spec [items]) def =
  case Anno.item items of
       Axiom_items ax ->
          case fst $ Anno.item ax of
               Text _ _ -> mkSimpleId $ def ++ "_" ++ show i
               Named_text n _ _ -> mkSimpleId n
specName i (CL.Basic_spec (_:_)) def = mkSimpleId $ def ++ "_" ++ show i

