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

import qualified Data.Set as Set

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
        (emptyAnno (Logic_decl (Logic_name
                                  (mkSimpleId $ show CommonLogic)
                                  Nothing
                                  Nothing
                               ) nullRange)
          : (concat $ foldl (
                \r bn -> (convertBS knownSpecs bn : r)
              ) [] $ zip bs knownSpecs
            )
        )
        nullRange
        []

-- Creates Nodes in the Logic Graph.
-- Also gives each non-named text a unique name in the graph.
convertBS :: [NAME] -> (BASIC_SPEC, NAME) -> [Anno.Annoted LIB_ITEM]
convertBS knownSpecs (b,n) =
  let imports = getImports b
  in  concatMap (downloadIfNotKnown knownSpecs) imports
        ++ [emptyAnno $ Spec_defn
            n
            emptyGenericity
            (createSpec imports b)
            nullRange]
        ++ metarelsBS (knownSpecs++imports) b

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
getImports_textMrs (Text_mrs (t,_)) = getImports_text t

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
          case Anno.item ax of
               Text_mrs (Text _ _, _) -> mkSimpleId $ def ++ "_" ++ show i
               Text_mrs (Named_text n _ _, _) -> mkSimpleId n
specName i (CL.Basic_spec (_:_)) def = mkSimpleId $ def ++ "_" ++ show i

metarelsBS :: [NAME] -> BASIC_SPEC -> [Anno.Annoted LIB_ITEM]
metarelsBS knownSpecs (CL.Basic_spec abis) =
  concatMap (metarelsBI knownSpecs . Anno.item) abis

metarelsBI :: [NAME] -> BASIC_ITEMS -> [Anno.Annoted LIB_ITEM]
metarelsBI knownSpecs (Axiom_items (Anno.Annoted (Text_mrs (_,mrs)) _ _ _)) =
  concatMap (metarelsMR knownSpecs) $ Set.elems mrs

metarelsMR :: [NAME] -> METARELATION -> [Anno.Annoted LIB_ITEM]
metarelsMR knownSpecs mr = case mr of
  RelativeInterprets t1 delta t2 smaps ->
      concatMap (downloadIfNotKnown knownSpecs) [t1,delta,t2]
      ++ [emptyAnno $ View_defn
                      (mkSimpleId "RelativeInterprets")
                      emptyGenericity
                      (View_type
                        (emptyAnno (Union [cnvimport t1, cnvimport delta] nullRange))
                        (cnvimport t2)
                        nullRange)
                      [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                      nullRange]
  NonconservativeExtends t1 t2 smaps ->
      concatMap (downloadIfNotKnown knownSpecs) [t1,t2]
      ++ [emptyAnno $ View_defn
                      (mkSimpleId "NonconservativeExtends")
                      emptyGenericity
                      (View_type
                        (cnvimport t1)
                        (cnvimport t2)
                        nullRange)
                      [G_symb_map $ G_symb_map_items_list CommonLogic smaps]
                      nullRange]

downloadIfNotKnown :: [NAME] -> NAME -> [Anno.Annoted LIB_ITEM]
downloadIfNotKnown knownSpecs n =
  if elem n knownSpecs then []
  else [emptyAnno $ Download_items
                  (emptyLibName $ tokStr n)
                  [Item_name $ n]
                  nullRange]
