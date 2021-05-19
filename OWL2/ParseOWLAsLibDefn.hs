{- |
Module      :  ./OWL2/ParseOWLAsLibDefn.hs
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module OWL2.ParseOWLAsLibDefn (parseOWLAsLibDefn) where

import qualified OWL2.AS as AS
import OWL2.MS

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Common.Id
import Common.IRI
import Common.LibName
import Common.ResultT
import Common.AS_Annotation
import Common.Utils

import Logic.Grothendieck

import OWL2.Logic_OWL2
import OWL2.ParseOWL

import Syntax.AS_Library
import Syntax.AS_Structured


-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWLAsLibDefn :: Bool                  -- ^ Sets Option.quick
         -> FilePath              -- ^ local filepath or uri
         -> ResultT IO [LIB_DEFN] -- ^ map: uri -> OntologyFile
parseOWLAsLibDefn quick fn = do
   (imap, ontodocs) <- parseOWL quick fn
   return $ map (convertToLibDefN imap) ontodocs

createSpec :: OntologyDocument -> [SPEC_NAME] -> Annoted SPEC
createSpec o imps = addImports imps . makeSpec $ G_basic_spec OWL2 o

convertone :: OntologyDocument -> SPEC_NAME -> [SPEC_NAME] -> Annoted LIB_ITEM
convertone o oname i = makeSpecItem oname $ createSpec o i

convertToLibDefN :: Map.Map String String -> OntologyDocument -> LIB_DEFN
convertToLibDefN imap o = Lib_defn ln
    (makeLogicItem OWL2 : imp_libs ++ [convertone o oname imps2]) nullRange []
  where ont = ontology o
        il = Map.toList imap
        is = map snd il
        ln = case lookup libstr $ map (\ (a, b) -> (b, a)) il of
            Just s -> setFilePath $ tryToStripPrefix "file:" s
            Nothing -> setFilePath libstr
          $ iriLibName oname
        imps = imports ont
        imps2 = filter ((`elem` is) . show . setAngles False) imps
        oname = name ont
        libstr = show $ setAngles False oname
        imp_libs = map (addDownload False) imps2
