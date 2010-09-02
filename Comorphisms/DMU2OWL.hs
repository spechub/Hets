{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  translating DMU xml to OWL
Copyright   :  (c) Christian Maeder, DFKI and Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

translating DMU xml to OWL using OntoDMU.jar by Marco Franke from BIBA
-}

module Comorphisms.DMU2OWL where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.ExtSign
import Common.GlobalAnnotations
import Common.ProofTree
import Common.Result
import Common.Utils

import DMU.Logic_DMU

import OWL.AS
import OWL.Logic_OWL
import OWL.Parse
import OWL.Morphism
import OWL.Sign
import OWL.StaticAnalysis
import OWL.Sublogic

import Text.ParserCombinators.Parsec

import Control.Monad

import System.Cmd (system)
import System.IO.Unsafe (unsafePerformIO)

-- | The identity of the comorphism
data DMU2OWL = DMU2OWL deriving Show

instance Language DMU2OWL -- default definition is okay

instance Comorphism DMU2OWL
   DMU () Text () () () Text (DefaultMorphism Text) () () ()
   OWL OWLSub OntologyFile Axiom SymbItems SymbMapItems
       Sign OWLMorphism Entity RawSymb ProofTree where
    sourceLogic DMU2OWL = DMU
    sourceSublogic DMU2OWL = top
    targetLogic DMU2OWL = OWL
    mapSublogic DMU2OWL _ = Just top
    map_theory DMU2OWL = mapTheory
    map_morphism DMU2OWL _ = return $ inclOWLMorphism emptySign emptySign
    has_model_expansion DMU2OWL = True
    is_weakly_amalgamable DMU2OWL = True
    isInclusionComorphism DMU2OWL = True

mapTheory :: (Text, [Named ()]) -> Result (Sign, [Named Axiom])
mapTheory = readOWL . unsafePerformIO . runOntoDMU . fromText . fst

runOntoDMU :: String -> IO String
runOntoDMU str = if null str then return "" else do
  ontoDMUpath <- getEnvDef "HETS_ONTODMU" "DMU/OntoDMU.jar"
  tmpFile <- getTempFile str "ontoDMU.xml"
  let outFile = tmpFile ++ ".het"
  system $ "java -jar " ++ ontoDMUpath ++ " -f " ++ tmpFile
    ++ " -o " ++ outFile
  readFile outFile

readOWL :: Monad m => String -> m (Sign, [Named Axiom])
readOWL str = case runParser (liftM2 const basicSpec eof) () "" str of
  Left err -> fail $ show err
  Right ontoFile -> case basicOWLAnalysis
    (ontoFile, emptySign, emptyGlobalAnnos) of
    Result ds ms -> case ms of
      Nothing -> fail $ showRelDiags 1 ds
      Just (_, ExtSign sig _, sens) -> return (sig, sens)

