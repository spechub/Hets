{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
{- |
Module      :  ./OWL2/DMU2OWL2.hs
Description :  translating DMU xml to OWL
Copyright   :  (c) Christian Maeder, DFKI and Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

translating DMU xml to OWL using OntoDMU.jar by Marco Franke from BIBA
-}

module OWL2.DMU2OWL2 where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.DefaultMorphism
import Common.ExtSign
import Common.GlobalAnnotations
import Common.ProofTree
import Common.Result
import Common.Utils
import Common.Lib.State

import qualified Data.Map as Map

import DMU.Logic_DMU

import OWL2.AS
import OWL2.MS
import OWL2.Logic_OWL2
import OWL2.Morphism
import OWL2.Sign
import OWL2.StaticAnalysis
import OWL2.ProfilesAndSublogics
import OWL2.ManchesterParser
import OWL2.Symbols
import OWL2.Function
import OWL2.Extract

import Text.ParserCombinators.Parsec (eof, runParser)

import Control.Monad

import System.Directory
import System.IO.Unsafe (unsafePerformIO)

-- | The identity of the comorphism
data DMU2OWL2 = DMU2OWL2 deriving Show

instance Language DMU2OWL2 -- default definition is okay

instance Comorphism DMU2OWL2
   DMU () Text () () () Text (DefaultMorphism Text) () () ()
   OWL2 ProfSub OntologyDocument Axiom SymbItems SymbMapItems
       Sign OWLMorphism Entity RawSymb ProofTree where
    sourceLogic DMU2OWL2 = DMU
    sourceSublogic DMU2OWL2 = top
    targetLogic DMU2OWL2 = OWL2
    mapSublogic DMU2OWL2 _ = Just top
    map_theory DMU2OWL2 = mapTheory
    map_morphism DMU2OWL2 _ = return $ inclOWLMorphism emptySign emptySign
    has_model_expansion DMU2OWL2 = True
    is_weakly_amalgamable DMU2OWL2 = True
    isInclusionComorphism DMU2OWL2 = True

mapTheory :: (Text, [Named ()]) -> Result (Sign, [Named Axiom])
mapTheory = readOWL . unsafePerformIO . runOntoDMU . fromText . fst

runOntoDMU :: String -> IO String
runOntoDMU str = if null str then return "" else do
  ontoDMUpath <- getEnvDef "HETS_ONTODMU" "DMU/OntoDMU.jar"
  tmpFile <- getTempFile str "ontoDMU.xml"
  (_, out, _) <- executeProcess "java"
    ["-jar", ontoDMUpath, "-f", tmpFile] ""
  removeFile tmpFile
  return out

readOWL :: Monad m => String -> m (Sign, [Named Axiom])
readOWL str = case runParser (liftM2 const ((basicSpec True) Map.empty) eof) () "" str of
  Left er -> fail $ show er
  Right ontoFile -> let
    newont = function Expand (StringMap $ prefixDeclaration ontoFile) ontoFile
    newstate = execState (extractSign newont) emptySign
    in case basicOWL2Analysis
    (ontoFile, newstate, emptyGlobalAnnos) of
    Result ds ms -> case ms of
      Nothing -> fail $ showRelDiags 1 ds
      Just (_, ExtSign sig _, sens) -> return (sig, sens)
