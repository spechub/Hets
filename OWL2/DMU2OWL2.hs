{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}
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

import DMU.Logic_DMU

import OWL2.AS
import OWL2.MS
import OWL2.Logic_OWL2
import OWL2.Parse
import OWL2.Morphism
import OWL2.Sign
import OWL2.StaticAnalysis
import OWL2.Sublogic
import OWL2.ManchesterParser
import OWL2.Symbols

import qualified Data.Set as Set
import Data.List
import qualified Data.Map as Map

import Text.ParserCombinators.Parsec (eof, runParser)

import Control.Monad

import System.Directory
import System.Process
import System.IO.Unsafe (unsafePerformIO)

-- | The identity of the comorphism
data DMU2OWL2 = DMU2OWL2 deriving Show

instance Language DMU2OWL2 -- default definition is okay

instance Comorphism DMU2OWL2
   DMU () Text () () () Text (DefaultMorphism Text) () () ()
   OWL2 OWLSub OntologyDocument Axiom SymbItems SymbMapItems
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
  (_, out, _) <- readProcessWithExitCode "java"
    ["-jar",  ontoDMUpath, "-f", tmpFile] ""
  removeFile tmpFile
  return out

readOWL :: Monad m => String -> m (Sign, [Named Axiom])
readOWL str = case runParser (liftM2 const basicSpec eof) () "" str of
  Left err -> fail $ show err
  Right ontoFile -> case basicOWL2Analysis
    (ontoFile, emptySign, emptyGlobalAnnos) of
    Result ds ms -> case ms of
      Nothing -> fail $ showRelDiags 1 ds
      Just (_, ExtSign sig _, sens) -> return (sig, sens)

addObjPropExpr :: ObjectPropertyExpression -> State Sign ()
addObjPropExpr = addEntity . Entity ObjectProperty . getObjRoleFromExpression

addDataPropExpr :: DataPropertyExpression -> State Sign ()
addDataPropExpr = addEntity . Entity DataProperty

addIndividual :: Individual -> State Sign ()
addIndividual = addEntity . Entity NamedIndividual

addAnnoProp :: AnnotationProperty -> State Sign ()
addAnnoProp = addEntity . Entity AnnotationProperty

addLiteral :: Literal -> State Sign ()
addLiteral (Literal _ ty) = case ty of
  Typed u -> addEntity $ Entity Datatype u
  _ -> return ()

addDType :: Datatype -> State Sign ()
addDType = addEntity . Entity Datatype

addDataRange :: DataRange -> State Sign ()
addDataRange dr = case dr of
  DataJunction _ lst -> mapM_ (\ cd -> addDataRange cd) lst
  DataComplementOf r -> addDataRange r
  DataOneOf cs -> mapM_ addLiteral cs
  DataType r fcs -> do
    addDType r
    mapM_ (addLiteral . snd) fcs

addFact :: Fact -> State Sign ()
addFact f = case f of
  ObjectPropertyFact _ obe _ ->
    do
      addObjPropExpr obe
  DataPropertyFact _ dpe _ ->
    do
      addDataPropExpr dpe


addDescription :: ClassExpression -> State Sign ()
addDescription desc = case desc of
  Expression u ->
      case u of
        QN _ "Thing" _ _ r -> addEntity $ Entity Class $
                          QN "owl" "Thing" False "" r
        QN _ "Nothing" _ _ r -> addEntity $ Entity Class $
                          QN "owl" "Nothing" False "" r
        v -> addEntity $ Entity Class v
  ObjectJunction _ ds -> mapM_ addDescription ds
  ObjectComplementOf d -> addDescription d
  ObjectOneOf is -> mapM_ addIndividual is
  ObjectValuesFrom _ opExpr d -> do
    addObjPropExpr opExpr
    addDescription d
  ObjectHasSelf opExpr -> addObjPropExpr opExpr
  ObjectHasValue opExpr i -> do
    addObjPropExpr opExpr
    addIndividual i
  ObjectCardinality (Cardinality _ _ opExpr md) -> do
    addObjPropExpr opExpr
    maybe (return ()) addDescription md
  DataValuesFrom _ dExp r -> do
    addDataPropExpr dExp
    addDataRange r
  DataHasValue dExp c -> do
    addDataPropExpr dExp
    addLiteral c
  DataCardinality (Cardinality _ _ dExp mr) -> do
    addDataPropExpr dExp
    maybe (return ()) addDataRange mr


comSigLFB :: ListFrameBit
          -> State Sign()
comSigLFB lfb = 
  case lfb of
    AnnotationBit ab -> 
      do
        let map2nd = map snd ab
        mapM_ addAnnoProp map2nd
    ExpressionBit ancls -> do
      let clslst = map snd ancls
      mapM_ addDescription clslst
    ObjectBit anob ->
      do
        let map2nd = map snd anob
        mapM_ addObjPropExpr map2nd
    DataBit dlst ->
      do
        let map2nd = map snd dlst
        mapM_ addDataPropExpr map2nd
    IndividualSameOrDifferent anind ->
      do
        let map2nd = map snd anind
        mapM_ addIndividual map2nd
    ObjectCharacteristics anch -> 
      return ()      
    DataPropRange dr ->
      do
        let map2nd = map snd dr
        mapM_ addDataRange map2nd
    IndividualFacts fct ->     
      do
        let map2nd = map snd fct
        mapM_ addFact map2nd
        
      
comSigAFB :: AnnFrameBit
          -> State Sign ()
comSigAFB afb =
  case afb of
    AnnotationFrameBit -> return ()
    DataFunctional -> return ()
    DatatypeBit dr -> do
      addDataRange dr
    ClassDisjointUnion cls -> do
      mapM_ addDescription cls
    ClassHasKey obe dpe -> do
      mapM_ addObjPropExpr obe
      mapM_ addDataPropExpr dpe  
    ObjectSubPropertyChain ope -> do
      mapM_ addObjPropExpr ope
 
       
completeSignForFrame :: Frame -> State Sign()
completeSignForFrame f = 
  case f of
    Frame ex fblist ->
      case fblist of
        [ListFrameBit _rel lfb] -> comSigLFB lfb
        [AnnFrameBit _an anf] -> comSigAFB anf

-- execState in Common/Lib/State.hs

completeSign :: OntologyDocument -> State Sign()
completeSign od = 
  mapM_ completeSignForFrame $ ontFrames $ ontology od

