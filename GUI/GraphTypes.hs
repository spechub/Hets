{- |
Module      :  $Header$
Description :  Types for the Central GUI of Hets
Copyright   :  (c) Jorina Freya Gerken, Till Mossakowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic)
-}

module GUI.GraphTypes
    ( GInfo(..)
    , ConversionMaps(..)
    , emptyConversionMaps
    , emptyGInfo
    , DGraphAndAGraphNode
    , DGraphAndAGraphEdge
    , InternalNames(..)
    , ConvFunc
    )
    where

import GUI.AbstractGraphView(Descr, GraphInfo, initgraphs)
import GUI.ProofManagement (GUIMVar)

import Syntax.AS_Library
import Syntax.Print_AS_Library()

import Static.DevGraph(LibEnv, emptyLibEnv)

import Common.Id(nullRange)
import Common.Doc(text, ($+$))
import Common.DocUtils(Pretty, pretty)
import qualified Common.InjMap as InjMap

import Driver.Options(HetcatsOpts, defaultHetcatsOpts)

import Data.IORef
import Data.Graph.Inductive.Graph(Node)

import Control.Concurrent.MVar(newEmptyMVar)

{- Maps used to track which node resp edge of the abstract graph
correspondes with which of the development graph and vice versa and
one Map to store which libname belongs to which development graph-}
data ConversionMaps = ConversionMaps
    { dgAndabstrNode :: DGraphAndAGraphNode
    , dgAndabstrEdge :: DGraphAndAGraphEdge
    } deriving Show

-- | Pretty instance for ConversionMaps
instance Pretty ConversionMaps where
  pretty convMaps =
       text "dg2abstrNode"
    $+$ pretty (InjMap.getAToB $ dgAndabstrNode convMaps)
    $+$ text "dg2abstrEdge"
    $+$ pretty (InjMap.getAToB $ dgAndabstrEdge convMaps)
    $+$ text "abstr2dgNode"
    $+$ pretty (InjMap.getBToA $ dgAndabstrNode convMaps)
    $+$ text "abstr2dgEdge"
    $+$ pretty (InjMap.getBToA $ dgAndabstrEdge convMaps)

-- | types of the Maps above
type DGraphAndAGraphNode = InjMap.InjMap (LIB_NAME, Node) Descr
type DGraphAndAGraphEdge =
    InjMap.InjMap (LIB_NAME, (Descr, Descr, String)) Descr

data InternalNames =
     InternalNames { showNames :: Bool,
                     updater :: [(String,(String -> String) -> IO ())] }

-- | Global datatype for all GUI functions
data GInfo = GInfo
             { libEnvIORef :: IORef LibEnv
             , descrIORef :: IORef Descr
             , conversionMapsIORef :: IORef ConversionMaps
             , graphId :: Descr
             , nextGraphId :: IORef Descr
             , gi_LIB_NAME :: LIB_NAME
             , gi_GraphInfo :: GraphInfo
             , internalNamesIORef :: IORef InternalNames
               -- show internal names?
             , gi_hetcatsOpts :: HetcatsOpts
             , visibleNodesIORef :: IORef [[Node]]
             , proofGUIMVar :: GUIMVar
             }

{- | Type of the convertGraph function. Used as type of a parameter of some 
     functions in GraphMenu and GraphLogic. -}
type ConvFunc =  GInfo -> LIB_NAME -> LibEnv -> HetcatsOpts
              -> String -> IO (Descr, GraphInfo, ConversionMaps)

-- | Creates empty conversionmaps
emptyConversionMaps :: ConversionMaps
emptyConversionMaps =
  ConversionMaps {dgAndabstrNode = InjMap.empty::DGraphAndAGraphNode,
                  dgAndabstrEdge = InjMap.empty::DGraphAndAGraphEdge}

-- | Creates an empty GInfo
emptyGInfo :: IO GInfo
emptyGInfo = do
  iorLE <- newIORef emptyLibEnv
  iorD <- newIORef (0 :: Descr)
  iorNGI <- newIORef (0 :: Descr)
  iorCM <- newIORef emptyConversionMaps
  graphInfo <- initgraphs
  iorIN <- newIORef $ InternalNames False []
  iorVN <- newIORef ([] :: [[Node]])
  guiMVar <- newEmptyMVar
  return $ GInfo {libEnvIORef = iorLE,
                  descrIORef = iorD,
                  conversionMapsIORef = iorCM,
                  graphId = 0,
                  nextGraphId = iorNGI,
                  gi_LIB_NAME = Lib_id $ Indirect_link "" nullRange "" noTime,
                  gi_GraphInfo = graphInfo,
                  internalNamesIORef = iorIN,
                  gi_hetcatsOpts = defaultHetcatsOpts,
                  visibleNodesIORef = iorVN,
                  proofGUIMVar = guiMVar}
