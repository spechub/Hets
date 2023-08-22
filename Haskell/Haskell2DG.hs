{- |
Module      :  ./Haskell/Haskell2DG.hs
Description :  create a development graph from Haskell modules
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

process Haskell files
-}

module Haskell.Haskell2DG (anaHaskellFile) where

import Text.ParserCombinators.Parsec
import qualified Data.Map as Map
import Common.Result
import Common.Id
import Common.IRI (simpleIdToIRI)
import Common.GlobalAnnotations
import Common.LibName
import Common.Utils

import Haskell.HatAna
import Haskell.HatParser
import Haskell.Logic_Haskell

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck

import Static.GTheory
import Static.DevGraph
import Static.DgUtils
import Static.ComputeTheory

import Driver.Options

anaHaskellFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaHaskellFile opts file = do
    str <- readFile file
    putIfVerbose opts 2 $ "Reading file " ++ file
    case runParser hatParser () file str of
      Left err -> do
          putIfVerbose opts 0 $ show err
          return Nothing
      Right b -> case hatAna (b, emptySign, emptyGlobalAnnos) of
         Result es Nothing -> do
           putIfVerbose opts 0 $ unlines $ map show es
           return Nothing
         Result _ (Just (_, sig, sens)) -> do
          let (bas, _, _) = fileparse downloadExtensions file
              mName = simpleIdToIRI $ mkSimpleId bas
              name = makeName mName
              node_contents = newNodeLab name DGBasic
                $ G_theory Haskell Nothing sig startSigId (toThSens sens)
                  startThId
              dg = emptyDG
              node = getNewNodeDG dg
              dg1 = insNodeDG (node, node_contents) dg
              moduleS = "Module"
              nodeSig = NodeSig node $ signOf $ dgn_theory node_contents
              ln = emptyLibName moduleS
              esig = EmptyNode $ Logic Haskell
              gEnv = Map.singleton mName
                      $ SpecEntry $ ExtGenSig (GenSig esig [] esig) nodeSig
              dg2 = dg1 { globalEnv = gEnv }
              libEnv = Map.singleton ln $ computeDGraphTheories Map.empty dg2
          return $ Just (ln, libEnv)
