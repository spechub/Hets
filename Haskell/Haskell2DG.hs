{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

process Haskell files

-}

module Haskell.Haskell2DG (anaHaskellFile) where

import Data.Graph.Inductive.Graph
import Text.ParserCombinators.Parsec
import qualified Common.Lib.Map as Map
import Common.Result
import Common.Id
import Common.GlobalAnnotations
import Common.Utils

import Syntax.AS_Library

import Haskell.HatAna
import Haskell.HatParser
import Haskell.Logic_Haskell

import Logic.Logic
import Logic.Prover
import Logic.Grothendieck

import Static.DevGraph
import Driver.WriteFn
import Driver.Options

anaHaskellFile :: HetcatsOpts -> FilePath -> IO (Maybe (LIB_NAME, LibEnv))
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
          let (bas, dir, _) = fileparse downloadExtensions file
              mName = mkSimpleId bas
              name = makeName $ mName
              node_contents = DGNode
                 { dgn_name = name
                 , dgn_theory = G_theory Haskell sig 0 (toThSens sens) 0
                 , dgn_nf = Nothing
                 , dgn_sigma = Nothing
                 , dgn_origin = DGBasic
                 , dgn_cons = None
                 , dgn_cons_status = LeftOpen
                 }
              dg = devGraph emptyGlobalContext
              node = getNewNode dg
              dg' = insNode (node, node_contents) dg
              moduleS = "Module"
              nodeSig = NodeSig node $ signOf $ dgn_theory node_contents
              ln = Lib_id (Direct_link moduleS (Range []))
              gEnv = Map.singleton mName
                      $ SpecEntry ( EmptyNode $ Logic Haskell, []
                                  , G_sign Haskell emptySign 0, nodeSig)
              ctxt = emptyGlobalContext
                { globalEnv = gEnv
                , devGraph = dg' }
              libEnv = Map.singleton ln ctxt
          writeSpecFiles opts (pathAndBase dir moduleS)
                         libEnv emptyGlobalAnnos (ln, gEnv)
          return $ Just (ln, libEnv)

