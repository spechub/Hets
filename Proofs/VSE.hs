{- |
Module      :  $Header$
Description :  Interface to send structured theories to the VSE prover
Copyright   :  (c) C. Maeder, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  needs POSIX

call an adaption of VSE II to hets

the prover should be attached to a node's menu (if applicable) but take the
whole library environment as in- and output like development graph rules.
-}

module Proofs.VSE where

import Static.GTheory
import Static.DevGraph
import Static.DGTranslation

import Proofs.DGFlattening
import Proofs.QualifyNames

import Common.ExtSign
import Common.LibName
import Common.Result
import Common.ResultT
import Common.SExpr
import Common.Utils

import Logic.Prover
import Logic.Comorphism
import Logic.Coerce

import VSE.Logic_VSE

import VSE.Prove
import VSE.ToSExpr
import Comorphisms.CASL2VSE

import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph (Node, labNodes)

import Control.Monad.Trans
import System.Process
import Text.ParserCombinators.Parsec

preprocess :: LibEnv -> Result LibEnv
preprocess le = libEnv_flattening_heterogen le
  >>= libEnv_flattening_hiding
  >>= libEnv_flattening_dunions
  >>= qualifyLibEnv
  >>= flip libEnv_translation (Comorphism CASL2VSE)

{-
getImportedNodes :: Set.Set Node -> DGraph -> Node -> [LNode DGNodeLab]
getImportedNodes known dg node =
  let (pres, _, lab , _) = safeContextDG "Proofs.VSE" dg node
      ps = Set.fromList $ map snd pres
      ns = Set.toList $ Set.delete node $ Set.difference ps known
-}

-- | applies basic inference to a given node and whole import tree above
prove :: [AnyComorphism] -> (LIB_NAME, Node) -> LibEnv
      -> IO (Result (LibEnv, Result G_theory))
prove _cms (ln, _node) libEnv =
  runResultT $ do
    libEnv' <- liftR $ preprocess libEnv
    let dGraph = elfilter (isGlobalDef . dgl_type) $ dgBody
           $ lookupDGraph ln libEnv'
        ns = map snd $ labNodes dGraph
        errfile = "hetvse.out"
        thName lbl = map (\ c -> if elem c "/,[]: " then '-' else c)
                          $ shows (getLIB_ID ln) "_" ++ getDGNodeName lbl
    ts <- liftR $ mapM
      (\ lbl -> do
         G_theory lid (ExtSign sign0 _) _ sens0 _ <- return $ dgn_theory lbl
         (sign1, sens1) <- coerceBasicTheory lid VSE ""
            (sign0, toNamedList sens0)
         return $ addUniformRestr sign1 sens1) ns
    lift $ do
       vseBin <- getEnvDef "HETS_VSE" "hetsvse"
       (inp, out, _, cp) <-
           runInteractiveProcess vseBin ["-std"] Nothing Nothing
       readMyMsg cp out nameP
       sendMyMsg inp $ "(" ++ unlines (map thName ns) ++ ")"
       mapM_ (const $ readMyMsg cp out linksP >> sendMyMsg inp "nil") ns
       mapM_ (\ (fsig, _) -> do
           readMyMsg cp out sigP
           -- only the non-imported bits need to be sent
           sendMyMsg inp $ show $ prettySExpr $ vseSignToSExpr fsig) ts
       mapM_ (\ (fsig, sens) -> do
           readMyMsg cp out lemsP
           sendMyMsg inp $ show $ prettySExpr
             $ SList $ map (namedSenToSExpr fsig) sens) ts
       ms <- getProcessExitCode cp
       case ms of
         Just _ -> do
           putStrLn $ vseBin ++ " unavailable"
           return []
         Nothing -> do
           revres <- readRest cp out ""
           let res = reverse revres
           case parse parseSExprs errfile res of
             Right l -> mapM_ (print . prettySExpr) l
             Left e -> do
               writeFile errfile res
               print e
           return []
    return (libEnv, Result [] Nothing)


