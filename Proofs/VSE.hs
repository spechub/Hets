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
import Static.PrintDevGraph
import Static.DGTranslation

import Proofs.DGFlattening
import Proofs.QualifyNames

import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Result
import Common.ResultT
import Common.SExpr
import Common.Utils
import Common.Lib.Graph (Gr)

import Logic.Prover
import Logic.Comorphism
import Logic.Coerce

import VSE.Logic_VSE

import VSE.Prove
import VSE.ToSExpr
import Comorphisms.CASL2VSE

import Data.Char
import Data.Maybe
import Data.Graph.Inductive.Basic (elfilter)
import Data.Graph.Inductive.Graph hiding (out)

import Control.Monad.Trans
import System.Process
import Text.ParserCombinators.Parsec

preprocess :: LibEnv -> Result LibEnv
preprocess le = libEnv_flattening_hiding le
  >>= libEnv_flattening_renamings
  >>= libEnv_flattening_dunions
  >>= qualifyLibEnv
  >>= flip libEnv_translation (Comorphism CASL2VSE)

thName :: LIB_NAME -> LNode DGNodeLab -> String
thName ln (n, lbl) = map (\ c -> if elem c "/,[]: " then '-' else c)
           $ shows (getLIB_ID ln) "_" ++ getDGNodeName lbl ++ "_" ++ show n

-- | applies basic inference to a given node and whole import tree above
prove :: [AnyComorphism] -> (LIB_NAME, Node) -> LibEnv
      -> IO (Result (LibEnv, Result G_theory))
prove _cms (ln, _node) libEnv =
  runResultT $ do
    libEnv' <- liftR $ preprocess libEnv
    let dGraph = elfilter (isGlobalDef . dgl_type) $ dgBody
           $ lookupDGraph ln libEnv'
        nls = labNodes dGraph
        ns = map snd nls
        errfile = "hetvse.out"
    ts <- liftR $ mapM
      (\ lbl -> do
         G_theory lid (ExtSign sign0 _) _ sens0 _ <- return $ dgn_theory lbl
         (sign1, sens1) <- coerceBasicTheory lid VSE ""
            (sign0, toNamedList sens0)
         let (sign2, sens2) = addUniformRestr sign1 sens1
         return
           ( show $ prettySExpr
             $ qualVseSignToSExpr (mkSimpleId $ getDGNodeName lbl)
               (getLIB_ID ln) sign2
           , show $ prettySExpr
             $ SList $ map (namedSenToSExpr sign2) sens2)) ns
    lift $ do
       vseBin <- getEnvDef "HETS_VSE" "hetsvse"
       (inp, out, _, cp) <-
           runInteractiveProcess vseBin ["-std"] Nothing Nothing
       readMyMsg cp out nameP
       sendMyMsg inp $ "(" ++ unlines (map (thName ln) nls) ++ ")"
       mapM_ (\ nl -> do
           readMyMsg cp out linksP
           sendMyMsg inp $ getLinksTo ln dGraph nl) nls
       mapM_ (\ (fsig, _) -> do
           readMyMsg cp out sigP
           sendMyMsg inp fsig) ts
       mapM_ (\ (_, sens) -> do
           readMyMsg cp out lemsP
           sendMyMsg inp sens) ts
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

getLinksTo :: LIB_NAME -> Gr DGNodeLab DGLinkLab -> LNode DGNodeLab -> String
getLinksTo ln dg (n, lbl) = show $ prettySExpr $ SList
  $ map (\ (s, _, el) -> SList
    [ SSymbol "definition-link"
    , SSymbol $ filter (not . isSpace) $ showEdgeId $ dgl_id el
    , SSymbol $ thName ln (s, fromMaybe (error "getLinksTo") $ lab dg s)
    , SSymbol $ thName ln (n, lbl)
    , SList [SSymbol "global"]
    , SList [SSymbol "morphism"]])
  $ filter (\ (s, _, _) -> s /= n) $ inn dg n

