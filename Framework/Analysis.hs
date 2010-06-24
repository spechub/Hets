{- |
Module      :  $Header$
Description :  Analyzes a logic definition
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis ( anaLogicDef ) where

import Framework.AS
import Framework.Logic_Framework
import Framework.LogicFram
import Framework.WriteLogic

import qualified LF.Logic_LF as Logic_LF
import qualified Isabelle.Logic_Isabelle as Logic_Isabelle
import qualified Maude.Logic_Maude as Logic_Maude

import qualified Data.Map as Map

import Static.DevGraph
import Static.GTheory

import System.Directory

import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic
import Logic.Comorphism
import Logic.Coerce

import Common.ExtSign
import Common.Result
import Common.DocUtils

import LF.Framework

import Debug.Trace

-- analyzes a logic definition
anaLogicDef :: LogicDef -> DGraph -> IO DGraph
anaLogicDef ld dg =
  case meta ld of
    LF       -> anaLogicDefH Logic_LF.LF ld dg
    Isabelle -> anaLogicDefH Logic_Isabelle.Isabelle ld dg
    Maude    -> anaLogicDefH Logic_Maude.Maude ld dg

anaLogicDefH :: LogicFram lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol
                       proof_tree
                => lid -> LogicDef -> DGraph -> IO DGraph
anaLogicDefH ml ld dg = do
  case retrieveDiagram ml ld dg of
       Result _ (Just (ltruth,lmod,lpf)) -> do
           buildLogic ml (newlogicName ld) ltruth lmod lpf
           return $ addLogicDef2DG ld dg
       _ -> fail ""
  
 -- creates a node for the logic definition
addLogicDef2DG :: LogicDef -> DGraph -> DGraph
addLogicDef2DG ld dg =
  let node = getNewNodeDG dg
      name = newlogicName ld
      nodeName = emptyNodeName { getName = name }
      info = newNodeInfo DGBasic
      extSign = makeExtSign Framework ld
      gth = noSensGTheory Framework extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node,nodeLabel) dg

      emptyNode = EmptyNode $ Logic Framework
      genSig = GenSig emptyNode [] emptyNode
      nodeSig = NodeSig node $ G_sign Framework extSign startSigId
      gEntry = SpecEntry $ ExtGenSig genSig nodeSig
      dg2 = dg1 { globalEnv = Map.insert name gEntry $ globalEnv dg1 }
      in dg2

{- constructs the diagram in the signature category of the meta logic
   which represents the object logic -}
retrieveDiagram :: LogicFram lid sublogics basic_spec sentence symb_items
                          symb_map_items sign morphism symbol raw_symbol
                          proof_tree
                   => lid -> LogicDef -> DGraph -> 
                      Result (morphism, morphism, morphism)
retrieveDiagram ml (LogicDef _ _ sy t _ m p) dg = do
  lSyn <- lookupSig ml sy dg
  ltruth <- lookupMorph ml t dg
  lmod <- lookupMorph ml m dg
  lpf <- lookupMorph ml p dg
  
  if (dom ltruth /= baseSig ml || cod ltruth /= lSyn) then
     error $ "The morphism " ++ (show t) ++ " must go from Base to " ++
             (show sy) ++ "." else
     if (dom lmod /= lSyn) then
        error $ "The morphism " ++ (show m) ++ " must go from " ++
                (show sy) ++ "." else
        if (dom lpf /= lSyn) then
           error $ "The morphism " ++ (show p) ++ " must go from " ++
                   (show sy) ++ "." else
           return (ltruth,lmod,lpf)  

-- looks up a signature by name
lookupSig :: Logic lid sublogics basic_spec sentence symb_items symb_map_items
                   sign morphism symbol raw_symbol proof_tree
             => lid -> SIG_NAME -> DGraph -> Result sign
lookupSig l n dg = do
  let extSig = case lookupGlobalEnvDG n dg of
                 Just (SpecEntry es) -> es
                 _ -> error $ "The signature " ++ (show n) ++
                              " could not be found." 
  case extSig of
    ExtGenSig _ (NodeSig _ (G_sign l' (ExtSign sig _) _)) ->
      if Logic l /= Logic l'
         then error $ "The signature " ++ (show n)  ++
                      " is not in the logic " ++ (show l) ++ "."
         else coercePlainSign l' l "" sig

-- looks up a morphism by name
lookupMorph :: Logic lid sublogics basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree
               => lid -> MORPH_NAME -> DGraph -> Result morphism
lookupMorph l n dg = do
  let extView = case lookupGlobalEnvDG n dg of
                  Just (ViewEntry ev) -> ev
                  Just (StructEntry ev) -> ev
                  _ -> error $ "The morphism " ++ (show n) ++
                               " could not be found."
  case extView of
    ExtViewSig _ (GMorphism c _ _ morph _) _ -> do
      let l' = targetLogic c
      if Logic l /= Logic l' 
         then error $ "The morphism " ++ (show n) ++
                      " is not in the logic " ++ (show l) ++ "."
         else coerceMorphism l' l "" morph

-- constructs the logic instance for the object logic
buildLogic :: LogicFram lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol raw_symbol proof_tree
              => lid -> NAME -> morphism -> morphism -> morphism -> IO ()
buildLogic ml lT ltruth _ _ = do
  let l = show $ pretty lT
  let loginst = writeLogic ml l
  --createDirectory l
  writeFile (l ++ "/" ++ "Logic_" ++ l ++ ".hs") loginst
  writeFile (l ++ "/" ++ "Syntax.hs") $ show ltruth
  return ()


       

 
  

