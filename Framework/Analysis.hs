{- |
Module      :  $Header$
Description :  Analyzes a logic definition
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis ( anaLogicDef ) where

import Framework.AS
import Framework.Logic_Framework

import qualified LF.Logic_LF as Logic_LF
import qualified Isabelle.Logic_Isabelle as Logic_Isabelle
import qualified Maude.Logic_Maude as Logic_Maude

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Static.DevGraph
import Static.GTheory

import System.Directory

import Logic.Grothendieck
import Logic.ExtSign
import Logic.Logic
import Logic.Comorphism
import Logic.Coerce

import Common.Result
import Common.Parsec
import Common.AnnoState
import Common.Lexer
import Common.Token
import Common.Id

import Text.ParserCombinators.Parsec

import LF.Framework ()

dynLogicsDir :: FilePath
dynLogicsDir = "Comorphisms"

dynLogicsFile :: FilePath
dynLogicsFile = "DynLogicList.hs"

dynLogicsCon :: String
dynLogicsCon = "dynLogicList"

-- analyzes a logic definition
anaLogicDef :: LogicDef -> DGraph -> IO DGraph
anaLogicDef ld dg =
  case meta ld of
    LF -> anaLogicDefH Logic_LF.LF ld dg
    Isabelle -> anaLogicDefH Logic_Isabelle.Isabelle ld dg
    Maude -> anaLogicDefH Logic_Maude.Maude ld dg

anaLogicDefH :: LogicFram lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol
                       proof_tree
                => lid -> LogicDef -> DGraph -> IO DGraph
anaLogicDefH ml ld dg = do
  case retrieveDiagram ml ld dg of
       Result _ (Just (ltruth, lmod, lpf)) -> do
           let l = tokStr $ newlogicName ld
           buildLogic ml l ltruth lmod lpf
           addLogic2LogicList l
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
      dg1 = insNodeDG (node, nodeLabel) dg

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
                      Result (morphism, Maybe morphism, Maybe morphism)
retrieveDiagram ml (LogicDef _ _ s m p _) dg = do
  ltruth <- lookupMorph ml s dg
  lmod <- if (m == nullTok)
             then return Nothing
             else do v <- lookupMorph ml m dg
                     return $ Just v
  lpf <- if (p == nullTok)
            then return Nothing
            else do v <- lookupMorph ml p dg
                    return $ Just v 

  if (dom ltruth /= getBaseSig ml) then
     error $ "The morphism " ++ (show s) ++
             " must originate from the Base signature for " ++
             (show ml) ++ "." else do
  if (isJust lmod && (dom $ fromJust lmod) /= cod ltruth) then
     error $ "The morphisms " ++ (show s) ++
             " and " ++ (show m) ++ " must be composable." else do
  if (isJust lpf && (dom $ fromJust lpf) /= cod ltruth) then
     error $ "The morphisms " ++ (show s) ++
             " and " ++ (show p) ++ " must be composable." else do
  return (ltruth, lmod, lpf)

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
              => lid -> String -> morphism -> Maybe morphism ->
                 Maybe morphism -> IO ()
buildLogic ml l ltruth _ _ = do
  exists <- doesDirectoryExist l
  if exists then
     error $ "The directory " ++ l ++ " already exists.\n" ++
             "Please choose a different object logic name." else do

  createDirectory l
  let logicC = writeLogic ml l
  let syntaxC = writeSyntax ml l ltruth
  writeFile (l ++ "/" ++ "Logic_" ++ l ++ ".hs") logicC
  writeFile (l ++ "/" ++ "Syntax.hs") syntaxC
  return ()

-- includes the newly-defined logic in the logic list
addLogic2LogicList :: String -> IO ()
addLogic2LogicList l = do
  let file = dynLogicsDir ++ "/" ++ dynLogicsFile
  contentsOld <- readFile file
  let res = runParser (parser l) (emptyAnnos ()) "" contentsOld
  case res of
      Right contentsNew -> writeFile file contentsNew
      Left er -> error $ show er 

parser :: String -> AParser st String
parser l = do
  let l_imp = "import " ++ l ++ "." ++ "Logic_" ++ l
  let l_log = "Logic " ++ l

  header <- skipUntil "module"
  mod_decl <- do m <- asStr "module"
                 n <- moduleName
                 w <- asStr "where"
                 return $ intercalate " " [m,n,w]
  imps <- do many1 $ do
             i <- asStr "import"
             n <- moduleName
             return $ intercalate " " [i,n]
  log_var_decl <- do v <- asStr dynLogicsCon
                     s <- asStr "::"
                     t <- do oBracketT
                             asStr "AnyLogic"
                             cBracketT
                             return "[AnyLogic]"
                     return $ intercalate " " [v,s,t]
  log_var_def <- do v <- asStr dynLogicsCon
                    s <- asStr "="
                    return $ intercalate " " [v,s]
  log_list <- do oBracketT
                 ( do cBracketT
                      return []
                   <|>
                   do (xs,_) <- logParser `separatedBy` commaT
                      cBracketT
                      return xs )
  
  return $ header ++ mod_decl ++ "\n\n" ++
           (intercalate "\n" (imps ++ [l_imp])) ++ "\n\n" ++
           log_var_decl ++ "\n" ++ log_var_def ++ " " ++ "[" ++
           (intercalate ", " $ log_list ++ [l_log]) ++ "]"

skipUntil :: String -> AParser st String
skipUntil lim = do
  res <- many $ (reserved [lim] $ many1 $ noneOf whiteChars) <|>
                (many1 $ oneOf whiteChars)
  return $ concat res

asStr :: String -> AParser st String
asStr x = do
  res <- asKey x
  return $ tokStr res

moduleName :: AParser st String
moduleName = do
  m <- simpleId
  dotT
  n <- simpleId
  return $ tokStr m ++ "." ++ tokStr n
       
logParser :: AParser st String     
logParser = do
  l <- asKey "Logic"
  n <- simpleId
  return $ tokStr l ++ " " ++ tokStr n
