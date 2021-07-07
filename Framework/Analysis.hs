{- |
Module      :  ./Framework/Analysis.hs
Description :  Analyzes a logic definition
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable
-}

module Framework.Analysis
     ( anaLogicDef
     , anaComorphismDef
     , addLogic2LogicList
     , addHLogic
     , addComorphism2ComorphismList
     ) where

import Framework.AS
import Framework.Logic_Framework

import qualified LF.Logic_LF as Logic_LF
import qualified Isabelle.Logic_Isabelle as Logic_Isabelle
import qualified Maude.Logic_Maude as Logic_Maude

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import Static.DevGraph
import Static.DgUtils
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
import Common.IRI (iriToStringUnsecure, nullIRI)
import Common.Keywords
import Common.ExtSign

import Text.ParserCombinators.Parsec

import LF.Framework ()

dynLogicsDir :: FilePath
dynLogicsDir = "Comorphisms"

dynLogicsFile :: FilePath
dynLogicsFile = "DynLogicList.hs"

dynLogicsCon :: String
dynLogicsCon = "dynLogicList"

dynComorphismsDir :: FilePath
dynComorphismsDir = "Comorphisms"

dynComorphismsFile :: FilePath
dynComorphismsFile = "DynComorphismList.hs"

dynComorphismsCon :: String
dynComorphismsCon = "dynComorphismList"

{- ----------------------------------------------------------------------------
Logic analysis -}

-- analyzes a logic definition
anaLogicDef :: LogicDef -> DGraph -> IO DGraph
anaLogicDef ld dg =
  case meta ld of
    LF -> anaLogicDefH Logic_LF.LF ld dg
    Isabelle -> anaLogicDefH Logic_Isabelle.Isabelle ld dg
    Maude -> anaLogicDefH Logic_Maude.Maude ld dg

anaLogicDefH :: LogicalFramework lid sublogics basic_spec sentence symb_items
                       symb_map_items sign morphism symbol raw_symbol
                       proof_tree
                => lid -> LogicDef -> DGraph -> IO DGraph
anaLogicDefH ml ld dg =
  case retrieveDiagram ml ld dg of
       Result _ (Just (ltruth, lmod, found, lpf)) -> do
           let l = iriToStringUnsecure $ newlogicName ld
           buildLogic ml l ltruth lmod found lpf
           addLogic2LogicList l
           return $ addLogicDef2DG ld dg
       _ -> error ""

{- constructs the diagram in the signature category of the meta logic
   which represents the object logic -}
retrieveDiagram :: LogicalFramework lid sublogics basic_spec sentence symb_items
                          symb_map_items sign morphism symbol raw_symbol
                          proof_tree
                   => lid -> LogicDef -> DGraph ->
                      Result (morphism, Maybe morphism,
                              Maybe sign, Maybe morphism)
retrieveDiagram ml (LogicDef _ _ s m f p _) dg = do
  ltruth <- lookupMorph ml s dg
  lmod <- if m == nullIRI
             then return Nothing
             else do v <- lookupMorph ml m dg
                     return $ Just v
  found <- if f == nullIRI
              then return Nothing
              else do v <- lookupSig ml f dg
                      return $ Just v
  lpf <- if p == nullIRI
            then return Nothing
            else do v <- lookupMorph ml p dg
                    return $ Just v
{- if (dom ltruth /= base_sig ml) then
error $ "The morphism " ++ (show s) ++
" must originate from the Base signature for " ++
(show ml) ++ "." else do -}
  if isJust lmod && dom (fromJust lmod) /= cod ltruth then
     error $ "The morphisms " ++ show s ++
             " and " ++ show m ++ " must be composable."
    else if isJust lpf && dom (fromJust lpf) /= cod ltruth then
     error $ "The morphisms " ++ show s ++
             " and " ++ show p ++ " must be composable."
    else return (ltruth, lmod, found, lpf)

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

-- constructs the logic instance for the object logic
buildLogic :: LogicalFramework lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol raw_symbol proof_tree
              => lid -> String -> morphism -> Maybe morphism ->
                 Maybe sign -> Maybe morphism -> IO ()
buildLogic ml l ltruth maybeMod _ maybePf = do
  exists <- doesDirectoryExist l
  if exists then
     error $ "The directory " ++ l ++ " already exists.\n" ++
             "Please choose a different object logic name." else do

  createDirectory l
  let logicCl = write_logic ml l
  writeFile (l ++ "/" ++ "Logic_" ++ l ++ ".hs") logicCl
  let syntaxCl = write_syntax ml l ltruth
  writeFile (l ++ "/" ++ "Syntax.hs") syntaxCl
  if isNothing maybeMod then
     error $ "Please provide a model theory for " ++ l ++ "\n" else do
  let modCl = write_model ml l $ fromJust maybeMod
  writeFile (l ++ "/" ++ "Model.hs") modCl
  if isNothing maybePf then
     error $ "Please provide a proof theory for " ++ l ++ "\n" else do
  let proofCl = write_proof ml l $ fromJust maybePf
  writeFile (l ++ "/" ++ "Proof.hs") proofCl
  return ()

-- includes the newly-defined logic in the logic list
addLogic2LogicList :: String -> IO ()
addLogic2LogicList l = do
  let file = dynLogicsDir ++ "/" ++ dynLogicsFile
  contentsOld <- readFile file
  let res = runParser (parser l) (emptyAnnos ()) "" contentsOld
  case res of
    Right contentsNew -> if isInfixOf ("import " ++ l ++ ".Logic_" ++ l) contentsOld
      then
      error $ show $ l ++ " already in DynLogicList"
      else
      writeFile file contentsNew
    Left er -> error $ show er

addHLogic :: String -> IO ()
addHLogic hld = do
  let file = dynLogicsDir ++ "/" ++ dynLogicsFile
  contentsOld <- readFile file
  let res = runParser (parserh hld) (emptyAnnos ()) "" contentsOld
  case res of 
    Right contentsNew -> 
     writeFile file contentsNew
    Left er -> error $ show er

{- ----------------------------------------------------------------------------
Comorphism analysis -}

anaComorphismDef :: ComorphismDef -> DGraph -> IO DGraph
anaComorphismDef cd dg =
  case metaC cd of
    LF -> anaComorphismDefH Logic_LF.LF cd dg
    Isabelle -> anaComorphismDefH Logic_Isabelle.Isabelle cd dg
    Maude -> anaComorphismDefH Logic_Maude.Maude cd dg

anaComorphismDefH :: LogicalFramework lid sublogics basic_spec sentence symb_items
                            symb_map_items sign morphism symbol raw_symbol
                            proof_tree
                     => lid -> ComorphismDef -> DGraph -> IO DGraph
anaComorphismDefH ml (ComorphismDef nc m sL tL sM pM mM) dg =
   let c = iriToStringUnsecure nc
       s = iriToStringUnsecure sL
       t = iriToStringUnsecure tL
   in case anaComH ml (ComorphismDef nc m sL tL sM pM mM) dg of
        Result _ (Just (symM, pfM, modM)) -> do
             buildComorphism ml c s t symM pfM modM
             addComorphism2ComorphismList c
             return $ addComorphismDef2DG (ComorphismDef nc m sL tL sM pM mM) dg
        _ -> error ""

anaComH :: LogicalFramework lid sublogics basic_spec sentence symb_items
                            symb_map_items sign morphism symbol raw_symbol
                            proof_tree
                     => lid -> ComorphismDef -> DGraph -> Result (morphism,
                            morphism, morphism)
anaComH ml (ComorphismDef _ _ sL tL sM pM mM) dg =
     let sLName = iriToStringUnsecure sL
         tLName = iriToStringUnsecure tL
         sLSyn = getMorphL ml sLName "Syntax"
         sLPf = getMorphL ml sLName "Proof"
         sLMod = getMorphL ml sLName "Model"
         tLSyn = getMorphL ml tLName "Syntax"
         tLPf = getMorphL ml tLName "Proof"
         tLMod = getMorphL ml tLName "Model" in do
     synM <- lookupMorph ml sM dg
     pfM <- lookupMorph ml pM dg
     modM <- lookupMorph ml mM dg
     if cod sLSyn /= dom synM then error $
      "the domain of the syntax morphism has" ++
      " to be the syntax of the source logic.\n"
      else if cod tLSyn /= cod synM then error $
        "the codomain of the syntax morphism has" ++
        " to be the syntax of the target logic.\n"
            else if cod sLPf /= dom pfM then error $
              "the domain of the proof morphism has to be the" ++
              " proof theory of the source logic.\n" ++ show (cod sLPf) ++
              "\n\n" ++ show (dom pfM) ++ "\n"
                  else if cod tLPf /= cod pfM then error $
                    "the codomain of the proof morphism has" ++
                    " to be the proof theory of the target logic.\n"
                            else if cod sLMod /= dom modM
                            then error $ "the domain of the model morphism" ++
                            " has to be the model theory of the source logic.\n"
                            ++ show (cod sLMod) ++ "\n" ++ show (dom modM)
                            ++ "\n"
                              else if cod tLMod /= cod modM then error $
                                "the codomain of the model morphism has" ++
                                " to be the model theory of the target logic.\n"
                                   else case (composeMorphisms synM tLPf,
                                              composeMorphisms sLPf pfM) of
                                      (Result _ comM1, Result _ comM2) ->
                                       if comM1 /= comM2 then error $
                                           "the syntax - proof diagram does" ++
                                           " not commute.\n"
                                       else case (composeMorphisms synM tLMod,
                                                  composeMorphisms sLPf modM) of
                                             (Result _ comM3, Result _ comM4) ->
                                              if comM3 /= comM4 then error $
                                                "the syntax - model diagram" ++
                                                " does not commute.\n"
                                              else return (synM, pfM, modM)

getMorphL :: LogicalFramework lid sublogics basic_spec sentence symb_items
                            symb_map_items sign morphism symbol raw_symbol
                            proof_tree
                     => lid -> String -> String -> morphism
getMorphL ml logicName fileName =
     let file = logicName ++ "/" ++ fileName ++ ".hs"
     in read_morphism ml file

addComorphismDef2DG :: ComorphismDef -> DGraph -> DGraph
addComorphismDef2DG cd dg =
  let node = getNewNodeDG dg
      name = newcomorphismName cd
      nodeName = emptyNodeName { getName = name }
      info = newNodeInfo DGBasic
      extSign = makeExtSign FrameworkCom cd
      gth = noSensGTheory FrameworkCom extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node, nodeLabel) dg

      emptyNode = EmptyNode $ Logic FrameworkCom
      genSig = GenSig emptyNode [] emptyNode
      nodeSig = NodeSig node $ G_sign FrameworkCom extSign startSigId
      gEntry = SpecEntry $ ExtGenSig genSig nodeSig
      dg2 = dg1 { globalEnv = Map.insert name gEntry $ globalEnv dg1 }
  in dg2


buildComorphism :: LogicalFramework lid sublogics basic_spec sentence symb_items
                    symb_map_items sign morphism symbol raw_symbol proof_tree
              => lid -> String -> String -> String
                   -> morphism -> morphism -> morphism -> IO ()
buildComorphism ml c s t synM pfM modM = do
  exists <- doesFileExist ("Comorphisms" ++ "/" ++ c ++ ".hs")
  if exists
     then error $ "The comorphism " ++ c ++ "already exists.\n"
     else do
  let comorphismC = write_comorphism ml c s t synM pfM modM
  writeFile ("Comorphisms" ++ "/" ++ c ++ ".hs") comorphismC
  return ()

addComorphism2ComorphismList :: String -> IO ()
addComorphism2ComorphismList c = do
  let file = dynComorphismsDir ++ "/" ++ dynComorphismsFile
  contentsOld <- readFile file
  let res = runParser (parserc c) (emptyAnnos ()) "" contentsOld  -- !!
  case res of
      Right contentsNew -> writeFile file contentsNew
      Left er -> error $ show er


{- ----------------------------------------------------------------------------
Auxiliary functions -}

-- looks up a signature by name
lookupSig :: Logic lid sublogics basic_spec sentence symb_items symb_map_items
                   sign morphism symbol raw_symbol proof_tree
             => lid -> SIG_NAME -> DGraph -> Result sign
lookupSig l n dg = do
  let extSig = case lookupGlobalEnvDG n dg of
                 Just (SpecEntry es) -> es
                 _ -> error $ "The signature " ++ show n ++
                              " could not be found."
  case extSig of
    ExtGenSig _ (NodeSig _ (G_sign l' (ExtSign sig _) _)) ->
      if Logic l /= Logic l'
         then error $ "The signature " ++ show n ++
                      " is not in the logic " ++ show l ++ "."
         else coercePlainSign l' l "" sig

-- looks up a morphism by name
lookupMorph :: Logic lid sublogics basic_spec sentence symb_items symb_map_items
                     sign morphism symbol raw_symbol proof_tree
               => lid -> MORPH_NAME -> DGraph -> Result morphism
lookupMorph l n dg = do
  let extView = case lookupGlobalEnvDG n dg of
                  Just (ViewOrStructEntry _ ev) -> ev
                  _ -> error $ "The morphism " ++ show n ++
                               " could not be found."
  case extView of
    ExtViewSig _ (GMorphism c _ _ morph _) _ -> do
      let l' = targetLogic c
      if Logic l /= Logic l'
         then error $ "The morphism " ++ show n ++
                      " is not in the logic " ++ show l ++ "."
         else coerceMorphism l' l "" morph


parser :: String -> AParser st String
parser l = do
  let l_imp = "import " ++ l ++ "." ++ "Logic_" ++ l
  let l_log = "Logic " ++ l

  header <- skipUntil "module"
  mod_decl <- do m <- asStr "module"
                 n <- moduleName
                 w <- asStr "where"
                 return $ unwords [m, n, w]
  imps <- many1 $ do
             i <- asStr "import"
             n <- moduleName
             return $ unwords [i, n]
  log_var_decl <- do v <- asStr dynLogicsCon
                     s <- asStr "::"
                     t <- do oBracketT
                             asStr "AnyLogic"
                             cBracketT
                             return "[AnyLogic]"
                     return $ unwords [v, s, t]
  log_var_def <- do v <- asStr dynLogicsCon
                    s <- asStr "="
                    return $ unwords [v, s]
  log_list <- do oBracketT
                 (do cBracketT
                     return [])
                   <|>
                   do (xs, _) <- logParser `separatedBy` commaT
                      cBracketT
                      return xs
  hlg_var_decl <- do v <- asStr "dynHLogicList"
                     s <- asStr "::"
                     t <- do oBracketT
                             oParenT
                             asStr "String"
                             commaT
                             asStr "HLogicDef"
                             cParenT
                             cBracketT
                             return "[(String, HLogicDef)]"
                     return $ unwords [v, s, t]
  hlog_var_def <- do v <- asStr "dynHLogicList"
                     s <- asStr "="
                     return $ unwords [v, s]
  hlog_list <- do oBracketT
                  (do cBracketT
                      return [])
                   <|>
                   do (xs, _) <- hLogParser `separatedBy` commaT
                      cBracketT
                      return xs
  return $ header ++ mod_decl ++ "\n\n" ++
           intercalate "\n" (imps ++ [l_imp]) ++ "\n\n" ++
           log_var_decl ++ "\n" ++ log_var_def ++ " " ++ "[" ++
           intercalate ", " (log_list ++ [l_log]) ++ "]" ++ "\n\n" ++
           hlg_var_decl ++ "\n" ++ hlog_var_def ++ " " ++ "[\n   " ++
           (intercalate "  ,\n" hlog_list) ++ " ]"

parserh :: String -> AParser st String
parserh hlog = do  
  header <- skipUntil "module"
  mod_decl <- do m <- asStr "module"
                 n <- moduleName
                 w <- asStr "where"
                 return $ unwords [m, n, w]
  imps <- many1 $ do
             i <- asStr "import"
             n <- moduleName
             return $ unwords [i, n]
  log_var_decl <- do v <- asStr dynLogicsCon
                     s <- asStr "::"
                     t <- do oBracketT
                             asStr "AnyLogic"
                             cBracketT
                             return "[AnyLogic]"
                     return $ unwords [v, s, t]
  log_var_def <- do v <- asStr dynLogicsCon
                    s <- asStr "="
                    return $ unwords [v, s]
  log_list <- do oBracketT
                 (do cBracketT
                     return [])
                   <|>
                   do (xs, _) <- logParser `separatedBy` commaT
                      cBracketT
                      return xs
  hlg_var_decl <- do v <- asStr "dynHLogicList"
                     s <- asStr "::"
                     t <- do oBracketT
                             oParenT
                             asStr "String"
                             commaT
                             asStr "HLogicDef"
                             cParenT
                             cBracketT
                             return "[(String, HLogicDef)]"
                     return $ unwords [v, s, t]
  hlog_var_def <- do v <- asStr "dynHLogicList"
                     s <- asStr "="
                     return $ unwords [v, s]
  hlog_list <- do oBracketT
                  (do cBracketT
                      return [])
                   <|>
                   do (xs, _) <- hLogParser `separatedBy` commaT
                      cBracketT
                      return xs
  return $ header ++ mod_decl ++ "\n\n" ++
           intercalate "\n" imps ++ "\n\n" ++
           log_var_decl ++ "\n" ++ log_var_def ++ " " ++ "[" ++
           intercalate ", " log_list ++ "]" ++ "\n\n" ++
           hlg_var_decl ++ "\n" ++ hlog_var_def ++ " " ++ "[\n   " ++
           intercalate "\n  ," (hlog_list ++ [hlog]) ++ " ]" 


parserc :: String -> AParser st String
parserc c = do
     let com_imp = "import " ++ "Comorphisms." ++ c
     let com_c = "Comorphism " ++ c

     header <- skipUntil "module"
     mod_decl <- do m <- asStr "module"
                    n <- moduleName
                    w <- asStr "where"
                    return $ unwords [m, n, w]
     imps <- many1 $ do
                i <- asStr "import"
                n <- moduleName
                return $ unwords [i, n]
     com_var_decl <- do v <- asStr dynComorphismsCon
                        s <- asStr "::"
                        t <- do oBracketT
                                asStr "AnyComorphism"
                                cBracketT
                                return "[AnyComorphism]"
                        return $ unwords [v, s, t]
     com_var_def <- do v <- asStr dynComorphismsCon
                       s <- asStr "="
                       return $ unwords [v, s]
     com_list <- do oBracketT
                    (do cBracketT
                        return [])
                        <|>
                        do (xs, _) <- comParser `separatedBy` commaT
                           cBracketT
                           return xs
     return $ header ++ mod_decl ++ "\n\n" ++
              intercalate "\n" (imps ++ [com_imp]) ++ "\n\n" ++
              com_var_decl ++ "\n" ++
              com_var_def ++ " " ++ "[" ++
              intercalate ", " (com_list ++ [com_c]) ++ "]"

skipUntil :: String -> AParser st String
skipUntil lim = do
  res <- many $ reserved [lim] (many1 $ noneOf whiteChars) <|>
                many1 (oneOf whiteChars)
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

hLogParser :: AParser st String
hLogParser = do
 l <- asStr "("
 char '"'
 k <- simpleId
 char '"'
 c <- asStr ","
 hld <- asStr "HLogicDef"
 char '"'
 hldn <- simpleId
 char '"'
 let parseHQ = do 
      l1 <- asStr "("
      char '"'
      (strs, _) <- scanAnyWords `separatedBy` skip --TODO: this should only work for quants but not for logics!
      let lg = concat $ intersperse " " strs
      char '"'
      c1 <- asStr ","
      subl <- do 
         n <- asStr "Nothing"
         return n 
         <|> do
         j <- asStr "Just"
         char '"'
         sub <- simpleId
         char '"'
         return $ j ++ " \"" ++ tokStr sub ++ "\""
      r1 <- asStr ")"
      return $ l1 ++ "\"" ++ lg ++ "\"" ++ c1 ++ " " ++ subl ++ r1  
      <|> return ""
      
     parseConstr =  do
      s <- asStr "ReflexiveMod" 
           <|> asStr "TransitiveMod"
           <|> asStr "SymmetricMod" 
           <|> asStr "SerialMod"
           <|> asStr "EuclideanMod"
           <|> asStr "FunctionalMod"
           <|> asStr "LinearMod"
           <|> asStr "TotalMod"
           <|> do
            s1 <- asStr sameInterpretationS
            char '"' -- _oP <- oParenT
            (str, _) <- scanAnyWords `separatedBy` skip -- ) `separatedBy` commaT
            char '"' -- _cP <- cParenT
            return $ s1 ++ "\""  ++ (concat $ intersperse " " str) ++ "\"" 
            -- this needs testing!
           <|> do
            s1 <- asStr sameDomainS
            _ <- skip
            arg <- asStr "False" <|> asStr "True"
            _ <- skip
            return $ s1 ++ " " ++ arg
           <|> do
            return "" 
      return s 
    
 hldb <- parseHQ
 hldf <- asStr "True" <|> asStr "False"
 _ <- oBracketT
 (hldc, _) <- parseConstr `separatedBy` commaT
 _ <- cBracketT
 _ <- oBracketT
 (hldq, _) <- parseHQ `separatedBy` commaT
 _ <- cBracketT
-- HLogicDef aString  
--           (bString, Nothing) | (bString, Just cString) 
--           True | False
--           [semconstr] -- still need a parser for this one!
--           [(String, Nothing) | (String, Just String) `separatedBy`]
 let hldString = intercalate " " 
                  [hld, "\"" ++ tokStr hldn ++ "\"", hldb, hldf, "[" ++ (intercalate "," hldc) ++ "]",  "[" ++ (intercalate "," hldq) ++ "]"]
 r <- asStr ")"
 return $ l ++ "\"" ++  tokStr k ++ "\"" ++ c ++ " " ++ hldString ++ r

logParser :: AParser st String
logParser = do
  l <- asKey "Logic"
  n <- simpleId
  return $ tokStr l ++ " " ++ tokStr n

comParser :: AParser st String
comParser = do
     c <- asKey "Comorphism"
     n <- simpleId
     return $ tokStr c ++ " " ++ tokStr n
