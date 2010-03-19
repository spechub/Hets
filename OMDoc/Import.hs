{- |
Module      :  $Header$
Description :  Transforms an OMDoc file into a development graph
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Given an OMDoc file, we transform it to a development graph by
following also all library links.
-}

module OMDoc.Import -- (anaOMDocFile)
    where

import Driver.Options

import Common.Result
import Common.ResultT
-- import Common.ExtSign
import Common.Id
import Common.LibName
-- import Common.AS_Annotation

import Logic.Logic
import Logic.ExtSign
-- import Logic.Coerce
-- import Logic.Prover
import Logic.Grothendieck
-- import Logic.Comorphism

import Comorphisms.LogicList

import Static.DevGraph
import Static.GTheory

import OMDoc.DataTypes
import OMDoc.XmlInterface (xmlIn, uriEncodeCD)

import System.Directory

-- import Data.Graph.Inductive.Graph
import Data.Maybe
import Data.List
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans

import Network.URI

--------------------- Import Environment Interface ---------------------

--sorry = error "Under construction"

data ImpEnv = ImpEnv { libMap :: Map.Map URI (LibName, DGraph) }

initialEnv :: ImpEnv
initialEnv = ImpEnv { libMap = Map.empty }

getLibEnv :: ImpEnv -> LibEnv
getLibEnv = Map.fromList . Map.elems . libMap

addDGToEnv :: ImpEnv -> URI -> LibName -> DGraph -> ImpEnv
addDGToEnv e u ln dg = e { libMap = Map.insert u (ln, dg) $ libMap e }

lookupLib :: ImpEnv -> URI -> Maybe (LibName, DGraph)
lookupLib e = flip Map.lookup $ libMap e

{- TODO:
getNode :: ImpEnv -> (LibName, DGraph) -> UriCD
        -> (LibName, DGraph, LNode DGNodeLab)
getNode e ucd =
    case getUri ucd of
      Just u ->
          let (ln, dg) = fromMaybe
                         (error $ "getNode: couldn't find node" ++ show ucd)
                         $ lookupLib e u
          in getModule
-}            
              
              
--------------------- URI Functions ---------------------

readURL :: URI -> IO String
readURL u = if elem (uriScheme u) ["", "file:"] then readFile $ uriPath u
            else error $ "readURI: Unsupported URI-scheme " ++ uriScheme u

getLogicFromMeta :: Maybe OMCD -> AnyLogic
getLogicFromMeta mCD =
    let p (Logic lid) = case omdoc_metatheory lid of
                          Just cd' -> (fromJust mCD) == cd'
                          _ -> False
    in if isNothing mCD then defaultLogic else
           case find p logicList of
             Just al -> al
             _ -> defaultLogic

toURI :: String -> URI
toURI s = case parseURIReference s of
            Just u -> u
            _ -> error $ "toURI: can't parse as uri " ++ s

libNameFromURL :: String -> URI -> IO LibName
libNameFromURL s u = do let fp = uriPath u
                        mt <- getModificationTime fp
                        return $ setFilePath fp mt $ emptyLibName s

type UriCD = (Maybe URI, String)

getUri :: UriCD -> Maybe URI
getUri = fst

getModule :: UriCD -> String
getModule = snd

toUriCD :: OMCD -> UriCD
toUriCD cd = let [base, m] = cdToList cd in
             if null base then (Nothing, m) else (Just $ toURI base, m)


--------------------- Top level functions ---------------------

-- | Translates an OMDoc file to a LibEnv
anaOMDocFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaOMDocFile opts fp = do
  dir <- getCurrentDirectory
  let url = fromJust $ relativeTo (toURI fp) $ toURI $ dir ++ "/"
  putIfVerbose opts 2 $ "anaOMDocFile: Importing OMDoc file " ++ show url
  Result ds mEnvLn <- runResultT $ importLib initialEnv url
  showDiags opts ds
  return $ fmap (\ (env, ln, _) -> (ln, getLibEnv env)) mEnvLn



--------------------- OMDoc traversal ---------------------

-- | Adds the OMDoc file and the closure of its imports to the environment
importLib :: ImpEnv -> URI -> ResultT IO (ImpEnv, LibName, DGraph)
importLib e u =
    case lookupLib e u of
      Just (ln, dg) -> return (e, ln, dg)
      _ -> do
        xmlString <- lift $ readURL u
        OMDoc n l <- liftR $ xmlIn xmlString
        ln <- lift $ libNameFromURL n u
        (e', dg) <- foldM (addTLToDGraph ln) (e, emptyDG) l
        return (addDGToEnv e' u ln dg, ln, dg)


-- | Adds a view or theory to the DG, the ImpEnv may also be modified.
addTLToDGraph :: LibName -> (ImpEnv, DGraph) -> TLElement
              -> ResultT IO (ImpEnv, DGraph)
-- adding a theory to the DG
addTLToDGraph ln (e, dg) (TLTheory n mCD l) =
    let nd = getNewNodeDG dg
        ndName = emptyNodeName { getName = Token n nullRange }
        ndInfo = newNodeInfo DGBasic
    in case getLogicFromMeta mCD of
         Logic lid -> do
           let extSig = makeExtSign lid $ empty_signature lid
               gth = noSensGTheory lid extSig startSigId
           return $ (e, insNodeDG (nd, newInfoNodeLab ndName ndInfo gth) dg)

-- TODO: adding a view to the DG
addTLToDGraph ln (e, dg) (TLView n from to mMor) = 
    return (e, dg)


{-

TODO:
addTCToDGraph :: LibName -> (ImpEnv, DGraph) -> TCElement
              -> ResultT IO (ImpEnv, DGraph)
addTCToDGraph ln p@(e, dg) tc =
    case tc of
      -- import
      TCImport _ from morph ->
          do
            -- get source sign
            -- get target sign
            -- 
            DefLink

      -- TODO: other elements
      _ -> return p


importLib
induced_from_to_morphism ::
             lid -> EndoMap raw_symbol -> ExtSign sign symbol
                 -> ExtSign sign symbol -> Result morphism

-- inserts a morphism as a link to the development graph
addMorphToDG :: Morphism -> DGraph -> LibEnvFull -> DGraph
addMorphToDG morph dg libs =
  let gmorph = gEmbed $ G_morphism LF morph startMorId
      thmStatus = Proven (DGRule "Type-checked") emptyProofBasis
      linkKind = case morphType morph of
                      Definitional -> DefLink
                      Postulated -> ThmLink thmStatus
                      Unknown -> error "Unknown morphism type."
      consStatus = ConsStatus Cons.None Cons.None LeftOpen
      linkType = ScopedLink Global linkKind consStatus
      linkLabel = defDGLink gmorph linkType SeeTarget
      (node1,dg1) = addRefNode dg (source morph) libs
      (node2,dg2) = addRefNode dg1 (target morph) libs
      in snd $ insLEdgeDG (node1,node2,linkLabel) dg2



addTheory :: ImpEnv -> DGraph -> TLElement -> IO ImpEnv
addTheory e dg (TLTheory n mMeta l) = do
  -- make the labeled node and 

-- inserts a signature as a node to the development graph
addSigToDG :: Sign -> DGraph -> (Node,DGraph)
addSigToDG sig dg =
  let node = getNewNodeDG dg
      m = sigModule sig
      nodeName = emptyNodeName { getName = Token m nullRange }
      info = newNodeInfo DGBasic
      extSign = makeExtSign LF sig
      gth = noSensGTheory LF extSign startSigId
      nodeLabel = newInfoNodeLab nodeName info gth
      dg1 = insNodeDG (node,nodeLabel) dg
      in (node,dg1)


readOMDoc


-}