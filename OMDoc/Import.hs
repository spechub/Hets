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

module OMDoc.Import (anaOMDocFile)
    where

import Common.Result
import Common.ResultT
-- import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Utils
-- import Common.AS_Annotation

import Driver.ReadFn (libNameToFile)
import Driver.Options (rmSuffix, HetcatsOpts, putIfVerbose, showDiags)

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
import OMDoc.XmlInterface (xmlIn)

import System.Directory

import Data.Graph.Inductive.Graph (LNode)
import Data.Maybe
import Data.List
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans

import Network.URI

-- * Import Environment Interface

sorry = error "Under construction"

-- | the keys consist of the filepaths without suffix!
data ImpEnv = ImpEnv { libMap :: Map.Map FilePath (LibName, DGraph) }

initialEnv :: ImpEnv
initialEnv = ImpEnv { libMap = Map.empty }

getLibEnv :: ImpEnv -> LibEnv
getLibEnv = Map.fromList . Map.elems . libMap

addDGToEnv :: ImpEnv -> LibName -> DGraph -> ImpEnv
addDGToEnv e ln dg =
    e { libMap = Map.insert (libNameToFile ln) (ln, dg) $ libMap e }

lookupLib :: ImpEnv -> URI -> Maybe (LibName, DGraph)
lookupLib e u = Map.lookup (rmSuffix $ uriPath u) $ libMap e


lookupNode :: ImpEnv -> CurrentLib -> UriCD -> Maybe (LibName, LNode DGNodeLab)
lookupNode e (ln, dg) ucd =
    let mn = getModule ucd in
    if cdInLib ucd ln then
        case lookupNodeByName mn dg of
          Nothing -> error $ "lookupNode: Node not found: " ++ mn
          Just lnode -> Just (ln, lnode)
    else case lookupLib e $ fromJust $ getUri ucd of
           Nothing -> Nothing
           Just (ln', dg') -> fmap (\n -> (ln', n)) $ lookupNodeByName mn dg'

  
-- * URI Functions

readURL :: URI -> IO String
readURL u = if isFileURI u then readFile $ uriPath u
            else error $ "readURI: Unsupported URI-scheme " ++ uriScheme u

toURI :: String -> URI
toURI s = case parseURIReference s of
            Just u -> u
            _ -> error $ "toURI: can't parse as uri " ++ s

libNameFromURL :: String -> URI -> IO LibName
libNameFromURL s u = do let fp = uriPath u
                        mt <- getModificationTime fp
                        return $ setFilePath fp mt $ emptyLibName s

-- | Compute an absolute URI for a supplied URI relative to the given filepath.
resolveURI :: URI -> FilePath -> URI
resolveURI u fp = fromMaybe (error $ "toURI: can't resolve uri " ++ show u)
                  $ relativeTo u $ toURI fp

-- | Is the scheme of the uri empty or file?
isFileURI :: URI -> Bool
isFileURI u = elem (uriScheme u) ["", "file:"]


type UriCD = (Maybe URI, String)

getUri :: UriCD -> Maybe URI
getUri = fst

getModule :: UriCD -> String
getModule = snd

toUriCD :: OMCD -> UriCD
toUriCD cd = let [base, m] = cdToList cd in
             if null base then (Nothing, m) else (Just $ toURI base, m)


getLogicFromMeta :: Maybe OMCD -> AnyLogic
getLogicFromMeta mCD =
    let p (Logic lid) = case omdoc_metatheory lid of
                          Just cd' -> (fromJust mCD) == cd'
                          _ -> False
    in if isNothing mCD then defaultLogic else
           case find p logicList of
             Just al -> al
             _ -> defaultLogic

cdInLib :: UriCD -> LibName -> Bool
cdInLib ucd ln = case getUri ucd of
                   Nothing -> True
                   Just url -> isFileURI url && getFilePath ln == uriPath url

-- | Compute an absolute URI for a supplied UriCD relative to the given LibName.
uriInLib :: UriCD -> LibName -> URI
uriInLib = sorry

-- * Main translation functions

-- | Translates an OMDoc file to a LibEnv
anaOMDocFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaOMDocFile opts fp = do
  dir <- getCurrentDirectory
  putIfVerbose opts 2 $ "anaOMDocFile: Importing OMDoc file " ++ fp
  Result ds mEnvLn <- runResultT $ importLib initialEnv
                      $ resolveURI (toURI fp) $ dir ++ "/"
  showDiags opts ds
  return $ fmap (\ (env, ln, _) -> (ln, getLibEnv env)) mEnvLn


-- * OMDoc traversal

-- | If the lib is not already in the environment, the OMDoc file and
--   the closure of its imports is added to the environment.
importLib :: ImpEnv -- ^ The import environment
          -> URI -- ^ The url of the OMDoc file
          -> ResultT IO (ImpEnv, LibName, DGraph)
importLib e u =
    case lookupLib e u of
      Just (ln, dg) -> return (e, ln, dg)
      _ -> readLib e u

-- | The OMDoc file and the closure of its imports is added to the environment.
readLib :: ImpEnv -- ^ The import environment
        -> URI -- ^ The url of the OMDoc file
        -> ResultT IO (ImpEnv, LibName, DGraph)
readLib e u = do
  xmlString <- lift $ readURL u
  OMDoc n l <- liftR $ xmlIn xmlString
  ln <- lift $ libNameFromURL n u
  (e', dg) <- foldM (addTLToDGraph ln) (e, emptyDG) l
  return (addDGToEnv e' ln dg, ln, dg)

-- | Adds the Theory in the OMCD and the containing lib to the environment
importTheory :: ImpEnv -- ^ The import environment
             -> CurrentLib -- ^ The current lib
             -> OMCD -- ^ The cd which points to the Theory
             -> ResultT IO (ImpEnv, CurrentLib, LNode DGNodeLab)
importTheory e cl@(ln, dg) cd =
    let ucd = toUriCD cd in
    case lookupNode e (ln, dg) ucd of
      Just (ln', nd)
          | ln == ln' -> return (e, cl, nd)
          | otherwise -> let (lnode, dg') = addNodeRefToDG nd ln' dg
                         in return (e, (ln, dg'), lnode)
      _ -> do
        let u = uriInLib ucd ln
        (e', ln', dg') <- readLib e u
        case lookupNodeByName (getModule ucd) dg of
          Just nd -> let (lnode, dg'') = addNodeRefToDG nd ln' dg'
                     in return (e', (ln', dg''), lnode)
          Nothing -> error $ "importTheory: couldn't find node: " ++ show cd
        -- import the lib to the environment, search the node in the devgraph
        -- and add a refnode to it


-- | Adds a view or theory to the DG, the ImpEnv may also be modified.
addTLToDGraph :: LibName -> (ImpEnv, DGraph) -> TLElement
              -> ResultT IO (ImpEnv, DGraph)
-- adding a theory to the DG
addTLToDGraph ln (e, dg) (TLTheory n mCD l) =
    let TCClf iInfo syms sens adt nameMap = classifyTCs l
        -- I. Compute local sig and add the node to the DGraph
        (lnode, dg') = addNodeToDG dg n $ getLogicFromMeta mCD
    in do
      -- II. Lookup all imports (= follow and create them first) 
      ((e', dg''), iIL) <- followImports ln (e, dg') iInfo
       -- III. Compute morphisms and update local sig stepwise
       -- IV. Create links from the morphisms
       --     (and insert DGNodeRefs if neccessary)
       -- V. Add the sentences to the Node
       -- VI. Update the Node in the DGraph
      return $ (e', dg'')

-- TODO: adding a view to the DG
addTLToDGraph ln (e, dg) (TLView n from to mMor) = 
    return (e, dg)



followImports :: LibName -> (ImpEnv, DGraph) -> [ImportInfo OMCD]
              -> ResultT IO ((ImpEnv, DGraph), [ImportInfo LinkNode])
followImports ln env l = mapAccumLCM (curry snd) (followImport ln) env l


followImport :: LibName -> (ImpEnv, DGraph) -> ImportInfo OMCD
             -> ResultT IO ((ImpEnv, DGraph), ImportInfo LinkNode)
followImport ln (e, dg) (ImportInfo (cd, n, morph)) = 
    -- 1. lookup node
    -- 2. return fmapped entry
    sorry


-- * Development Graph and LibEnv interface

-- | Adds an empty Node of the given logic to the development graph.
addNodeToDG :: DGraph -> String -> AnyLogic -> (LNode DGNodeLab, DGraph)
addNodeToDG dg n lg =
    case lg of
      Logic lid ->
          let nd = getNewNodeDG dg
              ndName = emptyNodeName { getName = Token n nullRange }
              ndInfo = newNodeInfo DGBasic
              extSig = makeExtSign lid $ empty_signature lid
              gth = noSensGTheory lid extSig startSigId
              newNode = (nd, newInfoNodeLab ndName ndInfo gth)
          in (newNode, insNodeDG newNode dg)


addNodeRefToDG :: LNode DGNodeLab -> LibName -> DGraph -> (LNode DGNodeLab, DGraph)
addNodeRefToDG = sorry

-- * Theory-types and -utils


type CurrentLib = (LibName, DGraph)

type LinkNode = (Maybe LibName, LNode DGNodeLab)

newtype ImportInfo a = ImportInfo (a, String, TCMorphism)

instance Functor ImportInfo where fmap f (ImportInfo (x,y,z))
                                      = ImportInfo (f x, y, z)

data TCClassification = TCClf {
      importInfo :: [ImportInfo OMCD] -- ^ Import-info
    , sigElems :: [TCElement] -- ^ Signature symbols
    , sentences :: [TCElement] -- ^ Theory sentences
    , adts :: [[OmdADT]] -- ^ ADTs
    , notations :: (Map.Map OMName String) -- ^ Notations
    }
    

emptyClassification :: TCClassification
emptyClassification = TCClf [] [] [] [] Map.empty

classifyTCs :: [TCElement] -> TCClassification
classifyTCs l = foldr classifyTC emptyClassification l

classifyTC :: TCElement -> TCClassification -> TCClassification
classifyTC tc clf =
    case tc of
      TCSymbol n tp sr mDef
          | elem sr [Obj, Typ] -> clf { sigElems = tc : sigElems clf }
          | otherwise -> clf { sentences = tc : sentences clf }
      TCNotation (cd, omn) n ->
          if cdIsEmpty cd then 
              clf { notations = Map.insert omn n $ notations clf }
          else clf
      TCADT l -> clf { adts = l : adts clf }
      TCImport n from morph ->
          clf { importInfo = ImportInfo (from, n, morph) : importInfo clf }
      TCComment _ -> clf


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