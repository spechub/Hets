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
import Common.ExtSign
import Common.Id
import Common.LibName
import Common.Utils
-- import Common.AS_Annotation

import Driver.ReadFn (libNameToFile)
import Driver.Options (rmSuffix, HetcatsOpts, putIfVerbose, showDiags)

import Logic.Logic
import Logic.ExtSign
import Logic.Coerce
-- import Logic.Prover
import Logic.Grothendieck
-- import Logic.Comorphism

import Comorphisms.LogicList

import Static.DevGraph
import Static.GTheory
import Static.AnalysisStructured

import OMDoc.DataTypes
import OMDoc.XmlInterface (xmlIn)

import System.Directory

import Data.Graph.Inductive.Graph (LNode, Node)
import Data.Maybe
import Data.List
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Control.Monad
import Control.Monad.Trans

import Network.URI

-- only for debugging
import Debug.Trace
import System.IO
-- * Import Environment Interface

{-
sorry :: a
sorry = error "Under construction"

debugOut :: String -> ResultT IO ()
debugOut = lift . putStrLn . ("Debug: " ++)
-}

mytrace :: [String] -> IO ()
mytrace  = hPutStrLn stderr . concat

{- | There are three important maps for each theory:
 1. OMName -> symbol, the NameSymbolMap stores for each OMDoc name the
                      translated hets symbol
 2. OMName -> String, the nameMap stores the notation information of the
                      OMDoc names, identity mappings are NOT stored here!
 3. SigMapI symbol, this signature map is just a container to store map 1 and 2
-}
type NameSymbolMap = G_mapofsymbol OMName

-- | the keys consist of the filepaths without suffix!
data ImpEnv =
    ImpEnv { libMap :: Map.Map FilePath (LibName, DGraph)
           , nsymbMap :: Map.Map (LibName, String) NameSymbolMap }

initialEnv :: ImpEnv
initialEnv = ImpEnv { libMap = Map.empty, nsymbMap = Map.empty }

getLibEnv :: ImpEnv -> LibEnv
getLibEnv = Map.fromList . Map.elems . libMap

addDGToEnv :: ImpEnv -> LibName -> DGraph -> ImpEnv
addDGToEnv e ln dg =
    e { libMap = Map.insert (libNameToFile ln) (ln, dg) $ libMap e }

addNSMapToEnv :: ImpEnv -> LibName -> String -> NameSymbolMap -> ImpEnv
addNSMapToEnv e ln nm nsm =
    e { nsymbMap = Map.insert (ln, nm) nsm $ nsymbMap e }

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
           Just (ln', dg') -> fmap (\ n -> (ln', n)) $ lookupNodeByName mn dg'

lookupNSMap :: ImpEnv -> LibName -> Maybe LibName -> String -> NameSymbolMap
lookupNSMap e ln mLn nm =
    let ln' = fromMaybe ln mLn
        mf = Map.findWithDefault
             $ error $ "lookupNSMap: lookup failed for " ++ show (mLn, nm, nsymbMap e)
    in mf (ln', nm) $ nsymbMap e


lookupNotation :: SigMapI a -> OMName -> String
lookupNotation smi n = Map.findWithDefault (name n) n $ sigMapINotations smi


-- * URI Functions

readURL :: URI -> IO String
readURL u = if isFileURI u then mytrace ["readURL: ", show u] >> (readFile $ uriPath u)
            else error $ "readURI: Unsupported URI-scheme " ++ uriScheme u

toURI :: String -> URI
toURI s = case parseURIReference s of
            Just u -> u
            _ -> error $ "toURI: can't parse as uri " ++ s

libNameFromURL :: String -> URI -> IO LibName
libNameFromURL s u = do
  let fp = uriPath u
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
uriRelativeToLib :: UriCD -> LibName -> URI
uriRelativeToLib ucd ln =
    let fp = getFilePath ln in
    case getUri ucd of
      Just u -> resolveURI u fp
      _ -> toURI fp


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
-- the closure of its imports is added to the environment.
importLib :: ImpEnv -- ^ The import environment
          -> URI -- ^ The url of the OMDoc file
          -> ResultT IO (ImpEnv, LibName, DGraph)
importLib e u =
    lift (mytrace ["importLib: ", show u]) >> 
    case lookupLib e u of
      Just (ln, dg) -> lift (mytrace ["foundLib: ", show ln]) >> return (e, ln, dg)
      _ -> readLib e u

-- | The OMDoc file and the closure of its imports is added to the environment.
readLib :: ImpEnv -- ^ The import environment
        -> URI -- ^ The url of the OMDoc file
        -> ResultT IO (ImpEnv, LibName, DGraph)
readLib e u = do
  xmlString <- lift $ readURL u
  OMDoc n l <- liftR $ xmlIn xmlString
  lift $ mytrace ["readlib: ", n, " -- ", show u]
  ln <- lift $ libNameFromURL n u
  (e', dg) <- foldM (addTLToDGraph ln) (e, emptyDG) l
  return (addDGToEnv e' ln dg, ln, dg)

-- | Adds the Theory in the OMCD and the containing lib to the environment
importTheory :: ImpEnv -- ^ The import environment
             -> CurrentLib -- ^ The current lib
             -> OMCD -- ^ The cd which points to the Theory
             -> ResultT IO ( ImpEnv -- ^ the updated environment
                           , LibName -- ^ the origin libname of the theory
                           , DGraph -- ^ the updated devgraph of the current lib
                           , LNode DGNodeLab -- ^ the corresponding node
                           )
importTheory e (ln, dg) cd =
    let ucd = toUriCD cd in
    case lookupNode e (ln, dg) ucd of
      Just (ln', nd)
          | ln == ln' -> trace ("importTheory: already linked " ++ show ucd) $ return (e, ln, dg, nd)
          | otherwise -> let (lnode, dg') = addNodeAsRefToDG nd ln' dg
                         in trace ("importTheory: not linked " ++ show ucd) $ return (e, ln', dg', lnode)
      -- if lookupNode finds nothing implies that ln is not the current libname!
      _ -> do
        let u = uriRelativeToLib ucd ln
        lift $ mytrace ["{importTheory: new lib ", show ucd]
        (e', ln', refDg) <- readLib e u
        lift $ mytrace ["read lib: ", show ln', " nsymbMap size: ", show $ Map.size $ nsymbMap e']
        case lookupNodeByName (getModule ucd) refDg of
          -- don't add the node to the refDG but to the original DG!
          Just nd -> let (lnode, dg') = addNodeAsRefToDG nd ln' dg
                     in trace ("importTheory: added refnode}") $ return (e', ln', dg', lnode)
          Nothing -> error $ "importTheory: couldn't find node: " ++ show cd


-- | Adds a view or theory to the DG, the ImpEnv may also be modified.
addTLToDGraph :: LibName -> (ImpEnv, DGraph) -> TLElement
              -> ResultT IO (ImpEnv, DGraph)
-- adding a theory to the DG
addTLToDGraph ln (e, dg) (TLTheory n mCD l) = do
  let clf = classifyTCs l

  -- I. Compute initial signature
  lift $ mytrace ["{processing theory: ", n]
  (gSig, nsmap) <- liftR $ initialSig clf $ getLogicFromMeta mCD

  -- II. Lookup all imports (= follow and create them first),
  -- and insert DGNodeRefs if neccessary.
  ((e', dg'), iIL) <- followImports ln (e, dg) $ importInfo clf

  lift $ mytrace [ "followed Imports: nsymbMap size: "
                 , show $ Map.size $ nsymbMap e'
                 , "iIL: ", show iIL]

  -- III. Compute morphisms and update local sig stepwise.
  (gSig', iIWL) <- computeMorphisms e' ln nsmap gSig iIL

  lift $ mytrace [ "computed Morphisms"]

  -- IV. Add the sentences to the Node.
  -- TODO

  -- V. Add the Node to the DGraph.
  let ((nd, _), dg'') = addNodeToDG dg' n gSig'
      -- VI. Create links from the morphisms.
      dg''' = addLinksToDG nd dg'' iIWL
      -- add the new name symbol map to the environment
      e'' = addNSMapToEnv e' ln n nsmap
  lift $ mytrace ["added nsmap for theory: ", n, " nsymbMap size: ", show $ Map.size $ nsymbMap e'']

  return $ trace ("Theory processed}") $ (e'', dg''')


-- TODO: adding a view to the DG
addTLToDGraph _ (e, dg) _ = -- (TLView n from to mMor) =
    return (e, dg)


-- ** Utils to compute DGNodes from OMDoc Theories

computeMorphisms :: ImpEnv -> LibName -> NameSymbolMap -> G_sign
                 -> [ImportInfo LinkNode]
                 -> ResultT IO (G_sign, [LinkInfo])
computeMorphisms e ln nsmap = mapAccumLM (computeMorphism e ln nsmap)

computeMorphism :: ImpEnv -- ^ The import environment for lookup purposes
                -> LibName -- ^ Current libname
                -> NameSymbolMap -- ^ OMDoc symbol to Hets symbol map
                -> G_sign -- ^ target signature
                -> ImportInfo LinkNode -- ^ source label with OMDoc morphism
                -> ResultT IO (G_sign, LinkInfo)
computeMorphism e ln nsmap tGSig iIL@(ImportInfo (_, (from, lbl)) n _)
    = case dgn_theory lbl of
        G_theory sLid (ExtSign sSig _) _ _ _ ->
            case tGSig of
              G_sign tLid (ExtSign tSig _) sigId ->
                  do
                    -- 1. build the morphism
                    -- compute first the symbol-map
                    symMap <- computeSymbolMap e ln nsmap iIL tLid
                    let
                        f = symbol_to_raw tLid
                        rsMap = Map.fromList $ map (\ (x, y) -> (f x, f y) )
                                symMap
                    -- REMARK: Logic-homogeneous environment assumed
                    sSig' <- coercePlainSign sLid tLid "computeMorphism" sSig
                    mor <- liftR $ induced_from_morphism tLid rsMap sSig'
                    -- 2. build the GMorphism and update the signature
                    newSig <- liftR $ signature_union tLid tSig $ cod mor
                    let gMor = gEmbed $ mkG_morphism tLid mor
                        newGSig = G_sign tLid (makeExtSign tLid newSig) sigId
                    -- 3. update the signature
                    return (newGSig, (gMor, globalDef, mkLinkOrigin n, from))

mkLinkOrigin :: String -> DGLinkOrigin
mkLinkOrigin s = DGLinkMorph $ mkSimpleId s

computeSymbolMap :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        ImpEnv -> LibName -> NameSymbolMap -> ImportInfo LinkNode -> lid
               -> ResultT IO [(symbol, symbol)]
computeSymbolMap e ln nsmap (ImportInfo (mLn, (_, lbl)) _ morph) lid =
  case (lookupNSMap e ln mLn $ getDGNodeName lbl, nsmap) of
    (G_mapofsymbol sLid sm, G_mapofsymbol tLid tm) ->
        do
          -- REMARK: Logic-homogeneous environment assumed
          let sNSMap = coerceMapofsymbol sLid lid sm
              tNSMap = coerceMapofsymbol tLid lid tm
              mf = Map.findWithDefault $ error "computeSymbolMap: lookup failed"
              -- function for the map functor
              f (omn, ome) =
                  case ome of
                    OMS qn ->
                        let tSymName = (unqualName qn)
                            tSym = mf tSymName tNSMap
                        in (mf omn sNSMap, tSym)
                    _ -> error "computeSymbolMap: Nonsymbol element mapped"
          return $ map f morph


followImports :: LibName -> (ImpEnv, DGraph) -> [ImportInfo OMCD]
              -> ResultT IO ((ImpEnv, DGraph), [ImportInfo LinkNode])
followImports ln = mapAccumLCM (curry snd) (followImport ln)

-- | We lookup the theory referenced by the cd in the environment
-- and add it if neccessary to the environment.
followImport :: LibName -> (ImpEnv, DGraph) -> ImportInfo OMCD
             -> ResultT IO ((ImpEnv, DGraph), ImportInfo LinkNode)
followImport ln (e, dg) iInfo@(ImportInfo cd  _ _) = do
  lift $ mytrace ["following: ", show ln, " --> ", show cd]
  (e', ln', dg', lnode) <- importTheory e (ln, dg) cd
  let linknode = (if ln == ln' then Nothing else Just ln', lnode)
  return $ ((e', dg'), fmap (const linknode) iInfo)


-- * Development Graph and LibEnv interface


-- | returns a function compatible with mapAccumLM for TCElement processing.
--   Used in initialSig.
sigmapAccumFun :: (Monad m, Show a) => (SigMapI a -> TCElement -> String -> m a)
               -> SigMapI a -> TCElement -> m (SigMapI a, a)
sigmapAccumFun f smi s = do
  let n = tcName s
      hetsname = lookupNotation smi n
  s' <- trace ("lookup for " ++ show n) $ f smi s hetsname
  let smi' = smi { sigMapISymbs = Map.insert n s' $ sigMapISymbs smi }
  trace ("returns " ++ show s') $ return (smi', s')


-- | Builds an initial Sig and a name map of the given logic and classification.
initialSig :: TCClassification -> AnyLogic -> Result (G_sign, NameSymbolMap)
initialSig clf lg =
    case lg of
      Logic lid ->
          do
            let initSM = SigMapI Map.empty $ notations clf
            -- accumulates symbol mappings in the symbMap in SigMapI
            -- while creating symbols from OMDoc symbols
            (sm, symbs) <- mapAccumLM (sigmapAccumFun $ omdocToSym lid) initSM
                           $ sigElems clf
            -- adding the symbols to the empty signature
            sig <- foldM (add_symb_to_sign lid) (empty_signature lid) symbs
            let gsig = G_sign lid (makeExtSign lid sig) startSigId
            return (gsig, G_mapofsymbol lid $ sigMapISymbs sm)

-- | Adds Edges from the LinkInfo list to the development graph.
addLinksToDG :: Node -> DGraph -> [LinkInfo] -> DGraph
addLinksToDG nd = foldl (addLinkToDG nd)

-- | Adds Edge from the LinkInfo to the development graph.
addLinkToDG :: Node -> DGraph -> LinkInfo -> DGraph
addLinkToDG to dg (gMor, lt, lo, from) = insLink dg gMor lt lo from to


-- | Adds a Node from the given signature to the development graph.
addNodeToDG :: DGraph -> String -> G_sign -> (LNode DGNodeLab, DGraph)
addNodeToDG dg n gSig =
    case gSig of
      G_sign lid eSig sigId ->
          let nd = getNewNodeDG dg
              -- we should parse the name and restore the NodeName
              ndName = makeName $ mkSimpleId n
              ndInfo = newNodeInfo DGBasic
              gth = noSensGTheory lid eSig sigId
              newNode = (nd, newInfoNodeLab ndName ndInfo gth)
          in (newNode, insNodeDG newNode dg)


addNodeAsRefToDG :: LNode DGNodeLab -> LibName -> DGraph
                 -> (LNode DGNodeLab, DGraph)
addNodeAsRefToDG (nd, lbl) ln dg =
    let info = newRefInfo ln nd
        refNodeM = lookupInAllRefNodesDG info dg
        nd' = getNewNodeDG dg
        lnode = (nd', lbl { nodeInfo = info })
        dg1 = insNodeDG lnode dg
        dg2 = addToRefNodesDG nd' info dg1
    in case refNodeM of
         Just refNode -> ((refNode, labDG dg refNode), dg)
         _ -> (lnode, dg2)


-- * Theory-utils

type CurrentLib = (LibName, DGraph)

type LinkNode = (Maybe LibName, LNode DGNodeLab)

type LinkInfo = (GMorphism, DGLinkType, DGLinkOrigin, Node)

data ImportInfo a = ImportInfo a String TCMorphism deriving Show

instance Functor ImportInfo where fmap f (ImportInfo x y z)
                                      = ImportInfo (f x) y z

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
      TCSymbol _ _ sr _
          | elem sr [Obj, Typ] -> clf { sigElems = tc : sigElems clf }
          | otherwise -> clf { sentences = tc : sentences clf }
      TCNotation (cd, omn) n ->
          if cdIsEmpty cd then
              clf { notations = Map.insert omn n $ notations clf }
          else clf
      TCADT l -> clf { adts = l : adts clf }
      TCImport n from morph ->
          clf { importInfo = (ImportInfo from n morph) : importInfo clf }
      TCComment _ -> clf
