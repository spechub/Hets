{-# LANGUAGE ExistentialQuantification #-}
{- |
Module      :  ./OMDoc/Import.hs
Description :  Transforms an OMDoc file into a development graph
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

Given an OMDoc file, a Library Environment is constructed from it by
following all library links.

The import requires the following interface functions to be instantiated
for each logic

Signature Category:
ide, cod

Sentences:
symmap_of

StaticAnalysis:
id_to_raw, symbol_to_raw, induced_from_morphism, induced_from_to_morphism
, signature_union, empty_signature, add_symb_to_sign

Logic:
omdoc_metatheory, omdocToSym, omdocToSen

These functions have default implementations which are sufficient
in many cases:
addOMadtToTheory, addOmdocToTheory


-}

module OMDoc.Import where

import Common.Result
import Common.ResultT
import Common.ExtSign
import Common.Id
import Common.IRI
import Common.LibName
import Common.Utils
import Common.XmlParser (readXmlFile)

import Driver.ReadFn (libNameToFile)
import Driver.Options (rmSuffix, HetcatsOpts, putIfVerbose, showDiags)

import Logic.Logic
    ( AnyLogic (Logic)
    , Logic ( omdoc_metatheory, omdocToSym, omdocToSen, addOMadtToTheory
           , addOmdocToTheory)
    , Category (ide, cod)
    , StaticAnalysis ( induced_from_morphism, induced_from_to_morphism
                    , signature_union, empty_signature, add_symb_to_sign
                    , symbol_to_raw, id_to_raw )
    , Sentences (symmap_of) )
import Logic.ExtSign
import Logic.Coerce
import Logic.Prover
import Logic.Grothendieck

import Comorphisms.LogicList
import Comorphisms.LogicGraph

import Static.DevGraph
import Static.DgUtils
import Static.GTheory
import Static.AnalysisStructured
import Static.ComputeTheory

import OMDoc.DataTypes
import OMDoc.XmlInterface (xmlIn)

import System.Directory

import Data.Graph.Inductive.Graph (LNode, Node)
import Data.Maybe
import Data.List
import qualified Data.Map as Map
import Control.Monad
import Control.Monad.Trans

-- * Import Environment Interface

{- | There are three important maps for each theory:
 1. OMName -> symbol, the NameSymbolMap stores for each OMDoc name the
                      translated hets symbol
 2. OMName -> String, the NameMap stores the notation information of the
                      OMDoc names, identity mappings are NOT stored here!
 3. SigMapI symbol, this signature map is just a container to store map 1 and 2
-}
type NameSymbolMap = G_mapofsymbol OMName

-- | The keys of libMap consist of the filepaths without suffix!
data ImpEnv =
    ImpEnv {
      libMap :: Map.Map FilePath (LibName, DGraph)
    , nsymbMap :: Map.Map (LibName, String) NameSymbolMap
    , hetsOptions :: HetcatsOpts
    }

initialEnv :: HetcatsOpts -> ImpEnv
initialEnv opts = ImpEnv { libMap = Map.empty
                         , nsymbMap = Map.empty
                         , hetsOptions = opts }

getLibEnv :: ImpEnv -> LibEnv
getLibEnv e = computeLibEnvTheories $
              Map.fromList $ Map.elems $ libMap e

addDGToEnv :: ImpEnv -> LibName -> DGraph -> ImpEnv
addDGToEnv e ln dg =
    e { libMap = Map.insert (libNameToFile ln) (ln, dg) $ libMap e }

addNSMapToEnv :: ImpEnv -> LibName -> String -> NameSymbolMap -> ImpEnv
addNSMapToEnv e ln nm nsm =
    e { nsymbMap = Map.insert (ln, nm) nsm $ nsymbMap e }

lookupLib :: ImpEnv -> IRI -> Maybe (LibName, DGraph)
lookupLib e u = Map.lookup (rmSuffix $ show $ iriPath u) $ libMap e


lookupNode :: ImpEnv -> CurrentLib -> IriCD
           -> Maybe ( LibName -- the origin libname of the theory
                    , LNode DGNodeLab -- the (eventually reference) node
                    )
lookupNode e (ln, dg) ucd =
    let mn = getModule ucd in
    if cdInLib ucd ln then
        case filterLocalNodesByName mn dg of
          [] -> error $ "lookupNode: Node not found: " ++ mn
          lnode : _ -> Just (ln, lnode)
    else case lookupLib e $ fromJust $ getIri ucd of
           Nothing -> Nothing
           Just (ln', dg') ->
               case filterRefNodesByName mn ln' dg of
                 lnode : _ -> Just (ln', lnode)
                 [] -> listToMaybe
                   $ map (\ n -> (ln', n)) $ filterLocalNodesByName mn dg'

lookupNSMap :: ImpEnv -> LibName -> Maybe LibName -> String -> NameSymbolMap
lookupNSMap e ln mLn nm =
    let ln' = fromMaybe ln mLn
        mf = Map.findWithDefault
             $ error $ concat [ "lookupNSMap: lookup failed for "
                              , show (ln', nm), "\n", show mLn, "\n"
                              , show $ nsymbMap e ]
    in mf (ln', nm) $ nsymbMap e


rPutIfVerbose :: ImpEnv -> Int -> String -> ResultT IO ()
rPutIfVerbose e n s = lift $ putIfVerbose (hetsOptions e) n s

rPut :: ImpEnv -> String -> ResultT IO ()
rPut e = rPutIfVerbose e 1

rPut2 :: ImpEnv -> String -> ResultT IO ()
rPut2 e = rPutIfVerbose e 2

-- * IRI Functions

readFromURL :: (FilePath -> IO a) -> IRI -> IO a
readFromURL f u = if isFileIRI u then f $ show $ iriPath u
                  else error $ "readFromURL: Unsupported IRI-scheme "
                           ++ iriScheme u

toIRI :: String -> IRI
toIRI s = case parseIRIReference s of
            Just u -> u
            _ -> error $ "toIRI: can't parse as iri " ++ s

libNameFromURL :: String -> IRI -> LibName
libNameFromURL s u = setFilePath (show $ iriPath u) $ emptyLibName s

-- | Compute an absolute IRI for a supplied IRI relative to the given filepath.
resolveIRI :: IRI -> FilePath -> IRI
resolveIRI u fp = fromMaybe (error $ "toIRI: can't resolve iri " ++ show u)
                  $ relativeTo u $ toIRI fp

-- | Is the scheme of the iri empty or file?
isFileIRI :: IRI -> Bool
isFileIRI u = elem (iriScheme u) ["", "file:"]


type IriCD = (Maybe IRI, String)

showIriCD :: IriCD -> String
showIriCD (mIri, s) = case mIri of
                        Just u -> show u ++ "?" ++ s
                        _ -> s

getIri :: IriCD -> Maybe IRI
getIri = fst

getModule :: IriCD -> String
getModule = snd


-- | Compute an absolute IRI for a supplied CD relative to the given LibName
toIriCD :: OMCD -> LibName -> IriCD
toIriCD cd ln =
    let [base, m] = cdToList cd
        fp = getFilePath ln
        mU = if null base then Nothing
             else Just $ resolveIRI (toIRI base) fp
    in (mU, m)

getLogicFromMeta :: Maybe OMCD -> AnyLogic
getLogicFromMeta mCD =
    let p (Logic lid) = case omdoc_metatheory lid of
                          Just cd' -> fromJust mCD == cd'
                          _ -> False
    in if isNothing mCD then defaultLogic else
           case find p logicList of
             Just al -> al
             _ -> defaultLogic

cdInLib :: IriCD -> LibName -> Bool
cdInLib ucd ln = case getIri ucd of
                   Nothing -> True
                   Just url -> isFileIRI url && getFilePath ln == (show $ iriPath url)


-- * Main translation functions

-- | Translates an OMDoc file to a LibEnv
anaOMDocFile :: HetcatsOpts -> FilePath -> IO (Maybe (LibName, LibEnv))
anaOMDocFile opts fp = do
  dir <- getCurrentDirectory
  putIfVerbose opts 2 $ "Importing OMDoc file " ++ fp
  Result ds mEnvLn <- runResultT $ importLib (initialEnv opts)
                      $ resolveIRI (toIRI fp) $ dir ++ "/"
  showDiags opts ds
  return $ fmap (\ (env, ln, _) -> (ln, getLibEnv env)) mEnvLn


-- * OMDoc traversal

{- | If the lib is not already in the environment, the OMDoc file and
the closure of its imports is added to the environment. -}
importLib :: ImpEnv -- ^ The import environment
          -> IRI -- ^ The url of the OMDoc file
          -> ResultT IO (ImpEnv, LibName, DGraph)
importLib e u =
    case lookupLib e u of
      Just (ln, dg) -> return (e, ln, dg)
      _ -> readLib e u

-- | The OMDoc file and the closure of its imports is added to the environment.
readLib :: ImpEnv -- ^ The import environment
        -> IRI -- ^ The url of the OMDoc file
        -> ResultT IO (ImpEnv, LibName, DGraph)
readLib e u = do
  rPut e $ "Downloading " ++ show u ++ " ..."
  xmlString <- lift $ readFromURL readXmlFile u
  OMDoc n l <- ResultT $ xmlIn xmlString
  {- the name of the omdoc is used as the libname, no relationship between the
  libname and the filepath! -}
  let ln = libNameFromURL n u
  rPut e $ "Importing library " ++ show ln
  (e', dg) <- foldM (addTLToDGraph ln) (e, emptyDG) l
  rPut e $ "... loaded " ++ show u
  return (addDGToEnv e' ln dg, ln, dg)

-- | Adds the Theory in the OMCD and the containing lib to the environment
importTheory :: ImpEnv -- ^ The import environment
             -> CurrentLib -- ^ The current lib
             -> OMCD -- ^ The cd which points to the Theory
             -> ResultT IO ( ImpEnv -- the updated environment
                           , LibName -- the origin libname of the theory
                           , DGraph -- the updated devgraph of the current lib
                           , LNode DGNodeLab -- the corresponding node
                           )
importTheory e (ln, dg) cd = do
  let ucd = toIriCD cd ln
  rPut2 e $ "Looking up theory " ++ showIriCD ucd ++ " ..."
  case lookupNode e (ln, dg) ucd of
    Just (ln', nd)
        | ln == ln' ->
            do
              rPut2 e "... found local node."
              return (e, ln, dg, nd)
        | isDGRef $ snd nd ->
            do
              rPut2 e "... found already referenced node."
              return (e, ln', dg, nd)
        | otherwise ->
            do
              rPut2 e "... found node, referencing it ..."
              let (lnode, dg') = addNodeAsRefToDG nd ln' dg
              rPut2 e "... done"
              return (e, ln', dg', lnode)
    -- if lookupNode finds nothing implies that ln is not the current libname!
    _ -> do
      let u = fromJust $ getIri ucd
      rPut2 e "... node not found, reading lib."
      (e', ln', refDg) <- readLib e u
      case filterLocalNodesByName (getModule ucd) refDg of
        -- don't add the node to the refDG but to the original DG!
        nd : _ -> let (lnode, dg') = addNodeAsRefToDG nd ln' dg
                   in return (e', ln', dg', lnode)
        [] -> error $ "importTheory: couldn't find node: " ++ show cd


-- | Adds a view or theory to the DG, the ImpEnv may also be modified.
addTLToDGraph :: LibName -> (ImpEnv, DGraph) -> TLElement
              -> ResultT IO (ImpEnv, DGraph)
-- adding a theory to the DG
addTLToDGraph ln (e, dg) (TLTheory n mCD l) = do

  rPut e $ "Importing theory " ++ n

  let clf = classifyTCs l

  {- I. Lookup all imports (= follow and create them first),
  and insert DGNodeRefs if neccessary. -}
  ((e', dg'), iIL) <- followImports ln (e, dg) $ importInfo clf

  -- II. Compute morphisms and update initial sig and name symbol map stepwise.
  ((nsmap, gSig), iIWL) <-
      computeMorphisms e' ln (notations clf)
                           (initialSig $ getLogicFromMeta mCD) iIL

  -- III. Compute local signature
  (nsmap', gSig') <- liftR $ localSig clf nsmap gSig

  -- IV. Add the sentences to the Node.
  gThy <- liftR $ addSentences clf nsmap' gSig'

  -- V. Complete the morphisms with final signature
  iIWL' <- liftR $ completeMorphisms (signOf gThy) iIWL

  -- VI. Add the Node to the DGraph.
  let ((nd, _), dg'') = addNodeToDG dg' n gThy
      -- VII. Create links from the morphisms.
      dg''' = addLinksToDG nd dg'' iIWL'
      -- add the new name symbol map to the environment
      e'' = addNSMapToEnv e' ln n nsmap'

  return (e'', dg''')


addTLToDGraph ln (e, dg) (TLView n from to mMor) = do

  rPut e $ "Importing view " ++ n

  {- follow the source and target of the view and insert DGNodeRefs
  if neccessary.
  use followTheory for from and to. -}
  ((e', dg'), [lkNdFrom, lkNdTo]) <- followTheories ln (e, dg) [from, to]
  lkInf <- computeViewMorphism e' ln $ ImportInfo (lkNdFrom, lkNdTo) n mMor
  let dg'' = addLinkToDG
             {- this error should never occur as the linkinfo contains
             a to-node.
             The error is used here as a "don't care element" of type Node -}
             (error "addTLToDGraph: TLView - Default node not available")
             dg' lkInf
  return (e', dg'')


-- ** Utils to compute DGNodes from OMDoc Theories

{-
 the morphisms are incomplete because the target signature
 wasn't complete at the time of morphism computation.
 we complete the morphisms by composing them with signature inclusions
 to the complete target signature
-}
completeMorphisms :: G_sign -- ^ the complete target signature
                  -> [LinkInfo] -- ^ the incomplete morphisms
                  -> Result [LinkInfo]
completeMorphisms gsig = mapR (fmapLI $ completeMorphism $ ide gsig)

completeMorphism :: GMorphism -- ^ the target signature id morphism
                 -> GMorphism -- ^ the incomplete morphism
                 -> Result GMorphism
completeMorphism idT gmorph = compInclusion logicGraph gmorph idT


computeMorphisms :: ImpEnv -> LibName
                 -> Map.Map OMName String -- ^ Notations
                 -> (NameSymbolMap, G_sign)
                 -> [ImportInfo LinkNode]
                 -> ResultT IO ((NameSymbolMap, G_sign), [LinkInfo])
computeMorphisms e ln nots = mapAccumLM (computeMorphism e ln nots)

{- | Computes the morphism for an import link and updates the signature
and the name symbol map with the imported symbols -}
computeMorphism :: ImpEnv -- ^ The import environment for lookup purposes
                -> LibName -- ^ Current libname
                -> Map.Map OMName String -- ^ Notations of target signature
                -> (NameSymbolMap, G_sign) {- ^ OMDoc symbol to Hets symbol map
                                           and target signature -}
                -> ImportInfo LinkNode -- ^ source label with OMDoc morphism
                -> ResultT IO ((NameSymbolMap, G_sign), LinkInfo)
computeMorphism e ln nots (nsmap, tGSig) (ImportInfo (mLn, (from, lbl)) n morph)
    = case dgn_theory lbl of
        G_theory sLid _ (ExtSign sSig _) _ _ _ ->
            case tGSig of
              G_sign tLid (ExtSign tSig _) sigId ->
                  do
                    let sourceNSMap = lookupNSMap e ln mLn $ getDGNodeName lbl
                    {- 1. build the morphism
                    compute first the symbol-map -}
                    symMap <- computeSymbolMap (Just nots) sourceNSMap nsmap
                              morph tLid
                    let
                        f = symbol_to_raw tLid
                        g (Left (_, rs)) = rs
                        g (Right s) = symbol_to_raw tLid s
                        rsMap = Map.fromList $ map (\ (x, y) -> (f x, g y) )
                                symMap
                    -- REMARK: Logic-homogeneous environment assumed
                    sSig' <- coercePlainSign sLid tLid "computeMorphism" sSig
                    mor <- liftR $ induced_from_morphism tLid rsMap sSig'
                    {- 2. build the GMorphism and update the signature
                    and the name symbol map -}
                    newSig <- liftR $ signature_union tLid tSig $ cod mor
                    let gMor = gEmbed $ mkG_morphism tLid mor
                        newGSig = G_sign tLid (makeExtSign tLid newSig) sigId
                        {- function for filtering the raw symbols in the
                        nsmap update -}
                        h (s, Left (n', _)) = Just (s, n')
                        h (_, Right _) = Nothing
                        nsmap' = updateSymbolMap tLid mor nsmap
                                 $ mapMaybe h symMap
                    return ( (nsmap', newGSig)
                           , (gMor, globalDef, mkLinkOrigin n, from, Nothing))

-- | Computes the morphism for a view
computeViewMorphism :: ImpEnv -- ^ The import environment for lookup purposes
                    -> LibName -- ^ Current libname
                    -> ImportInfo (LinkNode, LinkNode)
                    -- ^ OMDoc morphism with source and target node
                    -> ResultT IO LinkInfo
computeViewMorphism e ln (ImportInfo ( (mSLn, (from, lblS))
                                     , (mTLn, (to, lblT))) n morph)
    = case (dgn_theory lblS, dgn_theory lblT) of
        (G_theory sLid _ eSSig _ _ _, G_theory tLid _ eTSig _ _ _) ->
            do
              let nsmapS = lookupNSMap e ln mSLn $ getDGNodeName lblS
                  nsmapT = lookupNSMap e ln mTLn $ getDGNodeName lblT
              {- 1. build the morphism
              compute first the symbol-map -}
              symMap <- computeSymbolMap Nothing nsmapS nsmapT morph tLid
              let f = symbol_to_raw tLid
                  {- this can't occur as we do not provide a notation map
                  to computeSymbolMap -}
                  g (Left _) = error "computeViewMorphism: impossible case"
                  g (Right s) = symbol_to_raw tLid s
                  rsMap = Map.fromList
                          $ map (\ (x, y) -> (f x, g y) ) symMap
              -- REMARK: Logic-homogeneous environment assumed
              eSSig' <- coerceSign sLid tLid "computeViewMorphism" eSSig
              mor <- liftR $ induced_from_to_morphism tLid rsMap eSSig' eTSig
              -- 2. build the GMorphism
              let gMor = gEmbed $ mkG_morphism tLid mor
              return (gMor, globalThm, mkLinkOrigin n, from, Just to)


mkLinkOrigin :: String -> DGLinkOrigin
mkLinkOrigin s = DGLinkMorph $ simpleIdToIRI $ mkSimpleId s

{- | For each entry (s, n) in l we enter the mapping (n, m(s))
to the name symbol map -}
updateSymbolMap :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        lid -> morphism -- ^ a signature morphism m
            -> NameSymbolMap
            -> [(symbol, OMName)] -- ^ a list l of symbol to OMName mappings
            -> NameSymbolMap
updateSymbolMap lid mor nsmap l =
    case nsmap of
      G_mapofsymbol lid' sm ->
          let f nsm (s, n) = Map.insert n (g s) nsm -- fold function
              g s = Map.findWithDefault
                    (error $ "updateSymbolMap: symbol not found " ++ show s)
                    s $ symmap_of lid mor
              sm' = coerceMapofsymbol lid' lid sm
          in G_mapofsymbol lid $ foldl f sm' l

{- | Computes a symbol map for the given TCMorphism. The symbols are looked
   up in the provided maps. For each symbol not found in the target map we
   return a OMName, raw symbol pair in order to insert the missing entries
   in the target name symbol map later. If notations are not present, all
   lookup failures end up in errors.
-}
computeSymbolMap :: forall lid sublogics
        basic_spec sentence symb_items symb_map_items
         sign morphism symbol raw_symbol proof_tree .
        Logic lid sublogics
         basic_spec sentence symb_items symb_map_items
          sign morphism symbol raw_symbol proof_tree =>
        Maybe (Map.Map OMName String) -- ^ Notations for missing symbols in map
            -> NameSymbolMap -> NameSymbolMap -> TCMorphism -> lid
            -> ResultT IO [(symbol, Either (OMName, raw_symbol) symbol)]
computeSymbolMap mNots nsmapS nsmapT morph lid =
  case (nsmapS, nsmapT) of
    (G_mapofsymbol sLid sm, G_mapofsymbol tLid tm) ->
        do
          -- REMARK: Logic-homogeneous environment assumed
          let sNSMap = coerceMapofsymbol sLid lid sm
              tNSMap = coerceMapofsymbol tLid lid tm
              mf msg = Map.findWithDefault
                       $ error $ "computeSymbolMap: lookup failed for " ++ msg
              -- function for notation lookup
              g = lookupNotationInMap
                  $ fromMaybe (error "computeSymbolMap: no notations") mNots
              -- function for map
              f (omn, omimg) =
                  let tSymName = case omimg of
                                   Left s -> mkSimpleName s
                                   Right (OMS qn) -> unqualName qn
                                   _ -> error $ "computeSymbolMap: Nonsymbol "
                                        ++ "element mapped"
                  in ( mf (show omn) omn sNSMap
                     , case Map.lookup tSymName tNSMap of
                         Just ts -> Right ts
                         _ -> Left (tSymName, id_to_raw lid $ nameToId
                                                $ g tSymName))
          return $ map f morph


followImports :: LibName -> (ImpEnv, DGraph) -> [ImportInfo OMCD]
              -> ResultT IO ((ImpEnv, DGraph), [ImportInfo LinkNode])
followImports ln = mapAccumLCM (curry snd) (followImport ln)

{- | Ensures that the theory for the given OMCD is available in the environment.
See also 'followTheory' -}
followImport :: LibName -> (ImpEnv, DGraph) -> ImportInfo OMCD
             -> ResultT IO ((ImpEnv, DGraph), ImportInfo LinkNode)
followImport ln x iInfo = do
  (x', linknode) <- followTheory ln x $ iInfoVal iInfo
  return (x', fmap (const linknode) iInfo)


followTheories :: LibName -> (ImpEnv, DGraph) -> [OMCD]
               -> ResultT IO ((ImpEnv, DGraph), [LinkNode])
followTheories ln = mapAccumLCM (curry snd) (followTheory ln)

{- | We lookup the theory referenced by the cd in the environment
and add it if neccessary to the environment. -}
followTheory :: LibName -> (ImpEnv, DGraph) -> OMCD
             -> ResultT IO ((ImpEnv, DGraph), LinkNode)
followTheory ln (e, dg) cd = do
  (e', ln', dg', lnode) <- importTheory e (ln, dg) cd
  let mLn = if ln == ln' then Nothing else Just ln'
  return ((e', dg'), (mLn, lnode))


-- * Development Graph and LibEnv interface


{- | returns a function compatible with mapAccumLM for TCElement processing.
Used in localSig. -}
sigmapAccumFun :: (Monad m, Show a) => (SigMapI a -> TCElement -> String -> m a)
               -> SigMapI a -> TCElement -> m (SigMapI a, a)
sigmapAccumFun f smi s = do
  let n = tcName s
      hetsname = lookupNotation smi n
  s' <- f smi s hetsname
  let smi' = smi { sigMapISymbs = Map.insert n s' $ sigMapISymbs smi }
  return (smi', s')


-- | Builds an initial signature and a name map of the given logic.
initialSig :: AnyLogic -> (NameSymbolMap, G_sign)
initialSig lg =
    case lg of
      Logic lid ->
          ( G_mapofsymbol lid Map.empty
          , G_sign lid (makeExtSign lid $ empty_signature lid) startSigId)

-- | Adds the local signature to the given signature and name symbol map
localSig :: TCClassification -> NameSymbolMap -> G_sign
         -> Result (NameSymbolMap, G_sign)
localSig clf nsmap gSig =
    case (gSig, nsmap) of
      (G_sign lid _ _, G_mapofsymbol lid' sm) ->
          do
            let smi = SigMapI (coerceMapofsymbol lid' lid sm) $ notations clf
            {- accumulates symbol mappings in the symbMap in SigMapI
            while creating symbols from OMDoc symbols -}
            (sm', symbs) <- mapAccumLM (sigmapAccumFun $ omdocToSym lid) smi
                           $ sigElems clf
            -- adding the symbols to the empty signature
            sig <- foldM (add_symb_to_sign lid) (empty_signature lid) symbs
            let locGSig = G_sign lid (makeExtSign lid sig) startSigId
            -- combining the local and the given signature
            gSig' <- gsigUnion logicGraph True gSig locGSig
            return (G_mapofsymbol lid $ sigMapISymbs sm', gSig')


-- | Adds sentences and logic dependent signature elements to the given sig
addSentences :: TCClassification -> NameSymbolMap -> G_sign -> Result G_theory
addSentences clf nsmap gsig =
    case (nsmap, gsig) of
      (G_mapofsymbol lidM sm, G_sign lid (ExtSign sig _) ind1) ->
          do
            let sigm = SigMapI (coerceMapofsymbol lidM lid sm)
                    $ notations clf
            -- 1. translate sentences
            mSens <- mapM (\ tc -> omdocToSen lid sigm tc
                       $ lookupNotation sigm $ tcName tc) $ sentences clf

            -- 2. translate adts
            (sig', sens') <- addOMadtToTheory lid sigm (sig, catMaybes mSens)
                             $ adts clf

            {- 3. translate rest of theory
            (all the sentences or just those which returned Nothing?) -}
            (sig'', sens'') <- addOmdocToTheory lid sigm (sig', sens')
                               $ sentences clf

            return $ G_theory lid Nothing (mkExtSign sig'') ind1
                       (toThSens sens'') startThId


-- | Adds Edges from the LinkInfo list to the development graph.
addLinksToDG :: Node -> DGraph -> [LinkInfo] -> DGraph
addLinksToDG nd = foldl (addLinkToDG nd)

-- | Adds Edge from the LinkInfo to the development graph.
addLinkToDG :: Node -> DGraph -> LinkInfo -> DGraph
addLinkToDG to dg (gMor, lt, lo, from, mTo) =
    insLink dg gMor lt lo from $ fromMaybe to mTo


-- | Adds a Node from the given 'G_theory' to the development graph.
addNodeToDG :: DGraph -> String -> G_theory -> (LNode DGNodeLab, DGraph)
addNodeToDG dg n gth =
    let nd = getNewNodeDG dg
        ndName = parseNodeName n
        ndInfo = newNodeInfo DGBasic
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
     in case refNodeM of
         Just refNode -> ((refNode, labDG dg refNode), dg)
         _ -> (lnode, dg1)


-- * Theory-utils

type CurrentLib = (LibName, DGraph)

type LinkNode = (Maybe LibName, LNode DGNodeLab)

type LinkInfo = (GMorphism, DGLinkType, DGLinkOrigin, Node, Maybe Node)

data ImportInfo a = ImportInfo a String TCMorphism deriving Show

iInfoVal :: ImportInfo a -> a
iInfoVal (ImportInfo x _ _) = x

instance Functor ImportInfo where
  fmap f (ImportInfo x y z) = ImportInfo (f x) y z

fmapLI :: Monad m => (GMorphism -> m GMorphism) -> LinkInfo -> m LinkInfo
fmapLI f (gm, x, y, z, t) = do
  gm' <- f gm
  return (gm', x, y, z, t)

data TCClassification = TCClf {
      importInfo :: [ImportInfo OMCD] -- ^ Import-info
    , sigElems :: [TCElement] -- ^ Signature symbols
    , sentences :: [TCElement] -- ^ Theory sentences
    , adts :: [[OmdADT]] -- ^ ADTs
    , notations :: Map.Map OMName String -- ^ Notations
    }


emptyClassification :: TCClassification
emptyClassification = TCClf [] [] [] [] Map.empty

classifyTCs :: [TCElement] -> TCClassification
classifyTCs = foldr classifyTC emptyClassification

classifyTC :: TCElement -> TCClassification -> TCClassification
classifyTC tc clf =
    case tc of
      TCSymbol _ _ sr _
          | elem sr [Obj, Typ] -> clf { sigElems = tc : sigElems clf }
          | otherwise -> clf { sentences = tc : sentences clf }
      TCNotation (cd, omn) n (Just "hets") ->
          if cdIsEmpty cd then
              clf { notations = Map.insert omn n $ notations clf }
          else clf
      TCADT l -> clf { adts = l : adts clf }
      TCImport n from morph ->
          clf { importInfo = ImportInfo from n morph : importInfo clf }
      TCComment _ -> clf
      TCSmartNotation {} -> error "classifyTC: unexpected SmartNotation"
      TCFlexibleNotation {} ->
          error "classifyTC: unexpected FlexibleNotation"
      -- just for the case TCNotation with a style different from hets
      _ -> clf
