{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

analyse OWL files by calling the external Java parser.
-}

module OWL.OWLAnalysis (structureAna, parseOWL) where

import OWL.AS
import OWL.Namespace
import OWL.Logic_OWL
import OWL.ReadWrite()
import OWL.StaticAnalysis
import OWL.Sign
import OWL.StructureAnalysis

import Static.GTheory
import Static.DevGraph

import Common.Id
import Common.GlobalAnnotations
import Common.ExtSign
import Common.LibName
import Common.Result
import Common.Utils
import Common.AS_Annotation hiding (isAxiom, isDef)
import Common.ATerm.ReadWrite
import Common.ATerm.Unshared

import Driver.Options

import Logic.Comorphism
import Logic.Grothendieck
import Logic.Logic
import Logic.Prover

import System.IO
import System.Time
import System.Cmd (system)
import System.Exit
import System.Environment (getEnv)
import System.Posix.Process

import qualified Data.Map as Map
import qualified Data.List as List
import Data.Graph.Inductive.Graph
import qualified Data.Graph.Inductive.Query.DFS as DFS
import qualified Data.Graph.Inductive.Query.BFS as BFS
import Data.Maybe (fromJust)


-- | call for owl parser (env. variable $HETS_OWL_TOOLS muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO OntologyMap        -- ^ map: uri -> OntologyFile
parseOWL filename  =
  do
    pwd <- getEnv "PWD"
    if null filename
       then
         error "empty file name!"
       else do
           pid <- getProcessID
           currTime <- getClockTime
           calend <- toCalendarTime currTime
           let tmpFile = "/tmp/" ++ (basename filename) ++ "-"
                         ++ (show pid) ++ "-" ++ (buildTime calend)
                         ++ ".term"
              --           "/home/jiang/tmp/output.aterm"
           if checkUri filename
               then
                 do exitCode <-
                        system ("$HETS_OWL_TOOLS/owl_parser "
                                ++ filename ++
                               " " ++ tmpFile)
                    run exitCode tmpFile
               else if (head filename) == '/'
                     then
                      do
                        exitCode <-
                         system ("$HETS_OWL_TOOLS/owl_parser file://"
                                 ++ filename ++ " " ++ tmpFile)
                        run exitCode tmpFile
                     else do
                           exitCode <-
                            system("$HETS_OWL_TOOLS/owl_parser file://"
                                   ++ pwd ++ "/" ++ filename ++
                                   " " ++ tmpFile)
                           run exitCode tmpFile

       where buildTime cTime =
                 (show $ ctYear cTime) ++ (show $ ctMonth cTime) ++
                 (show $ ctDay cTime) ++ (show $ ctHour cTime) ++
                 (show $ ctMin cTime) ++ (show $ ctSec cTime)

             run :: ExitCode -> FilePath -> IO OntologyMap
             run exitCode tmpFile
                 | exitCode == ExitSuccess =
                     do
                       putStrLn tmpFile
                       t <- parseProc tmpFile
                       -- system ("cat  " ++ tmpFile)
                       return t
                 | otherwise =  error ("process stop! " ++ (show exitCode))

-- | parse the tmp-ATerm-file from java-owl-parser
parseProc :: FilePath -> IO OntologyMap
parseProc filename =
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d

       case aterm of
         AList paarList _ -> do
             let om = Map.fromList $ parsingAll paarList
             return om
         _ -> error ("false file: " ++ show filename ++ ".")

-- | parse an ontology with all imported ontologies
parsingAll :: [ATerm] -> [(String, OntologyFile)]
parsingAll [] = []
parsingAll (aterm:res) =
             (aTerm2Ontology aterm):(parsingAll res)

-- | translates ATerm to ontologyFile.
aTerm2Ontology :: ATerm -> (String, OntologyFile)
aTerm2Ontology (AAppl "UOPaar" [AAppl ouri _  _, ontoFile] _) =
      (if head ouri == '"' then read ouri::String else ouri,
             propagateNspaces (namespaces parsedOntologFile) parsedOntologFile)
    where parsedOntologFile = fromATerm ontoFile:: OntologyFile

aTerm2Ontology _ = error "false ontology file."

-- | structure analysis bases of ontologyMap from owl parser
structureAna :: FilePath
             -> HetcatsOpts
             -> OntologyMap
             -> IO (Maybe (LIB_NAME, -- filename
                    LibEnv           -- DGraphs for imported modules
                   ))
structureAna file opt ontoMap =
    do
       let (newOntoMap, dg) = buildDevGraph ontoMap
       case  (analysis opt) of
         Structured -> do                   -- only structure analysis
            printMsg $ labNodesDG dg
            putStrLn $ show $ dgBody dg
            return (Just (simpleLibName file,
                          simpleLibEnv file $ reverseGraph dg))
         Skip       -> return $ fail ""     -- Nothing is ambiguous
         _          -> staticAna file opt (newOntoMap, dg)
     where -- output Analyzing messages for structured anaylsis
           printMsg :: [LNode DGNodeLab] -> IO()
           printMsg [] = putStrLn ""
           printMsg ((_, node):rest) =
               do putStrLn ("Analyzing ontology - printMsg " ++
                            (showName $ dgn_name node))
                  printMsg rest

-- simpleLibEnv and simpleLibName builded two simple lib-entities for
-- showGraph
simpleLibEnv :: FilePath -> DGraph -> LibEnv
simpleLibEnv filename dg =
    Map.singleton (simpleLibName filename) dg
           { globalEnv = Map.singleton (mkSimpleId "")
                (SpecEntry (ExtGenSig (JustNode nodeSig) [] g_sign nodeSig))}
       where nodeSig = NodeSig 0 g_sign
             g_sign = G_sign OWL (mkExtSign emptySign) startSigId

simpleLibName :: FilePath -> LIB_NAME
simpleLibName s = Lib_id $ Direct_link ("library_" ++ s) nullRange

-- | static analysis if the HetcatesOpts is not only Structured.
-- | sequence call for nodesStaticAna on the basis of topologically
-- | sort of all nodes
staticAna :: FilePath
          -> HetcatsOpts
          -> (OntologyMap, DGraph)
          -> IO (Maybe (LIB_NAME,     -- filename
                        LibEnv        -- DGraphs for imported modules
                       ))
staticAna file opt (ontoMap, dg) =
    do let topNodes = DFS.topsort $ dgBody dg
--       putStrLn $ show ontoMap
       Result diagnoses res <-
           nodesStaticAna (reverse topNodes) Map.empty ontoMap Map.empty dg []
       case res of
           Just (_, dg', _) -> do
            showDiags opt $ List.nub diagnoses
            let dg'' = insEdgesDG (reverseLinks $ labEdgesDG dg')
                           (delEdgesDG (edgesDG dg') dg')
            -- putStrLn $ show dg''
            return (Just (simpleLibName file,
                          simpleLibEnv file dg''))
           _            -> error "no devGraph..."

-- | a map to save which node has been analysed.
type SignMap = Map.Map Node (Sign, [Named Sentence])

getBFSnodeList :: Node -> DGraph -> [LNode DGNodeLab]
getBFSnodeList h dg = reverse $ map (matchNode dg) $ BFS.bfs h $ dgBody dg

-- | call to static analyse of all nodes
nodesStaticAna :: [Node]            -- ^ topologically sort of graph
               -> SignMap           -- ^ an map of analyzed nodes
               -> OntologyMap       -- ^ an map of parsed ontology
               -> Namespace         -- ^ global namespaces
               -> DGraph            -- ^ current graph
               -> [Diagnosis]       -- ^ diagnosis of result
               -> IO (Result (SignMap, DGraph, Namespace))
                      -- ^ result is tuple of new map of signs and sentences,
                      -- ^ new grpah, and new global namespace map.
nodesStaticAna [] signMap _ ns dg diag =
    return $ Result diag (Just (signMap, dg, ns))
nodesStaticAna (h:r) signMap ontoMap globalNs dg diag = do
    Result digs res <-
        -- Each node must be analyzed with the associated imported nodes.
        -- Those search for imported nodes is by bfs accomplished.
        nodeStaticAna (getBFSnodeList h dg)
                          (emptySign, diag)
                          signMap ontoMap globalNs dg
    case res of
        Just (newSignMap, newDg, newGlobalNs) ->
            nodesStaticAna r newSignMap ontoMap newGlobalNs newDg (diag++digs)
        Nothing ->
               -- Warning or Error message
            nodesStaticAna r signMap ontoMap globalNs dg (diag++digs)

-- | call to static analyse of single nodes
nodeStaticAna :: [LNode DGNodeLab]   -- ^ imported nodes of one node
                                     -- ^ (incl. itself)
              -> (Sign, [Diagnosis]) -- ^ here saved incoming sign, diagnoses
              -> SignMap             -- ^ an map of analyzed nodes
              -> OntologyMap         -- ^ an map of parsed ontology
              -> Namespace           -- ^ global namespaces
              -> DGraph              -- ^ current graph
              -> IO (Result (SignMap, DGraph, Namespace))
nodeStaticAna [] _ _ _ _ _ = return $ Result [] Nothing  -- remove warning
-- the last node in list is current top node.
nodeStaticAna
    ((n,topNode):[]) (inSig, oldDiags) signMap ontoMap globalNs dg =
  do
    let nn = dgn_name topNode
        nodeName = getName nn
    putStrLn ("Analyzing ontology " ++ (show nodeName))
    case Map.lookup n signMap of
     Just _ ->
        return $ Result oldDiags (Just (signMap, dg, globalNs))
     _   ->
      do
        -- putStrLn $ show $ ontoMap
        let ontoF@(OntologyFile _ (Ontology mid _ _ _)) = fromJust $
                           Map.lookup (getNameFromNode nn) ontoMap
            Result diag res =
                 -- static analysis of current ontology with all sign of
                 -- imported ontology.
                 basicOWLAnalysis (ontoF, inSig, emptyGlobalAnnos)
        case res of
          Just (_, ExtSign accSig _, sent) ->
            do
             let (newGlobalNs, tMap) =
                     integrateNamespaces globalNs (namespaceMap accSig)
                 newSent = map (renameNamespace tMap) sent
                 difSig = diffSig accSig inSig
                 newDifSig = renameNamespace tMap difSig
                 newSig  = mkExtSign $ renameNamespace tMap accSig
                 -- the new node (with sign and sentence) has the sign of
                 -- accumulated sign with imported signs, but the sentences
                 -- is only of current ontology, because all sentences of
                 -- imported ontoloies can be automatically outputed by
                 -- showTheory (see GUI)
                 newLNode = (n, topNode
                   { dgn_theory = G_theory OWL newSig startSigId
                                  (toThSens newSent) startThId })
                 -- by remove of an node all associated edges are also deleted
                 -- so the deges must be saved before remove the node, then
                 -- appended again.
                 -- The out edges (after reverse are inn edges) must
                 -- also with new signature be changed.
                 ledges = innDG dg n ++
                          map (changeGMorOfEdges newSig) (outDG dg n)
                 newG = insEdgesDG ledges (insNodeDG newLNode
                                           (delNodeDG n dg))

             return $ Result (oldDiags ++ diag)
                     (Just ((Map.insert n (newDifSig, newSent) signMap),
                            newG, newGlobalNs))
          _   -> do let actDiag = mkDiag Error
                                    ("error by analysing of "
                                     ++ (show mid)) ()
                    putStrLn (show diag)
                    return $ Result (actDiag:oldDiags) Nothing
            -- The GMorphism of edge should also with new Signature be changed,
            -- since with "show theory" the edges also with Sign one links
            -- (see Static.DevGraph.joinG_sentences).
      where changeGMorOfEdges newSign (n1, n2, edge) =
                let newCMor = idComorphism (Logic OWL)
                    Result _ newGMor = gEmbedComorphism newCMor
                                       (G_sign OWL newSign startSigId)
                in  (n1, n2, edge {dgl_morphism = fromJust newGMor})

-- The other nodes in list are examined whether they were already analyzed.
-- if yes then signs of it for further analysis are taken out; otherwise they
-- are first analyzed (with complete part tree of this node).
nodeStaticAna ((n, _):r) (inSig, oldDiags) signMap ontoMap globalNs dg
 =
  do
   case Map.lookup n signMap of
     Just (sig, _) ->
        nodeStaticAna r ((integSign sig inSig), oldDiags)
                             signMap ontoMap globalNs dg
     Nothing ->
       do
         Result digs' res' <-
                 nodeStaticAna (getBFSnodeList n dg)
                                   (emptySign, [])
                                   signMap ontoMap globalNs dg
         case res' of
          Just (signMap', dg', globalNs') ->
            do
             let (sig', _) = fromJust $ Map.lookup n signMap'
             nodeStaticAna r
                  ((integSign sig' inSig), (oldDiags ++ digs'))
                  signMap' ontoMap globalNs' dg'
          _  -> do error "Error by analysis : nodeStaticAna"
                   nodeStaticAna r (inSig, oldDiags)
                                         signMap ontoMap globalNs dg

-- | build up two sign
integSign :: Sign -> Sign -> Sign
integSign inSig totalSig =
    let (newNamespace, transMap) =
            integrateNamespaces (namespaceMap totalSig) (namespaceMap inSig)
    in  addSign (renameNamespace transMap inSig)
                (totalSig {namespaceMap = newNamespace})

-- | turn edges over
reverseLinks :: [LEdge DGLinkLab] -> [LEdge DGLinkLab]
reverseLinks [] = []
reverseLinks ((source, target, edge):r) =
    (target, source, edge):(reverseLinks r)

-- | turn all edges over of graph
reverseGraph :: DGraph -> DGraph
reverseGraph dg =
    let newLinks = reverseLinks $ labEdgesDG dg
    in insEdgesDG newLinks (delEdgesDG (edgesDG dg) dg)

-- | find a node in DevGraph
matchNode :: DGraph -> Node -> LNode DGNodeLab
matchNode dgraph node =
             let (mcontext, _ ) = matchDG node dgraph
                 (_, _, dgNode, _) = fromJust mcontext
             in (node, dgNode)
