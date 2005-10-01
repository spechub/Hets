{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  portable

-}

module OWL_DL.OWLAnalysis where

import OWL_DL.AS
import OWL_DL.Namespace
import OWL_DL.Logic_OWL_DL
import Common.ATerm.ReadWrite
import Common.ATerm.Unshared
import System(system)
import System.Exit
import System.Environment(getEnv)
import qualified Common.Lib.Map as Map
import qualified List as List
import OWL_DL.StructureAna
import Data.Graph.Inductive.Graph
import Static.DevGraph
import OWL_DL.StaticAna
import OWL_DL.Sign
import Common.GlobalAnnotations
import Common.Result
import Common.AS_Annotation
import Syntax.AS_Library
import Driver.Options
import Common.Id
import Logic.Grothendieck
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.BFS
import Maybe(fromJust)

-- | call for owl parser (env. variable $HETS_OWL_PARSER muss be defined)
parseOWL :: FilePath              -- ^ local filepath or uri
         -> IO OntologyMap        -- ^ map: uri -> Ontology  
parseOWL filename  = 
  do
    pwd <- getEnv "PWD" 
    if null filename 
       then
         error "empty file name!"
       else if checkUri $ filename 
               then
                 do exitCode <- 
                        system ("$HETS_OWL_PARSER/owl_parser " ++ filename)
                        -- system ("./OWL_DL/owl_parser " ++ filename)
                    run exitCode 
               else if (head filename) == '/' 
                       then
                         do exitCode <-
                                system ("$HETS_OWL_PARSER/owl_parser file://"
                                        ++ filename)
                                -- system ("./OWL_DL/owl_parser file://"
                                --      ++ filename)
                            run exitCode 
                       else do exitCode <- 
                                 system ("$HETS_OWL_PARSER/owl_parser file://"
                                         ++ pwd ++ "/" ++ filename)
                                 -- system ("./OWL_DL/owl_parser file://"
                                 --      ++ pwd ++ "/" ++ filename)
                               run exitCode 

       where run :: ExitCode  -> IO OntologyMap
             run exitCode 
                 | exitCode == ExitSuccess =  
                     parseProc "./OWL_DL/output.term"
                 | otherwise =  error ("process stop! " ++ (show exitCode))

-- | parse the file "output.term" from java-owl-parser
parseProc :: FilePath -> IO OntologyMap
parseProc filename = 
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case aterm of
         AList paarList _ ->
             return $ Map.fromList $ parsingAll paarList
         _ -> error ("false file: " ++ show filename ++ ".")
          
-- | parse an ontology with all imported ontologies           
parsingAll :: [ATerm] -> [(String, Ontology)]
parsingAll [] = []
parsingAll (aterm:res) =
             (ontologyParse aterm):(parsingAll res)
      
-- | ontology parser, this version ignore validation, massages of java-parser.
ontologyParse :: ATerm -> (String, Ontology)
ontologyParse 
    (AAppl "UOPaar" 
        [AAppl uri _  _, 
         AAppl "OWLParserOutput" [_, _, _, onto] _] _) 
    = case ontology of
      Ontology _ _ namespace ->
          (if head uri == '"' then read uri::String else uri, 
           propagateNspaces namespace $ createAndReduceClassAxiom ontology)
   where ontology = fromATerm onto::Ontology 
ontologyParse _ = error "false ontology file."

-- remove equivalent disjoint class axiom, create equivalentClasses, 
-- subClassOf axioms, and sort directives (definitions of classes and 
-- properties muss be moved to begin of directives)
createAndReduceClassAxiom :: Ontology -> Ontology
createAndReduceClassAxiom (Ontology oid directives ns) =
    let (definition, axiom, other) =  
            findAndCreate (List.nub directives) ([], [], []) 
        directives' = reverse definition ++ reverse axiom ++ reverse other
    in  Ontology oid directives' ns
    
   where findAndCreate :: [Directive] 
                       -> ([Directive], [Directive], [Directive])
                       -> ([Directive], [Directive], [Directive])
                          -- (definition of concept and role, axiom, rest)
         findAndCreate [] res = res
         findAndCreate (h:r) (def, axiom, rest) = 
             case h of
             Ax (Class cid _ Complete _ desps) ->
                 -- the original directive must also be saved.
                 findAndCreate r 
                    (h:def,(Ax (EquivalentClasses (DC cid) desps)):axiom,rest)
             Ax (Class cid _ Partial _ desps) ->
                 if null desps then
                    findAndCreate r (h:def, axiom, rest) 
                    else 
                     findAndCreate r (h:def, 
                                      (appendSubClassAxiom cid desps) ++ axiom,
                                      rest) 
             Ax (EnumeratedClass _ _ _ _) -> 
                 findAndCreate r (h:def, axiom, rest)
             Ax (DisjointClasses _ _ _) ->
                             if any (eqClass h) r then
                                findAndCreate r (def, axiom, rest)
                                else findAndCreate r (def,h:axiom, rest)
             Ax (DatatypeProperty _ _ _ _ _ _ _) -> 
                 findAndCreate r (h:def, axiom, rest)
             Ax (ObjectProperty _ _ _ _ _ _ _ _ _) -> 
                 findAndCreate r (h:def, axiom, rest)
             _ -> findAndCreate r (def, axiom, h:rest)
             
         appendSubClassAxiom :: ClassID -> [Description] -> [Directive]
         appendSubClassAxiom _ [] = []
         appendSubClassAxiom cid (hd:rd) =
             (Ax (SubClassOf (DC cid) hd)):(appendSubClassAxiom cid rd) 

         eqClass :: Directive -> Directive -> Bool
         eqClass dj1 dj2 =
              case dj1 of
              Ax (DisjointClasses c1 c2 _) ->
                  case dj2 of
                  Ax (DisjointClasses c3 c4 _) ->
                      if (c1 == c4 && c2 == c3) 
                         then True
                         else False
                  _ -> False
              _ -> False

-- | structure analysis bases of ontologyMap from owl parser
structureAna :: FilePath
             -> HetcatsOpts
             -> OntologyMap
             -> IO (Maybe (LIB_NAME, -- filename
                    (),   -- as tree
                    (),   -- development graph
                    LibEnv    -- DGraphs for imported modules 
                   ))
structureAna file opt ontoMap =
    do 
       let (newOntoMap, dg) = buildDevGraph ontoMap
       case analysis opt of
         Structured -> do
            printMsg $ labNodes dg
            -- putIfVerbose opt 1 "Structure anaylsing finished. "   
            return (Just (simpleLibName file, (), (), 
                          simpleLibEnv file $ reverseGraph dg))
         _          -> staticAna file (newOntoMap, dg)
     where printMsg :: [LNode DGNodeLab] -> IO()
           printMsg [] = putStrLn ""
           printMsg ((_, node):rest) =
               do putStrLn ("Analyzing ontology " ++ 
                            (showName $ dgn_name node))
                  printMsg rest

-- simpleLibEnv and simpleLibName builded two simple lib-entities for 
-- showGraph
simpleLibEnv :: FilePath -> DGraph -> LibEnv
simpleLibEnv filename dg =
    Map.singleton (simpleLibName filename) 
           (emptyGlobalAnnos, Map.singleton (mkSimpleId "") 
            (SpecEntry ((JustNode nodeSig), [], g_sign, nodeSig)), dg)
       where nodeSig = NodeSig 0 g_sign
             g_sign = G_sign OWL_DL emptySign

simpleLibName :: FilePath -> LIB_NAME
simpleLibName s = Lib_id (Direct_link ("library_" ++ s) (Range []))

-- | static analysis if the HetcatesOpts is not only Structured. 
staticAna :: FilePath
          -> (OntologyMap, DGraph)
          -> IO (Maybe (LIB_NAME, -- filename
                        (),   -- as tree
                        (),   -- development graph
                        LibEnv    -- DGraphs for imported modules 
                       ))
staticAna file (ontoMap, dg) =  
    do let topNodes = topsort dg
       Result _ res <-
               nodesStaticAna (reverse topNodes) Map.empty ontoMap dg []
       case res of
           Just (_, dg') ->         
            return (Just (simpleLibName file, 
                          (), (),
                          simpleLibEnv file 
                          (insEdges (reverseLinks $ labEdges dg) 
                           (delEdges (edges dg') dg')
                          )))
           _            -> error "no devGraph..."

-- | a map to save which node has been analysed.
type SignMap = Map.Map Node (Sign, [Named Sentence])

-- | call to static analyse of all nodes
nodesStaticAna :: [Node] 
               -> SignMap 
               -> OntologyMap
               -> DGraph 
               -> [Diagnosis]
               -> IO (Result (SignMap, DGraph))
nodesStaticAna [] signMap _ dg diag = 
    return $ Result diag (Just (signMap, dg)) 
nodesStaticAna (h:r) signMap ontoMap dg diag = do
    Result digs res <- 
        nodeStaticAna (reverse $ map (matchNode dg) (bfs h dg)) 
                          (emptySign, [], diag)
                          signMap ontoMap dg 
    case res of
        Just (newSignMap, newDg) -> 
                nodesStaticAna r newSignMap ontoMap newDg (diag++digs)
        Prelude.Nothing -> 
               -- Warning or Error message
            nodesStaticAna r signMap ontoMap dg (diag++digs)
    
-- | call to static analyse of single nodes
nodeStaticAna :: [LNode DGNodeLab]
              -> (Sign, [Named Sentence], [Diagnosis])   
              -> SignMap
              -> OntologyMap
              -> DGraph
              -> IO (Result (SignMap, DGraph))
nodeStaticAna [] _ _ _ _ = 
    do putStrLn "Static anaylsing finished."
       return initResult
nodeStaticAna ((n,topNode):[]) (inSig, inSent, oldDiags) signMap ontoMap dg =
  do
    let nn@(nodeName, _, _) = dgn_name topNode
    putStrLn ("Analyzing ontology " ++ (show nodeName))
    case Map.lookup n signMap of
     Just _ -> 
        return $ Result oldDiags (Just (signMap, dg))
     _   -> 
      do
        let ontology@(Ontology mid _ _) = fromJust $ 
                   Map.lookup (getNameFromNode nn) ontoMap
            Result diag res = 
                 basicOWL_DLAnalysis (ontology, inSig, emptyGlobalAnnos)
        case res of  
	  Just (_,difSig,accSig,sent) ->
            do    
	     let {- (_, tMap) = 
		     integrateNamespaces (namespaceMap inSig) 
					     (namespaceMap accSig)
		 sent' = map (renameNamespace tMap) sent
		 -}
	         accSent = inSent ++ sent 
                 newLNode = 
		     (n, topNode {dgn_theory = 
				  G_theory OWL_DL accSig (toThSens accSent)
				 }) 
		 ledges = (inn dg n) ++ (out dg n)
	         newG = (insEdges ledges (insNode newLNode (delNode n dg)))
	     return $ Result (oldDiags ++ diag)
		      (Just ((Map.insert n (difSig, sent) signMap), newG))
	  _   -> do let actDiag = mkDiag Error 
				    ("error by analysing of " ++ (show mid)) ()
                    return $ Result (actDiag:oldDiags) Prelude.Nothing 

nodeStaticAna ((n, _):r) (inSig, inSent, oldDiags) signMap ontoMap dg =
  do
   case Map.lookup n signMap of
     Just (sig, nsen) -> 
       let (_, tMap) = 
               integrateNamespaces (namespaceMap inSig) (namespaceMap sig)
       in  nodeStaticAna r ((integSign sig inSig), 
                            (inSent ++ (map (renameNamespace tMap) nsen)), 
                            oldDiags)
                       signMap ontoMap dg
     Prelude.Nothing ->
       do        
         Result digs' res' <-
                 nodeStaticAna (reverse $ map (matchNode dg) (bfs n dg)) 
                                   (emptySign, [], [])
                                   signMap ontoMap dg 
         case res' of
          Just (signMap', dg') ->
            do
             let (sig', nsen') = fromJust $ Map.lookup n signMap'
                 (_, tMap) = 
                     integrateNamespaces (namespaceMap inSig) 
                                             (namespaceMap sig')
             nodeStaticAna r 
                  ((integSign sig' inSig),
                   (inSent ++ (map (renameNamespace tMap) nsen')),
                   (oldDiags ++ digs'))
                  signMap' ontoMap dg'
          _  -> do error "Error by analysis : nodeStaticAna"
                   nodeStaticAna r (inSig, inSent, oldDiags)
                                         signMap ontoMap dg

integSign :: Sign -> Sign -> Sign
integSign inSig totalSig =
    let (newNamespace, transMap) = 
            integrateNamespaces (namespaceMap totalSig) (namespaceMap inSig)
    in  addSign (renameNamespace transMap inSig)
                (totalSig {namespaceMap = newNamespace})

reverseLinks :: [LEdge DGLinkLab] -> [LEdge DGLinkLab]
reverseLinks [] = []
reverseLinks ((source, target, edge):r) = 
    (target, source, edge):(reverseLinks r)

reverseGraph :: DGraph -> DGraph
reverseGraph dg =
    let newLinks = reverseLinks $ labEdges dg
    in  insEdges newLinks (delEdges (edges dg) dg)
   
-- | find a node in DevGraph
matchNode :: DGraph -> Node -> LNode DGNodeLab
matchNode dgraph node =
             let (mcontext, _ ) = match node dgraph
                 (_, _, dgNode, _) = fromJust mcontext
             in (node, dgNode)
