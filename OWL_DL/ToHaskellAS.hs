{- |
Module      :  $Header$
Copyright   :  Heng Jiang, Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  jiang@tzi.de
Stability   :  provisional
Portability :  non-portable (uni, imports Static.DevGraph)

-}

module Main() where

import OWL_DL.AS
import OWL_DL.Namespace
import OWL_DL.Logic_OWL_DL
import Common.ATerm.ReadWrite
import Common.ATerm.Unshared
import System.Exit
import System(getArgs, system)
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
import Common.AS_Annotation hiding (isDef,isAxiom)
import Syntax.AS_Library
import Driver.Options
import GUI.ShowGraph
import Common.Id
import Logic.Grothendieck
import Logic.Prover
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.Query.BFS
import Maybe(fromJust)

main :: IO()
main =
    do args <- getArgs
       if (null args) || (length args > 2) then
          showHelp
          -- default option : output OWL_DL abstract syntax
          else if length args == 1 then
                  process 'a' args
                  else case head args of
                       "-a" -> process 'a' $ tail args
                       -- output abstract syntax
                       "-g" -> process 'g' $ tail args
                       -- show graph of structure
                       "-h" -> showHelp
                       "-i" -> showHelp
                       -- test integrate ontology
                       "-r" -> process 'r' $ tail args
                       -- output result of static analysis
                       "-s" -> process 's' $ tail args
                       -- output DevGraph from structure analysis
                       "-t" -> process 't' $ tail args
                       -- output ATerm
                       _    -> error ("unknow option: " ++ (head args))

       where isURI :: String -> Bool
             isURI str = let preU = take 7 str
                         in if preU == "http://" || preU == "file://"
                               then True
                               else False

             run :: ExitCode -> Char -> IO()
             run exitCode opt
                 | exitCode == ExitSuccess =  processor2 opt "output.term"
                 | otherwise =  error "process stop!"

             process :: Char -> [String] -> IO()
             process opt args  =
                 do
                  pwd <- getEnv "PWD"
                  if (head $ head args) == '-' then
                     showHelp
                     else if isURI $ head args then
                             do exitCode <- system ("./processor " ++ head args)
                                run exitCode opt
                             else if (head $ head args) == '/' then
                                     do exitCode <- system ("./processor file://" ++ head args)
                                        run exitCode opt
                                     else do exitCode <- system ("./processor file://" ++ pwd ++ "/" ++ head args)
                                             run exitCode opt

showHelp :: IO()
showHelp =
    do putStrLn "\nUsage: readAStest [option] <URI or file>"
       putStrLn "  -a\t\t--abstract\t\toutput OWL_DL abstract syntax"
       putStrLn "  -g\t\t--gui\t\t\tshow graph of structure"
       putStrLn "  -h\t\t--help\t\t\tprint usage information and exit"
       putStrLn "  -i\t\t--integrate\t\ttest integrate ontology"
       putStrLn "  -r\t\t--static\t\toutput result (list) of static analysis for each include ontologies"
       putStrLn "  -s\t\t--structure\t\toutput total result of static analysis from structure analysis"
       putStrLn "  -t\t\t--Aterm\t\t\toutput ATerm from OWL_DL parser\n"

-- |
-- the first argument it decides whether the abstract syntax or ATerm is shown,
-- the second argument is the ATerm file which can be read in.
processor2 :: Char -> String  -> IO()
processor2 opt filename =
    do d <- readFile filename
       let aterm = getATermFull $ readATerm d
       case opt of
       -- 'a' -> outputList 'a' aterm
            't' -> putStrLn $ show aterm
            's' -> outputList 's' filename aterm
            'r' -> outputList 'r' filename aterm
            'i' -> outputList 'i' filename aterm
            'g' -> outputList 'g' filename aterm
            _   -> outputList 'a' filename aterm

outputList :: Char -> String -> ATerm -> IO()
outputList opt filename aterm =
    case aterm of
       AList paarList _ ->
           case opt of
           'a' -> outputAS paarList
           's' -> outputTotalStaticAna paarList
           'r' -> printResOfStatic paarList
           'i' -> testIntegrate paarList
           'g' -> outputGraph filename paarList
           u   -> error ("unknow option: -" ++ [u])
       _ -> error "error by reading file."

-- test for integrate ontologies (for option -i)
testIntegrate :: [ATerm] -> IO()
testIntegrate al =
    do let ontologies = map snd $ reverse $ parsingAll al
       putStrLn $ show (foldl integrateOntology emptyOntology ontologies)

-- |
-- this function show the abstract syntax of each OWL ontology from
-- UOPaar list.
outputAS :: [ATerm] -> IO()
outputAS [] = putStrLn ""
outputAS (aterm:res) =
       case aterm of
          AAppl "UOPaar" [_, AAppl "OWLParserOutput" [valid, msg, _, _] _] _ ->
              do  let (uri, ontology) = ontologyParse aterm
                  putStrLn ("URI: " ++ uri)
                  putStrLn $ fromATerm valid
                  putStrLn $ show (buildMsg msg)
--                putStrLn $ show namespace
                  putStrLn $ show ontology
                  outputAS res
          _ -> error "false file."

-- output total signature and sentences with all ontologies which are imported
-- (from the graph of structure analysis)
outputTotalStaticAna :: [ATerm] -> IO()
outputTotalStaticAna al =
    do let p = reverse $ parsingAll al
           (ontoMap, dg) = buildDevGraph (Map.fromList p)
       -- putStrLn $ show dg
       -- putStrLn $ show $
       --               nodesStaticAna (reverse $ topsort' dg) emptySign ontoMap
       -- putStrLn $ show $ (rdff [12] dg)
           topNodes = topsort dg
       -- putStrLn $ show $ topNodes
       -- putStrLn $ show $ map (\x -> bfs x dg) topNodes
        -- subTreeList = map (\x -> bfs x dg) top
           -- lnodeList =  map (map (\y -> matchNode dg y)) subTreeList
       let Result _ res =
               nodesStaticAna' (reverse topNodes) Map.empty ontoMap dg []
       case res of
           Just (_, dg') ->
            do -- putStrLn $ show sm
               showGraph "" defaultHetcatsOpts $
                 Just (simpleLibName "",
                       simpleLibEnv "" $ insEdges (rev $ labEdges dg)
                                       $ delEdges (edges dg') dg')
           _            -> error "no devGraph..."

    where rev :: [LEdge DGLinkLab] -> [LEdge DGLinkLab]
          rev [] = []
          rev ((source, target, edge):r) = (target, source, edge):(rev r)

matchNode :: DGraph -> Node -> LNode DGNodeLab
matchNode dgraph node =
             let (mcontext, _ ) = match node dgraph
                 (_, _, dgNode, _) = fromJust mcontext
             in (node, dgNode)

type SignMap = Map.Map Node (Sign, [Named Sentence])

nodesStaticAna' :: [Node]
               -> SignMap
               -> OntologyMap
               -> DGraph
               -> [Diagnosis]
               -> Result (SignMap, DGraph)
nodesStaticAna' [] signMap _ dg diag = Result diag (Just (signMap, dg))
nodesStaticAna' (h:r) signMap ontoMap dg diag =
    let Result digs res =
            nodeStaticAna (reverse $ map (matchNode dg) (bfs h dg))
                          (emptySign, [], diag)
                          signMap ontoMap dg
    in  case res of
        Just (newSignMap, newDg) ->
            nodesStaticAna' r newSignMap ontoMap newDg (diag++digs)
        Prelude.Nothing ->
            nodesStaticAna' r signMap ontoMap dg (diag++digs)


nodeStaticAna :: [LNode DGNodeLab]
              -> (Sign, [Named Sentence], [Diagnosis])
              -> SignMap
              -> OntologyMap
              -> DGraph
              -> Result (SignMap, DGraph)
nodeStaticAna [] _ _ _ _ = initResult
nodeStaticAna ((n,topNode):[]) (inSig, _, oldDiags) signMap ontoMap dg =
    case Map.lookup n signMap of
    Just _ ->
        Result oldDiags (Just (signMap, dg))
    _   ->
        let ontology@(Ontology _ _ _) = fromJust $
                   Map.lookup (getNameFromNode $ dgn_name topNode) ontoMap
            Result diag res =
                 basicOWL_DLAnalysis (ontology, inSig, emptyGlobalAnnos)
        in  case res of
            Just (_, accSig, sent) ->
             let newLNode = (n, topNode {dgn_theory = G_theory OWL_DL accSig
                                         (toThSens sent)})
                 ledges = (inn dg n) ++ (out dg n)
             in  Result (oldDiags ++ diag)
                        $ Just (Map.insert n (accSig, sent) signMap,
                               insEdges ledges $ insNode newLNode $
                                        delNode n dg)
            _   -> Result oldDiags Prelude.Nothing

nodeStaticAna ((n, _):r) (inSig, inSent, oldDiags) signMap ontoMap dg =
     case Map.lookup n signMap of
     Just (sig, nsen) ->
         nodeStaticAna r ((integSign sig inSig), (inSent ++ nsen), oldDiags)
                       signMap ontoMap dg
     Prelude.Nothing ->
         let Result digs' res' =
                 nodeStaticAna (reverse $ map (matchNode dg) (bfs n dg))
                                   (emptySign, [], [])
                                   signMap ontoMap dg
         in case res' of
            Just (signMap', dg') ->
             let (sig', nsen') = fromJust $ Map.lookup n signMap'
             in  nodeStaticAna r
                  ((integSign sig' inSig),(inSent ++ nsen'),(oldDiags ++ digs'))
                  signMap' ontoMap dg'
            _  -> nodeStaticAna r (inSig, inSent, oldDiags)
                                signMap ontoMap dg

integSign :: Sign -> Sign -> Sign
integSign inSig totalSig =
    let (newNamespace, transMap) =
            integrateNamespaces (namespaceMap totalSig) (namespaceMap inSig)
    in  addSign (renameNamespace transMap inSig)
                (totalSig {namespaceMap = newNamespace})

-- for graph of structure analysis
outputGraph :: String -> [ATerm] -> IO()
outputGraph filename al =
    do let p = reverse $ parsingAll al
           (_, dg) = buildDevGraph (Map.fromList p)
       showGraph filename defaultHetcatsOpts $
           Just (simpleLibName filename, simpleLibEnv filename dg)

-- for static analysis
printResOfStatic :: [ATerm] -> IO()
printResOfStatic al =
   putStrLn $ show (map output $ parsingAll al)
   where output :: (String, Ontology)
        --      -> Result (Ontology,Sign,Sign,[Named Sentence])
                -> Result (Sign,[Named Sentence])
         output (_, ontology) =
             let Result diagsA (Just (_, accSig, namedSen)) =
                     basicOWL_DLAnalysis (ontology,
                                          emptySign,
                                          emptyGlobalAnnos)
             in  Result diagsA (Just (accSig, namedSen))

-- parse of ontology which from current file with its imported ontologies
parsingAll :: [ATerm] -> [(String, Ontology)]
parsingAll [] = []
parsingAll (aterm:res) =
             (ontologyParse aterm):(parsingAll res)

ontologyParse :: ATerm -> (String, Ontology)
ontologyParse
    (AAppl "UOPaar"
        [AAppl uri _  _,
         AAppl "OWLParserOutput" [_, _, _, onto] _] _)
    = case ontology of
      Ontology _ _ namespace ->
          (if head uri == '"' then read uri::String else uri,
           -- namespace,
           propagateNspaces namespace $ createAndReduceClassAxiom ontology)
   where ontology = fromATerm onto::Ontology
ontologyParse _ = error "false ontology file."

buildMsg :: ATerm -> Message
buildMsg at = case at of
              AAppl "Message" [AList msgl _] _ ->
                  mkMsg msgl (Message [])
              _ -> error "illegal message:)"
    where
    mkMsg :: [ATerm] -> Message -> Message
    mkMsg [] (Message msg) = Message (reverse msg)
    mkMsg (h:r) (Message preRes) =
      case h of
      AAppl "Message" [a,b,c] _ ->
        mkMsg r (Message ((fromATerm a, fromATerm b, fromATerm c):preRes))
      AAppl "ParseWarning" warnings _ ->
        mkMsg r (Message (("ParserWarning", fromATerm $ head warnings, ""):preRes))
      AAppl "ParseError" errors _ ->
        mkMsg r (Message (("ParserError", fromATerm $ head errors, ""):preRes))
      _ -> error "unknow message."

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
                 -- h:(Ax (EquivalentClasses (DC cid) desps)):(findAndCreate r)
             Ax (Class cid _ Partial _ desps) ->
                 if null desps then
                    findAndCreate r (h:def, axiom, rest) -- h:(findAndCreate r)
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

-- static analysis based on order of imports graph (dfs)
nodesStaticAna :: [DGNodeLab]
               -> Sign
               -> OntologyMap
               -> Result (Ontology, Sign, [Named Sentence])
nodesStaticAna [] _ _ = initResult
nodesStaticAna (hnode:rnodes) inSign ontoMap =
    let ontology@(Ontology mid _ _) = fromJust $
                   Map.lookup (getNameFromNode $ dgn_name hnode) ontoMap
        Result diag res =
            basicOWL_DLAnalysis (ontology, inSign, emptyGlobalAnnos)
    in  case res of
        Just ((Ontology _ directives namespace), accSig, sent) ->
            concatResult
            (Result diag
              (Just ((Ontology mid directives namespace), accSig, sent)))
            (nodesStaticAna rnodes accSig ontoMap)
        _   -> nodesStaticAna rnodes inSign ontoMap

simpleLibEnv :: String -> DGraph -> LibEnv
simpleLibEnv filename dg =
    Map.singleton (simpleLibName filename) emptyGlobalContext
           { globalEnv = Map.singleton (mkSimpleId "")
             (SpecEntry ((JustNode nodeSig), [], g_sign, nodeSig))
           , devGraph = dg }
       where nodeSig = NodeSig 0 g_sign
             g_sign = G_sign OWL_DL emptySign

simpleLibName :: String -> LIB_NAME
simpleLibName s = Lib_id (Direct_link ("library_" ++ s) (Range []))
