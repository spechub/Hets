{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Heng Jiang, Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

-}


module OWL_DL.StructureAna where

import Static.DevGraph
import Data.Graph.Inductive.Graph
import OWL_DL.Sign
import OWL_DL.Logic_OWL_DL
import OWL_DL.AS
-- import Common.DefaultMorphism
import Data.Graph.Inductive.Query.DFS
import Logic.Grothendieck
import Logic.Logic
import Logic.Coerce
import Common.Id
import Common.Result
import List
import Logic.Prover
import qualified Data.Map as Map
-- import qualified Data.Set as Set
import Maybe(fromJust)
import Char(isDigit)
import OWL_DL.Namespace

import Debug.Trace

type OntologyMap = Map.Map String Ontology

buildDevGraph :: OntologyMap -> (OntologyMap, DGraph)
buildDevGraph ontoMap = 
    if detectLoop sscList then
       rebuildDGraph sscList ontoMap' dg
      else (ontoMap', dg)
     
   where (ontoMap', dg) = 
             Map.foldWithKey graphFromMap 
                    (ontoMap, Data.Graph.Inductive.Graph.empty) 
                    ontoMap
         sscList = scc dg

-- ^ detect loop reference in graph
detectLoop :: [[Node]] -> Bool
detectLoop nl = 
    any (\x -> length x > 1) nl 

graphFromMap :: String -> Ontology 
             -> (OntologyMap, DGraph) 
             -> (OntologyMap, DGraph)
graphFromMap uri onto (ontoMap, dg) =
    let existedLNodes = labNodes dg
        currentSign = simpleSign $ QN "" uri ""
       -- get current node
        (lnode, ontoMap1) = 
            createLNodes [uri] existedLNodes ontoMap 
        cl@(ind, _) = head lnode
        importsList = searchImports onto
       -- create LabNodes from imports list, thsi incl. the LNodes which been
       -- existed because of building of edge.
        (tagLNodes, ontoMap2) = 
            createLNodes importsList (nub (cl:existedLNodes)) ontoMap1
       -- if tagnode existed then it muss be reduced.
        newLNodes = reduceLNodes (cl:tagLNodes) dg

        morphism = idComorphism (Logic OWL_DL) 
        Result _ (Just comorphism) = 
             gEmbedComorphism morphism (G_sign OWL_DL currentSign 0) 
        -- TODO: check if gEmbed (Logic.Grothendieck) and G_morphism 
        -- works better:
        --   gEmbed :: G_morphism -> GMorphism
        --   data G_morphism = G_morphism lid morphism
        --   data GMorpihism = GMorphism cid sign morphism
        --   data AnyComorphism = Comorphism cid
        --   moeglicher Weg: 
        --     sigma2 <- coerceSign lid1 lid2 "XXXXXX" sigma
        --     sys = sym_of lid sigma
        --     sys1 = sym_of lid sigma1
        --     mor = adjustPos pos $ cogenerated_sign lid 
        --              (sys1 `Set.difference` sys) sigma2
        --      gEmbed (G_morphism lid mor)
        ledgeList = map (\y -> 
                             let (indT, _) = y
                             in (ind, indT, DGLink { dgl_morphism = comorphism,
                                                     dgl_type = GlobalDef,
                                                     dgl_origin = DGImports
                                                   })
                        ) tagLNodes
    in  if isEmpty dg then
             (ontoMap2, (mkGraph newLNodes ledgeList))
           else 
             (ontoMap2, insEdges ledgeList (insNodes newLNodes dg))
             
                              
searchImports :: Ontology -> [String]
searchImports (Ontology _ directives _) = findImports directives
    where
    findImports :: [Directive] -> [String]
    findImports [] = []
    findImports (hd:rd) = 
        case hd of
        Ax (OntologyProperty oid uriannos) ->   
            if localPart oid == "imports" then
               findImports' uriannos
               else findImports rd
        _ -> findImports rd
    findImports' :: [OWL_DL.AS.Annotation] -> [String]
    findImports' [] = []
    findImports' (ha:ra) =
        case ha of
        URIAnnotation _ qn ->
            (localPart qn):(findImports' ra)
        _ -> []
          
createLNodes :: [String] -> [LNode DGNodeLab] 
             -> OntologyMap 
             -> ([LNode DGNodeLab], OntologyMap)
createLNodes [] _ om = ([], om)
createLNodes (hs:rs) exLNodes om =
    let lnode@(_, currentLN) = buildLNodeFromStr hs ((length exLNodes)-1)
    in  -- if the node already existed muss be anyhow also created 
        -- for building of edges. But the ontology map need not to
        -- change
        if isEqLNode currentLN exLNodes then
           let (newLNodes, ontoMap') = createLNodes rs exLNodes om
           in (
               (getLnode currentLN exLNodes):newLNodes,
               ontoMap'
              )
           else let lnode' = disambiguateName lnode exLNodes
                    (newLNodes, ontoMap') =
                        createLNodes rs (lnode':exLNodes) om
                    (sid, _, _) = dgn_name $ snd lnode'
                in  
                   (
                     lnode':newLNodes,
                     Map.delete hs (Map.insert (show sid) 
                                    (case Map.lookup hs ontoMap' of
                                      Just res -> res
                                      Prelude.Nothing -> emptyOntology
                                    ) 
                                    ontoMap')
                    )
    
    where 
          -- get (LNode DGNodeLab) with LabNode 
          getLnode _ [] = error "LNode not found"
          getLnode node (hx:rx) | dgn_theory node == (dgn_theory $ snd hx) = hx
                                | otherwise = getLnode node rx

          isEqLNode :: DGNodeLab -> [LNode DGNodeLab] -> Bool
          isEqLNode cn exn = 
              any (\x -> (dgn_theory cn) == (dgn_theory $ snd x)) exn

          disambiguateName :: (LNode DGNodeLab)
                           -> [LNode DGNodeLab] 
                           -> (LNode DGNodeLab)
          disambiguateName (ind, dgn) exn = 
            let name@(sid, u1, u2) = dgn_name dgn
                nameSet = map (dgn_name . snd) exn
                name' = if name `elem` nameSet then
                           let n = show sid
                               nsid = if isDigit $ head $ reverse n then
                                         take ((length n) - 1) n
                                         else n
                           in  fromJust $ find (not . flip elem nameSet)
                                   [(mkSimpleId (nsid ++
                                            (show (i::Int))),u1,u2)|i<-[1..]]
                         else name
            in  (ind, dgn {dgn_name = name'})
                                  
buildLNodeFromStr :: String -> Int -> (LNode DGNodeLab)
buildLNodeFromStr uri i =
    let name = uriToName uri
        nodeName = makeName $ mkSimpleId name
        currentSign = simpleSign $ QN "" uri ""
    in  (i+1, DGNode { dgn_name = nodeName,
                       dgn_theory = G_theory OWL_DL currentSign 0 noSens 0,
                       -- lass erstmal kein Signatur.
                       -- dgn_sens = G_l_sentence_list OWL_DL [],
                       dgn_nf = Prelude.Nothing,
                       dgn_sigma = Prelude.Nothing,
                       dgn_origin = DGBasic,
                       dgn_cons = None,
                       dgn_cons_status = LeftOpen
                     }
        )

-- remove existed nodes in graph
reduceLNodes :: [LNode DGNodeLab] -> DGraph -> [LNode DGNodeLab]
reduceLNodes [] _ = []
reduceLNodes (hn@(ind, _):rn) dg =
      if gelem ind dg then
         reduceLNodes rn dg
         else hn:(reduceLNodes rn dg)



rebuildDGraph :: [[Node]] -> OntologyMap -> DGraph -> (OntologyMap, DGraph)
rebuildDGraph [] ontoMap dg = (ontoMap, dg)
rebuildDGraph (hd:rs) ontoMap dg 
   | length hd <= 1 = rebuildDGraph rs ontoMap dg
   | otherwise      = 
       let (ontoMap', dg') = integrateScc hd ontoMap dg
       in   rebuildDGraph rs ontoMap' dg'

integrateScc :: [Node] -> OntologyMap -> DGraph -> (OntologyMap, DGraph)
integrateScc nodeList ontoMap dg =
    let decomps = map (fromJust . fst . flip match dg) nodeList 
        (_, _, lnodes,_) = unzip4 decomps
        dgnNames = map (getNameFromNode . dgn_name) lnodes
        theories = map dgn_theory lnodes
        ontologies = map (\x -> case Map.lookup x ontoMap of
                                Just res -> res
                                Prelude.Nothing -> emptyOntology
                         ) dgnNames
        newName = makeName $ mkSimpleId $ (\z -> take ((length z) -1) z) $ 
                    foldr (\x y -> x ++ "_" ++ y) "" dgnNames
        newTheory = integrateTheory theories
        newNodeNum = noNodes dg
    in  (
         Map.insert (getNameFromNode newName)
                    (foldl integrateOntology emptyOntology ontologies)
                    (Map.filterWithKey (\x _ -> not $ x `elem` dgnNames) ontoMap), 
         delNodes nodeList 
           $ changeEdges decomps newNodeNum 
           $ insNode (newNodeNum, 
                 DGNode { dgn_name = newName,
                          dgn_theory = newTheory,
                          dgn_nf = Prelude.Nothing,
                          dgn_sigma = Prelude.Nothing,
                          dgn_origin = DGintegratedSCC,
                          dgn_cons = None,
                          dgn_cons_status = LeftOpen
                        }
                ) dg
        )

-- simple integrate Theory
integrateTheory :: [G_theory] -> G_theory
integrateTheory theories = 
  foldl assembleTheories emptyOWL_DLTheory theories
   where
    assembleTheories :: G_theory -> G_theory -> G_theory
    assembleTheories (G_theory lid1 sign1 _ theSen1 _) 
                     (G_theory lid2 sign2 _ theSen2 _) =
              let thSen2' = maybe (error "could not coerce sentences") 
                        id (coerceThSens lid2 lid1 "" theSen2)
                  sign2' = maybe (error "could not coerce sign") 
                        id (coerceSign lid2 lid1 "" sign2)
                  csign = case signature_union lid1 sign2' sign1 of
                          Result dgs mv -> 
                              maybe (error ("sig_union"++show dgs)) id mv
              in G_theory lid1 csign 0 (joinSens theSen1 thSen2') 0 



getNameFromNode :: NODE_NAME -> String
getNameFromNode (sid, _, _) = show sid

changeEdges :: [Context DGNodeLab DGLinkLab] -> Node -> DGraph -> DGraph
changeEdges [] _ dg = dg
changeEdges ((fromNodes, n, _, toNodes):r) newNode dg =
    changeEdges r newNode $ changeTo toNodes $ changeFrom fromNodes dg
    where changeFrom :: [(DGLinkLab, Node)] -> DGraph -> DGraph
          changeFrom [] dg2 = dg2
          changeFrom ((dgLink,fn):rf) dg2 
            | fn `gelem` dg2 = 
                changeFrom rf $ insEdge (fn, newNode, dgLink) $ 
                                    delEdge (fn, n) dg2
            | otherwise = changeFrom rf dg2
                
          changeTo :: [(DGLinkLab, Node)] -> DGraph -> DGraph
          changeTo [] dg2 = dg2
          changeTo ((dgLink,tn):rf) dg2 
            | tn `gelem` dg2 = 
                changeTo rf $ insEdge (newNode, tn, dgLink) $ 
                                    delEdge (n, tn) dg2
            | otherwise = changeTo rf dg2

emptyOWL_DLTheory:: G_theory
emptyOWL_DLTheory = G_theory OWL_DL emptySign 0 noSens 0




