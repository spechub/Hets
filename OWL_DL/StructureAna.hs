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
-- import OWL_DL.ReadWrite
-- import Common.DefaultMorphism
import Data.Graph.Inductive.Query.DFS
import Text.XML.HXT.DOM.XmlTreeTypes
import Logic.Grothendieck
import Logic.Logic
import Common.Id
import Common.Result
import List
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Maybe(fromJust)
import Debug.Trace
-- import Data.Graph.Inductive.Tree

buildDevGraph :: Map.Map String Ontology -> DGraph
buildDevGraph ontoMap = if detectLoop sscList then
			   rebuildDGraph sscList dg
			   else dg
        where dg = (Map.foldWithKey graphFromMap 
		    Data.Graph.Inductive.Graph.empty 
		    ontoMap)
	      sscList = scc (trace ("DEBUG: " ++ (show $ dfs' dg)) dg)

detectLoop :: [[Node]] -> Bool
detectLoop nl = 
    any (\x -> length x > 1) nl	

graphFromMap :: String -> Ontology -> DGraph -> DGraph
-- buildDevGraph [] dg = dg
graphFromMap uri onto dg =            --  ((uri, onto):r) dg = 
    let existedLNodes = labNodes dg
	-- existedLEdges = labEdges dg
	
        currentSign = simpleSign $ strToQN uri
	cl@(ind, _) = head $ createLNodes [uri] existedLNodes
	importsList = searchImports onto
	tagLNodes = createLNodes importsList (nub (cl:existedLNodes))
	newLNodes = reduceLNodes (cl:tagLNodes) dg
{-
	morphismList = 
		  map (\x -> GMorphism OWL_DL 
		             currentSign 
		             (ideOfDefaultMorphism $ simpleSign $ strToQN x)
		      ) $ reverse importsList
-}
	morphism = idComorphism (Logic OWL_DL) 
	Result _ (Just comorphism) = 
	    gEmbedComorphism morphism (G_sign OWL_DL currentSign)	
	ledgeList = map (\y -> 
		             let (indT, _) = y
		             in (ind, indT, DGLink { dgl_morphism = comorphism,
						     dgl_type = GlobalDef,
						     dgl_origin = DGImports
						   })
                        ) tagLNodes
    in  if isEmpty dg then
             mkGraph newLNodes ledgeList
	   else 
	     insEdges ledgeList (insNodes newLNodes dg)
	     
			      
searchImports :: Ontology -> [String]
searchImports (Ontology _ directives _) = findImports directives
					
findImports :: [Directive] -> [String]
findImports [] = []
findImports (hd:rd) = 
    case hd of
       Ax (OntologyProperty oid uriannos) ->   --   [URIAnnotation aid qn]) ->
	    if localPart oid == "imports" then
	       findImports' uriannos
	       else findImports rd
       _ -> findImports rd
  where findImports' :: [Annotation] -> [String]
	findImports' [] = []
	findImports' (ha:ra) =
	    case ha of
	      URIAnnotation _ qn ->
		  (localPart qn):(findImports' ra)
	      _ -> []
	  
createLNodes :: [String] -> [LNode DGNodeLab] -> [LNode DGNodeLab]
createLNodes [] _ = []
createLNodes (hs:rs) exLNodes =
    let lnode@(_, currentLN) = buildLNodeFromStr hs ((length exLNodes) -1)
    in  if isEqLNode currentLN exLNodes then
	   (getLnode currentLN exLNodes):(createLNodes rs exLNodes)
	   else let lnode' = disambiguateName lnode exLNodes
                in  lnode':(createLNodes rs (lnode':exLNodes))
    
    where getLnode _ [] = error "LNode not found"
	  getLnode node (hx:rx) | dgn_sign node == (dgn_sign $ snd hx) = hx
			        | otherwise = getLnode node rx

          isEqLNode :: DGNodeLab -> [LNode DGNodeLab] -> Bool
	  isEqLNode cn exn = 
	      any (\x -> (dgn_sign cn) == (dgn_sign $ snd x)) exn

          disambiguateName :: (LNode DGNodeLab)
			   -> [LNode DGNodeLab] 
			   -> (LNode DGNodeLab)
          disambiguateName (ind, dgn) exn = 
	    let name@(sid, u1, u2) = dgn_name dgn
		nameSet = map (dgn_name . snd) exn
                name' = if name `elem` nameSet then
		          fromJust $ find (not . flip elem nameSet)
                          [(mkSimpleId ((show sid)++(show (i::Int))),u1,u2)|i<-[1..]]
			 else name
            in  (ind, dgn {dgn_name = name'})
		     
				  
strToQN :: String -> QName
strToQN str = 
    let str' = if head str == '"' then
	          read str::String
		  else str
        nodeName = fst $ span (/='/') $ reverse str'
    in  if head nodeName == '#' then
	   QN "" (fst $ span (/='.') (reverse $ tail nodeName)) str'  
	   -- QN prefix local uri
	   else QN ""  (fst $ span (/='.') (reverse nodeName)) str'

buildLNodeFromStr :: String -> Int -> (LNode DGNodeLab)
buildLNodeFromStr uri i =
    let name = strToQN uri
	nodeName = makeName $ mkSimpleId $ localPart name
	currentSign = simpleSign name
    in  (i+1, DGNode { dgn_name = nodeName,
		       dgn_theory = G_theory OWL_DL currentSign Set.empty,
		       -- lass erstmal kein Signatur.
		       -- dgn_sens = G_l_sentence_list OWL_DL [],
		       dgn_nf = Prelude.Nothing,
		       dgn_sigma = Prelude.Nothing,
		       dgn_origin = DGBasic,
		       dgn_cons = None,
		       dgn_cons_status = LeftOpen
		     }
	)

reduceLNodes :: [LNode DGNodeLab] -> DGraph -> [LNode DGNodeLab]
reduceLNodes [] _ = []
reduceLNodes (hn@(ind, _):rn) dg =
      if gelem ind dg then
	 reduceLNodes rn dg
	 else hn:(reduceLNodes rn dg)

rebuildDGraph :: [[Node]] -> DGraph -> DGraph
rebuildDGraph [] dg = dg
rebuildDGraph (hd:rs) dg 
   | length hd <= 1 = rebuildDGraph rs dg
   | otherwise = rebuildDGraph rs $ integrateScc hd dg

integrateScc :: [Node] -> DGraph -> DGraph
integrateScc nodeList dg =
    let decomps = map (fromJust . fst . flip match dg) nodeList 
	(_, _, lnodes,_) = unzip4 decomps
 	dgnNames = map (getNameFromNode . dgn_name) lnodes
	theories = map dgn_theory lnodes
	
        newName = makeName $ mkSimpleId $ (\z -> take ((length z) -1) z) $ 
		    foldr (\x y -> x ++ "_" ++ y) "" dgnNames
	newTheory = integrateTheory theories
	newNodeNum = (noNodes dg)
    in  insNode (newNodeNum, 
		 DGNode { dgn_name = newName,
			  dgn_theory = newTheory,
			  dgn_nf = Prelude.Nothing,
			  dgn_sigma = Prelude.Nothing,
			  dgn_origin = DGintegratedSCC,
			  dgn_cons = None,
			  dgn_cons_status = LeftOpen
		       	}
		) $ changeEdges2 decomps newNodeNum (delNodes nodeList dg)

-- simple integrate Theory
integrateTheory :: [G_theory] -> G_theory
integrateTheory theories = head theories
{-
  foldl assembleTheories emptyOWL_DLTheory theories
   where
    assembleTheories :: G_theory -> G_theory -> G_theory
    assembleTheories (G_theory _ sign1 theSen1) 
		     (G_theory _ sign2 theSen2) =
          G_theory OWL_DL (addSign sign1 sign2)   
		          (Set.union theSen1 theSen2)
-}
    

getNameFromNode :: NODE_NAME -> String
getNameFromNode (sid, _, _) = show sid

changeEdges2 :: [Context DGNodeLab DGLinkLab] -> Node -> DGraph -> DGraph
changeEdges2 [] _ dg = dg
changeEdges2 ((fromNodes, n, _, toNodes):r) newNode dg =
    changeEdges2 r newNode $ changeTo toNodes $ changeFrom fromNodes dg
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






