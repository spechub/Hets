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
import Common.DefaultMorphism
import Text.XML.HXT.DOM.XmlTreeTypes
import Logic.Grothendieck
import Common.Id
import List
import qualified Common.Lib.Map as Map
-- import Debug.Trace
-- import Data.Graph.Inductive.Tree

buildDevGraph :: Map.Map String Ontology -> DGraph
buildDevGraph ontoMap = Map.foldWithKey graphFromMap Data.Graph.Inductive.Graph.empty ontoMap

graphFromMap :: String -> Ontology -> DGraph -> DGraph
-- buildDevGraph [] dg = dg
graphFromMap uri onto dg =            --  ((uri, onto):r) dg = 
    let existedLNodes = labNodes dg
	-- existedLEdges = labEdges dg
	
        currentSign = simpleSign $ strToQN uri
	cl@(ind, currentLnode) = head $ createLNodes [uri] existedLNodes
	importsList = searchImports onto
	tagLNodes = createLNodes importsList (nub (cl:existedLNodes))
	newLNodes = reduceLNodes (cl:tagLNodes) dg

	morphismList = 
		  map (\x -> GMorphism OWL_DL 
		             currentSign 
		             (ideOfDefaultMorphism $ simpleSign $ strToQN x)
		      ) $ reverse importsList
	ledgeList = map (\(x, y) -> 
		             let (indT, _) = y
		             in (ind, indT, DGLink { dgl_morphism = x,
						     dgl_type = GlobalDef,
						     dgl_origin = DGBasic
						   })
                        ) (zip morphismList tagLNodes)
    in  if isEmpty dg then
             mkGraph newLNodes ledgeList
	     
	   else 
	     insEdges ledgeList (insNodes newLNodes dg)
	     
			      
searchImports :: Ontology -> [String]
searchImports (Ontology _ directives) = findImports directives
					
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
	   else let lnode' = disambiguateName lnode 1 exLNodes
                in  lnode':(createLNodes rs (lnode':exLNodes))
    
    where getLnode _ [] = error "LNode not found"
	  getLnode node (hx:rx) | dgn_sign node == (dgn_sign $ snd hx) = hx
			        | otherwise = getLnode node rx

          isEqLNode :: DGNodeLab -> [LNode DGNodeLab] -> Bool
	  isEqLNode cn exn = 
	      any (\x -> (dgn_sign cn) == (dgn_sign $ snd x)) exn

          disambiguateName :: (LNode DGNodeLab) -> Int
			   -> [LNode DGNodeLab] 
			   -> (LNode DGNodeLab)
          disambiguateName cn@(ind, dgn) end exn = 
              if any (\x -> (dgn_name dgn) == (dgn_name $ snd x)) exn then
		 disambiguateName (ind, newDgn) (end+1) exn
		 else cn
	     where newDgn = 
		    case dgn of
		    DGNode (sid, u1, u2 ) p2 p3 p4 p5 p6->
		      let idstr = show sid
			  re = take ((length idstr) - (length $ showInt (end -1))) (show sid) 
		          newID = mkSimpleId (re++(showInt end))
			  newName = (newID, u1, u2) 
		      in  DGNode newName p2 p3 p4 p5 p6
		    u -> u 
			     
				  
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
	currentSign = simpleSign $ name
    in  (i+1, DGNode { dgn_name = nodeName,
		       dgn_sign = G_sign OWL_DL currentSign,
		       -- lass erstmal kein Signatur.
		       dgn_sens = G_l_sentence_list OWL_DL [],
		       dgn_nf = Prelude.Nothing,
		       dgn_sigma = Prelude.Nothing,
		       dgn_origin = DGBasic
		     }
	)

reduceLNodes :: [LNode DGNodeLab] -> DGraph -> [LNode DGNodeLab]
reduceLNodes [] _ = []
reduceLNodes (hn@(ind, _):rn) dg =
      if gelem ind dg then
	 reduceLNodes rn dg
	 else hn:(reduceLNodes rn dg)


