
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002

   Some functions for building and accessing the datastructures 
   of GlobalAnnotations. This module should avoid further cyclic
   dependencies.

   todo:

-}


module GlobalAnnotationsFunctions 
    (emptyGlobalAnnos,initGlobalAnnos,setGlobalAnnos,addGlobalAnnos) 
    where

import Id
import AS_Library
import AS_Annotation
import Print_AS_Annotation
import PrettyPrint
import GlobalAnnotations

import Graph
import FiniteMap
import List (nub,mapAccumL)

emptyGlobalAnnos :: GlobalAnnos
emptyGlobalAnnos = GA (emptyFM,empty) emptyFM emptyFM emptyLiteralAnnos

initGlobalAnnos :: LIB_DEFN -> GlobalAnnos
initGlobalAnnos ld = setGlobalAnnos emptyGlobalAnnos ld

setGlobalAnnos :: GlobalAnnos -> LIB_DEFN -> GlobalAnnos
setGlobalAnnos ga ld = addGlobalAnnos ga annos
    where annos = case ld of Lib_defn _ _ _ as -> as	  

addGlobalAnnos :: GlobalAnnos -> [Annotation] -> GlobalAnnos
addGlobalAnnos ga annos = 
    ga { prec_annos    = store_prec_annos    (prec_annos  ga)   annos
       , assoc_annos   = store_assoc_annos   (assoc_annos ga)   annos
       , display_annos = store_display_annos (display_annos ga) annos
       , literal_annos = store_literal_annos (literal_annos ga) annos
       }

store_prec_annos :: PrecedenceGraph -> [Annotation] -> PrecedenceGraph
store_prec_annos (nm,pgr) ans = 
    let pans = filter (\an -> case an of
		              Prec_anno _ _ _ _ -> True
        		      _                 -> False) ans
	ids        = nub $ concatMap allIds pans
	id_nodes   = zip (newNodes (length ids) pgr) ids
	node_map   = addListToFM nm $ map (\(x,y) -> (y,x)) id_nodes
	the_edges  = concat $ (\(_,l) -> l) $ 
		     mapAccumL labelEdges 1 $ map (mkNodePairs node_map) pans
    in (node_map,insEdges the_edges $ insNodes id_nodes pgr)
	
allIds :: Annotation -> [Id]
allIds (Prec_anno _ ll rl _) = ll ++ rl
allIds _ = error "unsupported annotation"

labelEdges :: Int -> [(Node,Node)] -> (Int,[(Node,Node,Int)])
labelEdges lab ps = 
    (lab+1,map (\(s,t) -> (s,t,lab)) ps) 

mkNodePairs :: FiniteMap Id Node -> Annotation -> [(Node,Node)]
mkNodePairs nmap pan = 
    map (\(s,t) -> (lookup' s,lookup' t)) $ mkPairs pan
    where lookup' i = case lookupFM nmap i of
		      Just n  -> n
		      Nothing -> error $ "no node for " ++ show i

mkPairs :: Annotation -> [(Id,Id)]
mkPairs (Prec_anno True  ll rl _) = concatMap ((zip ll) . repeat) rl
mkPairs (Prec_anno False ll rl _) = concatMap ((zip ll) . repeat) rl ++
				    concatMap ((zip rl) . repeat) ll
mkPairs _ = error "unsupported annotation"

store_assoc_annos :: AssocMap ->  [Annotation] -> AssocMap
store_assoc_annos am ans = addListToFM am assocs
    where assocs = concat $ map conn $ filter assocA ans
	  conn (Lassoc_anno is _) = map (conn' ALeft)  is
	  conn (Rassoc_anno is _) = map (conn' ARight) is
	  conn _ = error "filtering isn't implented correct"
	  conn' sel i = (i,sel)
	  assocA an = case an of
		       Lassoc_anno _ _ -> True
		       Rassoc_anno _ _ -> True
		       _               -> False

store_display_annos :: DisplayMap -> [Annotation] -> DisplayMap
store_display_annos dm ans = addListToFM dm disps
    where disps = map conn $ filter displayA ans
	  conn (Display_anno i sxs _) = (i,sxs)
	  conn _ = error "filtering isn't implemented correct"
	  displayA an = case an of
		        Display_anno _ _ _ -> True
		        _                  -> False

emptyLiteralAnnos :: LiteralAnnos
emptyLiteralAnnos = LA { string_lit  = Nothing
			, list_lit   = Nothing 
			, number_lit = Nothing
			, float_lit  = Nothing
			}

store_literal_annos :: LiteralAnnos -> [Annotation] -> LiteralAnnos
store_literal_annos la ans = 
    la { string_lit = setStringLit (string_lit la) ans
       , list_lit   = setListLit   (list_lit la)   ans
       , number_lit = setNumberLit (number_lit la) ans
       , float_lit  = setFloatLit  (float_lit la)  ans
       }

setStringLit :: Maybe (Id,Id) -> [Annotation] -> Maybe (Id,Id)
setStringLit mids ans = 
    case sans of
	      []     -> mids
	      [a]    -> Just $ getIds a
	      (a:as) -> if all (sameIds a) as then
			   Just $ getIds a
			else 
			   annotationConflict "string" sans
    where sans = filter (\a -> case a of 
			       String_anno _ _ _ -> True
			       _    -> False) ans
	  getIds (String_anno id1 id2 _) = (id1,id2)
	  getIds _ = error "filtering dosent worked: GAF.setStringLit"

setFloatLit :: Maybe (Id,Id) -> [Annotation] -> Maybe (Id,Id)
setFloatLit mids ans = 
    case sans of
	      []     -> mids
	      [a]    -> Just $ getIds a
	      (a:as) -> if all (sameIds a) as then
			   Just $ getIds a
			else 
			   annotationConflict "floating" sans
    where sans = filter (\a -> case a of 
			       Float_anno _ _ _ -> True
			       _    -> False) ans
	  getIds (Float_anno id1 id2 _) = (id1,id2)
	  getIds _ = error "filtering dosent worked: GAF.setFloatLit"

setNumberLit :: Maybe Id -> [Annotation] -> Maybe Id
setNumberLit mids ans = 
    case sans of
	      []     -> mids
	      [a]    -> Just $ getId a
	      (a:as) -> if all (sameIds a) as then
			   Just $ getId a
			else 
			   annotationConflict "number" sans
    where sans = filter (\a -> case a of 
			       Number_anno _ _ -> True
			       _    -> False) ans
	  getId (Number_anno id1 _) = id1
	  getId _ = error "filtering dosent worked: GAF.setNumberLit"

setListLit :: Maybe (Id,Id,Id) -> [Annotation] -> Maybe (Id,Id,Id)
setListLit mids ans = 
    case sans of
	      []     -> mids
	      [a]    -> Just $ getIds a
	      (a:as) -> if all (sameIds a) as then
			   Just $ getIds a
			else 
			   annotationConflict "list" sans
    where sans = filter (\a -> case a of 
			       List_anno _ _ _ _ -> True
			       _    -> False) ans
	  getIds (List_anno id1 id2 id3 _) = (id1,id2,id3)
	  getIds _ = error "filtering dosent worked: GAF.setListLit"

sameIds :: Annotation -> Annotation -> Bool
sameIds (List_anno lid1 lid2 lid3 _) (List_anno rid1 rid2 rid3 _) =
    lid1==rid1 && lid2==rid2 && lid3==rid3
sameIds (String_anno lid1 lid2 _) (String_anno rid1 rid2 _) =
    lid1==rid1 && lid2==rid2 
sameIds (Float_anno lid1 lid2 _) (Float_anno rid1 rid2 _) =
    lid1==rid1 && lid2==rid2 
sameIds (Number_anno lid1 _) (Number_anno rid1 _) =
    lid1==rid1 
sameIds a1 a2 =
    error $ "*** wrong annotation combination for GAF.sameIds:\n"
	  ++ spp a1 ++ spp a2
    where spp a = show $ printText0 emptyGlobalAnnos a
-------------------------------------------------------------------------
-- |
-- an error function for Annotations

annotationConflict :: String -> [Annotation] -> a
annotationConflict tp ans = 
    error $ "*** conflicting %"++ tp ++ " annotations:\n"
	      ++ (show $ printText0 emptyGlobalAnnos ans)