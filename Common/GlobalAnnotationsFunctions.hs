
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002
-}
{- |
   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  non-portable (import Common.PrettyPrint)

   Some functions for building and accessing the datastructures 
   of GlobalAnnotations. This module should avoid further cyclic
   dependencies.

   todo:

-}

module Common.GlobalAnnotationsFunctions 
    ( emptyGlobalAnnos, addGlobalAnnos
    , precRel, isLAssoc, isRAssoc, isAssoc, isLiteral, getLiteralType
    , store_prec_annos, store_assoc_annos
    , nullStr, nullList, bracketList
    ) 
    where

import Common.Id
import Common.AS_Annotation
import Common.Print_AS_Annotation
import Common.PrettyPrint
import Common.GlobalAnnotations

import Common.Lib.Graph
import Common.GraphUtils
import Common.Lib.Map hiding (filter, map)

import Prelude hiding (lookup)
import Data.List (nub,mapAccumL)
import Data.Maybe (fromJust)

addGlobalAnnos :: GlobalAnnos -> [Annotation] -> GlobalAnnos
addGlobalAnnos ga annos = 
    let ga'= ga { prec_annos    = store_prec_annos    (prec_annos  ga)   annos
		, assoc_annos   = store_assoc_annos   (assoc_annos ga)   annos
		, display_annos = store_display_annos (display_annos ga) annos
		, literal_annos = store_literal_annos (literal_annos ga) annos
		} 
	in  ga' {literal_map = up_literal_map 
		                    (literal_map ga') (literal_annos ga') }

store_prec_annos :: PrecedenceGraph -> [Annotation] -> PrecedenceGraph
store_prec_annos (nm,pgr) ans = 
    let pans = filter (\an -> case an of
		              Prec_anno _ _ _ _ -> True
        		      _                 -> False) ans
	ids        = nub $ concatMap allPrecIds pans
	id_nodes   = zip (newNodes (length ids) pgr) ids
	node_map   = nm `union` fromList (map (\(x,y) -> (y,x)) id_nodes)
	the_edges  = concat $ (\(_,l) -> l) $ 
		     mapAccumL (labelEdges (+1)) 1 $ 
			            map (mkNodePairs node_map) pans
    in (node_map,
        reflexiveClosure (-5) $ transitiveClosure (-3) $ 
			         insEdges the_edges $ insNodes id_nodes pgr)
	
mkNodePairs :: Map Id Node -> Annotation -> [(Node,Node)]
mkNodePairs nmap pan = 
    map (\(s,t) -> (lookup' s,lookup' t)) $ mkPairs pan
    where lookup' i = case lookup i nmap of
		      Just n  -> n
		      Nothing -> error $ "no node for " ++ show i

mkPairs :: Annotation -> [(Id,Id)]
mkPairs (Prec_anno True  ll rl _) = concatMap ((zip ll) . repeat) rl
mkPairs (Prec_anno False ll rl _) = concatMap ((zip ll) . repeat) rl ++
				    concatMap ((zip rl) . repeat) ll
mkPairs _ = error "unsupported annotation"

precRel :: PrecedenceGraph -- ^ Graph describing the precedences
	-> Id -- ^ x oID (y iid z) -- outer id
	-> Id -- ^ x oid (y iID z) -- inner id
	-> PrecRel
precRel (imap,g) out_id in_id =
    case (o_n `inSuc` i_n,o_n `inPre` i_n) of
    (False,True)  -> Lower
    (True,False)  -> Higher
    (True,True)   -> ExplGroup BothDirections
    (False,False) -> ExplGroup NoDirection
    where i_n = lookup in_id imap
	  o_n = lookup out_id imap
	  mn1 `inSuc` mn2 = inRel (suc g) mn1 mn2
	  mn1 `inPre` mn2 = inRel (pre g) mn1 mn2
	  inRel rel mn1 mn2 = case mn1 of 
			      Nothing -> False
			      Just n1 -> case mn2 of
					 Nothing -> False
					 Just n2 -> n1 `elem` rel n2

---------------------------------------------------------------------------

store_assoc_annos :: AssocMap ->  [Annotation] -> AssocMap
store_assoc_annos am ans = am `union` fromList assos
    where assos = concat $ map conn $ filter assocA ans
	  conn (Lassoc_anno is _) = map (conn' ALeft)  is
	  conn (Rassoc_anno is _) = map (conn' ARight) is
	  conn _ = error "filtering isn't implented correct"
	  conn' sel i = (i,sel)
	  assocA an = case an of
		       Lassoc_anno _ _ -> True
		       Rassoc_anno _ _ -> True
		       _               -> False

isLAssoc :: AssocMap -> Id -> Bool
isLAssoc = isAssoc ALeft

isRAssoc :: AssocMap -> Id -> Bool
isRAssoc = isAssoc ARight

isAssoc :: AssocEither -> AssocMap -> Id -> Bool
isAssoc ae amap i =
    case lookup i amap of
    Nothing              -> False
    Just ae' | ae' == ae -> True
	     | otherwise -> False

---------------------------------------------------------------------------

store_display_annos :: DisplayMap -> [Annotation] -> DisplayMap
store_display_annos dm ans = dm `union` fromList disps
    where disps = map conn $ filter displayA ans
	  conn (Display_anno i sxs _) = (i,sxs)
	  conn _ = error "filtering isn't implemented correct"
	  displayA an = case an of
		        Display_anno _ _ _ -> True
		        _                  -> False


----------------------------------------------------------------------

up_literal_map :: LiteralMap -> LiteralAnnos -> LiteralMap
up_literal_map lmap la =
    let oids = toList lmap
	(sids,rem_str) = case string_lit la of
			 Nothing      -> ([],False)
			 Just (i1,i2) -> ([(i1,StringCons),(i2,StringNull)],
					  True)
        (lids,rem_lst) = case list_lit la of
			 Nothing -> ([],False)
			 Just (i1,i2,i3) -> ([(i1,ListBrackets),
					      (i2,ListCons),
					      (i3,ListNull)],True)
	(nid,rem_num)  = case number_lit la of
			 Nothing -> ([],False)
			 Just i  -> ([(i,Number)],True)
	(fids,rem_flo) = case float_lit la of
			 Nothing -> ([],False)
			 Just (i1,i2) -> ([(i1,Fraction),(i2,Floating)],
					  True)
	remids = (if rem_str then
		   map fst $ filter (\(_,x) ->    x == StringCons 
                                               || x == StringNull) oids  
		 else []) ++
		 (if rem_lst then
		   map fst $ filter (\(_,x) ->    x == ListCons 
                                               || x == ListNull
					       || x == ListBrackets) oids  
		 else []) ++
		 (if rem_num then
		   map fst $ filter (\(_,x) ->    x == Number) oids  
		 else []) ++
		 (if rem_flo then
		   map fst $ filter (\(_,x) ->    x == Floating 
					       || x == Fraction) oids  
		 else [])
    in (foldr delete lmap remids) `union` 
       fromList (lids ++ fids ++ nid ++ sids)

isLiteral :: LiteralMap -> Id -> Bool
isLiteral lmap i = case lookup i lmap of
		   Just _  -> True
		   Nothing -> False

getLiteralType :: LiteralMap -> Id -> LiteralType
getLiteralType lmap i =
    case lookup i lmap of
    Just t  -> t
    Nothing -> error $ show i ++ " is not a literal id"

store_literal_annos :: LiteralAnnos -> [Annotation] -> LiteralAnnos
store_literal_annos la ans = 
    let string_lit' = setStringLit (string_lit la) ans
        list_lit'   = setListLit   (list_lit la)   ans    
        test_diff s l = let (s_null,s_conc) = fromJust s
		            (l_null,l_conc) = (\(_,n,c)-> (n,c)) (fromJust l)
                            isNothing x = case x of
					  Nothing -> True
					  _ -> False
	                in or [ isNothing s
			      , isNothing l
			      , s_null /= l_null
			      , s_conc /= l_conc ]
        diff = test_diff string_lit' list_lit'
    in if diff then
           la { string_lit = string_lit'
	      , list_lit   = list_lit'
	      , number_lit = setNumberLit (number_lit la) ans
	      , float_lit  = setFloatLit  (float_lit la)  ans
	      }
       else
         error "%string- and %list-annotions use same identifiers"

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
	  getIds _ = error "filtering doesn't worked: GAF.setStringLit"

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
	  getIds _ = error "filtering doesn't worked: GAF.setFloatLit"

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
	  getId _ = error "filtering doesn't worked: GAF.setNumberLit"

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
	  getIds _ = error "filtering doesn't worked: GAF.setListLit"

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

nullStr, nullList, bracketList :: GlobalAnnos -> Id		 
nullStr ga = case string_lit $ literal_annos ga of
	     Just (n,_) -> n
	     Nothing    -> error "nullStr Id not found"

nullList ga = case list_lit $ literal_annos ga of
	      Just (_,n,_) -> n
	      Nothing    -> error "nullList Id not found"

bracketList ga = case list_lit $ literal_annos ga of
	      Just (b,_,_) -> b
	      Nothing    -> error "bracketList Id not found"

-------------------------------------------------------------------------

-- | an error function for Annotations

annotationConflict :: String -> [Annotation] -> a
annotationConflict tp ans = 
    error $ ("*** conflicting %"++ tp ++ " annotations:\n"
	      ++ showPretty ans "")

