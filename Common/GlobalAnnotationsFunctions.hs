
{- HetCATS/GlobalAnnotations.hs
   $Id$
   Author: Klaus Lüttich
   Year:   2002
-}
{- |
   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  portable

   Some functions for building and accessing the datastructures 
   of GlobalAnnotations. 

   todo: yield a proper result instead of runtime errors for conflicts

-}

module Common.GlobalAnnotationsFunctions 
    ( emptyGlobalAnnos, addGlobalAnnos
    , precRel, isLAssoc, isRAssoc, isAssoc, isLiteral, getLiteralType
    , store_prec_annos, store_assoc_annos
    , nullStr, nullList, getListBrackets, listBrackets
    ) 
    where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map

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
store_prec_annos pgr = Rel.transClosure . 
    foldr ( \ an p0  -> case an of 
	    Prec_anno prc lIds hIds _ -> 
	             foldr ( \ li p1 -> 
			     foldr ( \ hi p2 -> 
				     if li == hi then error 
				     ("prec_anno with equal ids: " ++
				      show li ++ " < " ++ show hi)
				     else if Rel.transMember hi li p2 then
				     error ("prec_anno conflict: " ++
					    show li ++ " < " ++ show hi ++
					    "\n" ++ show p2)
				     else 
				     case prc of 
				     Lower -> Rel.insert li hi p2
				     Higher -> Rel.insert hi li p2
				     BothDirections -> 
				           Rel.insert hi li (Rel.insert 
							     li hi p2)
				     NoDirection -> p2)
			     p1 hIds)
	              p0 lIds
	    _ -> p0 ) pgr  

precRel :: PrecedenceGraph -- ^ Graph describing the precedences
	-> Id -- ^ x oID (y iid z) -- outer id
	-> Id -- ^ x oid (y iID z) -- inner id
	-> PrecRel
-- a 'Lower' corresponds to %prec {out_id} < {in_id} 
precRel pg out_id in_id =
    case (Rel.member in_id out_id pg, Rel.member out_id in_id pg) of
    (False,True)  -> Lower
    (True,False)  -> Higher
    (True,True)   -> BothDirections
    (False,False) -> NoDirection

---------------------------------------------------------------------------

store_assoc_annos :: AssocMap ->  [Annotation] -> AssocMap
store_assoc_annos am = Map.union am . Map.fromList .
    foldr ( \ an l -> 
	    case an of 
	    Assoc_anno as is _ -> map ( \ a -> (a, as)) is ++ l
	    _ -> l ) []

isLAssoc :: AssocMap -> Id -> Bool
isLAssoc = isAssoc ALeft

isRAssoc :: AssocMap -> Id -> Bool
isRAssoc = isAssoc ARight

isAssoc :: AssocEither -> AssocMap -> Id -> Bool
isAssoc ae amap i =
    case Map.lookup i amap of
    Nothing              -> False
    Just ae' | ae' == ae -> True
	     | otherwise -> False

---------------------------------------------------------------------------

store_display_annos :: DisplayMap -> [Annotation] -> DisplayMap
store_display_annos dm = Map.union dm . Map.fromList .
    foldr ( \ an l -> 
	    case an of 
	    Display_anno i sxs _ -> (i,sxs) : l
	    _ -> l) []

----------------------------------------------------------------------

up_literal_map :: LiteralMap -> LiteralAnnos -> LiteralMap
up_literal_map lmap la =
    let oids = Map.toList lmap
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
    in (foldr Map.delete lmap remids) `Map.union` 
       Map.fromList (lids ++ fids ++ nid ++ sids)

isLiteral :: LiteralMap -> Id -> Bool
isLiteral lmap i = case Map.lookup i lmap of
		   Just _  -> True
		   Nothing -> False

getLiteralType :: LiteralMap -> Id -> LiteralType
getLiteralType lmap i =
    case Map.lookup i lmap of
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
setStringLit = 
    foldr ( \ a m ->
	    case a of 
	    String_anno id1 id2 _ ->
	        case m of 
	        Nothing -> Just (id1, id2)
	        Just p -> 
	            if (id1, id2) == p then m
	            else error ("conflict %string " ++ showId id1 "," 
				++ showId id2 " and " ++ show p)
	    _ -> m )

setFloatLit :: Maybe (Id,Id) -> [Annotation] -> Maybe (Id,Id)
setFloatLit = 
    foldr ( \ a m ->
	    case a of 
	    Float_anno id1 id2 _ ->
	        case m of 
	        Nothing -> Just (id1, id2)
	        Just p -> 
	            if (id1, id2) == p then m
	            else error ("conflict %floating " ++ showId id1 "," 
				++ showId id2 " and " ++ show p)
	    _ -> m )

setNumberLit :: Maybe Id -> [Annotation] -> Maybe Id
setNumberLit =
    foldr ( \ a m -> 
	    case a of 
	    Number_anno id1 _ -> 
	        case m of 
	        Nothing -> Just id1
	        Just id2 -> 
	            if id1 == id2 then m
	            else error ("conflict %number " ++ showId id1 " and " 
	                  ++ show id2)
	    _ -> m )

setListLit :: Maybe (Id,Id,Id) -> [Annotation] -> Maybe (Id,Id,Id)
setListLit = 
    foldr ( \ a m ->
	    case a of 
	    List_anno id1 id2 id3 _ ->
	        case m of 
	        Nothing -> Just (id1, id2, id3)
	        Just p -> 
	            if (id1, id2, id3) == p then m
	            else error ("conflict %list " ++ showId id1 "," 
				++ showId id2 "'" ++ showId id3 " and " 
				++ show p)
	    _ -> m )

-------------------------------------------------------------------------

nullStr, nullList :: GlobalAnnos -> Id		 
nullStr ga = case string_lit $ literal_annos ga of
	     Just (n,_) -> n
	     Nothing    -> error "nullStr Id not found"

nullList ga = case list_lit $ literal_annos ga of
	      Just (_,n,_) -> n
	      Nothing    -> error "nullList Id not found"

---------------------------------------------------------------------------

getListBrackets :: Id -> ([Token], [Token])
getListBrackets (Id b _ _) = 
    let (b1, rest) = break isPlace b
	b2 = if null rest then [] 
	     else filter (not . isPlace) rest
    in (b1, b2)

listBrackets :: GlobalAnnos -> ([Token], [Token])
listBrackets g = 
    case list_lit $ literal_annos g of
		Nothing -> ([], [])
		Just (bs, _, _) -> getListBrackets bs

-------------------------------------------------------------------------

