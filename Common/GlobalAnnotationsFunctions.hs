
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
    , precRel, isLAssoc, isRAssoc, isAssoc, getLiteralType
    , store_prec_annos, store_assoc_annos
    , getListBrackets, listBrackets
    ) 
    where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

addGlobalAnnos :: GlobalAnnos -> [Annotation] -> GlobalAnnos
addGlobalAnnos ga annos = 
             ga { prec_annos    = store_prec_annos    (prec_annos  ga)   annos
		, assoc_annos   = store_assoc_annos   (assoc_annos ga)   annos
		, display_annos = store_display_annos (display_annos ga) annos
		, literal_annos = store_literal_annos (literal_annos ga) annos
		, literal_map   = store_literal_map (literal_map ga) annos
		} 

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
				     BothDirections -> 
				           Rel.insert hi li (Rel.insert 
							     li hi p2)
				     _ -> error "prec_anno relation")
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
    Nothing  -> False
    Just ae' -> ae' == ae 

---------------------------------------------------------------------------

store_display_annos :: DisplayMap -> [Annotation] -> DisplayMap
store_display_annos = 
    foldr ( \ an m -> 
	    case an of 
	    Display_anno i sxs _ -> 
	       let t = Map.findWithDefault Map.empty i m in 
	       Map.insert i 
	       (foldr ( \ (df, str) tab ->
			let oldStr = Map.findWithDefault str df tab in 
			if oldStr == str then  
			Map.insert df str tab
			else error ("conflict: " ++ show an)
		      ) t sxs) m
	    _ -> m )

----------------------------------------------------------------------

getLiteralType ::  GlobalAnnos -> Id -> LiteralType
getLiteralType ga i = 
    Map.findWithDefault NoLiteral i $ literal_map ga

store_literal_map :: LiteralMap -> [Annotation] -> LiteralMap
store_literal_map = 
    foldr ( \ a m -> let err = error ("conflict: " ++ show a) in
	    case a of 
	    Number_anno id1 _ -> 
	        let oc = Map.findWithDefault Number id1 m
	            in if oc == Number -- repeated or new
	            then Map.insert id1 Number m else err  
	    String_anno id1 id2 _ ->
	        let c = StringCons id1
                    oc = Map.findWithDefault c id2 m
	            on = Map.findWithDefault StringNull id1 m
	            in if oc == c && on == StringNull then
	            Map.insert id1 StringNull $ Map.insert id2 c m
	            else err
	    Float_anno id1 id2 _ ->
	        let oc = Map.findWithDefault Fraction id1 m
	            on = Map.findWithDefault Floating id2 m
	            in if oc == Fraction && on == Floating then
	            Map.insert id2 Floating $ Map.insert id1 Fraction m
	            else err
	    List_anno id1 id2 id3 _ -> 
	        let c = ListCons id1 id2
	            n = ListNull id1
                    oc = Map.findWithDefault c id3 m
	            on = Map.findWithDefault n id2 m
	            in if c == oc && n == on then
	            Map.insert id2 n $ Map.insert id3 c m  
	            else err
	    _ -> m )

store_literal_annos :: LiteralAnnos -> [Annotation] -> LiteralAnnos
store_literal_annos la ans = 
           la { string_lit = setStringLit (string_lit la) ans
	      , list_lit = setListLit (list_lit la) ans
	      , number_lit = setNumberLit (number_lit la) ans
	      , float_lit  = setFloatLit  (float_lit la)  ans
	      }

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

setListLit :: Set.Set (Id,Id,Id) -> [Annotation] -> Set.Set (Id,Id,Id)
setListLit = 
    foldr ( \ a s ->
            case a of 
            List_anno id1 id2 id3 _ ->
                    let cs = Set.filter ( \ ( o1, o2, o3) -> 
                                 o1 == id1 || o2 == id2 || o3 == id3) s in
                    if Set.isEmpty cs then Set.insert (id1, id2, id3) s 
                    else error ("conflict %list " ++ showId id1 "," 
                                ++ showId id2 "'" ++ showId id3 " and " 
                                ++ show (Set.findMin cs))
            _ -> s )

-------------------------------------------------------------------------

getListBrackets :: Id -> ([Token], [Token], [Id])
getListBrackets (Id b cs _) = 
    let (b1, rest) = break isPlace b
	b2 = if null rest then [] 
	     else filter (not . isPlace) rest
    in (b1, b2, cs)

listBrackets :: GlobalAnnos -> Id -> Id
listBrackets g i = 
    case Map.findWithDefault Number i $ literal_map g of
    ListNull b -> b
    ListCons b _ -> b
    _ -> error "listBrackets"

-------------------------------------------------------------------------

