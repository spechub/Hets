
{- |

   Module      :  $Header$
   Copyright   :  (c) Christian Maeder, Klaus Lüttich and Uni Bremen 2002-2003
   Licence     :  All rights reserved.


   Maintainer  :  hets@tzi.de
   Stability   :  provisional
   Portability :  portable

   Some functions for building and accessing the datastructures 
   of GlobalAnnotations. 

   todo: yield a proper result instead of runtime errors for conflicts

-}

module Common.AnalyseAnnos
    ( emptyGlobalAnnos, addGlobalAnnos
    , precRel, isLAssoc, isRAssoc, isAssoc, getLiteralType
    , store_prec_annos, store_assoc_annos
    , getListBrackets, listBrackets
    ) 
    where

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Print_AS_Annotation
import Common.PrettyPrint
import Common.Result
import Control.Monad

import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

addGlobalAnnos :: GlobalAnnos -> [Annotation] -> Result GlobalAnnos
addGlobalAnnos ga annos = 
    do n_prec_annos <- store_prec_annos (prec_annos  ga)   annos
       n_assoc_annos <- store_assoc_annos (assoc_annos ga)   annos
       n_display_annos <- store_display_annos (display_annos ga) annos
       n_literal_annos <- store_literal_annos (literal_annos ga) annos
       n_literal_map <- store_literal_map (literal_map ga) annos

       return ga { prec_annos =  n_prec_annos
		 , assoc_annos = n_assoc_annos 
		 , display_annos = n_display_annos
		 , literal_annos = n_literal_annos
		 , literal_map = n_literal_map}
  

store_prec_annos :: PrecedenceGraph -> [Annotation] -> Result PrecedenceGraph
store_prec_annos pgr ans = fmap Rel.transClosure $
    foldM ( \ p0 an -> case an of 
	    Prec_anno prc lIds hIds _ -> 
                 foldM (\ p1 li -> 
	             foldM ( \ p2 hi -> -- hi und pi2 getauscht 
			     if li == hi 
			     then Result [mkDiag Error 
				       "prec_anno with equal id" hi] (Just p2)
			     else case prc of 
			            Lower -> if Rel.transMember hi li p2 
				             then Result [mkDiag Error 
							("prec_anno conflict: "
							 ++ showId li " < " 
							 ++ showId hi "\n" 
							 ++ showRel p2 "") hi] 
			                                   (Just p2)
			                     else return (Rel.insert li hi p2)
                                    BothDirections -> 
				             if Rel.transMember hi li p2 == 
				                Rel.transMember li hi p2 
				             then return (Rel.insert hi li 
				                         (Rel.insert li hi p2))
                                             else Result [mkDiag Error
							("prec_anno conflict: "
							  ++ showId li " <> " 
							  ++ showId hi "\n" 
							  ++ showRel p2 "") hi]
			                                   (Just p2)
			            _ -> Result [mkDiag Error 
				                 "prec_anno relation" hi] 
		                                (Just p2)
			     ) p1 hIds
	               ) p0 lIds	                           
	    _ -> return p0) pgr ans
    where showRel r = showSepList (showString "\n") showIdPair $ Rel.toList r

 
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
store_assoc_annos :: AssocMap ->  [Annotation] -> Result AssocMap
store_assoc_annos
    = foldM ( \ am0 an ->
	      case an of 
	      Assoc_anno as is _ -> 
	        foldM ( \ am1 i -> 
			let v = Map.lookup i am1 in 
			case v of 
			Nothing -> return $ Map.insert i as am1 
			Just os -> Result [if as == os then mkDiag Hint 
				"repeated associative identifier" i
					               else mkDiag Error 
				"identifier has already other associativity" i]
		                $ Just am1 ) am0 is
	      _ -> return am0 )

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

store_display_annos :: DisplayMap -> [Annotation] -> Result DisplayMap
store_display_annos = 
    foldM ( \ m an -> 
	    case an of 
	    Display_anno i sxs _ -> 
	       do let t = Map.findWithDefault Map.empty i m
	          dm <- foldM ( \ tab (df, str) ->
			let oldStr = Map.findWithDefault str df tab in 
			if oldStr == str 
			then return $ Map.insert df str tab
			else Result [mkDiag Error ("conflict: " 
                                     ++ showPretty an "") an] $ Just tab
			      ) t sxs
                  return $ Map.insert i dm m  
	    _ -> return m )

----------------------------------------------------------------------

getLiteralType ::  GlobalAnnos -> Id -> LiteralType
getLiteralType ga i = 
    Map.findWithDefault NoLiteral i $ literal_map ga

store_literal_map :: LiteralMap -> [Annotation] -> Result LiteralMap
store_literal_map = 
    foldM ( \ m a -> 
	    case a of 
	    Number_anno id1 _ -> 
	        let oc = Map.findWithDefault Number id1 m in 
	        if oc == Number -- repeated or new
	        then return $ Map.insert id1 Number m 
	        else Result [mkDiag Error 
			       ("conflict: " ++ showPretty a "") id1] $ Just m
	    String_anno id1 id2 _ ->
	        let c = StringCons id1
                    oc = Map.findWithDefault c id2 m
	            on = Map.findWithDefault StringNull id1 m
	            in 
	        if oc == c && on == StringNull 
	        then return $ Map.insert id1 StringNull $ Map.insert id2 c m
	        else Result [ mkDiag Error 
			      ("conflict: " ++ showPretty a "") id1] $ Just m
	    Float_anno id1 id2 _ ->
	        let oc = Map.findWithDefault Fraction id1 m
	            on = Map.findWithDefault Floating id2 m
	            in 
	        if oc == Fraction && on == Floating 
	        then return $ Map.insert id2 Floating 
	                           $ Map.insert id1 Fraction m
	        else  Result [mkDiag Error 
			      ("conflict: " ++ showPretty a "") id1] $ Just m
	    List_anno id1 id2 id3 _ -> 
	        let c = ListCons id1 id2
	            n = ListNull id1
                    oc = Map.findWithDefault c id3 m
	            on = Map.findWithDefault n id2 m
	            in if c == oc && n == on 
	            then return $ Map.insert id2 n $ Map.insert id3 c m  
	            else  Result [mkDiag Error ("conflict: " 
						++ showPretty a "") id1] 
	                                 $ Just m
	    _ -> return m )

store_literal_annos :: LiteralAnnos -> [Annotation] -> Result LiteralAnnos
store_literal_annos la ans = 
    do n_string_lit <- setStringLit (string_lit la) ans
       n_list_lit <- setListLit (list_lit la) ans
       n_number_lit <- setNumberLit (number_lit la) ans
       n_float_lit <- setFloatLit (float_lit la) ans
       return la { string_lit = n_string_lit
		 , list_lit = n_list_lit
		 , number_lit = n_number_lit
		 , float_lit  = n_float_lit
		 }

showIdPair :: (Id, Id) -> ShowS
showIdPair (i1, i2) = showId i1 . showString "," . showId i2

setStringLit :: Maybe (Id,Id) -> [Annotation] -> Result (Maybe (Id,Id))
setStringLit = 
    foldM ( \ m a ->
            case a of 
            String_anno id1 id2 _ ->
	        let q = (id1, id2) in
                case m of 
                 Nothing -> return $ Just q
                 Just p -> 
                     if q == p 
	             then return m
                     else Result [mkDiag Error 
				 ("conflict %string " ++ showIdPair q
                                  " and " ++ showIdPair p "") id1] $ Just m
            _ -> return m )

setFloatLit :: Maybe (Id,Id) -> [Annotation] -> Result (Maybe (Id,Id))
setFloatLit = 
    foldM ( \ m a ->
	    case a of 
	    Float_anno id1 id2 _ ->
	        let q = (id1, id2) in
	        case m of 
                Nothing -> return $ Just q
                Just p -> 
                    if q == p 
	            then return $ m
                    else  Result [mkDiag Error 
				 ("conflict %floating  " ++ showIdPair q
                                  " and " ++ showIdPair p "") id1] $ Just m
            _ -> return m )

setNumberLit :: Maybe Id -> [Annotation] -> Result (Maybe Id)
setNumberLit =
    foldM ( \ m a -> 
	    case a of 
	    Number_anno id1 _ -> 
	        case m of 
	        Nothing -> return $ Just id1
	        Just id2 -> 
	            if id1 == id2 then return m
	            else Result [mkDiag Error 
				 ("conflict %number " ++ showId id1 " and " 
				  ++ showId id2 "") id1] $ Just m
	    _ -> return m )

setListLit :: Set.Set (Id,Id,Id) -> [Annotation] -> Result (Set.Set (Id,Id,Id))
setListLit = 
    foldM ( \ s a ->
            case a of 
            List_anno id1 id2 id3 _ ->
                    let p = (id1, id2, id3)
	                cs = Set.filter ((==) p) s in
                    if Set.isEmpty cs then return $ Set.insert p s 
                    else Result [mkDiag Error 
				 ("conflict" ++ showTriple p ++ 
                                  " and" ++ showTriple (Set.findMin cs)) id1] 
	                         $ Just s
            _ -> return s )
    where showTriple (i1, i2, i3) = " %list " ++ showId i1 "," 
                                ++ showId i2 "," ++ showId i3 "" 

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

