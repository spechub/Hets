module CASL.StaticSortAna where

import CASL.Sign

ana_SORT_ITEM :: LocalEnv -> Posed (Annoted SORT_ITEM) 
	      -> Result LocalEnv

ana_SORT_ITEM env paItem = 
    case item $ posedItem paItem of
    Sort_decl s:ss ps -> 
	let l = Posed s (extPos paItem) :
		zipWith ( \ so p -> Posed so $ ExtPos Comma p)
		ss (ps ++ repeat nullPos) :: [Posed SortId]
	    in do al <- mapM (ana_single_SORT env emptySortRels Nothing) l
		  mapM update_ann_SORT_ITEM env $  
		       map (\ a -> mapAnnoted (const a) $ 
			    posedItem paItem) al
		  
ana_single_SORT :: LocalEnv -> SortRels -> Maybe SortDefn 
		-> Posed SortId -> Result SortItem

update_ann_SORT_ITEM :: LocalEnv -> Annoted SortItem
		      -> Result LocalEnv

		


