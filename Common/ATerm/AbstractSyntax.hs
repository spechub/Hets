{- todo:
    * Datentyp auf Annotationen umstellen
      dazu einiges auskommentieren ..done
      Weiter mit 'writeATerm'  ..done
  
    * Zugriffsfunktionen für ATermTable auf Annotationen anpassen ..done

    * Neuen Datentyp für shared ATerms: ShATerm mit Annotationen
       (ungefähr so: data ShATerm = ShAAppl String [Int]) ..done

    * Umkehrfuntion zu getATermFull programmieren, Signatur und Name 
      siehe toATermTable

-}

module Common.ATerm.AbstractSyntax where

import Common.Lib.Map hiding (map)

data ATerm = AAppl String [ATerm] [ATerm]
           | AList [ATerm]        [ATerm]
           | AInt  Integer        [ATerm]
	     deriving (Read,Show,Eq,Ord)

data ShATerm = ShAAppl String [Int] [Int]
	     | ShAList [Int]        [Int]
	     | ShAInt  Integer      [Int]  
	       deriving (Read,Show,Eq,Ord)

type ATermTable = (Map ShATerm Int,Map Int ShATerm, Int)

emptyATermTable :: ATermTable
emptyATermTable =  (empty,empty,0)

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t tbl = 
{-   if hasATerm t tbl then 
       (tbl,getATermIndex t tbl)
    else
       addATerm' t tbl
-}
  case i of
    -1 -> addATerm' t tbl
    _ -> (tbl,i)
    where
    i = getATermIndex t tbl 
    addATerm' t (a_iFM,i_aFM,i) = 
	      if member i i_aFM then
		 error err_destruct_up
	      else
	         ((insert t i a_iFM,insert i t i_aFM,i+1),i)


addATerm1 :: ShATerm -> ATermTable -> ATermTable
addATerm1 t tbl = fst $ addATerm t tbl 


{-
hasATerm :: ShATerm -> ATermTable -> Bool
hasATerm t (a_iFM,_,_) = elemFM t a_iFM 
-}

getATerm :: ATermTable -> ShATerm
getATerm (_,i_aFM,i) = findWithDefault (ShAInt (-1) []) (i-1) i_aFM  



getATermFull :: ATermTable -> ATerm
getATermFull at = 
    let t = getATerm at
    in case t of
       (ShAInt i as)    -> AInt i (map conv as)
       (ShAList l as)   -> AList (map conv l) (map conv as)
       (ShAAppl c l as) -> AAppl c (map conv l) (map conv as)
    where conv t = getATermFull (getATermByIndex1 t at) 

toATermTable :: ATerm -> ATermTable
toATermTable at = fst $ addToTable at emptyATermTable
                  where
                  addToTable :: ATerm -> ATermTable -> (ATermTable,Int) 
                  addToTable (AAppl s ats anns) att = let (att1,ats')  = addToTableList ats att
							  (att2,anns') = addToTableList anns att1
						      in addATerm (ShAAppl s ats' anns') att2
                  addToTable (AList ats anns)   att = let (att1,ats')  = addToTableList ats att
							  (att2,anns') = addToTableList anns att1
                                                      in addATerm (ShAList ats' anns') att2
                  addToTable (AInt i anns)      att = let (att1,anns') = addToTableList anns att
                                                      in addATerm (ShAInt i anns') att1
                  addToTableList :: [ATerm] -> ATermTable -> (ATermTable,[Int])
		  addToTableList []       att = (att,[])
                  addToTableList (at:ats) att = let (att1,i)  = addToTable at att
                                                    (att2,is) = addToTableList ats att1
                                                in (att2,i:is)

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (a_iFM,_,_) = findWithDefault (-1) t a_iFM 

getATermByIndex :: Int -> ATermTable -> (ATermTable,ShATerm)
getATermByIndex i (a_iFM,i_aFM,_) = 
    ((a_iFM,i_aFM,i+1),findWithDefault (error "getATermByIndex: No entry for ATerm in ATermTable") i i_aFM) 

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i at = fst $ getATermByIndex i at


--- some error messages --------
err_ref_index   = "*** ATermTable: reference  points to reference"

err_destruct_up = "*** ATermTable: attempt to make a destructive update"

err_wrong_store = 
    "*** ATermTable: only references are allowed as args or elems"

err_wrong_sp_call =
    "*** ATermTable: getATermSp: only one aterm nesting allowed"

err_const_no_match = "*** getATermSp: constructors don't match:"

err_index_store = "*** addATermSp: attempt to add an AIndex"






































