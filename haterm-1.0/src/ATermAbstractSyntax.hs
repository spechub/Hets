module ATermAbstractSyntax where

import FiniteMap

data ATerm = AAppl String [ATerm]
           | AList [ATerm]
           | AInt Integer
	   | AIndex Int    -- Used for maximal sharing
             deriving (Read,Show,Eq,Ord)


type ATermTable = (FiniteMap ATerm Int,FiniteMap Int ATerm, Int)

emptyATermTable :: ATermTable
emptyATermTable =  (emptyFM,emptyFM,0)

addATerm :: ATerm -> ATermTable -> (ATermTable,ATerm)
addATerm t tbl = 
    if hasATerm t tbl then 
       (tbl,AIndex (getATermIndex t tbl))
    else
       addATerm' t tbl
    where addATerm' t (a_iFM,i_aFM,i) = 
	      if elemFM i i_aFM then
		 error err_destruct_up
	      else
	         ((addToFM a_iFM t i,addToFM i_aFM i t,i+1), AIndex i)

addATerm1 :: ATerm -> ATermTable -> ATermTable
addATerm1 t tbl = let (tbl',_) = addATerm t tbl in tbl'

addATermSp :: ATerm -> ATermTable -> (ATermTable,ATerm)
addATermSp t tbl = 
    case t of 
    (AAppl s [])   -> addATerm t tbl
    (AAppl s [t']) -> let (tbl',t'') = case t' of 
				       (AIndex _) -> (tbl,t')
				       otherwise  -> addATermSp t' tbl
		      in addATerm (AAppl s [t'']) tbl'
    (AAppl s ts)   -> addATerm t tbl
    (AIndex _)     -> error err_index_store
    otherwise      -> addATerm t tbl

addATermSp1 :: ATerm -> ATermTable -> ATermTable
addATermSp1 t tbl = let (tbl',_) = addATermSp t tbl in tbl'

hasATerm :: ATerm -> ATermTable -> Bool
hasATerm t (a_iFM,_,_) = elemFM t a_iFM 

getATerm :: ATermTable -> ATerm
getATerm (_,i_aFM,i) = lookupWithDefaultFM i_aFM (AIndex (-1)) (i-1)

getATermFull :: ATermTable -> ATerm
getATermFull at = 
    let t = getATerm at
    in case t of
       (AInt _)    -> t
       (AIndex _)  -> error err_wrong_store
       (AList l)   -> AList (map conv l)
       (AAppl c l) -> AAppl c (map conv l)
    where conv t = getATermFull (getATermByIndexSp1 t at)

getATermSp :: ATermTable -> ATerm -> Maybe ATerm
getATermSp at (AAppl s [])   = let aterm@(AAppl s' _) = getATerm at
			       in if s == s' then Just aterm
				  else Nothing
getATermSp at (AAppl s [t']) = let (AAppl s' ts) = getATerm at
				   mat = case ts of
					 [t]  -> Just (getATermByIndexSp1 t at)
					 _    -> Nothing
			       in if s == s' then 
				    case mat of 
					   (Just at') -> 
					       case getATermSp at' t' of 
							(Just t'') -> 
							 Just (AAppl s' [t''])
							Nothing   -> Nothing
					   Nothing    -> Nothing
				  else
				    Nothing
getATermSp at _              = error err_wrong_sp_call

getATermIndex :: ATerm -> ATermTable -> Int
getATermIndex t (a_iFM,_,_) = lookupWithDefaultFM a_iFM (-1) t

getATermByIndex :: Int -> ATermTable -> (ATermTable,ATerm)
getATermByIndex i (a_iFM,i_aFM,_) = 
    ((a_iFM,i_aFM,i+1),lookupWithDefaultFM i_aFM (AIndex (-1)) i)

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i at = let (at',_) = getATermByIndex i at in at'

getATermByIndexSp :: ATerm -> ATermTable -> (ATermTable,ATerm)
getATermByIndexSp t tbl = getATermByIndex (atermIndexToInt t) tbl

getATermByIndexSp1 :: ATerm -> ATermTable -> ATermTable
getATermByIndexSp1 t tbl = getATermByIndex1 (atermIndexToInt t) tbl

atermIndexToInt            :: ATerm -> Int
atermIndexToInt (AIndex i) = i
atermIndexToInt _          = error (err_wrong_store++
				    "\n*** atermIndexToInt: cannot convert non index")
--- some error messages --------
err_ref_index   = "*** ATermTable: reference  points to reference"

err_destruct_up = "*** ATermTable: attempt to make a destructive update"

err_wrong_store = 
    "*** ATermTable: only references are allowed as args or elems"

err_wrong_sp_call =
    "*** ATermTable: getATermSp: only one aterm nesting allowed"

err_const_no_match = "*** getATermSp: constructors don't match:"

err_index_store = "*** addATermSp: attempt to add an AIndex"



