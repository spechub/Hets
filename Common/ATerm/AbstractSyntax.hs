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

module Common.ATerm.AbstractSyntax 
    (ATerm(..),
     ShATerm(..),
     ATermTable,
     emptyATermTable,
     addATerm,addATerm1,
     getATerm,getATermFull,
     getATermIndex,getTopIndex,
     getATermByIndex,getATermByIndex1,
     toATermTable
    )  
    where

import Data.FiniteMap
import GHC.Read
import GHC.Show
{-
import Text.ParserCombinators.ReadPrec
import qualified Text.Read.Lex as L
-}
data ATerm = AAppl String [ATerm] [ATerm]
           | AList [ATerm]        [ATerm]
           | AInt  Integer        [ATerm]
	     deriving (Read,Show,Eq,Ord)

data ShATerm = ShAAppl {-# UNPACK #-} !String {-# UNPACK #-} ![Int] ![Int]
	     | ShAList {-# UNPACK #-} ![Int]         ![Int]
	     | ShAInt  {-# UNPACK #-} !Integer       ![Int]  
	       deriving (Read,Show,Eq,Ord)

data ATermTable = ATT (FiniteMap ShATerm Int) (FiniteMap Int ShATerm) 
                      {-# UNPACK #-} !Int

{-instance Show ATermTable where
    showsPrec _ (ATT fm1 fm2 i) = 
	showString "ATT " . shows (fmToList fm1) . showChar ' ' . shows (fmToList fm2) . showChar ' ' . shows i

instance Read ATermTable where
    readPrec =
      parens (prec appPrec (
        do L.Ident "ATT" <- lexP
           x              <- step readPrec
           y              <- step readPrec
           z              <- step readPrec
           return (ATT (listToFM x) (listToFM y) z)))
-}
emptyATermTable :: ATermTable
emptyATermTable =  ATT emptyFM emptyFM 0

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t tbl = 
  if ind == -1 then addATerm' tbl else (tbl,ind)
    where
    ind = getATermIndex t tbl 
    addATerm' (ATT a_iFM i_aFM i1) = 
	      if elemFM i1 i_aFM then
		 error err_destruct_up
	      else
	      case t of 
	      ShAAppl _ inds anns -> check inds anns
	      ShAList   inds anns -> check inds anns
	      ShAInt  _      anns -> check anns []
	where shorter = all (<i1)
	      check is as = 
		  if shorter is && shorter as
		  then (ATT (addToFM a_iFM t i1) 
			    (addToFM i_aFM i1 t) (i1+1),i1)
		  else error ("inconsistent addATerm call: " ++ show t)

addATerm1 :: ShATerm -> ATermTable -> ATermTable
addATerm1 t tbl = fst $ addATerm t tbl 


{-
hasATerm :: ShATerm -> ATermTable -> Bool
hasATerm t (a_iFM,_,_) = elemFM t a_iFM 
-}

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ i_aFM i) = 
    lookupWithDefaultFM i_aFM (ShAInt (-1) []) (i-1)

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ i) = i-1

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
    addToTable (AAppl s ats anns) att = 
	let (att1,ats')  = addToTableList ats att
	    (att2,anns') = addToTableList anns att1
	in addATerm (ShAAppl s ats' anns') att2
    addToTable (AList ats anns)   att = 
	let (att1,ats')  = addToTableList ats att
	    (att2,anns') = addToTableList anns att1
        in addATerm (ShAList ats' anns') att2
    addToTable (AInt i anns)      att = 
	let (att1,anns') = addToTableList anns att
        in addATerm (ShAInt i anns') att1
    addToTableList :: [ATerm] -> ATermTable -> (ATermTable,[Int])
    addToTableList []       att = (att,[])
    addToTableList (at1:ats) att = 
	let (att1,i)  = addToTable at1 att
            (att2,is) = addToTableList ats att1
        in (att2,i:is)

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (ATT a_iFM _ _) = lookupWithDefaultFM a_iFM (-1) t

getATermByIndex :: Int -> ATermTable -> (ATermTable,ShATerm)
getATermByIndex i (ATT a_iFM i_aFM _) = 
    (ATT a_iFM i_aFM (i+1),
     lookupWithDefaultFM i_aFM
         (error "getATermByIndex: No entry for ATerm in ATermTable") i) 

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i at = fst $ getATermByIndex i at

{-
--- some error messages --------

err_ref_index,err_destruct_up,err_wrong_store,
  err_wrong_sp_call,err_const_no_match,err_index_store :: String

err_ref_index   = "*** ATermTable: reference  points to reference"
-}
err_destruct_up :: String
err_destruct_up = "*** ATermTable: attempt to make a destructive update"
{-
err_wrong_store = 
    "*** ATermTable: only references are allowed as args or elems"

err_wrong_sp_call =
    "*** ATermTable: getATermSp: only one aterm nesting allowed"

err_const_no_match = "*** getATermSp: constructors don't match:"

err_index_store = "*** addATermSp: attempt to add an AIndex"
-}