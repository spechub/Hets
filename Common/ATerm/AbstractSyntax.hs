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
     addATerm,addATerm1,addATermNoFullSharing,
     getATerm,getATermFull,
     getATermIndex,getTopIndex,
     getATermByIndex,getATermByIndex1,
     toATermTable,getReferencingATerms
    )  
    where

import qualified Common.Lib.Map as Map
import List
import Control.Exception (assert)

data ATerm = AAppl String [ATerm] [ATerm]
           | AList [ATerm]        [ATerm]
           | AInt  Integer        [ATerm]
	     deriving (Read,Show,Eq,Ord)

data ShATerm = ShAAppl {-# UNPACK #-} !String {-# UNPACK #-} ![Int] ![Int]
	     | ShAList {-# UNPACK #-} ![Int]         ![Int]
	     | ShAInt  {-# UNPACK #-} !Integer       ![Int]  
	       deriving (Read,Show,Eq,Ord)

data ATermTable = ATT (Map.Map ShATerm Int) (Map.Map Int ShATerm) 
                      {-# UNPACK #-} !Int

data ShChoice = Full | NoFull 

emptyATermTable :: ATermTable
emptyATermTable =  ATT Map.empty Map.empty 0

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable,Int)
addATermNoFullSharing = addATerm' NoFull

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm = addATerm' Full

addATerm' :: ShChoice -> ShATerm -> ATermTable -> (ATermTable,Int)
addATerm' cho t (ATT a_iDFM i_aDFM i1) = 
        -- asserts are only checked without optimization
        assert (not (Map.member i1 i_aDFM)) (
           assert (consistent)
	     (case cho of
	      Full -> insertFull
	      NoFull -> insertNoFull))
    where insertFull =
             (let (mayInd,dfm1) = {-# SCC "fm1_f" #-} 
                         Map.insertLookupWithKey (\_ _ y -> y)  
                             t i1 a_iDFM
	          -- here we get Just index, if there is already a
	          -- mapping of t to i1 otherwise we get Nothing and
	          -- the new relation is defined.
                  dfm2 = {-# SCC "fm2_f" #-} 
	                 maybe (Map.insert i1 t i_aDFM) 
	                       -- mapping not defined => set it
	                       (\_->i_aDFM) 
	                       -- otherwise return unchanged map
                               mayInd
	          (newATT_ind,return_ind) = 
	             -- calculate new indices for ATT and the Term as well
	             -- Nothing means old ATT index i1 is now mapped to t
                     --   and new ATT index is (i1+1)
                     -- Just means leave ATT index i1 unchanged 
                     --   and t has already index old index
                     maybe (i1+1,i1) (\old_ind->(i1,old_ind)) mayInd
              in (ATT dfm1 dfm2 newATT_ind,return_ind))
          insertNoFull = 
             (let dfm1 = {-# SCC "fm1_nf" #-} 
                         Map.insertWithKey 
                             (\_ _ _ -> error ("destructive update with: "
                                                ++ show t))  
                             t i1 a_iDFM
                  dfm2 = {-# SCC "fm2_nf" #-} Map.insert i1 t i_aDFM
              in (ATT dfm1 dfm2 (i1+1),i1))

          shorter = all (<i1)
	  check is as = (shorter is && shorter as)
	  consistent = case t of 
                       ShAAppl  _ inds anns -> check inds anns
		       ShAList    inds anns -> check inds anns
		       ShAInt _        anns -> check anns []

addATerm1 :: ShATerm -> ATermTable -> ATermTable
addATerm1 t tbl = fst $ addATerm t tbl 

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ i_aFM i) = 
    Map.findWithDefault (ShAInt (-1) []) (i-1) i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ i) = i-1

getReferencingATerms :: ATermTable -> Int -> Int -> [[ShATerm]]
getReferencingATerms att@(ATT dfm _ _) depth i 
    | depth <= 0 = []
    | otherwise = 
	let ats = nub $ Map.keys $ Map.filterWithKey (\at _ -> case at of
                                  ShAAppl _ inds _ -> i `elem` inds
                                  _  -> False) dfm
            get (ShAAppl _ inds _) = 
                concatMap (getReferencingATerms att (depth-1)) inds
            get _ = 
                error ("something in getReferencingATerms went realy wrong")
        in [ats] ++ if depth - 1  > 1 then concatMap get ats else [[]]

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
getATermIndex t (ATT a_iDFM _ _) = Map.findWithDefault (-1) t a_iDFM

getATermByIndex :: Int -> ATermTable -> (ATermTable,ShATerm)
getATermByIndex i (ATT a_iDFM i_aDFM _) = 
    (ATT a_iDFM i_aDFM (i+1),
     Map.findWithDefault
         (error "getATermByIndex: No entry for ATerm in ATermTable") i
         i_aDFM) 

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