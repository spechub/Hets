{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

-}

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
     addATerm,addATermNoFullSharing,
     getATerm,getATermFull,
     getATermIndex,getTopIndex,
     getATermByIndex1,
     toATermTable
    )
    where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Map as DMap
-- import UnsafeCoerce(unsafePtrEq)

data ATerm = AAppl String [ATerm] [ATerm]
           | AList [ATerm]        [ATerm]
           | AInt  Integer        [ATerm]
             deriving (Eq,Ord)

data ShATerm = ShAAppl String [Int] [Int]
             | ShAList [Int]        [Int]
             | ShAInt  Integer      [Int] 
--               deriving (Eq,Ord)

compareShATerm :: ShATerm -> ShATerm -> Ordering
compareShATerm a b = -- if unsafePtrEq a b then EQ else 
    case (a, b) of
    (ShAAppl s1 i1 j1, ShAAppl s2 i2 j2) -> compare (s1, i1, j1) (s2, i2, j2)
    (ShAAppl _ _ _, _) -> LT
    (ShAList i1 j1, ShAList i2 j2) -> compare (i1, j1) (i2, j2)
    (ShAList _ _, ShAInt _ _) -> LT
    (ShAInt i1 j1, ShAInt i2 j2) -> compare (i1, j1) (i2, j2)
    _ -> GT

instance Eq ShATerm where
  a == b = compareShATerm a b == EQ

instance Ord ShATerm where
  compare a b = compareShATerm a b

data ATermTable = ATT !(Map.Map ShATerm Int) !(DMap.Map Int ShATerm) Int

emptyATermTable :: ATermTable
emptyATermTable =  ATT Map.empty DMap.empty (-1)

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable,Int)
addATermNoFullSharing t (ATT a_iDFM i_aDFM i1) = let j = i1 + 1 in
    (ATT (Map.insert t j a_iDFM) (DMap.insert j t i_aDFM) j, j)

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t at@(ATT a_iDFM _ _) = 
  case Map.lookup t a_iDFM of
    Nothing -> addATermNoFullSharing t at
    Just i -> (at, i)  

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ i_aFM i) = 
    DMap.findWithDefault (ShAInt (-1) []) i i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ i) = i

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

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT a_iDFM i_aDFM _) = ATT a_iDFM i_aDFM i
