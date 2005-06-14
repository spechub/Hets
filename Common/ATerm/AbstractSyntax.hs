{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.AbstractSyntax 
    (ShATerm(..),
     ATermTable,
     emptyATermTable,
     addATerm,addATermNoFullSharing,
     getATerm,
     getATermIndex,getTopIndex,
     getATermByIndex1) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Map as DMap

data ShATerm = ShAAppl String [Int] [Int]
             | ShAList [Int]        [Int]
             | ShAInt  Integer      [Int] 
               deriving (Eq,Ord)

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

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (ATT a_iDFM _ _) = Map.findWithDefault (-1) t a_iDFM

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT a_iDFM i_aDFM _) = ATT a_iDFM i_aDFM i
