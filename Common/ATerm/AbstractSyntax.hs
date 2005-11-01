{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

-}

module Common.ATerm.AbstractSyntax 
    (ShATerm(..),
     ATermTable,
     emptyATermTable,
     addATerm,addATermNoFullSharing,
     getATerm, toReadonlyATT,
     getATermIndex,getTopIndex,
     getATermByIndex1) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Map as DMap
import Data.Array

data ShATerm = ShAAppl String [Int] [Int]
             | ShAList [Int]        [Int]
             | ShAInt  Integer      [Int] 
               deriving (Eq,Ord)

data IntMap = Updateable !(DMap.Map Int ShATerm)
            | Readonly !(Array Int ShATerm)

empty :: IntMap
empty = Updateable $ DMap.empty

insert :: Int -> ShATerm -> IntMap -> IntMap
insert i s t = case t of 
    Updateable m -> Updateable $ DMap.insert i s m
    _ -> error "ATerm.insert"

find :: Int -> IntMap -> ShATerm
find i t = case t of 
    Updateable m -> DMap.findWithDefault (ShAInt (-1) []) i m
    Readonly a -> a ! i

data ATermTable = ATT !(Map.Map ShATerm Int) !IntMap !Int

toReadonlyATT :: ATermTable -> ATermTable
toReadonlyATT (ATT s t i) = ATT s 
    (case t of 
     Updateable m -> Readonly $ array (0, i) $ DMap.toList m 
     _ -> t ) i 

emptyATermTable :: ATermTable
emptyATermTable =  ATT Map.empty empty (-1)

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable,Int)
addATermNoFullSharing t (ATT a_iDFM i_aDFM i1) = let j = i1 + 1 in
    (ATT (Map.insert t j a_iDFM) (insert j t i_aDFM) j, j)

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t at@(ATT a_iDFM _ _) = 
  case Map.lookup t a_iDFM of
    Nothing -> addATermNoFullSharing t at
    Just i -> (at, i)  

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ i_aFM i) = find i i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ i) = i

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (ATT a_iDFM _ _) = Map.findWithDefault (-1) t a_iDFM

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT a_iDFM i_aDFM _) = ATT a_iDFM i_aDFM i
