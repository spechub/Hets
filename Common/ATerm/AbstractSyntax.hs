{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

data types and utilities for shared ATerms and the ATermTable
-}

module Common.ATerm.AbstractSyntax
    (ShATerm(..),
     ATermTable,
     emptyATermTable,
     addATerm,addATermNoFullSharing,
     getATerm, toReadonlyATT,
     getATermIndex,getTopIndex,
     getATerm', setATerm', getShATerm,
     getATermByIndex1, str2Char, integer2Int
    ) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Map as DMap
import Common.DynamicUtils
import Data.Array

data ShATerm = ShAAppl String [Int] [Int]
             | ShAList [Int]        [Int]
             | ShAInt  Integer      [Int]
               deriving (Eq, Ord)

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
                      (Map.Map (Int, String) Dynamic)

toReadonlyATT :: ATermTable -> ATermTable
toReadonlyATT (ATT s t i dM) = ATT s
    (case t of
     Updateable m -> Readonly $ listArray (0, i) $ DMap.elems m
     _ -> t ) i dM

emptyATermTable :: ATermTable
emptyATermTable =  ATT Map.empty empty (-1) Map.empty

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable,Int)
addATermNoFullSharing t (ATT a_iDFM i_aDFM i1 dM) = let j = i1 + 1 in
    (ATT (Map.insert t j a_iDFM) (insert j t i_aDFM) j dM, j)

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t at@(ATT a_iDFM _ _ _) =
  case Map.lookup t a_iDFM of
    Nothing -> addATermNoFullSharing t at
    Just i -> (at, i)

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ i_aFM i _) = find i i_aFM

getShATerm :: Int -> ATermTable -> ShATerm
getShATerm i (ATT _ i_aFM _ _) = find i i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ i _) = i

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (ATT a_iDFM _ _ _) = Map.findWithDefault (-1) t a_iDFM

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT a_iDFM i_aDFM _ dM) = ATT a_iDFM i_aDFM i dM

getATerm' :: Int -> String -> ATermTable -> Maybe Dynamic
getATerm' i str (ATT _ _ _ dM) = Map.lookup (i, str) dM

setATerm' :: Int -> String -> Dynamic -> ATermTable -> ATermTable
setATerm' i str d (ATT a_iDFM i_aDFM m dM) =
    ATT a_iDFM i_aDFM m $! Map.insert (i, str) d dM

-- | conversion of a string in double quotes to a character
str2Char :: String -> Char
str2Char ('\"' : sr) = conv' (init sr) where
                               conv' [x] = x
                               conv' ['\\', x] = case x of
                                   'n'  -> '\n'
                                   't'  -> '\t'
                                   'r'  -> '\r'
                                   '\"' -> '\"'
                                   _    -> error "strToChar"
                               conv' _ = error "String not convertible to char"
str2Char _         = error "String doesn't begin with '\"'"

-- | conversion of an unlimited integer to a machine int
integer2Int :: Integer -> Int
integer2Int x = if toInteger ((fromInteger :: Integer -> Int) x) == x
                  then fromInteger x
                  else error $ "Integer to big for Int: " ++ show x
