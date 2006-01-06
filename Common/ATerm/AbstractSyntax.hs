{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(imports System.Mem.StableName)

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
     Key(..), newATermTable, getKey, setKey, mkKey,
     getATermByIndex1, str2Char, integer2Int
    ) where

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Map as DMap
import qualified Common.Lib.Map as HTab
import Common.DynamicUtils
import Data.Array
import System.Mem.StableName
import GHC.Prim
import qualified Data.List as List

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

data EqKey = EqKey !(StableName ()) !TypeRep deriving Eq

data Key = Key !Int !String !EqKey

mkKey :: Typeable a => a -> IO Key
mkKey t = do
    s <- makeStableName t
    let ty = typeOf t
    return $ Key (hashStableName s) (show ty) $ EqKey (unsafeCoerce# s) ty

data ATermTable = ATT
    !(HTab.Map Int (Map.Map String [(EqKey, Int)]))
    !(Map.Map ShATerm Int) !IntMap !Int
    !(Map.Map (Int, String) Dynamic)

toReadonlyATT :: ATermTable -> ATermTable
toReadonlyATT (ATT h s t i dM) = ATT h s
    (case t of
     Updateable m -> Readonly $ listArray (0, i) $ DMap.elems m
     _ -> t ) i dM

emptyATermTable :: ATermTable
emptyATermTable = ATT HTab.empty Map.empty empty (-1) Map.empty

newATermTable :: IO ATermTable
newATermTable = return $ emptyATermTable

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable,Int)
addATermNoFullSharing t (ATT h a_iDFM i_aDFM i1 dM) = let j = i1 + 1 in
    (ATT h (Map.insert t j a_iDFM) (insert j t i_aDFM) j dM, j)

addATerm :: ShATerm -> ATermTable -> (ATermTable,Int)
addATerm t at@(ATT _ a_iDFM _ _ _) =
  case Map.lookup t a_iDFM of
    Nothing -> addATermNoFullSharing t at
    Just i -> (at, i)

setKey :: Key -> Int -> ATermTable -> IO (ATermTable, Int)
setKey k i (ATT t s l m d) = return (ATT (setHKey k i t) s l m d, i)

setHKey :: Key -> Int -> (HTab.Map Int (Map.Map String [(EqKey, Int)]))
          -> (HTab.Map Int (Map.Map String [(EqKey, Int)]))
setHKey (Key h st k) i t = case HTab.lookup h t of
    Nothing -> HTab.insert h (Map.singleton st [(k, i)]) t
    Just m  -> case Map.lookup st m of
        Nothing -> HTab.insert h (Map.insert st [(k, i)] m) t
        Just l -> HTab.insert h (Map.insert st ((k, i) : l) m) t

getKey :: Key -> ATermTable -> IO (Maybe Int)
getKey (Key h st k) (ATT t _ _ _ _) = return $ case HTab.lookup h t of
    Nothing -> Nothing
    Just m -> case Map.lookup st m of
        Nothing -> Nothing
        Just l -> List.lookup k l

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ _ i_aFM i _) = find i i_aFM

getShATerm :: Int -> ATermTable -> ShATerm
getShATerm i (ATT _ _ i_aFM _ _) = find i i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ _ i _) = i

getATermIndex :: ShATerm -> ATermTable -> Int
getATermIndex t (ATT _ a_iDFM _ _ _) = Map.findWithDefault (-1) t a_iDFM

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT h a_iDFM i_aDFM _ dM) = ATT h a_iDFM i_aDFM i dM

getATerm' :: Int -> String -> ATermTable -> Maybe Dynamic
getATerm' i str (ATT _ _ _ _ dM) = Map.lookup (i, str) dM

setATerm' :: Int -> String -> Dynamic -> ATermTable -> ATermTable
setATerm' i str d (ATT h a_iDFM i_aDFM m dM) =
    ATT h a_iDFM i_aDFM m $ Map.insert (i, str) d dM

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
