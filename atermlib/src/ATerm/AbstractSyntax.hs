{-# LANGUAGE MagicHash #-}
{- |
Module      :  $Header$
Description :  the abstract syntax of shared ATerms and their lookup table
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2002-2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(imports System.Mem.StableName and GHC.Prim)

the data types 'ShATerm' and 'ATermTable' plus some utilities
-}

module ATerm.AbstractSyntax
    (ShATerm(..),
     ATermTable,
     emptyATermTable,
     addATerm,
     getATerm, toReadonlyATT,
     getTopIndex,
     getATerm', setATerm', getShATerm,
     Key, getKey, setKey, mkKey,
     getATermByIndex1, str2Char, integer2Int
    ) where

import qualified Data.Map as Map
import qualified Data.Map as IntMap
import Data.Dynamic
import Data.Array
import System.Mem.StableName
import GHC.Prim
import qualified Data.List as List
import Data.Maybe

data ShATerm =
    ShAAppl String [Int] [Int]
  | ShAList [Int]        [Int]
  | ShAInt  Integer      [Int]
    deriving (Show, Eq, Ord)

data IntMap =
    Updateable !(IntMap.Map Int ShATerm)
  | Readonly !(Array Int ShATerm)

empty :: IntMap
empty = Updateable IntMap.empty

insert :: Int -> ShATerm -> IntMap -> IntMap
insert i s t = case t of
    Updateable m -> Updateable $ IntMap.insert i s m
    _ -> error "ATerm.insert"

find :: Int -> IntMap -> ShATerm
find i t = case t of
    Updateable m -> IntMap.findWithDefault (ShAInt (-1) []) i m
    Readonly a -> a ! i

data EqKey = EqKey (StableName ()) TypeRep deriving Eq

data Key = Key Int EqKey

mkKey :: Typeable a => a -> IO Key
mkKey t = do
    s <- makeStableName t
    return $ Key (hashStableName s) $ EqKey (unsafeCoerce# s) $ typeOf t

data ATermTable = ATT
    (IntMap.Map Int [(EqKey, Int)])
    !(Map.Map ShATerm Int) !IntMap Int
    !(IntMap.Map Int [Dynamic])

toReadonlyATT :: ATermTable -> ATermTable
toReadonlyATT (ATT h s t i dM) = ATT h s
    (case t of
     Updateable m -> Readonly $ listArray (0, i) $ IntMap.elems m
     _ -> t ) i dM

emptyATermTable :: ATermTable
emptyATermTable = ATT IntMap.empty Map.empty empty (-1) IntMap.empty

addATermNoFullSharing :: ShATerm -> ATermTable -> (ATermTable, Int)
addATermNoFullSharing t (ATT h a_iDFM i_aDFM i1 dM) = let j = i1 + 1 in
    (ATT h (Map.insert t j a_iDFM) (insert j t i_aDFM) j dM, j)

addATerm :: ShATerm -> ATermTable -> (ATermTable, Int)
addATerm t at@(ATT _ a_iDFM _ _ _) =
  case Map.lookup t a_iDFM of
    Nothing -> addATermNoFullSharing t at
    Just i -> (at, i)

setKey :: Key -> Int -> ATermTable -> IO (ATermTable, Int)
setKey (Key h e) i (ATT t s l m d) =
    return (ATT (IntMap.insertWith (++) h [(e, i)] t) s l m d, i)

getKey :: Key -> ATermTable -> IO (Maybe Int)
getKey (Key h k) (ATT t _ _ _ _) =
    return $ List.lookup k $ IntMap.findWithDefault [] h t

getATerm :: ATermTable -> ShATerm
getATerm (ATT _ _ i_aFM i _) = find i i_aFM

getShATerm :: Int -> ATermTable -> ShATerm
getShATerm i (ATT _ _ i_aFM _ _) = find i i_aFM

getTopIndex :: ATermTable -> Int
getTopIndex (ATT _ _ _ i _) = i

getATermByIndex1 :: Int -> ATermTable -> ATermTable
getATermByIndex1 i (ATT h a_iDFM i_aDFM _ dM) = ATT h a_iDFM i_aDFM i dM

getATerm' :: Typeable t => Int -> ATermTable -> Maybe t
getATerm' i (ATT _ _ _ _ dM) =
    listToMaybe $ mapMaybe fromDynamic $ IntMap.findWithDefault [] i dM

setATerm' :: Typeable t => Int -> t -> ATermTable -> ATermTable
setATerm' i t (ATT h a_iDFM i_aDFM m dM) =
    ATT h a_iDFM i_aDFM m $ IntMap.insertWith (++) i [toDyn t] dM

-- | conversion of a string in double quotes to a character
str2Char :: String -> Char
str2Char str = case str of
    '\"' : sr@(_ : _) -> conv' (init sr) where
      conv' r = case r of
        [x] -> x
        ['\\', x] -> case x of
          'n'  -> '\n'
          't'  -> '\t'
          'r'  -> '\r'
          '\"' -> '\"'
          _ -> error "ATerm.AbstractSyntax: unexpected escape sequence"
        _ -> error "ATerm.AbstractSyntax: String not convertible to Char"
    _ -> error "ATerm.AbstractSyntax: String doesn't begin with '\"'"

-- | conversion of an unlimited integer to a machine int
integer2Int :: Integer -> Int
integer2Int x = if toInteger ((fromInteger :: Integer -> Int) x) == x
    then fromInteger x else
    error $ "ATerm.AbstractSyntax: Integer to big for Int: " ++ show x
