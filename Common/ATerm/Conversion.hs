{- |
Module      :  $Header$
Description :  the class ShATermConvertible and basic instances
Copyright   :  (c) Klaus Luettich, C. Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(imports ATerm.AbstractSyntax)

the class 'ShATermConvertible' depending on the class 'Typeable' for
converting datatypes to and from 'ShATerm's in 'ATermTable's, plus a
couple of basic instances and utilities
-}

module Common.ATerm.Conversion where

import Common.ATerm.AbstractSyntax
import qualified Data.Map as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.Typeable
import Data.List (mapAccumL)
import Data.Ratio
import Control.Monad

class Typeable t => ShATermConvertible t where
    -- functions for conversion to an ATermTable
    toShATermAux    :: ATermTable -> t -> IO (ATermTable, Int)
    toShATermList'  :: ATermTable -> [t] -> IO (ATermTable, Int)
    fromShATermAux  :: Int -> ATermTable -> (ATermTable, t)
    fromShATermList' :: Int -> ATermTable -> (ATermTable, [t])

    -- default functions ignore the Annotation part
    toShATermList' att ts = do
           (att2, inds) <- foldM (\ (att0, l) t -> do
                    (att1, i) <- toShATerm' att0 t
                    return (att1, i : l)) (att, []) ts
           return $ addATerm (ShAList (reverse inds) []) att2

    fromShATermList' ix att0 =
        case getShATerm ix att0 of
            ShAList ats _ ->
                mapAccumL (flip fromShATerm') att0 ats
            u -> fromShATermError "[]" u

toShATerm' :: ShATermConvertible t => ATermTable -> t -> IO (ATermTable, Int)
toShATerm' att t = do
       k <- mkKey t
       m <- getKey k att
       case m of
         Nothing -> do
           (att1, i) <- toShATermAux att t
           setKey k i att1
         Just i -> return (att, i)

fromShATerm' :: ShATermConvertible t => Int -> ATermTable -> (ATermTable, t)
fromShATerm' i att = case getATerm' i att of
        Just d -> (att, d)
        _ -> case fromShATermAux i att of
               (attN, t) -> (setATerm' i t attN, t)

fromShATermError :: String -> ShATerm -> a
fromShATermError t u =
  error $ "Cannot convert ShATerm to " ++ t ++ ": !" ++ show u

-- some instances -----------------------------------------------
instance ShATermConvertible Bool where
    toShATermAux att b = return
      $ addATerm (ShAAppl (if b then "T" else "F") [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "T" [] _ -> (att0, True)
            ShAAppl "F" [] _ -> (att0, False)
            u -> fromShATermError "Prelude.Bool" u

instance ShATermConvertible Integer where
    toShATermAux att x = return $ addATerm (ShAInt x []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAInt x _ -> (att0, x)
            u -> fromShATermError "Prelude.Integer" u

instance ShATermConvertible Int where
    toShATermAux att = toShATermAux att . toInteger
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAInt x _ -> (att0, integer2Int x)
            u -> fromShATermError "Prelude.Int" u

instance (ShATermConvertible a, Integral a)
    => ShATermConvertible (Ratio a) where
    toShATermAux att0 i = let (i1, i2) = (numerator i, denominator i) in do
       (att1,i1') <- toShATerm' att0 i1
       (att2,i2') <- toShATerm' att1 i2
       return $ addATerm (ShAAppl "Ratio" [i1',i2'] []) att2
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "Ratio" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, a' %  b') }}
            u -> fromShATermError "Prelude.Integral" u

instance ShATermConvertible Char where
    toShATermAux att c = return $ addATerm (ShAAppl (show [c]) [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl s [] _ -> (att0, str2Char s)
            u -> fromShATermError "Prelude.Char" u
    toShATermList' att s = return $ addATerm (ShAAppl (show s) [] []) att
    fromShATermList' ix att0 = case getShATerm ix att0 of
            ShAAppl s [] _ -> (att0, read s)
            u -> fromShATermError "Prelude.String" u

instance ShATermConvertible () where
    toShATermAux att _ = return $ addATerm (ShAAppl "U" [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "U" [] _ -> (att0, ())
            u -> fromShATermError "()" u

instance (ShATermConvertible a) => ShATermConvertible (Maybe a) where
    toShATermAux att mb = case mb of
        Nothing -> return $ addATerm (ShAAppl "N" [] []) att
        Just x -> do
          (att1, x') <- toShATerm' att x
          return $ addATerm (ShAAppl "J" [x'] []) att1
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "N" [] _ -> (att0, Nothing)
            ShAAppl "J" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Just a') }
            u -> fromShATermError "Prelude.Maybe" u

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (Either a b) where
    toShATermAux att0 (Left aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Left" [ aa' ] []) att1
    toShATermAux att0 (Right aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Right" [ aa' ] []) att1
    fromShATermAux ix att = case getShATerm ix att of
            ShAAppl "Left" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Left aa') }
            ShAAppl "Right" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Right aa') }
            u -> fromShATermError "Either" u

instance ShATermConvertible a => ShATermConvertible [a] where
    toShATermAux = toShATermList'
    fromShATermAux = fromShATermList'

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (a, b) where
    toShATermAux att0 (x,y) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      return $ addATerm (ShAAppl "" [x',y'] []) att2
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "" [a,b] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    (att2, (a', b'))}}
            u -> fromShATermError "(,)" u

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c)
    => ShATermConvertible (a, b, c) where
    toShATermAux att0 (x,y,z) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      (att3, z') <- toShATerm' att2 z
      return $ addATerm (ShAAppl "" [x',y',z'] []) att3
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "" [a,b,c] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    (att3, (a', b', c'))}}}
            u -> fromShATermError "(,,)" u

instance (ShATermConvertible a, ShATermConvertible b, ShATermConvertible c,
          ShATermConvertible d) => ShATermConvertible (a, b, c, d) where
  toShATermAux att0 (x,y,z,w) = do
      (att1, x') <- toShATerm' att0 x
      (att2, y') <- toShATerm' att1 y
      (att3, z') <- toShATerm' att2 z
      (att4, w') <- toShATerm' att3 w
      return $ addATerm (ShAAppl "" [x',y',z',w'] []) att4
  fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "" [a,b,c,d] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    case fromShATerm' b att1 of { (att2, b') ->
                    case fromShATerm' c att2 of { (att3, c') ->
                    case fromShATerm' d att3 of { (att4, d') ->
                    (att4, (a', b', c', d'))}}}}
            u -> fromShATermError "(,,,)" u

instance (Ord a, ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (Map.Map a b) where
    toShATermAux att fm = do
      (att1, i) <- toShATerm' att $ Map.toList fm
      return $ addATerm (ShAAppl "Map" [i] []) att1
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "Map" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Map.fromDistinctAscList a') }
            u -> fromShATermError "Map.Map" u

instance ShATermConvertible a => ShATermConvertible (IntMap.IntMap a) where
  toShATermAux att fm = do
      (att1, i) <- toShATerm' att $ IntMap.toList fm
      return $ addATerm (ShAAppl "IntMap" [i] []) att1
  fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "IntMap" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, IntMap.fromDistinctAscList a') }
            u -> fromShATermError "IntMap.IntMap" u

instance (Ord a, ShATermConvertible a) => ShATermConvertible (Set.Set a) where
    toShATermAux att set = do
      (att1, i) <-  toShATerm' att $ Set.toList set
      return $ addATerm (ShAAppl "Set" [i] []) att1
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "Set" [a] _ ->
                    case fromShATerm' a att0 of { (att1, a') ->
                    (att1, Set.fromDistinctAscList a') }
            u -> fromShATermError "Set.Set" u
