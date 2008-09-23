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
fromShATermError t u = error $ "Cannot convert ShATerm to "
                       ++ t ++ ": " ++ err u
    where err te = case te of
                  ShAAppl s l _ -> "!ShAAppl "++ s
                                   ++ " (" ++ show (length l) ++ ")"
                  ShAList l _   -> "!ShAList"
                                   ++ " (" ++ show (length l) ++ ")"
                  ShAInt i _    -> "!ShAInt " ++ show i

-- some instances -----------------------------------------------
instance ShATermConvertible Bool where
    toShATermAux att b = return $ case b of
                       True  -> addATerm (ShAAppl "T" [] []) att
                       False -> addATerm (ShAAppl "F" [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "T" [] _ -> (att0, True)
            ShAAppl "F" [] _ -> (att0, False)
            u -> fromShATermError "Prelude.Bool" u

instance ShATermConvertible Integer where
    toShATermAux att x = return $ addATerm (ShAInt x []) att
    fromShATermAux ix att0 =
         case getShATerm ix att0 of
            ShAInt x _ -> (att0, x)
            u -> fromShATermError "Prelude.Integer" u

instance ShATermConvertible Int where
    toShATermAux att x = toShATermAux att (toInteger x)
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAInt x _ -> (att0, integer2Int x)
            u -> fromShATermError "Prelude.Int" u

instance (ShATermConvertible a, Integral a)
    => ShATermConvertible (Ratio a) where
    toShATermAux att0 i = let (i1, i2) = (numerator i, denominator i) in do
       (att1,i1') <- toShATerm' att0 i1
       (att2,i2') <- toShATerm' att1 i2
       return $ addATerm (ShAAppl "Ratio" [i1',i2'] []) att2
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
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
    fromShATermList' ix att0 =
        case getShATerm ix att0 of
            ShAAppl s [] _ -> (att0, read s)
            u -> fromShATermError "Prelude.String" u

instance ShATermConvertible () where
    toShATermAux att _ = return $ addATerm (ShAAppl "U" [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "U" [] _ -> (att0, ())
            u -> fromShATermError "()" u
