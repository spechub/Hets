{-# OPTIONS -fscoped-type-variables #-}
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, C.Maeder, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable(imports AbstractSyntax)

the class ShATermConvertible and a few instances
-}

module Common.ATerm.Conversion where

import Common.ATerm.AbstractSyntax
import Common.DynamicUtils
import Data.List (mapAccumL)
import Data.Ratio
import Control.Monad

class Typeable t => ShATermConvertible t where
    -- functions for conversion to an ATermTable
    toShATerm       :: ATermTable -> t -> (ATermTable, Int)
    toShATermList   :: ATermTable -> [t] -> (ATermTable, Int)
    toShATerm'      :: ATermTable -> t -> IO (ATermTable, Int)
    toShATermAux    :: ATermTable -> t -> IO (ATermTable, Int)
    toShATermList'  :: ATermTable -> [t] -> IO (ATermTable, Int)
    fromShATermAux  :: Int -> ATermTable -> (ATermTable, t)
    fromShATermList' :: Int -> ATermTable -> (ATermTable, [t])

    toShATerm' att t = do
       k <- mkKey t
       m <- getKey k att
       case m of
         Nothing -> do
           (att1, i) <- toShATermAux att t
           setKey k i att1
         Just i -> return (att, i)
    toShATermAux att = return . toShATerm att
    toShATermList' att ts = do
       k <- mkKey ts
       m <- getKey k att
       case m of
         Nothing -> do
           (att2, inds) <- foldM (\ (att0, l) t -> do
                    (att1, i) <- toShATerm' att0 t
                    return (att1, i : l)) (att, []) ts
           case addATerm (ShAList (reverse inds) []) att2 of
             (att3, i) -> setKey k i att3
         Just i -> return (att, i)
    -- default functions ignore the Annotation part
    toShATermList att0 ts = case mapAccumL toShATerm att0 ts of
                          (att1, inds) -> addATerm (ShAList inds []) att1
    fromShATermList' ix att0 =
        case getShATerm ix att0 of
            ShAList ats _ ->
                mapAccumL (flip fromShATerm') att0 ats
            u -> fromShATermError "[]" u

fromShATerm :: ShATermConvertible t => ATermTable -> t
fromShATerm att = snd $ fromShATerm' (getTopIndex att) att

fromShATerm' :: ShATermConvertible t => Int -> ATermTable -> (ATermTable, t)
fromShATerm' i att :: (ATermTable, t) =
    let ty = show $ typeOf (undefined :: t) in
      case getATerm' i ty att of
        Just d -> (att, fromDyn d $ error $ "fromShATerm': generic " ++ ty)
        _ -> case fromShATermAux i att of
               (attN, t) -> (setATerm' i ty (toDyn t) attN, t)

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
    toShATerm att b = case b of
                       True  -> addATerm (ShAAppl "T" [] []) att
                       False -> addATerm (ShAAppl "F" [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "T" [] _ -> (att0, True)
            ShAAppl "F" [] _ -> (att0, False)
            u -> fromShATermError "Prelude.Bool" u

instance ShATermConvertible Integer where
    toShATerm att x = addATerm (ShAInt x []) att
    fromShATermAux ix att0 =
         case getShATerm ix att0 of
            ShAInt x _ -> (att0, x)
            u -> fromShATermError "Prelude.Integer" u

instance ShATermConvertible Int where
    toShATerm att x = toShATerm att (toInteger x)
    toShATermAux att x = toShATerm' att (toInteger x)
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAInt x _ -> (att0, integer2Int x)
            u -> fromShATermError "Prelude.Int" u

instance (ShATermConvertible a, Integral a)
    => ShATermConvertible (Ratio a) where
    toShATerm att0 i = let (i1, i2) = (numerator i, denominator i) in
       case toShATerm att0 i1 of
       (att1,i1') ->
          case toShATerm att1 i2 of
          (att2,i2') ->
              addATerm (ShAAppl "Ratio" [i1',i2'] []) att2
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
    toShATerm att c = addATerm (ShAAppl (show [c]) [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl s [] _ -> (att0, str2Char s)
            u -> fromShATermError "Prelude.Char" u
    toShATermList' att s = do
       k <- mkKey s
       m <- getKey k att
       case m of
         Nothing -> case toShATermList att s of
             (att3, i) -> setKey k i att3
         Just i -> return (att, i)
    toShATermList att s = addATerm (ShAAppl (show s) [] []) att
    fromShATermList' ix att0 =
        case getShATerm ix att0 of
            ShAAppl s [] _ -> (att0, read s)
            u -> fromShATermError "Prelude.String" u

instance ShATermConvertible () where
    toShATerm att _ = addATerm (ShAAppl "U" [] []) att
    fromShATermAux ix att0 = case getShATerm ix att0 of
            ShAAppl "U" [] _ -> (att0, ())
            u -> fromShATermError "()" u
