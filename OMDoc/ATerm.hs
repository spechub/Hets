{- |
Module      :  $Header$
Description :  Additional (manual) ATerm-Conversions for OMDoc
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Additional ATerm-Conversions for OMDoc.
-}
module OMDoc.ATerm where

import qualified Network.URI as URI

import Common.ATerm.Lib

import Data.Word

instance ShATermConvertible URI.URI where
  toShATermAux att0 u = do
    (att1, us) <- toShATerm' att0 ((URI.uriToString id u) "")
    return $ addATerm (ShAAppl "URI.URI" [us] []) att1
  fromShATermAux ix att0 =
    case getShATerm ix att0 of
      x@(ShAAppl "URI.URI" [us] _) ->
        case fromShATerm' us att0 of
          (att1, us') ->
            case URI.parseURIReference us' of
              Nothing ->
                fromShATermError "URI.URI" x
              Just uri ->
                (att1, uri)
      u -> fromShATermError "URI.URI" u


instance ShATermConvertible Float where
  toShATermAux att0 f = do
    (att1, fs) <- toShATerm' att0 (show f)
    return $ addATerm (ShAAppl "Float" [fs] []) att1
  fromShATermAux ix att0 =
    case getShATerm ix att0 of
      x@(ShAAppl "Float" [fs] _) ->
        case fromShATerm' fs att0 of
          (att1, fs') ->
            case readsPrec 0 fs' of
              [] ->
                fromShATermError "Float" x
              [(f, _)] ->
                (att1, f)
              _ ->
                fromShATermError "Float" x
      u -> fromShATermError "Float" u


instance ShATermConvertible Data.Word.Word8 where
  toShATermAux att0 w = toShATermAux att0 ((fromIntegral w)::Int)
  fromShATermAux ix att0 =
    case fromShATermAux ix att0 of
      (att1, i) ->
        (att1, fromIntegral (i :: Int))

instance (ShATermConvertible a, ShATermConvertible b) => ShATermConvertible (Either a b) where
  toShATermAux att0 (Left a) =
    do
     (att1, a') <- toShATerm' att0 a
     return $ addATerm (ShAAppl "Either.Left" [a'] []) att1
  toShATermAux att0 (Right b) =
    do
     (att1, b') <- toShATerm' att0 b
     return $ addATerm (ShAAppl "Either.Right" [b'] []) att1
  fromShATermAux ix att0 =
    case getShATerm ix att0 of
      (ShAAppl "Either.Left" [a] _) ->
        case fromShATerm' a att0 of
          (att1, a') ->
            (att1, Left a')
      (ShAAppl "Either.Right" [b] _) ->
        case fromShATerm' b att0 of
          (att1, b') ->
            (att1, Right b')
      u -> fromShATermError "Either" u
