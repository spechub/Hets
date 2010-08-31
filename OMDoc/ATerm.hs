{- |
Module      :  $Header$
Description :  Additional (manual) ATerm-Conversions for OMDoc
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Additional ATerm-Conversions for OMDoc.
-}
module OMDoc.ATerm where

import qualified Network.URI as URI

import ATerm.Lib

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
