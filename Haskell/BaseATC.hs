{- |
Module      :  $Header$
Description :  basic ShATermConvertible instances
Copyright   :  (c) Christian Maeder, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

a few basic 'ShATermConvertible' instances needed by "Haskell.ATC_Haskell"
-}

module Haskell.BaseATC () where

import Common.ATerm.Lib
import Data.Typeable
import SrcLoc

_tc_SrcLocTc :: TyCon
_tc_SrcLocTc = mkTyCon "SrcLoc"
instance Typeable SrcLoc where
    typeOf _ = mkTyConApp _tc_SrcLocTc []

instance ShATermConvertible SrcLoc where
  toShATermAux = toShATermAux_SrcLoc
  fromShATermAux = fromShATermAux_SrcLoc

toShATermAux_SrcLoc :: ATermTable -> SrcLoc -> IO (ATermTable, Int)
toShATermAux_SrcLoc att0 (SrcLoc aa ab ac ad) = do
        (att1,aa') <- toShATerm' att0 aa
        (att2,ab') <- toShATerm' att1 ab
        (att3,ac') <- toShATerm' att2 ac
        (att4,ad') <- toShATerm' att3 ad
        return $ addATerm (ShAAppl "SrcLoc" [ aa',ab',ac',ad' ] []) att4

fromShATermAux_SrcLoc :: Int -> ATermTable -> (ATermTable, SrcLoc)
fromShATermAux_SrcLoc ix att0 =
        case getShATerm ix att0 of
            ShAAppl "SrcLoc" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm' aa att0 of { (att1, aa') ->
                    case fromShATerm' ab att1 of { (att2, ab') ->
                    case fromShATerm' ac att2 of { (att3, ac') ->
                    case fromShATerm' ad att3 of { (att4, ad') ->
                    (att4, SrcLoc aa' ab' ac' ad') }}}}
            u -> fromShATermError "SrcLoc" u
