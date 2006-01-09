{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

a few basic 'ShATermConvertible' instances needed by "Haskell.ATC_Haskell"
-}

module Haskell.BaseATC where

import Common.ATerm.Lib
import Common.DynamicUtils
import SrcLoc

_tc_SrcLocTc :: TyCon
_tc_SrcLocTc = mkTyCon "SrcLoc"
instance Typeable SrcLoc where
    typeOf _ = mkTyConApp _tc_SrcLocTc []

instance (ShATermConvertible a, ShATermConvertible b)
    => ShATermConvertible (Either a b) where
    toShATermAux att0 (Left aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Left" [ aa' ] []) att1
    toShATermAux att0 (Right aa) = do
        (att1,aa') <- toShATerm' att0 aa
        return $ addATerm (ShAAppl "Right" [ aa' ] []) att1
    fromShATermAux ix att =
        case getShATerm ix att of
            ShAAppl "Left" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Left aa') }
            ShAAppl "Right" [ aa ] _ ->
                    case fromShATerm' aa att of { (att2, aa') ->
                    (att2, Right aa') }
            u -> fromShATermError "Either" u

instance ShATermConvertible SrcLoc where
    toShATermAux att0 (SrcLoc aa ab ac ad) = do
        (att1,aa') <- toShATerm' att0 aa
        (att2,ab') <- toShATerm' att1 ab
        (att3,ac') <- toShATerm' att2 ac
        (att4,ad') <- toShATerm' att3 ad
        return $ addATerm (ShAAppl "SrcLoc" [ aa',ab',ac',ad' ] []) att4
    fromShATermAux ix att0 =
        case getShATerm ix att0 of
            ShAAppl "SrcLoc" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm' aa att0 of { (att1, aa') ->
                    case fromShATerm' ab att1 of { (att2, ab') ->
                    case fromShATerm' ac att2 of { (att3, ac') ->
                    case fromShATerm' ad att3 of { (att4, ad') ->
                    (att4, SrcLoc aa' ab' ac' ad') }}}}
            u -> fromShATermError "SrcLoc" u
