{- | 
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

a few basic 'ShATermConvertible' instances needed by "Haskell.ATC_Haskell"
-}

module Haskell.BaseATC where

import Common.ATerm.Lib
import SrcLoc

instance (ShATermConvertible a, ShATermConvertible b) 
    => ShATermConvertible (Either a b) where
    toShATerm att0 (Left aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Left" [ aa' ] []) att1 }
    toShATerm att0 (Right aa) =
        case toShATerm att0 aa of { (att1,aa') ->
        addATerm (ShAAppl "Right" [ aa' ] []) att1 }
    fromShATerm att =
        case getATerm att of
            ShAAppl "Left" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Left aa' }
            ShAAppl "Right" [ aa ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    Right aa' }
            u -> fromShATermError "Either" u
    type_of _ = "Prelude.Either"

instance ShATermConvertible SrcLoc where
    toShATerm att0 (SrcLoc aa ab ac ad) =
        case toShATerm att0 aa of { (att1,aa') ->
        case toShATerm att1 ab of { (att2,ab') ->
        case toShATerm att2 ac of { (att3,ac') ->
        case toShATerm att3 ad of { (att4,ad') ->
        addATerm (ShAAppl "SrcLoc" [ aa',ab',ac',ad' ] []) att4 }}}}
    fromShATerm att =
        case getATerm att of
            ShAAppl "SrcLoc" [ aa,ab,ac,ad ] _ ->
                    case fromShATerm $ getATermByIndex1 aa att of { aa' ->
                    case fromShATerm $ getATermByIndex1 ab att of { ab' ->
                    case fromShATerm $ getATermByIndex1 ac att of { ac' ->
                    case fromShATerm $ getATermByIndex1 ad att of { ad' ->
                    SrcLoc aa' ab' ac' ad' }}}}
            u -> fromShATermError "SrcLoc" u
    type_of _ = "Haskell.SrcLoc"
