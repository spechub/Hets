{- |
Module      :  $Header$
Description :  compute subtype dependencies
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

compute subtype dependencies
-}

module HasCASL.TypeRel where

import Common.Id
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le

typeRel :: TypeMap -> Rel.Rel Id
typeRel = Rel.irreflex . Rel.transClosure . Map.foldWithKey ( \ i ti r ->
    Set.fold (Rel.insert i) r $ superTypes ti) Rel.empty

getRawKind :: TypeMap -> Id -> RawKind
getRawKind tm i = typeKind $
    Map.findWithDefault (error $ showId i " not find in type map") i tm

mkInjection :: TypeMap -> (Id, Id) -> OpInfo
mkInjection tm (i, j) = let r1 = getRawKind tm i in
    if r1 == getRawKind tm j then
        if r1 == rStar then OpInfo
            { opType = simpleTypeScheme $ mkFunArrType (toType i) FunArr
                       $ toType j
            , opAttrs = Set.empty
            , opDefn = NoOpDefn Fun }
        else error "mkInjection1"
    else error "mkInjection2"
