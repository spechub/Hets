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
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.DataAna
import Debug.Trace

typeRel :: TypeMap -> Rel.Rel Id
typeRel = Rel.irreflex . Rel.transClosure . Map.foldWithKey ( \ i ti r ->
    Set.fold (Rel.insert i) r $ superTypes ti) Rel.empty

getRawKind :: TypeMap -> Id -> RawKind
getRawKind tm i = typeKind $
    Map.findWithDefault (error $ showId i " not found in type map") i tm

-- | make a polymorphic function from a to b
mkInjOrProjType :: Arrow -> TypeScheme
mkInjOrProjType arr =
    TypeScheme [aTypeArg, bTypeArg] (mkFunArrType aType arr bType) nullRange

mkInjOrProj :: Arrow -> Set.Set OpInfo
mkInjOrProj arr = Set.singleton OpInfo
    { opType = mkInjOrProjType arr
    , opAttrs = Set.empty
    , opDefn = NoOpDefn Fun }

subtRelName :: Id
subtRelName = mkId [genToken "subt"]

subtRelType :: TypeScheme
subtRelType = TypeScheme [aTypeArg, bTypeArg]
  (mkFunArrType (mkProductType [aType, bType]) PFunArr unitType) nullRange

subtRel :: Set.Set OpInfo
subtRel = Set.singleton OpInfo
    { opType = subtRelType
    , opAttrs = Set.empty
    , opDefn = NoOpDefn Fun }

subtAxioms :: TypeMap -> [Named Sentence]
subtAxioms tm = map (subtAx tm) . Rel.toList $ typeRel tm

subtAx :: TypeMap -> (Id, Id) -> Named Sentence
subtAx tm (i1, i2) = let
    e1 = Map.findWithDefault (error "TypeRel.subtAx1") i1 tm
    e2 = Map.findWithDefault (error "TypeRel.subtAx2") i2 tm
    ps = nullRange
    txt = shows i1 "_<_" ++ show i2
    in makeNamed ("ga_subt_" ++ txt)
               $ Formula $ case (typeKind e1, typeKind e2) of
         (ClassKind (), ClassKind ()) -> let
             t1 = toType i1
             t2 = toType i2
             x1 = stringToId "x"
             x2 = stringToId "y"
             v1 = mkVarDecl x1 t1
             v2 = mkVarDecl x2 t2
            in mkForall (map GenVarDecl [v1, v2])
               $ mkTerm subtRelName subtRelType [t1, t2] ps
               $ TupleTerm [QualVar v1, QualVar v2] ps
         _ -> trace (show $ "higher kinds not yet supported " ++ txt)
              $ unitTerm trueId ps
