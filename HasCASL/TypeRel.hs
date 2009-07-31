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
typeRel = Rel.transReduce . Rel.irreflex . Rel.transClosure
  . Map.foldWithKey ( \ i ti r ->
    Set.fold (Rel.insert i) r $ superTypes ti) Rel.empty

getRawKind :: TypeMap -> Id -> RawKind
getRawKind tm i = typeKind $
    Map.findWithDefault (error $ showId i " not found in type map") i tm

-- | make a polymorphic function from a to b
mkInjOrProjType :: Arrow -> TypeScheme
mkInjOrProjType arr =
    TypeScheme [aTypeArg, bTypeArg] (mkFunArrType aType arr bType) nullRange

injType :: TypeScheme
injType = mkInjOrProjType FunArr

projType :: TypeScheme
projType = mkInjOrProjType PFunArr

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
subtAxioms tm = subtReflex : subtTrans : subtInjProj : injTrans
  : map (subtAx tm) (Rel.toList $ typeRel tm)

nr :: Range
nr = nullRange

subtAx :: TypeMap -> (Id, Id) -> Named Sentence
subtAx tm (i1, i2) = let
    e1 = Map.findWithDefault (error "TypeRel.subtAx1") i1 tm
    e2 = Map.findWithDefault (error "TypeRel.subtAx2") i2 tm
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
               $ mkSubtTerm t1 t2 v1 v2
         _ -> trace (show $ "higher kinds not yet supported " ++ txt)
              $ unitTerm trueId nr

mkSubtTerm :: Type -> Type -> VarDecl -> VarDecl -> Term
mkSubtTerm t1 t2 v1 v2 = mkTerm subtRelName subtRelType [t1, t2] nr
  $ TupleTerm [QualVar v1, QualVar v2] nr

subtReflex :: Named Sentence
subtReflex = let
  v1 = mkVarDecl (stringToId "x") aType
  v2 = mkVarDecl (stringToId "y") aType
  in makeNamed "ga_subt_reflexive" $ Formula
       $ mkForall (GenTypeVarDecl aTypeArg : map GenVarDecl [v1, v2])
         $ mkSubtTerm aType aType v1 v2

subtTrans :: Named Sentence
subtTrans = let
  v1 = mkVarDecl (stringToId "x") aType
  v2 = mkVarDecl (stringToId "y") bType
  v3 = mkVarDecl (stringToId "z") cType
  in makeNamed "ga_subt_transitive" $ Formula
     $ mkForall (map GenTypeVarDecl [aTypeArg, bTypeArg, cTypeArg]
                 ++ map GenVarDecl [v1, v2, v3])
     $ mkLogTerm implId nr
        (mkLogTerm andId nr
         (mkSubtTerm aType bType v1 v2)
         $ mkSubtTerm bType cType v2 v3)
        $ mkSubtTerm aType cType v1 v3

mkInjEq :: Type -> Type -> VarDecl -> VarDecl -> Term
mkInjEq t1 t2 v1 v2 =
   mkEqTerm eqId t2 nr (QualVar v2)
          $ mkTerm injName injType [t1, t2] nr
            $ QualVar v1

subtInjProj :: Named Sentence
subtInjProj = let
  v1 = mkVarDecl (stringToId "x") aType
  v2 = mkVarDecl (stringToId "y") bType
  in makeNamed "ga_subt_inj_proj" $ Formula
     $ mkForall (map GenTypeVarDecl [aTypeArg, bTypeArg]
                 ++ map GenVarDecl [v1, v2])
     $ mkLogTerm implId nr
        (mkSubtTerm aType bType v1 v2)
       $ mkLogTerm eqvId nr (mkInjEq aType bType v1 v2)
        $ mkEqTerm eqId aType nr (QualVar v1)
          $ mkTerm projName projType [bType, aType] nr
            $ QualVar v2

injTrans :: Named Sentence
injTrans =  let
  v1 = mkVarDecl (stringToId "x") aType
  v2 = mkVarDecl (stringToId "y") bType
  v3 = mkVarDecl (stringToId "z") cType
  in makeNamed "ga_inj_transitive" $ Formula
     $ mkForall (map GenTypeVarDecl [aTypeArg, bTypeArg, cTypeArg]
                 ++ map GenVarDecl [v1, v2, v3])
     $ mkLogTerm implId nr
        (mkLogTerm andId nr (mkSubtTerm aType bType v1 v2)
          $ mkSubtTerm bType cType v2 v3)
       $ mkLogTerm eqvId nr (mkInjEq aType cType v1 v3)
         $ mkLogTerm andId nr (mkInjEq aType bType v1 v2)
           $ mkInjEq bType cType v2 v3
