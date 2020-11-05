{- |
Module      :  ./HasCASL/TypeRel.hs
Description :  compute subtype dependencies
Copyright   :  (c) Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

compute subtype dependencies
-}

module HasCASL.TypeRel where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ClassAna
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.DataAna
import HasCASL.MinType
import HasCASL.Merge

import Common.Id
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set
import Data.Maybe

typeRel :: TypeMap -> Rel.Rel Id
typeRel = Rel.transReduce . Rel.irreflex . Rel.transClosure
  . Map.foldrWithKey ( \ i ti r ->
    Set.fold (Rel.insertPair i) r $ superTypes ti) Rel.empty

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

varRel :: Rel.Rel Id -> TypeMap -> Rel.Rel Id
varRel r =
  foldr (\ i -> Rel.insertPair i i) r . Map.keys
  . Map.filter (any (`elem` [CoVar, ContraVar]) . getKindAppl . typeKind)

subtAxioms :: TypeMap -> [Named Sentence]
subtAxioms tm0 =
  let tm = addUnit cpoMap tm0
      tr = varRel (typeRel tm) tm in
  if Rel.nullKeys $ typeRel tm0 then [] else
  subtReflex : subtTrans : subtInjProj : injTrans : idInj
  : map (subtAx tm) (Rel.toList tr)

nr :: Range
nr = nullRange

getKindAppl :: RawKind -> [Variance]
getKindAppl rk = case rk of
  ClassKind () -> []
  FunKind v _ r _ -> v : getKindAppl r

mkTypeArg :: Id -> Int -> TypeArg
mkTypeArg i c = TypeArg i NonVar (VarKind universe) rStar c Other nr

subtAx :: TypeMap -> (Id, Id) -> Named Sentence
subtAx tm (i1, i2) = let
    findType i = Map.findWithDefault
      (Map.findWithDefault (error "TypeRel.subtAx") i bTypes) i tm
    e1 = findType i1
    e2 = findType i2
    txt = shows i1 "_<_" ++ show i2
    l1 = getKindAppl $ typeKind e1
    l2 = getKindAppl $ typeKind e2
    l3 = zipWith minVariance l1 l2
    l4 = foldr (\ v (((tl, vl), pl), fl) ->
            let c = length pl + 1
                a = simpleIdToId $ genNumVar "a" c
                ta = mkTypeArg a (- (length tl + 1))
                b = simpleIdToId $ genNumVar "b" c
                tb = mkTypeArg b (- (length tl + 2))
                x = stringToId $ 'x' : show c
                y = stringToId $ 'y' : show c
                tx = typeArgToType ta
                ty = typeArgToType tb
                vx = mkVarDecl x tx
                vy = mkVarDecl y ty
            in (case v of
                  NonVar -> ((ta : tl, vx : vl), (tx, tx) : pl)
                  _ -> (([ta, tb] ++ tl, [vx, vy] ++ vl), (tx, ty) : pl)
               , case v of
                   CoVar -> mkSubtTerm tx ty vx vy : fl
                   ContraVar -> mkSubtTerm ty tx vy vx : fl
                   _ -> fl)) ((([], []), []), []) l3
    (args, fs) = l4
    (gens, acts) = args
    (act1, act2) = unzip acts
    (tyargs, vargs) = gens
    t1 = mkTypeAppl (toType i1) act1
    t2 = mkTypeAppl (toType i2) act2
    x1 = stringToId "x"
    x2 = stringToId "y"
    v1 = mkVarDecl x1 t1
    v2 = mkVarDecl x2 t2
    in makeNamed ("ga_subt_" ++ txt) $ Formula
         $ mkForall (map GenTypeVarDecl tyargs
                     ++ map GenVarDecl (vargs ++ [v1, v2]))
           $ (if null fs then id else
             mkLogTerm implId nr (foldr1 (mkLogTerm andId nr) fs))
               $ mkSubtTerm t1 t2 v1 v2

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

xa :: VarDecl
xa = mkVarDecl (stringToId "x") aType

yb :: VarDecl
yb = mkVarDecl (stringToId "y") bType

zc :: VarDecl
zc = mkVarDecl (stringToId "z") cType

xaToZc :: [GenVarDecl]
xaToZc = map GenTypeVarDecl [aTypeArg, bTypeArg, cTypeArg]
  ++ map GenVarDecl [xa, yb, zc]

subtTrans :: Named Sentence
subtTrans = makeNamed "ga_subt_transitive" $ Formula
     $ mkForall xaToZc
     $ mkLogTerm implId nr
        (mkLogTerm andId nr
         (mkSubtTerm aType bType xa yb)
         $ mkSubtTerm bType cType yb zc)
        $ mkSubtTerm aType cType xa zc

mkInjTerm :: Type -> Type -> Term -> Term
mkInjTerm t1 t2 = mkTerm injName injType [t1, t2] nr

mkInjEq :: Type -> Type -> VarDecl -> VarDecl -> Term
mkInjEq t1 t2 v1 v2 =
   mkEqTerm eqId t2 nr (QualVar v2)
          $ mkInjTerm t1 t2 $ QualVar v1

subtInjProj :: Named Sentence
subtInjProj = makeNamed "ga_subt_inj_proj" $ Formula
     $ mkForall (map GenTypeVarDecl [aTypeArg, bTypeArg]
                 ++ map GenVarDecl [xa, yb])
     $ mkLogTerm implId nr
        (mkSubtTerm aType bType xa yb)
       $ mkLogTerm eqvId nr (mkInjEq aType bType xa yb)
        $ mkEqTerm eqId aType nr (QualVar xa)
          $ mkTerm projName projType [bType, aType] nr
            $ QualVar yb

injTrans :: Named Sentence
injTrans = makeNamed "ga_inj_transitive" $ Formula
     $ mkForall xaToZc
     $ mkLogTerm implId nr
        (mkLogTerm andId nr (mkSubtTerm aType bType xa yb)
          $ mkLogTerm andId nr (mkSubtTerm bType cType yb zc)
            $ mkInjEq aType bType xa yb)
       $ mkLogTerm eqvId nr (mkInjEq aType cType xa zc)
           $ mkInjEq bType cType yb zc

idInj :: Named Sentence
idInj = makeNamed "ga_inj_identity"
  $ Formula $ mkForall [GenTypeVarDecl aTypeArg, GenVarDecl xa]
  $ mkInjEq aType aType xa xa

monos :: Env -> [Named Sentence]
monos e = concatMap (makeMonos e) . Map.toList $ assumps e

makeMonos :: Env -> (Id, Set.Set OpInfo) -> [Named Sentence]
makeMonos e (i, s) = makeEquivMonos e i . map opType $ Set.toList s

makeEquivMonos :: Env -> Id -> [TypeScheme] -> [Named Sentence]
makeEquivMonos e i l = case l of
  [] -> []
  t : r -> mapMaybe (makeEquivMono e i t) r ++ makeEquivMonos e i r

mkTypedTerm :: Term -> Type -> Range -> Term
mkTypedTerm t = TypedTerm t OfType

mkTypedEqTerm :: Id -> Type -> Range -> Term -> Term -> Term
mkTypedEqTerm i s r t1 t2 =
  mkEqTerm i s r (mkTypedTerm t1 s r) $ mkTypedTerm t2 s r

makeEquivMono :: Env -> Id -> TypeScheme -> TypeScheme -> Maybe (Named Sentence)
makeEquivMono e i s1 s2 = case getCommonSupertype e s1 s2 of
  Just (ty1, l1, ty2, l2, args, nTy) ->
    Just $ makeNamed "ga_monotonicity"
         $ Formula $ mkForall (map GenTypeVarDecl args)
           $ mkTypedEqTerm eqId nTy nr
           (mkInjTerm ty1 nTy
             $ QualOp Op (PolyId i [] nr) s1 l1 UserGiven nr)
           $ mkInjTerm ty2 nTy
             $ QualOp Op (PolyId i [] nr) s2 l2 UserGiven nr
  Nothing -> Nothing
