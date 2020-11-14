{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CASL2HasCASL.hs
Description :  embedding CASL into HasCASL
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2003-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to HasCASL.
-}

module Comorphisms.CASL2HasCASL where

import Logic.Logic
import Logic.Comorphism

import Common.AS_Annotation
import Common.Id
import Common.ProofTree
import Common.DocUtils

import qualified Data.HashMap.Strict as Map
import qualified Data.HashSet as Set

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as CasSub
import CASL.ToDoc
import CASL.Fold
import qualified CASL.AS_Basic_CASL as Cas
import qualified CASL.Sign as CasS
import qualified CASL.Morphism as CasM

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.Sublogic as HasSub
import HasCASL.FoldTerm as HasFold

-- | The identity of the comorphism
data CASL2HasCASL = CASL2HasCASL deriving (Show)

instance Language CASL2HasCASL -- default definition is okay

instance Comorphism CASL2HasCASL
               CASL CASL_Sublogics
               CASLBasicSpec Cas.CASLFORMULA Cas.SYMB_ITEMS
               Cas.SYMB_MAP_ITEMS
               CasS.CASLSign
               CasM.CASLMor
               CasS.Symbol CasM.RawSymbol ProofTree
               HasCASL Sublogic
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic CASL2HasCASL = CASL
    sourceSublogic CASL2HasCASL = CasSub.top
    targetLogic CASL2HasCASL = HasCASL
    mapSublogic CASL2HasCASL sl = Just $ sublogicUp $
        (if has_cons sl then sublogic_max need_hol else id)
        caslLogic
        { HasSub.has_sub = CasSub.has_sub sl
        , HasSub.has_part = CasSub.has_part sl
        , HasSub.has_eq = CasSub.has_eq sl
        , HasSub.has_pred = CasSub.has_pred sl
        , HasSub.which_logic = case CasSub.which_logic sl of
             CasSub.Atomic -> HasSub.Atomic
             CasSub.Horn -> HasSub.Horn
             CasSub.GHorn -> HasSub.GHorn
             CasSub.Prenex -> HasSub.FOL -- at least for now
             CasSub.FOL -> HasSub.FOL
             CasSub.SOL -> HasSub.HOL
        }
    map_morphism CASL2HasCASL = return . mapMor
    map_sentence CASL2HasCASL _ = return . toSentence
    map_symbol CASL2HasCASL _ = Set.singleton . mapSym
    map_theory CASL2HasCASL = return . mapTheory
    has_model_expansion CASL2HasCASL = True
    is_weakly_amalgamable CASL2HasCASL = True
    isInclusionComorphism CASL2HasCASL = True

fromOPTYPE :: Cas.OP_TYPE -> Type
fromOPTYPE (Cas.Op_type ok args res ps) = let
  (total, arr) = case ok of
    Cas.Total -> (True, FunArr)
    Cas.Partial -> (False, PFunArr)
  resTy = toType res
  in if null args then if total then resTy else mkLazyType resTy
  else mkFunArrType (mkProductTypeWithRange (map toType args) ps) arr resTy

fromOpType :: CasS.OpType -> Type
fromOpType = fromOPTYPE . CasS.toOP_TYPE

fromPREDTYPE :: Cas.PRED_TYPE -> Type
fromPREDTYPE (Cas.Pred_type args ps) =
   if null args then mkLazyType $ unitTypeWithRange ps
   else predType ps $ mkProductTypeWithRange (map toType args) ps

fromPredType :: CasS.PredType -> Type
fromPredType = fromPREDTYPE . CasS.toPRED_TYPE

mapTheory :: (CasS.TermExtension f, FormExtension f) =>
  (CasS.Sign f e, [Named (Cas.FORMULA f)]) -> (Env, [Named Sentence])
mapTheory (sig, sents) =
  (mapSig (CasS.getConstructors sents) sig, map (mapNamed toSentence) sents)

mapSig :: Set.HashSet (Id, CasS.OpType) -> CasS.Sign f e -> Env
mapSig = mapSigAux trId fromOpType fromPredType

-- | sort names or not translated
mapSigAux :: (Id -> Id) -> (CasS.OpType -> Type) -> (CasS.PredType -> Type)
  -> Set.HashSet (Id, CasS.OpType) -> CasS.Sign f e -> Env
mapSigAux trI trO trP constr sign =
    let f1 = map ( \ (i, ty) ->
                   (trI i, trO ty,
                            if Set.member (i, CasS.mkPartial ty)
                               constr then ConstructData $ CasS.opRes ty
                               else NoOpDefn Op))
             $ CasS.mapSetToList $ CasS.opMap sign
        f2 = map ( \ (i, ty) -> let pTy = trP ty in
                   (trI i, pTy, NoOpDefn
                   $ if isPredType pTy then Pred else Fun))
             $ CasS.mapSetToList $ CasS.predMap sign
        insF (i, ty, defn) m =
            let os = Map.findWithDefault Set.empty i m
            in Map.insert i (Set.insert
                             (OpInfo (simpleTypeScheme ty) Set.empty defn) os) m
     in initialEnv
     { classMap = Map.empty,
       typeMap = Map.fromList $ map
                 ( \ s -> (s, starTypeInfo
                           { superTypes = Set.delete s $
                                          CasS.supersortsOf s sign
                           })) $ Set.toList $ CasS.sortSet sign,
       assumps = foldr insF Map.empty (f1 ++ f2)}

mapMor :: CasM.Morphism f e m -> Morphism
mapMor m = let tm = CasM.sort_map m
               f1 = map ( \ ((i, ot), (j, t)) ->
                          ((trId i, simpleTypeScheme $ fromOpType ot),
                           (trId j, simpleTypeScheme $ mapType tm
                                 $ fromOpType ot { CasS.opKind = t })))
                    $ Map.toList $ CasM.op_map m
               f2 = map ( \ ((i, pt), j) ->
                          let ty = fromPredType pt
                          in ( (trId i, simpleTypeScheme ty)
                             , (trId j, simpleTypeScheme $ mapType tm ty)))
                    $ Map.toList $ CasM.pred_map m
            in (mkMorphism (mapSig Set.empty $ CasM.msource m)
                               (mapSig Set.empty $ CasM.mtarget m))
           { typeIdMap = tm , funMap = Map.fromList $ f2 ++ f1 }

mapSym :: CasS.Symbol -> Symbol
mapSym = mapSymAux trId fromOpType fromPredType

mapSymAux :: (Id -> Id) -> (CasS.OpType -> Type)
  -> (CasS.PredType -> Type) -> CasS.Symbol -> Symbol
mapSymAux trI trO trP s = let
  n = CasS.symName s
  i = trI n
  in case CasS.symbType s of
    CasS.OpAsItemType ot -> idToOpSymbol i . simpleTypeScheme $ trO ot
    CasS.PredAsItemType pt -> idToOpSymbol i . simpleTypeScheme $ trP pt
    CasS.SortAsItemType -> idToTypeSymbol n rStar
    CasS.SubsortAsItemType _ -> idToTypeSymbol n rStar

toQuant :: Cas.QUANTIFIER -> Quantifier
toQuant Cas.Universal = Universal
toQuant Cas.Existential = Existential
toQuant Cas.Unique_existential = Unique

toVarDecl :: Cas.VAR_DECL -> [GenVarDecl]
toVarDecl (Cas.Var_decl vs s ps) =
           map ( \ i -> GenVarDecl $
                 VarDecl (simpleIdToId i) (toType s) Other ps) vs

toSentence :: (CasS.TermExtension f, FormExtension f)
  => Cas.FORMULA f -> Sentence
toSentence f = case f of
   Cas.Sort_gen_ax cs b -> let
       (sorts, ops, smap) = Cas.recover_Sort_gen_ax cs
       genKind = if b then Free else Generated
       mapPart :: Cas.OpKind -> Partiality
       mapPart cp = case cp of
                Cas.Total -> HasCASL.As.Total
                Cas.Partial -> HasCASL.As.Partial
       in DatatypeSen $ map ( \ s ->
          DataEntry (Map.fromList smap) s genKind [] rStar
          $ Set.fromList $ map ( \ (i, t) ->
            let args = map toType $ CasS.opArgs t in
            Construct (if isInjName i then Nothing else Just i)
              (if null args then [] else [mkProductType args])
              (mapPart $ CasS.opKind t)
              $ if null args then [] else
              [map (\ a -> Select Nothing a HasCASL.As.Total) args])
          $ filter ( \ (_, t) -> CasS.opRes t == s)
                $ map ( \ o -> case o of
                        Cas.Qual_op_name i t _ -> (trId i, CasS.toOpType t)
                        _ -> error "CASL2HasCASL.toSentence") ops) sorts
   _ -> Formula $ toTerm f

toTerm :: (CasS.TermExtension f, FormExtension f) => Cas.FORMULA f -> Term
toTerm f = foldFormula (transRecord $ showDoc f "") f

transRecord :: CasS.TermExtension f => String -> Record f Term Term
transRecord str = let err = error $ "CASL2HasCASL.unexpected formula: " ++ str
  in (constRecord err err err)
  { foldQuantification = \ _ q -> QuantifiedTerm (toQuant q)
        . concatMap toVarDecl
  , foldJunction = \ _ j fs ps -> let
       (n, op) = case j of
          Cas.Con -> (trueId, andId)
          Cas.Dis -> (falseId, orId)
       in case fs of
        [] -> unitTerm n ps
        _ -> toBinJunctor op fs ps
  , foldRelation = \ _ f1 c f2 ps -> case c of
       Cas.Implication -> mkLogTerm implId ps f1 f2
       Cas.RevImpl -> mkLogTerm infixIf ps f2 f1
       Cas.Equivalence -> mkLogTerm eqvId ps f1 f2
  , foldNegation = \ _ frm ps -> mkTerm notId notType [] ps frm
  , foldAtom = \ _ b -> unitTerm $ if b then trueId else falseId
  , foldEquation = \ o t1 e t2 ps ->
        let Cas.Equation c1 _ _ _ = o in
        mkEqTerm (if e == Cas.Existl then exEq else eqId)
                     (typeOfTerm c1) ps t1 t2
  , foldPredication = \ _ qpn args qs ->
        let Cas.Qual_pred_name ui pty@(Cas.Pred_type ts _) ps = qpn
            i = trId ui
            sc = simpleTypeScheme $ fromPREDTYPE pty
            p = QualOp Pred (PolyId i [] ps) sc [] Infer ps
            in if null args then p else TypedTerm
              (ApplTerm p (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm tr Inferred (toType ty) ps)
                args ts) qs) qs)
              Inferred unitType ps
  , foldDefinedness = \ o t ps ->
        let Cas.Definedness c _ = o in
        mkTerm defId defType [typeOfTerm c] ps t
  , foldMembership = \ _ t -> TypedTerm t InType . toType
  , foldQuantOp = \ _ uo ty frm -> let o = trId uo in
         QuantifiedTerm Universal
         [GenVarDecl $ VarDecl o (fromOPTYPE ty) Other nullRange]
         (qualName2var o frm) nullRange
  , foldQuantPred = \ _ up ty frm -> let p = trId up in
         QuantifiedTerm Universal
         [GenVarDecl $ VarDecl p (fromPREDTYPE ty) Other nullRange]
         (qualName2var p frm) nullRange
  , foldQual_var = \ _ v ty ->
        QualVar . VarDecl (simpleIdToId v) (toType ty) Other
  , foldApplication = \ _ qon args qs ->
        let Cas.Qual_op_name ui ot ps = qon
            i = trId ui
            sc = simpleTypeScheme $ fromOPTYPE ot
            o = QualOp Op (PolyId i [] ps) sc [] Infer ps
            at = CasS.toOpType ot
        in if null args then o else TypedTerm
           (ApplTerm o (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm tr Inferred (toType ty) ps)
                args $ CasS.opArgs at) qs) qs)
           Inferred (toType $ CasS.opRes at) ps
  , foldSorted_term = \ _ trm -> TypedTerm trm OfType . toType
  , foldCast = \ _ trm -> TypedTerm trm AsType . toType
  , foldConditional = \ o t1 f t2 ps ->
        let Cas.Conditional c1 _ _ _ = o in
        mkTerm whenElse whenType [typeOfTerm c1] ps
          $ TupleTerm [t1, f, t2] ps
  , foldSort_gen_ax = \ _ cs _ ->
      error $ "unexpected sort generation constraint: "
      ++ unlines (map (`showDoc` "") $ recoverType cs)
      ++ "in: " ++ str
  }

typeOfTerm :: CasS.TermExtension f => Cas.TERM f -> Type
typeOfTerm = toType . CasS.sortOfTerm

-- | replace qualified names by variables in second order formulas
qualName2var :: Id -> Term -> Term
qualName2var i = HasFold.foldTerm mapRec
  { foldQualOp = \ t _ (PolyId j _ _) (TypeScheme _ ty _) _ _ ps ->
      if i == j then QualVar $ VarDecl i ty Other ps else t }

-- | the invisible identifier is reserved for application
trId :: Id -> Id
trId i@(Id ts cs ps) = if null cs && all isPlace ts then
  Id [genNumVar "empty" $ length ts] cs ps else i
