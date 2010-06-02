{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  embedding CASL into HasCASL
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2003-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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

import qualified Data.Map as Map
import qualified Data.Set as Set

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

fromOPTYPEAux :: Cas.OP_TYPE -> Type
fromOPTYPEAux ot =
    let (args, res, total, arr) = case ot of
                   Cas.Op_type Cas.Total ars rs _ ->
                       (ars, rs, True, FunArr)
                   Cas.Op_type Cas.Partial ars rs _ ->
                       (ars, rs, False, PFunArr)
        resTy = toType res
        in if null args then
           if total then resTy else mkLazyType resTy
           else mkFunArrType (mkProductType $ map toType args) arr resTy

fromOPTYPE :: Cas.OP_TYPE -> TypeScheme
fromOPTYPE = simpleTypeScheme . fromOPTYPEAux

fromOpType :: CasS.OpType -> Cas.OpKind -> TypeScheme
fromOpType ot ok =
    let args = map toType $ CasS.opArgs ot
        arg = mkProductType args
        res = toType $ CasS.opRes ot
    in simpleTypeScheme $
      if null args then case ok of
                Cas.Total -> res
                Cas.Partial -> mkLazyType res
       else mkFunArrType arg (case ok of
                Cas.Total -> FunArr
                Cas.Partial -> PFunArr) res

fromPREDTYPE :: Cas.PRED_TYPE -> Type
fromPREDTYPE (Cas.Pred_type args ps) =
   if null args then mkLazyType $ unitTypeWithRange ps
   else predType ps $ mkProductTypeWithRange (map toType args) ps

fromPredType :: CasS.PredType -> TypeScheme
fromPredType pt =
    let args = CasS.predArgs pt
    in simpleTypeScheme $ fromPREDTYPE $ Cas.Pred_type args $ getRange args

mapTheory :: Pretty f => (CasS.Sign f e, [Named (Cas.FORMULA f)])
          -> (Env, [Named Sentence])
mapTheory (sig, sents) =
    let constr = foldr getConstructors Set.empty sents
        env = mapSig constr sig
        newSents = map (mapNamed toSentence) sents
        in (env, newSents)

getConstructors :: Named (Cas.FORMULA f) -> Set.Set (Id, CasS.OpType)
                -> Set.Set (Id, CasS.OpType)
getConstructors f s = case sentence f of
   Cas.Sort_gen_ax cs _ -> let
       (_, ops, _) = Cas.recover_Sort_gen_ax cs
       in foldr ( \ (Cas.Qual_op_name i t _) ->
             Set.insert (i, (CasS.toOpType t) { CasS.opKind = Cas.Partial }))
             s ops
   _ -> s

mapSig :: Set.Set (Id, CasS.OpType) -> CasS.Sign f e -> Env
mapSig constr sign =
    let f1 = concatMap ( \ (i, s) ->
                   map ( \ ty -> (trId i, fromOpType ty $ CasS.opKind ty,
                            if Set.member (i, ty { CasS.opKind = Cas.Partial })
                               constr then ConstructData $ CasS.opRes ty
                               else NoOpDefn Op))
                         $ Set.toList s) $ Map.toList $ CasS.opMap sign
        f2 = concatMap ( \ (i, s) ->
                   map ( \ ty -> (trId i, fromPredType ty, NoOpDefn Pred))
                         $ Set.toList s) $ Map.toList $ CasS.predMap sign
        insF (i, ty, defn) m =
            let os = Map.findWithDefault Set.empty i m
                in Map.insert i (Set.insert (OpInfo ty Set.empty defn) os) m
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
                          ((trId i, fromOpType ot (CasS.opKind ot)),
                           (trId j, mapTypeOfScheme (mapType tm)
                                    $ fromOpType ot t)))
                    $ Map.toList $ CasM.op_map m
               f2 = map ( \ ((i, pt), j) ->
                          let sc = fromPredType pt
                          in ( (trId i, sc)
                             , (trId j, mapTypeOfScheme (mapType tm) sc)))
                    $ Map.toList $ CasM.pred_map m
            in (mkMorphism (mapSig Set.empty $ CasM.msource m)
                               (mapSig Set.empty $ CasM.mtarget m))
           { typeIdMap = tm , funMap = Map.fromList $ f2 ++ f1 }

mapSym :: CasS.Symbol -> Symbol
mapSym s = let i = trId $ CasS.symName s in
    case CasS.symbType s of
    CasS.OpAsItemType ot ->
        idToOpSymbol initialEnv i $ fromOpType ot $ CasS.opKind ot
    CasS.PredAsItemType pt -> idToOpSymbol initialEnv i $ fromPredType pt
    CasS.SortAsItemType -> idToTypeSymbol initialEnv i rStar
    _ -> error "Comorphisms.CASL2HasCASL.mapSym"

toQuant :: Cas.QUANTIFIER -> Quantifier
toQuant Cas.Universal = Universal
toQuant Cas.Existential = Existential
toQuant Cas.Unique_existential = Unique

toVarDecl :: Cas.VAR_DECL -> [GenVarDecl]
toVarDecl (Cas.Var_decl vs s ps) =
           map ( \ i -> GenVarDecl $
                 VarDecl (simpleIdToId i) (toType s) Other ps) vs

toSentence :: Pretty f => Cas.FORMULA f -> Sentence
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
                $ map ( \ (Cas.Qual_op_name i t _) ->
                        (trId i, CasS.toOpType t)) ops) sorts
   _ -> Formula $ toTerm f

toTerm :: Pretty f => Cas.FORMULA f -> Term
toTerm f = foldFormula (transRecord $ showDoc f "") f

transRecord :: String -> Record f Term Term
transRecord str = let err = error $ "CASL2HasCASL.unexpected formula: " ++ str
  in (constRecord err err err)
  { foldQuantification = \ _ q -> QuantifiedTerm (toQuant q)
        . concatMap toVarDecl
  , foldConjunction = \ _ fs ps -> case fs of
        [] -> unitTerm trueId ps
        _ -> toBinJunctor andId fs ps
  , foldDisjunction = \ _ fs ps -> case fs of
        [] -> unitTerm falseId ps
        _ -> toBinJunctor orId fs ps
  , foldImplication = \ _ f1 f2 b ps -> if b then mkLogTerm implId ps f1 f2
               else mkLogTerm infixIf ps f2 f1
  , foldEquivalence = \ _ f1 f2 ps -> mkLogTerm eqvId ps f1 f2
  , foldNegation = \ _ frm ps -> mkTerm notId notType [] ps frm
  , foldTrue_atom = \ _ -> unitTerm trueId
  , foldFalse_atom = \ _ -> unitTerm falseId
  , foldExistl_equation = \ (Cas.Existl_equation c1 _ _) t1 t2 ps ->
        mkEqTerm exEq (typeOfTerm c1) ps t1 t2
  , foldStrong_equation = \ (Cas.Strong_equation c1 _ _) t1 t2 ps ->
        mkEqTerm eqId (typeOfTerm c1) ps t1 t2
  , foldPredication = \ _ (Cas.Qual_pred_name ui pty@(Cas.Pred_type ts _) ps)
        args qs ->
        let i = trId ui
            sc = simpleTypeScheme $ fromPREDTYPE pty
            p = QualOp Pred (PolyId i [] ps) sc [] Infer ps
            in if null args then p else TypedTerm
              (ApplTerm p (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm tr Inferred (toType ty) ps)
                args ts) qs) qs)
              Inferred unitType ps
  , foldDefinedness = \ (Cas.Definedness c _) t ps ->
        mkTerm defId defType [typeOfTerm c] ps t
  , foldMembership = \ _ t -> TypedTerm t InType . toType
  , foldQuantOp = \ _ uo ty frm -> let o = trId uo in
         QuantifiedTerm Universal
         [GenVarDecl $ VarDecl o (fromOPTYPEAux ty) Other nullRange]
         (qualName2var o frm) nullRange
  , foldQuantPred = \ _ up ty frm -> let p = trId up in
         QuantifiedTerm Universal
         [GenVarDecl $ VarDecl p (fromPREDTYPE ty) Other nullRange]
         (qualName2var p frm) nullRange
  , foldQual_var = \ _ v ty ->
        QualVar . VarDecl (simpleIdToId v) (toType ty) Other
  , foldApplication = \ _ (Cas.Qual_op_name ui ot ps) args qs  ->
        let i = trId ui
            o = QualOp Op (PolyId i [] ps) (fromOPTYPE ot) [] Infer ps
            at = CasS.toOpType ot
        in if null args then o else TypedTerm
           (ApplTerm o (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm tr Inferred (toType ty) ps)
                args $ CasS.opArgs at) qs) qs)
           Inferred (toType $ CasS.opRes at) ps
  , foldSorted_term = \ _ trm -> TypedTerm trm OfType . toType
  , foldCast = \ _ trm -> TypedTerm trm AsType . toType
  , foldConditional = \ (Cas.Conditional c1 _ _ _) t1 f t2 ps ->
        mkTerm whenElse whenType [typeOfTerm c1] ps $ TupleTerm [t1, f, t2] ps
  , foldSort_gen_ax = \ _ cs _ ->
      error $ "unexpected sort generation constraint: "
      ++ unlines (map (flip showDoc "") $ recoverType cs)
      ++ "in: " ++ str
  }

typeOfTerm :: Cas.TERM f -> Type
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


