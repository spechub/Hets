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

import qualified Data.Map as Map
import qualified Data.Set as Set

-- CASL
import CASL.Logic_CASL
import CASL.Sublogic as CasSub
import qualified CASL.AS_Basic_CASL as Cas
import qualified CASL.Sign as CasS
import qualified CASL.Morphism as CasM

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.Sublogic as HasSub

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
        }
    map_morphism CASL2HasCASL = return . mapMor
    map_sentence CASL2HasCASL sig = return . toSentence sig
    map_symbol CASL2HasCASL = Set.singleton . mapSym
    map_theory CASL2HasCASL = return . mapTheory
    has_model_expansion CASL2HasCASL = True
    is_weakly_amalgamable CASL2HasCASL = True
    isInclusionComorphism CASL2HasCASL = True

fromOpType :: CasS.OpType -> Cas.FunKind -> TypeScheme
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

fromPredType :: CasS.PredType -> TypeScheme
fromPredType pt =
    let args = map toType $ CasS.predArgs pt
        p = getRange args
        arg = mkProductTypeWithRange args p
    in simpleTypeScheme $ if null args then mkLazyType $ unitTypeWithRange p
                          else predType p arg

mapTheory :: (CasS.Sign f e, [Named (Cas.FORMULA f)])
          -> (Env, [Named Sentence])
mapTheory (sig, sents) =
    let constr = foldr getConstructors Set.empty sents
        env = mapSig constr sig
        newSents = map (mapNamed (toSentence sig)) sents
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
                   map ( \ ty -> (i, fromOpType ty $ CasS.opKind ty,
                            if Set.member (i, ty { CasS.opKind = Cas.Partial })
                               constr then ConstructData $ CasS.opRes ty
                               else NoOpDefn Op))
                         $ Set.toList s) $ Map.toList $ CasS.opMap sign
        f2 = concatMap ( \ (i, s) ->
                   map ( \ ty -> (i, fromPredType ty, NoOpDefn Pred))
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
                          ((i, fromOpType ot (CasS.opKind ot)),
                           (j, mapTypeOfScheme (mapType tm)
                                    $ fromOpType ot t)))
                    $ Map.toList $ CasM.fun_map m
               f2 = map ( \ ((i, pt), j) ->
                          let sc = fromPredType pt
                          in ((i, sc), (j, mapTypeOfScheme (mapType tm) sc)))
                    $ Map.toList $ CasM.pred_map m
            in (mkMorphism (mapSig Set.empty $ CasM.msource m)
                               (mapSig Set.empty $ CasM.mtarget m))
           { typeIdMap = tm , funMap = Map.fromList $ f2 ++ f1 }

mapSym :: CasS.Symbol -> Symbol
mapSym s = let i = CasS.symName s in
    case CasS.symbType s of
    CasS.OpAsItemType ot ->
        idToOpSymbol initialEnv i $ fromOpType ot $ CasS.opKind ot
    CasS.PredAsItemType pt -> idToOpSymbol initialEnv i $ fromPredType pt
    CasS.SortAsItemType -> idToTypeSymbol initialEnv i rStar

toQuant :: Cas.QUANTIFIER -> Quantifier
toQuant Cas.Universal = Universal
toQuant Cas.Existential = Existential
toQuant Cas.Unique_existential = Unique

toVarDecl :: Cas.VAR_DECL -> [GenVarDecl]
toVarDecl (Cas.Var_decl vs s ps) =
           map ( \ i -> GenVarDecl $
                 VarDecl (simpleIdToId i) (toType s) Other ps) vs

toSentence :: CasS.Sign f e -> Cas.FORMULA f -> Sentence
toSentence sig f = case f of
   Cas.Sort_gen_ax cs b -> let
       (sorts, ops, smap) = Cas.recover_Sort_gen_ax cs
       genKind = if b then Free else Generated
       mapPart :: Cas.FunKind -> Partiality
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
                        (i, CasS.toOpType t)) ops) sorts
   _ -> Formula $ toTerm sig f

toTerm :: CasS.Sign f e -> Cas.FORMULA f -> Term
toTerm s f = case f of
    Cas.Quantification q vs frm ps ->
        QuantifiedTerm  (toQuant q)
                        (concatMap toVarDecl vs) (toTerm s frm) ps
    Cas.Conjunction fs ps ->
        case map (toTerm s) fs of
                [] -> unitTerm trueId ps
                ts -> toBinJunctor andId ts ps
    Cas.Disjunction fs ps ->
        case map (toTerm s) fs of
                [] -> unitTerm falseId ps
                ts -> toBinJunctor orId ts ps
    Cas.Implication f1 f2 b ps ->
        let t1 = toTerm s f1
            t2 = toTerm s f2
            in if b then mkLogTerm implId ps t1 t2
               else mkLogTerm infixIf ps t2 t1
    Cas.Equivalence f1 f2 ps ->
        mkLogTerm eqvId ps (toTerm s f1) $ toTerm s f2
    Cas.Negation frm ps -> mkTerm notId notType [] ps $ toTerm s frm
    Cas.True_atom ps -> unitTerm trueId ps
    Cas.False_atom ps -> unitTerm falseId ps
    Cas.Existl_equation t1 t2 ps ->
        mkEqTerm exEq (typeOfTerm t1) ps (fromTERM s t1) $ fromTERM s t2
    Cas.Strong_equation t1 t2 ps ->
        mkEqTerm eqId (typeOfTerm t1) ps (fromTERM s t1) $ fromTERM s t2
    Cas.Predication (Cas.Qual_pred_name i (Cas.Pred_type ts _) ps) args qs ->
        let sc = simpleTypeScheme $ if null ts then unitTypeWithRange ps
                 else predType ps $ mkProductTypeWithRange (map toType ts) ps
            p = QualOp Pred (PolyId i [] ps) sc [] Infer ps
            in if null args then p else TypedTerm
              (ApplTerm p (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm (fromTERM s tr) Inferred (toType ty) ps)
                args ts) qs) qs)
              Inferred unitType ps
    Cas.Definedness t ps ->
        mkTerm defId defType [typeOfTerm t] ps $ fromTERM s t
    Cas.Membership t ty ps -> TypedTerm (fromTERM s t) InType (toType ty) ps
    _ -> error "fromTERM"

fromOP_TYPE :: Cas.OP_TYPE -> TypeScheme
fromOP_TYPE ot =
    let (args, res, total, arr) = case ot of
                   Cas.Op_type Cas.Total ars rs _ ->
                       (ars, rs, True, FunArr)
                   Cas.Op_type Cas.Partial ars rs _ ->
                       (ars, rs, False, PFunArr)
        resTy = toType res
        in simpleTypeScheme $ if null args then
           if total then resTy else mkLazyType resTy
           else mkFunArrType (mkProductType $ map toType args) arr resTy

fromTERM :: CasS.Sign f e -> Cas.TERM f -> Term
fromTERM s t = case t of
    Cas.Qual_var v ty ps ->
        QualVar $ VarDecl (simpleIdToId v) (toType ty) Other ps
    Cas.Application (Cas.Qual_op_name i ot ps) args qs  ->
        let o = QualOp Op (PolyId i [] ps) (fromOP_TYPE ot) [] Infer ps
            at = CasS.toOpType ot
        in if null args then o else TypedTerm
           (ApplTerm o (mkTupleTerm (zipWith
               (\ tr ty -> TypedTerm (fromTERM s tr) Inferred (toType ty) ps)
                args $ CasS.opArgs at) qs) qs)
           Inferred (toType $ CasS.opRes at) ps
    Cas.Sorted_term trm ty ps ->
        TypedTerm (fromTERM s trm) OfType (toType ty) ps
    Cas.Cast trm ty ps -> TypedTerm (fromTERM s trm) AsType (toType ty) ps
    Cas.Conditional t1 f t2 ps -> mkTerm whenElse whenType [typeOfTerm t1] ps $
        TupleTerm [fromTERM s t1, toTerm s f, fromTERM s t2] ps
    _ -> error "fromTERM"

typeOfTerm :: Cas.TERM f -> Type
typeOfTerm = toType . CasS.sortOfTerm
