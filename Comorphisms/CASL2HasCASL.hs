{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Christian Maeder and Uni Bremen 2003
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from CASL to HasCASL.
-}

module Comorphisms.CASL2HasCASL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import Common.Lib.State
import Common.AS_Annotation
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import CASL.Sublogic as CasSub
import CASL.Sign
import qualified CASL.AS_Basic_CASL as Cas
import qualified CASL.Morphism as CasM

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.VarDecl
import HasCASL.AsUtils
import HasCASL.Morphism
import HasCASL.Sublogic as HasSub

-- | The identity of the comorphism
data CASL2HasCASL = CASL2HasCASL deriving (Show)

instance Language CASL2HasCASL -- default definition is okay

instance Comorphism CASL2HasCASL
               CASL CASL_Sublogics
               CASLBasicSpec CASLFORMULA Cas.SYMB_ITEMS Cas.SYMB_MAP_ITEMS
               CASLSign 
               CASLMor
               CasM.Symbol CasM.RawSymbol ()
               HasCASL HasCASL_Sublogics
               BasicSpec Sentence SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic CASL2HasCASL = CASL
    sourceSublogic CASL2HasCASL = CASL_SL
                      { CasSub.has_sub = True, -- simple subsorting in HasCASL
                        CasSub.has_part = True,
                        CasSub.has_cons = True,
                        CasSub.has_eq = True,
                        CasSub.has_pred = True,
                        CasSub.which_logic = CasSub.FOL
                      }
    targetLogic CASL2HasCASL = HasCASL
    targetSublogic CASL2HasCASL = HasSub.top
    map_morphism CASL2HasCASL = return . mapMor
    map_sentence CASL2HasCASL sig = return . toSentence sig
    map_symbol CASL2HasCASL = Set.singleton . mapSym
    map_theory CASL2HasCASL = return . mapTheory

toType :: Id -> Type
toType i = TypeName i star 0

fromOpType :: OpType -> Cas.FunKind -> TypeScheme
fromOpType ot ok = 
    let arrow = case ok of
                Cas.Total -> FunArr 
                Cas.Partial -> PFunArr
        args = map toType $ opArgs ot
        arg = mkProductType args []
        res = toType $ opRes ot
    in simpleTypeScheme $ if null args then res 
       else FunType arg arrow res []

fromPredType :: PredType -> TypeScheme
fromPredType pt = 
    let args = map toType $ predArgs pt
        arg = mkProductType args []
    in simpleTypeScheme $ if null args then logicalType else predType arg

mapTheory :: (Sign f e, [Named (Cas.FORMULA f)]) -> (Env, [Named Sentence])
mapTheory (sig, sents) = 
    let env = mapSig sig
        newSents = map (mapNamed (toSentence sig)) sents 
        dts = concatMap ( \ ns -> case sentence ns of
                          DatatypeSen ds -> ds
                          _ ->  []) newSents
        constr = concatMap ( \ (DataEntry im i _ _ alts) ->
                         let j = Map.findWithDefault i i im in
                         map ( \ (Construct o args p _sels) ->
                               (o, j, getConstrType (j, [], star) p
                                     $ map (mapType im) args)) alts) dts
        newEnv = execState (mapM_ ( \ (mo, j, ty) -> case mo of
                    Just o -> addOpId o (simpleTypeScheme ty) [] 
                                  $ ConstructData j
                    Nothing -> return Nothing) constr) env
        in (newEnv, newSents)

mapSig :: Sign f e -> Env
mapSig sign = 
    let f1 = concatMap ( \ (i, s) -> 
                   map ( \ ty -> (i, fromOpType ty (opKind ty), NoOpDefn Op))
                         $ Set.toList s) $ Map.toList $ opMap sign
        f2 = concatMap ( \ (i, s) -> 
                   map ( \ ty -> (i, fromPredType ty, NoOpDefn Pred))
                         $ Set.toList s) $ Map.toList $ predMap sign
     in execState (mapM_ ( \ (i, sc, defn) -> addOpId i sc [] defn)
                   (f2 ++ f1))
     initialEnv { classMap = Map.empty,
                  typeMap = Map.fromList $ map 
                  ( \ s -> (s, starTypeInfo 
                            { superTypes = map toType 
                            $ Set.toList $ supersortsOf s sign
                            })) $ Set.toList $ sortSet sign }

mapMor :: CasM.Morphism f e m -> Morphism
mapMor m = let tm = CasM.sort_map m 
               f1 = map ( \ ((i, ot), (j, t)) -> 
                          ((i, fromOpType ot (opKind ot)),
                           (j, mapTypeScheme tm 
                                    $ fromOpType ot t)))
                    $ Map.toList $ CasM.fun_map m
               f2 = map ( \ ((i, pt), j) -> 
                          let sc = fromPredType pt
                          in ((i, sc), (j, mapTypeScheme tm sc))) 
                    $ Map.toList $ CasM.pred_map m
            in (mkMorphism (mapSig $ CasM.msource m) (mapSig $ CasM.mtarget m))
           { typeIdMap = tm , funMap = Map.fromList (f2 ++ f1) }

mapSym :: CasM.Symbol -> Symbol
mapSym s = let i = CasM.symName s in 
    case CasM.symbType s of
    CasM.OpAsItemType ot -> 
        idToOpSymbol initialEnv i $ fromOpType ot $ opKind ot
    CasM.PredAsItemType pt -> idToOpSymbol initialEnv i $ fromPredType pt
    CasM.SortAsItemType -> idToTypeSymbol initialEnv i star
toQuant :: Cas.QUANTIFIER -> Quantifier
toQuant Cas.Universal = Universal 
toQuant Cas.Existential = Existential
toQuant Cas.Unique_existential = Unique

toVarDecl :: Cas.VAR_DECL -> [GenVarDecl]
toVarDecl (Cas.Var_decl vs s ps) =  
           map ( \ i -> GenVarDecl $ 
                 VarDecl (simpleIdToId i) (toType s) Other ps) vs

toSentence :: Sign f e -> Cas.FORMULA f -> Sentence 
toSentence sig f = case f of 
   Cas.Sort_gen_ax cs b -> let 
       (sorts, ops, smap) = Cas.recover_Sort_gen_ax cs
       genKind = if b then Free else Generated
       mapPart :: Cas.FunKind -> Partiality
       mapPart cp = case cp of
                Cas.Total -> HasCASL.As.Total
                Cas.Partial -> HasCASL.As.Partial
       in DatatypeSen 
          $ map ( \ s -> DataEntry (Map.fromList smap) s genKind []
                          (map ( \ (i, t, ps) -> 
                               let args = opArgs t in 
                               Construct (Just i) 
                                 (if null args then []
                                  else [mkProductType (map toType args) ps])
                               (mapPart $ opKind t) [])
                          $ filter ( \ (_, t, _) -> opRes t == s) 
                                $ map ( \ (Cas.Qual_op_name i t ps) -> 
                                      (i, toOpType t, ps)) ops)) sorts
   _ -> Formula $ toTerm sig f

toTerm :: Sign f e -> Cas.FORMULA f -> Term 
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
    Cas.Negation frm ps -> mkTerm notId notType ps $ toTerm s frm
    Cas.True_atom ps -> unitTerm trueId ps
    Cas.False_atom ps -> unitTerm falseId ps
    Cas.Existl_equation t1 t2 ps -> 
        mkEqTerm exEq ps (fromTERM s t1) $ fromTERM s t2
    Cas.Strong_equation t1 t2 ps -> 
        mkEqTerm eqId ps (fromTERM s t1) $ fromTERM s t2
    Cas.Predication (Cas.Qual_pred_name i (Cas.Pred_type ts rs) ps) args qs ->
        let sc = simpleTypeScheme $ if null ts then logicalType 
                 else predType $ mkProductType (map toType ts) rs 
            p = QualOp Pred (InstOpId i [] ps) sc ps
            in if null args then p else 
               ApplTerm p (mkTupleTerm (map (fromTERM s) args) qs) qs 
    Cas.Definedness t ps -> mkTerm defId defType ps $ fromTERM s t 
    Cas.Membership t ty ps -> TypedTerm (fromTERM s t) InType (toType ty) ps
    _ -> error "fromTERM"

fromOP_TYPE :: Cas.OP_TYPE -> TypeScheme
fromOP_TYPE ot = 
    let (args, res, ps, total, arr) = case ot of 
                   Cas.Op_type Cas.Total as rs qs -> 
                       (as, rs, qs, True, FunArr)
                   Cas.Op_type Cas.Partial as rs qs -> 
                       (as, rs, qs, False, PFunArr)
        resType = toType res
        in simpleTypeScheme $ if null args then 
           if total then resType else LazyType resType ps
           else FunType (mkProductType (map toType args) ps) arr resType ps

fromTERM :: Sign f e -> Cas.TERM f -> Term
fromTERM s t = case t of
    Cas.Qual_var v ty ps -> 
        QualVar $ VarDecl (simpleIdToId v) (toType ty) Other ps
    Cas.Application (Cas.Qual_op_name i ot ps) args qs  ->
        let o = QualOp Op (InstOpId i [] ps) (fromOP_TYPE ot) ps in
        if null args then o else
        ApplTerm o (mkTupleTerm (map (fromTERM s) args) qs) qs 
    Cas.Sorted_term trm ty ps -> 
        TypedTerm (fromTERM s trm) OfType (toType ty) ps
    Cas.Cast trm ty ps -> TypedTerm (fromTERM s trm) AsType (toType ty) ps
    Cas.Conditional t1 f t2 ps -> mkTerm whenElse whenType ps $
        TupleTerm [fromTERM s t1, toTerm s f, fromTERM s t2] ps
    _ -> error "fromTERM"
