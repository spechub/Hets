{- |
Module      :  $Header$
Copyright   :  (c) Till Mossakowski and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

   
   The embedding comorphism from CASL to HasCASL.

-}

module Comorphisms.CASL2HasCASL where

import Logic.Logic
import Logic.Comorphism
import Common.Id
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- CASL
import CASL.Logic_CASL 
import CASL.Sublogic
import CASL.Sign
import qualified CASL.AS_Basic_CASL as Cas
import qualified CASL.Morphism as CasM

import HasCASL.Logic_HasCASL
import HasCASL.As
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.VarDecl
import HasCASL.Unify
import HasCASL.Morphism

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
               BasicSpec Term SymbItems SymbMapItems
               Env Morphism Symbol RawSymbol () where
    sourceLogic CASL2HasCASL = CASL
    sourceSublogic CASL2HasCASL = CASL_SL
                      { has_sub = True, -- simple subsorting in HasCASL
                        has_part = True,
                        has_cons = True,
                        has_eq = True,
                        has_pred = True,
                        which_logic = FOL
                      }
    targetLogic CASL2HasCASL = HasCASL
    targetSublogic CASL2HasCASL = ()
    map_sign CASL2HasCASL sig = let e = mapSig sig in Just (e, [])
    map_morphism CASL2HasCASL = Just . mapMor
    map_sentence CASL2HasCASL sig = Just . toTerm sig
    map_symbol CASL2HasCASL = Set.single . mapSym

toType :: Id -> Type
toType i = TypeName i star 0

fromOpType :: OpType -> FunKind -> TypeScheme
fromOpType ot ok = 
    let arrow = case ok of
		CASL.Sign.Total -> FunArr 
                CASL.Sign.Partial -> PFunArr
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
			  ((i, TySc $ fromOpType ot (opKind ot)),
			   (j, TySc $ mapTypeScheme tm $ fromOpType ot t)))
		    $ Map.toList $ CasM.fun_map m
	       f2 = map ( \ ((i, pt), j) -> 
			  let sc = TySc $ fromPredType pt
			  in ((i, sc), (j, mapTySc tm sc))) 
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
    Cas.Predication (Cas.Qual_pred_name i (Cas.Pred_type ts rs) ps) as qs ->
	let sc = simpleTypeScheme $ if null ts then logicalType 
		 else predType $ mkProductType (map toType ts) rs 
	    in ApplTerm (QualOp Pred (InstOpId i [] ps) sc ps)
	       (mkTupleTerm (map (fromTERM s) as) qs) qs 
    Cas.Definedness t ps -> mkTerm defId defType ps $ fromTERM s t 
    Cas.Membership t ty ps -> TypedTerm (fromTERM s t) InType (toType ty) ps
    Cas.Sort_gen_ax _ _ -> unitTerm trueId [] -- missing
    _ -> error "fromTERM"

fromOP_TYPE :: Cas.OP_TYPE -> TypeScheme
fromOP_TYPE ot = 
    let (args, res, ps, total, arr) = case ot of 
		   Cas.Total_op_type as rs qs -> (as, rs, qs, True, FunArr)
		   Cas.Partial_op_type as rs qs -> (as, rs, qs, False, PFunArr)
	resType = toType res
	in simpleTypeScheme $ if null args then 
	   if total then resType else LazyType resType ps
	   else FunType (mkProductType (map toType args) ps) arr resType ps

fromTERM :: Sign f e -> Cas.TERM f -> Term
fromTERM s t = case t of
    Cas.Qual_var v ty ps -> QualVar (simpleIdToId v) (toType ty) ps
    Cas.Application (Cas.Qual_op_name i ot ps) as qs  ->
	ApplTerm (QualOp Op (InstOpId i [] ps) (fromOP_TYPE ot) ps)
	     (mkTupleTerm (map (fromTERM s) as) qs) qs 
    Cas.Sorted_term trm ty ps -> 
	TypedTerm (fromTERM s trm) OfType (toType ty) ps
    Cas.Cast trm ty ps -> TypedTerm (fromTERM s trm) AsType (toType ty) ps
    Cas.Conditional t1 f t2 ps -> mkTerm whenElse whenType ps $
	TupleTerm [fromTERM s t1, toTerm s f, fromTERM s t2] ps
    _ -> error "fromTERM"
