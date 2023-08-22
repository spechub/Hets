{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/HasCASL2THFP_P.hs
Description :  Comorphism from HasCASL to THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from HasCASL to THFP_P.
-}

module Comorphisms.HasCASL2THFP_P where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Id
import Common.AS_Annotation
import Common.Utils (number)
import Common.DocUtils

import HasCASL.Logic_HasCASL
import HasCASL.Sublogic
import HasCASL.Le as HCLe
import HasCASL.As as HCAs
import HasCASL.AsUtils
import HasCASL.Builtin

import THF.As as THFAs
import THF.Logic_THF
import THF.Cons as THFCons
import THF.Sign as THFSign
import THF.Translate
import THF.HasCASL2THF0Buildins
import THF.Utils (typeToUnitaryType, typeToBinaryType,
                  typeToTopLevelType)
import qualified THF.Sublogic as SL

import Control.Monad

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import Data.Char (toLower)
import Data.Maybe

-- Question: are the remaining symbol variants translatable?

-- | The identity of the comorphism
data HasCASL2THFP_P = HasCASL2THFP_P deriving Show

instance Language HasCASL2THFP_P

instance Comorphism HasCASL2THFP_P
                HasCASL Sublogic
                BasicSpec Sentence SymbItems SymbMapItems
                Env Morphism Symbol RawSymbol ()
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic HasCASL2THFP_P = HasCASL
    sourceSublogic HasCASL2THFP_P = reqSubLogicForTHFP -- topLogic
    targetLogic HasCASL2THFP_P = THF
    mapSublogic HasCASL2THFP_P _ = Just SL.tHFP_P
    map_theory HasCASL2THFP_P = transTheory
    map_symbol HasCASL2THFP_P env s = propagateErrors "" $
     transSymbol env s
    -- isInclusionComorphism HasCASL2THF0_ST = True
    has_model_expansion HasCASL2THFP_P = True

reqSubLogicForTHFP :: Sublogic
reqSubLogicForTHFP = Sublogic
    { has_sub = False
    , has_part = False
    , has_eq = True
    , has_pred = True
    , type_classes = NoClasses
    , has_polymorphism = False
    , has_type_constructors = False
    , has_products = True
    , which_logic = HOL }

-- Translation of a Theory

transTheory :: (Env, [Named Sentence]) -> Result (SignTHF, [Named THFFormula])
transTheory (env, hcnsl) = do
    (typs, icm) <- transTypeMap $ HCLe.typeMap env
    cons <- transAssumps (HCLe.assumps env) icm
    (nsl, ids) <- foldM (fNSen icm) ([], Set.empty) hcnsl
    let ax = preDefAxioms ids ++ reverse nsl
        aCons = Map.union cons (preDefHCAssumps ids)
    syms <- mkSymbolMap typs aCons
    let sig = THFSign.emptySign { types = typs
                                , consts = aCons
                                , symbols = syms }
    return (sig , ax)
  where
    fNSen :: IdConstantMap -> ([Named THFFormula], IdSet)
                -> Named Sentence -> Result ([Named THFFormula], IdSet)
    fNSen icm p@(nsl, ids) hcns = case sentence hcns of
      Formula _ -> do
        (ns, nids) <- transNamedSentence (Just icm) ids env hcns
        return (ns : nsl, nids)
      s -> do
        appendDiags [mkDiag Hint "ignoring" s]
        return p

-- Translation methods for the components a signature

transTypeMap :: HCLe.TypeMap -> Result (THFSign.TypeMap, Map.Map Id Constant)
transTypeMap tm = foldM trans (Map.empty, Map.empty) (Map.toList tm)
    where
        trans :: (THFSign.TypeMap, Map.Map Id Constant) -> (Id, HCLe.TypeInfo)
                    -> Result (THFSign.TypeMap, Map.Map Id Constant)
        trans (ttm, icm) (i, ti) = do
         c <- transTypeId i
         ti' <- transTypeInfo ti c
         return (Map.insert c ti' ttm, Map.insert i c icm)

transTypeInfo :: HCLe.TypeInfo -> THFAs.Constant -> Result THFSign.TypeInfo
transTypeInfo ti c = transRawKind (HCLe.typeKind ti)
 >>= \ tk -> return THFSign.TypeInfo
    { THFSign.typeId = c
    , THFSign.typeName = mkTypesName c
    , THFSign.typeKind = tk
    , THFSign.typeAnno = THFAs.Null }

transRawKind :: HCAs.RawKind -> Result THFCons.Kind
transRawKind rk = case rk of
    ClassKind () -> return Kind
    _ -> mkError "Type constructors are not supported!" nullRange

transAssumps :: HCLe.Assumps -> Map.Map Id Constant -> Result THFSign.ConstMap
transAssumps am icm = foldM insertConsts Map.empty (Map.toList am)
    where
        insertConsts :: THFSign.ConstMap -> (Id, Set.Set OpInfo)
                        -> Result THFSign.ConstMap
        insertConsts m (name, ops) = case Set.toList ops of
            [OpInfo ts _ _] -> do
                ty <- transOp ts
                c <- transAssumpId name
                let ci = THFSign.ConstInfo
                        { THFSign.constId = c
                        , THFSign.constName = mkConstsName c
                        , THFSign.constType = ty
                        , THFSign.constAnno = THFAs.Null }
                return $ Map.insert c ci m
            infos -> foldM (\ m' (OpInfo ts _ _, i) -> do
                    ty <- transOp ts
                    c <- transAssumpsId name i
                    let ci = THFSign.ConstInfo
                            { THFSign.constId = c
                            , THFSign.constName = mkConstsName c
                            , THFSign.constType = ty
                            , THFSign.constAnno = THFAs.Null }
                    return $ Map.insert c ci m'
                ) m (number infos)
        transOp :: TypeScheme -> Result THFCons.Type
        transOp (TypeScheme _ op _) = transType icm op

-- a mapping between ids of hascasl types and their representation in THF
type IdConstantMap = Map.Map Id THFAs.Constant

genIdConstantMap :: Env -> Result IdConstantMap
genIdConstantMap e = foldM (\ icm (i, _) -> do
            c <- transTypeId i
            return $ Map.insert i c icm)
    Map.empty (Map.toList (HCLe.typeMap e))

transType :: IdConstantMap -> HCAs.Type -> Result THFCons.Type
transType icm hct = case getTypeAppl hct of
    (TypeName tid _ n, tys)
        | null tys && tid == unitTypeId -> return OType
        | isProductId tid -> liftM ProdType $
            mapM (transType icm) tys
        | List.length tys == 1 && tid == lazyTypeId ->
            if isUnitType $ head tys
            then return OType
            else fatal_error "THF0 does not support partiality." nullRange
        | List.length tys == 2 -> if isArrow tid then do
                [ts1, ts2] <- mapM (transType icm) tys
                case ts1 of
                    THFCons.MapType _ _ ->
                        return $ THFCons.MapType (THFCons.ParType ts1) ts2
                    _ -> return (THFCons.MapType ts1 ts2)
            else fatal_error ("Application of Types in Constants is not " ++
                                "possible in THF0: " ++ show tid) (getRange tid)
        | n == 0 && null tys ->
            maybe (fatal_error ("unknown Type" ++ show tid) nullRange)
                (return . THFCons.CType) (Map.lookup tid icm)
        | n < 0 && null tys -> fmap THFCons.VType (transVarId tid)
    t -> fatal_error ("transType: Not a translatable type: " ++ show t)
                    (getRange hct)

isUnitType :: HCAs.Type -> Bool
isUnitType t = case t of
    TypeName i _ _ -> myEqId i unitTypeId
    _ -> False

{- method used to add a type to the tail of a type
it is used e.g. to transform Types of predicates into function types
by adding the boolean-Type OType to the tail.
Example:
insLast OType (OType > A > IType)  -->  OType > A > IType > OType -}
insLast :: THFCons.Type -> THFCons.Type -> THFCons.Type
insLast it t = case t of
    MapType t1 t2 -> MapType t1 (insLast it t2)
    t1 -> MapType t1 it

mkSymbolMap :: THFSign.TypeMap -> THFSign.ConstMap -> Result THFSign.SymbolMap
mkSymbolMap tm cm = foldM ins (Map.map typeInfoToSymbol tm) (Map.toList cm)
    where
        ins :: THFSign.SymbolMap -> (THFAs.Constant, THFSign.ConstInfo)
                                -> Result THFSign.SymbolMap
        ins sm (c, ci) = if Map.member c sm then
                fatal_error ("Two symbols with the same name detected: " ++
                                show (pretty c)) nullRange
            else return $ Map.insert c (constInfoToSymbol ci) sm

typeInfoToSymbol :: THFSign.TypeInfo -> THFCons.SymbolTHF
typeInfoToSymbol ti = THFCons.Symbol
    { THFCons.symId = THFSign.typeId ti
    , THFCons.symName = THFSign.typeName ti
    , THFCons.symType = THFCons.ST_Type $ THFSign.typeKind ti }

constInfoToSymbol :: THFSign.ConstInfo -> THFCons.SymbolTHF
constInfoToSymbol ci = THFCons.Symbol
    { THFCons.symId = THFSign.constId ci
    , THFCons.symName = THFSign.constName ci
    , THFCons.symType = THFCons.ST_Const $ THFSign.constType ci }


-- Transation of Symbols

{- Not supported symbols:
 ClassAsItemType RawKind
 SuperClassSymbol Kind
 SuperTypeSymbol Id
 TypeKindInstance Kind
 TypeAliasSymbol Type
-}

transSymbol :: Env -> Symbol -> Result (Set.Set SymbolTHF)
transSymbol sig1 sym1 = case HCLe.symType sym1 of
        TypeAsItemType rk ->
            case maybeResult (transTypeId $ HCLe.symName sym1) of
                Nothing -> return Set.empty
                Just c -> do
                 rk' <- transRawKind rk
                 return $ Set.singleton THFCons.Symbol
                        { THFCons.symId = c
                        , THFCons.symName = mkTypesName c
                        , THFCons.symType = ST_Type rk' }
        OpAsItemType ts -> return $ tsHelper ts tsOpType
        PredAsItemType ts -> return $ tsHelper ts tsPredType
        _ -> return Set.empty
    where
        tsOpType :: IdConstantMap -> TypeScheme -> Result THFCons.Type
        tsOpType icm (TypeScheme _ t _) = transType icm t
        tsPredType :: IdConstantMap -> TypeScheme -> Result THFCons.Type
        tsPredType icm (TypeScheme _ t _) = fmap (insLast OType)
                                                (transType icm t)
        tsHelper :: TypeScheme -> (IdConstantMap -> TypeScheme
                                -> Result THFCons.Type) -> Set.Set SymbolTHF
        tsHelper ts f = case Map.lookup (HCLe.symName sym1) (assumps sig1) of
            Just a
                | Set.size a <= 0 -> Set.empty
                | Set.size a == 1 -> tsHelper2 ts
                                        (transAssumpId $ HCLe.symName sym1) f
                | Set.size a >= 2 -> case List.lookup ts (number
                                        (map HCLe.opType (Set.toList a))) of
                    Nothing -> Set.empty
                    Just num -> tsHelper2 ts
                                    (transAssumpsId (HCLe.symName sym1) num) f
            _ -> tsHelper2 ts (transAssumpId $ HCLe.symName sym1) f
        tsHelper2 :: TypeScheme -> Result THFAs.Constant -> (IdConstantMap
                    -> TypeScheme -> Result THFCons.Type) -> Set.Set SymbolTHF
        tsHelper2 t rc f = case maybeResult rc of
            Nothing -> Set.empty
            Just c -> case maybeResult (genIdConstantMap sig1) of
                Nothing -> Set.empty
                Just icm -> case maybeResult (f icm t) of
                    Nothing -> Set.empty
                    Just tt -> Set.singleton
                        THFCons.Symbol { THFCons.symId = c
                                       , THFCons.symName = mkConstsName c
                                       , THFCons.symType = ST_Const tt }


-- Translating methods for Sentences

transNamedSentence :: Maybe IdConstantMap -> IdSet -> Env -> Named Sentence
                            -> Result (Named THFFormula, IdSet)
transNamedSentence micm ids sig ns' = do
    icm <- maybe (genIdConstantMap sig) return micm
    let ns = reName (\ n -> case n of
                            [] -> n
                            x : xs -> toLower x : xs) ns'
    case sentence ns of
        Formula term -> do
            (lf, nids) <- transTerm sig icm ids term
            return ( ns {sentence = TF_THF_Logic_Formula lf
                        , senAttr = fromMaybe (error "THF.transNamedSentence")
                          $ transToTHFString (senAttr ns) }
                   , nids)
        _ -> error "Data types or program equations are not allowed in THF0."

getFormulaRole :: Named HCLe.Sentence -> FormulaRole
getFormulaRole ns =
    if isAxiom ns
    then if wasTheorem ns then Theorem else Axiom
    else Lemma

transTerm :: Env -> IdConstantMap -> IdSet -> HCAs.Term
                        -> Result (THFLogicFormula, IdSet)
transTerm e icm ids t = case t of
    QuantifiedTerm q gcdl t1 r -> myFmap (TLF_THF_Unitary_Formula .
        TUF_THF_Quantified_Formula) (transQuantifiedTerm e icm ids q gcdl t1 r)
    LambdaTerm tl p t1 r -> transLamdaTerm e icm ids tl p t1 r
    TypedTerm t1 tq ty r -> redTypedTerm t1 tq ty r >>=
        transTerm e icm ids
    ApplTerm t1 t2 r -> transApplTerm e icm ids t1 t2 r
    QualVar (VarDecl i _ _ _) -> fmap (TLF_THF_Unitary_Formula . TUF_THF_Atom
            . T0A_Variable) (transVarId i) >>= (\ lf -> return (lf, ids))
    QualOp ob pid ts tl ik r -> myFmap (TLF_THF_Unitary_Formula
            . TUF_THF_Atom . T0A_Constant) (transQualOp e ids ob pid ts tl ik r)
    TupleTerm ts' _ -> do
     (ts, nids) <- foldM (\ (ts, ids') t' -> do
      (t'', ids'') <- transTerm e icm ids' t'
      return (ts ++ [t''], ids'')) ([], ids) ts'
     return (TLF_THF_Unitary_Formula . TUF_THF_Tuple $ ts, nids)
    TermToken _ ->
            fatal_error "Missing translation for term tokens." (getRange t)
    AsPattern {} ->
            fatal_error "As patterns are not supported in THF0." (getRange t)
    LetTerm {} ->
            fatal_error "Let terms are not supported in THF0." (getRange t)
    CaseTerm {} ->
            fatal_error "Case statements are not supported in THF." (getRange t)
    _ ->
            fatal_error "HasCASL2THF0.transTerm" (getRange t)


redTypedTerm :: HCAs.Term -> TypeQual -> HCAs.Type -> Range -> Result HCAs.Term
redTypedTerm t1 tq1 _ r1 =
    if elem tq1 [Inferred, OfType]
    then case t1 of
        TypedTerm t2 tq2 ty2 r2 -> redTypedTerm t2 tq2 ty2 r2
        _ -> return t1
    else fatal_error "Typed terms are not supported in THF0." r1

transQualOp :: Env -> IdSet -> OpBrand -> PolyId -> TypeScheme
            -> [HCAs.Type] -> InstKind -> Range -> Result (Constant, IdSet)
transQualOp e ids _ (PolyId i _ _) ts _ _ r = do
    let nids = if elem i (map fst bList) then Set.insert i ids else ids
    case Map.lookup i (assumps e) of
        Just s
            | Set.size s <= 0 -> fatal_error ("unknown op: " ++ show i) r
            | Set.size s == 1 -> transAssumpId i >>= (\ c -> return (c, nids))
            | Set.size s >= 2 -> case List.lookup ts (number
                                        (map HCLe.opType (Set.toList s))) of
                    Nothing -> fatal_error ("unknown op: " ++ show i) r
                    Just num ->
                        transAssumpsId i num >>= (\ c -> return (c, nids))
        _ -> transAssumpId i >>= (\ c -> return (c, nids))

transApplTerm :: Env -> IdConstantMap -> IdSet -> HCAs.Term -> HCAs.Term
                    -> Range -> Result (THFLogicFormula, IdSet)
transApplTerm e icm ids t1 t2 r = do
    let at = ApplTerm t1 t2 r
    case myGetAppl at of
        Nothing -> fatal_error
          ("unexpected Term Application: " ++ showDoc at "") r
        Just (t3, i, tl1)
            | elem i [exEq, andId, orId, eqvId, implId, infixIf, resId] ->
                case tl1 of
                    [TupleTerm tl2 _] ->
                        myFmap (TLF_THF_Binary_Formula . TBF_THF_Binary_Tuple
                                . TBT_THF_Apply_Formula . reverse)
                           (foldM fTrmToUf ([], ids) (t3 : tl2))
                    _ -> fatal_error ("unexpected arguments " ++ show tl1 ++
                            " for the function " ++ show i) r
            | i == eqId -> case tl1 of
                [TupleTerm tl2 _] -> do
                  (ufs, ids') <- foldM fTrmToUf ([], ids) tl2
                  (uf1, uf2) <- case ufs of
                                   [uf1, uf2] -> return (uf1, uf2)
                                   _ -> fatal_error ("equality needs " ++
                                         "exactly 2 arguments") r
                  return (TLF_THF_Binary_Formula $ TBF_THF_Binary_Pair
                           uf1 Infix_Equality uf2, ids')
                _ -> fatal_error ("unexpected arguments " ++ show tl1 ++
                       " for equality") r
            | i == whenElse ->
               case tl1 of
                [TupleTerm [then_, cond, else_] _] ->
                 let then_' = mkLogTerm andId
                      (Range $ joinRanges [rangeSpan then_, rangeSpan cond])
                      cond then_
                     else_' = mkLogTerm andId
                      (Range $ joinRanges [rangeSpan else_, rangeSpan cond])
                      (ApplTerm (mkOpTerm negId notType)
                                cond (getRange cond)) else_
                 in transTerm e icm ids (mkLogTerm orId r then_' else_')
                _ -> fatal_error "invalid whenElse" r
            | otherwise -> myFmap (TLF_THF_Binary_Formula . TBF_THF_Binary_Tuple
                                    . TBT_THF_Apply_Formula . reverse)
                                (foldM fTrmToUf ([], ids) (t3 : tl1))
  where
    fTrmToUf :: ([THFUnitaryFormula], IdSet) -> HCAs.Term
                    -> Result ([THFUnitaryFormula], IdSet)
    fTrmToUf (ufl, oids) t = do
        (uf, nids) <- myFmap lfToUf (transTerm e icm oids t)
        return (uf : ufl, nids)

{- | decompose an 'ApplTerm' into an application of an operation and a
     list of arguments -}
myGetAppl :: HCAs.Term -> Maybe (HCAs.Term, Id, [HCAs.Term])
myGetAppl = thrdM reverse . getRevAppl where
    thrdM :: (c -> c) -> Maybe (a, b, c) -> Maybe (a, b, c)
    thrdM f = fmap ( \ (a, b, c) -> (a, b, f c))
    getRevAppl :: HCAs.Term -> Maybe (HCAs.Term, Id, [HCAs.Term])
    getRevAppl t = case t of
        TypedTerm trm q _ _ -> case q of
            InType -> Nothing
            _ -> getRevAppl trm
        QualVar (VarDecl i _ _ _) -> Just (t, i, [])
        QualOp _ (PolyId i _ _) _ _ _ _ -> Just (t, i, [])
        ApplTerm t1 t2 _ -> thrdM (t2 :) $ getRevAppl t1
        _ -> Nothing

transLamdaTerm :: Env -> IdConstantMap -> IdSet -> [HCAs.Term] -> Partiality
                        -> HCAs.Term -> Range -> Result (THFLogicFormula, IdSet)
transLamdaTerm e icm ids tl _ t _ = do
        vl <- mapM trVar tl
        (uf, nids) <- myFmap lfToUf (transTerm e icm ids t)
        return (TLF_THF_Unitary_Formula $ T0UF_THF_Abstraction vl uf, nids)
    where
        trVar :: HCAs.Term -> Result THFVariable
        trVar t1 = case t1 of
            TypedTerm t2 tq ty r -> redTypedTerm t2 tq ty r >>= trVar
            QualVar vd -> transVarDecl icm vd
            _ -> fatal_error ("Unexpected term: " ++ show t1
                            ++ " Expected variable.") (getRange t1)

transQuantifiedTerm :: Env -> IdConstantMap -> IdSet -> HCAs.Quantifier
                        -> [HCAs.GenVarDecl] -> HCAs.Term -> Range
                        -> Result (THFAs.THFQuantifiedFormula, IdSet)
transQuantifiedTerm e icm ids q gcdl t r = case q of
        Universal -> tqHelper T0Q_ForAll
        Existential -> tqHelper T0Q_Exists
        Unique ->
            fatal_error "Unique quantifications are not supported yet." r
            {- two possible translatione for uniqueness:
            1. Ex: x . P(x) /\ Not (Ex : x,y . (P(x) /\ P(y) /\ not (x = y)))
            2. Ex: x . (All : y . (P(y) <=> x = y)) -}
    where
        tqHelper :: THFAs.Quantifier
                        -> Result (THFAs.THFQuantifiedFormula, IdSet)
        tqHelper quant = do
            vl <- mapM (transGenVatDecl icm) gcdl
            myFmap (T0QF_THF_Quantified_Var quant vl . lfToUf)
                   (transTerm e icm ids t)

transGenVatDecl :: IdConstantMap -> GenVarDecl
                    -> Result THFVariable
transGenVatDecl icm gvd = case gvd of
    GenVarDecl vd -> transVarDecl icm vd
    GenTypeVarDecl (TypeArg _ _ _ _ _ _ r) ->
        fatal_error "GenTypeVarDecl not supported" r

transVarDecl :: IdConstantMap -> VarDecl -> Result THFVariable
transVarDecl icm (VarDecl i t _ _) = do
    v <- transVarId i
    tlt <- transType icm t >>= typeToTopLevelType
    return $ TV_THF_Typed_Variable v tlt

genTuple :: [THFCons.Type] -> Result THFAs.THFBinaryType
genTuple ts = case ts of
  [] -> fatal_error "Empty product type" nullRange
  [tp] -> typeToBinaryType tp
  _ -> fmap TBT_THF_Xprod_Type $ mapR typeToUnitaryType ts

-- THFLogicFormula to THFUnitaryFormula
lfToUf :: THFLogicFormula -> THFUnitaryFormula
lfToUf lf = case lf of
    TLF_THF_Unitary_Formula uf -> uf
    _ -> TUF_THF_Logic_Formula_Par lf

-- Helper

type IdSet = Set.Set Id

myFmap :: (a -> b) -> Result (a, IdSet) -> Result (b, IdSet)
myFmap fun res = do
    (something, ids) <- res
    return (fun something, ids)
