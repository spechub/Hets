{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Static analysis for THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Static analysis for THF.
NOTE: This implementation covers only THF0!
-}

module THF.StaticAnalysisTHF (basicAnalysis) where

import THF.As as As
import THF.Cons
import THF.Print ()
import THF.PrintTHF
import THF.Sign

import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign
import Common.Lib.State

import Control.Monad

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

{-
QUESTION: how to treat fi_domain... in statAna
        how to handle SysType in isTypeConsistent
-}

-- it looks like the returned symbols inside the result are symbols that
-- were not "used" for the signature, so i propablly have to fix that.
-- Ask Christian.
basicAnalysis :: (BasicSpecTHF, SignTHF, GlobalAnnos) ->
        Result (BasicSpecTHF, ExtSign SignTHF SymbolTHF, [Named SentenceTHF])
basicAnalysis (BasicSpecTHF BSTHF _, _, _) =
    let err = mkDiag Error
            "Error: Static Analysis for general THF is not supported yet." ()
    in Result [err] Nothing
basicAnalysis (bs@(BasicSpecTHF BSTHF0 bs1), sig1, _) =
    let (diag1, bs2) = filterBS [] bs1
        (diag2, sig2, syms) = execState (fillSig bs2) (diag1, sig1, Set.empty)
        (diag3, ns) = getSentences bs2 (diag2, [])
    in Result (reverse diag3)           -- liste der  symbole ist noch falsch
            $ Just (bs, ExtSign sig2 syms, ns)

-- The diagnosis list must have a rverted order!
{- This functions delets all Comments and Includes because they are not needed
for the static analysis -}
filterBS :: [Diagnosis] -> [TPTP_THF] -> ([Diagnosis], [TPTP_THF])
filterBS d [] = (d, [])
filterBS d (t : rt) = case t of
    TPTP_Include i          -> let ds = (mkDiag Warning
                                            "Include will be ignored." i)
                               in filterBS (ds : d) rt
    TPTP_Comment _          -> filterBS d rt
    TPTP_Defined_Comment _  -> filterBS d rt
    TPTP_System_Comment _   -> filterBS d rt
    TPTP_Header _           -> filterBS d rt
    _                       -> let (diag, thf) = filterBS d rt
                               in (diag, t : thf)

-- IMPORTENT: the diag-list must have a reverted order
-- filter stuff not usefull things, like comments
fillSig :: [TPTP_THF] -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
fillSig [] = return ()
fillSig bs = mapM_ fillSingleType bs >> mapM_ fillSingleConst bs
    where
        fillSingleType t = case t of
            TPTP_THF_Annotated_Formula _ fr tf _ -> case fr of
                Type    ->
                    when (isType tf) $ case makeKind tf of
                        Right d         -> appandDiag d
                        Left (k, c, tc) -> insertType k c tc
                _       -> return ()
            _   -> return ()
        fillSingleConst t = case t of
            TPTP_THF_Annotated_Formula _ fr tf _ -> case fr of
                Type    ->
                    unless (isType tf) $ case makeType tf of
                        Right d             -> appandDiag d
                        Left (ty, c, tc)    -> insertConst ty c tc
                _       -> return ()
            _ -> return ()

appandDiag :: Diagnosis -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
appandDiag d = modify (\ (diag, s, syms) -> (d : diag, s, syms))

insertType :: Kind -> Constant -> THFTypedConst
                    -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
insertType k c tc = do
    (diag, sig, syms) <- get
    if sigHasConstSymbol c sig then appandDiag $ mkDiag Error
        "Duplicate definition a symbol as Type an Constant. Symbol: " c
     else
        if sigHasTypeSymbol c sig then
            unless (sigHasSameKind c k sig) $ appandDiag $
                mkDiag Error ("A Type with the same identifier"
                    ++ "but another Kind is already inside the signature") c
         else do -- everythign is fine
            let ti = TypeInfo { typeName = c, typeKind = k, typeDef = Just tc }
                sym = Symbol { symName = c, symType = ST_Type k }
            put (diag, sig { types = Map.insert c ti (types sig)
                           , symbols = Map.insert c sym (symbols sig) }
                , Set.insert sym syms)

insertConst :: Type -> Constant -> THFTypedConst
                    -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
insertConst t c tc = do
    (diag, sig, syms) <- get
    if sigHasTypeSymbol c sig then appandDiag $ mkDiag Error
        "Duplicate definition a symbol as Type an Constant. Symbol: " c
     else case isTypeConsistent t sig of
        Just d  -> appandDiag d
        _       ->
            if sigHasConstSymbol c sig then
                unless (sigHasSameType c t sig) $ appandDiag $ mkDiag Error
                ("A Constant with the same" ++
                "identifier but another Type is already inside the signature") c
            else do -- everything is fine
                let ci = ConstInfo { constName = c, constType = t
                                   , constDef = Just tc }
                    sym = Symbol { symName = c, symType = ST_Const t }
                put (diag, sig { consts = Map.insert c ci (consts sig)
                               , symbols = Map.insert c sym (symbols sig) }
                    , Set.insert sym syms)

-- Check if a type symbol is already inside the sig
sigHasTypeSymbol :: Constant -> SignTHF -> Bool
sigHasTypeSymbol c sig = Map.member c (types sig)

-- This Method is ment to be used after sigHasTypeSymbol
-- Check if a type symbol with the same kind is inside the Sig
-- If this is not the case me have a problem!
sigHasSameKind :: Constant -> Kind -> SignTHF -> Bool
sigHasSameKind c k sig = typeKind (types sig Map.! c) == k

-- Check if a const symbol is already inside the sig
sigHasConstSymbol :: Constant -> SignTHF -> Bool
sigHasConstSymbol c sig = Map.member c (consts sig)

-- This Method is ment to be used after sigHasConstSymbol
-- Check if a const symbol with the same type is inside the Sig
-- If this is not the case me have a problem!
sigHasSameType :: Constant -> Type -> SignTHF -> Bool
sigHasSameType c t sig = constType (consts sig Map.! c) == t

-- check if all cTypes inside the given Type are elements of the signaure.
-- Nothing means that everything is fine, otherwise Just diag will be returned.
isTypeConsistent :: Type -> SignTHF -> Maybe Diagnosis
isTypeConsistent t sig = case t of
    MapType t1 t2   ->
        let tc1 = isTypeConsistent t1 sig
            tc2 = isTypeConsistent t2 sig
        in if isNothing tc1 then tc2 else tc1
    CType c         -> if sigHasTypeSymbol c sig then Nothing
                       else Just $ mkDiag Error "Unknown type: " c
    SType _         -> Nothing -- how to handle these?
    _               -> Nothing

{- Get all sentences from the content of the BasicSpecTHF-}
-- QUESTION: Are conjecures sentences?
getSentences :: [TPTP_THF] -> ([Diagnosis], [Named SentenceTHF])
                           -> ([Diagnosis], [Named SentenceTHF])
getSentences [] dn = dn
getSentences (t : rt) dn@(d, ns) = case t of
    TPTP_THF_Annotated_Formula _ fr _ _ -> case fr of
        Type    -> getSentences rt dn
        Unknown -> let diag = (mkDiag Warning
                        "THFFormula with type \'unknown\' will be ignored." t)
                   in getSentences rt (diag : d, ns)
        Plain   -> let diag = (mkDiag Warning
                        "THFFormula with type \'plain\' will be ignored." t)
                   in getSentences rt (diag : d, ns)
        _       -> let (d1, ns1) = getSentences rt dn
                   in (d1, tptpthfToNS t : ns1)
    _ -> getSentences rt dn

-- make sure the formulaRole is not Type, Unknown or Plain
tptpthfToNS :: TPTP_THF -> Named SentenceTHF
tptpthfToNS t = case formulaRoleAF t of
    Definition          -> SenAttr { senAttr = show $ printTHF $ nameAF t
                          , isAxiom = True, isDef = True, wasTheorem = False
                          , simpAnno = Nothing, attrOrigin = Nothing
                          , sentence = thfFormulaAF t }
    Conjecture          -> SenAttr { senAttr = show $ printTHF $ nameAF t
                          , isAxiom = False, isDef = False, wasTheorem = False
                          , simpAnno = Nothing, attrOrigin = Nothing
                          , sentence = thfFormulaAF t }
    Negated_Conjecture  -> SenAttr { senAttr = show $ printTHF $ nameAF t
                          , isAxiom = False, isDef = False, wasTheorem = False
                          , simpAnno = Nothing, attrOrigin = Nothing
                          , sentence = thfFormulaAF t }
    _                   -> makeNamed (show $ printTHF $ nameAF t)
                                            (thfFormulaAF t)

-- This mathod generates the kind of a Type-Formula
makeKind :: THFFormula -> Either (Kind, Constant, THFTypedConst) Diagnosis
makeKind t = maybe (Right $ mkDiag Error "Error while parsing the Kind of:" t)
                Left (thfFormulaToKind t)

thfFormulaToKind :: THFFormula -> Maybe (Kind, Constant, THFTypedConst)
thfFormulaToKind (T0F_THF_Typed_Const tc) = thfTypedConstToKind tc
thfFormulaToKind _  = Nothing

thfTypedConstToKind :: THFTypedConst -> Maybe (Kind, Constant, THFTypedConst)
thfTypedConstToKind (T0TC_THF_TypedConst_Par tcp) =  thfTypedConstToKind tcp
thfTypedConstToKind tc@(T0TC_Typed_Const c tlt) =
            maybe Nothing (\ k -> Just (k, c, tc))
                (thfTopLevelTypeToKind tlt)

thfTopLevelTypeToKind :: THFTopLevelType -> Maybe Kind
thfTopLevelTypeToKind tlt = case tlt of
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeToKind bt
    T0TLT_Defined_Type _        -> Just Kind
    T0TLT_System_Type st        -> Just $ SysType st
    _                           -> Nothing

thfBinaryTypeToKind :: THFBinaryType -> Maybe Kind
thfBinaryTypeToKind bt = case bt of
    TBT_THF_Mapping_Type []         -> Nothing
    TBT_THF_Mapping_Type (_ : [])   -> Nothing
    TBT_THF_Mapping_Type mt         -> thfMappingTypeToKind mt
    T0BT_THF_Binary_Type_Par btp    -> thfBinaryTypeToKind btp
    _                               -> Nothing

thfMappingTypeToKind :: [THFUnitaryType] -> Maybe Kind
thfMappingTypeToKind [] = Nothing
thfMappingTypeToKind (u : []) = thfUnitaryTypeToKind u
thfMappingTypeToKind (u : ru) =
    let k1 = thfUnitaryTypeToKind u
        k2 = (thfMappingTypeToKind ru)
    in if isJust k1 && isJust k2
       then Just $ MapKind (fromJust k1) (fromJust k2) nullRange
       else Nothing

thfUnitaryTypeToKind :: THFUnitaryType -> Maybe Kind
thfUnitaryTypeToKind ut = case ut of
    T0UT_THF_Binary_Type_Par bt -> thfBinaryTypeToKind bt
    T0UT_Defined_Type _         -> Just Kind
    T0UT_System_Type st         -> Just $ SysType st
    _                           -> Nothing

-- get The Type of a Constant
makeType :: THFFormula -> Either (Type, Constant, THFTypedConst) Diagnosis
makeType t = maybe (Right $ mkDiag Error "Error while parsing the Type of:" t)
                Left (thfFormulaToType t)

thfFormulaToType :: THFFormula -> Maybe (Type, Constant, THFTypedConst)
thfFormulaToType (T0F_THF_Typed_Const tc) = thfTypedConstToType tc
thfFormulaToType _  = Nothing

thfTypedConstToType :: THFTypedConst -> Maybe (Type, Constant, THFTypedConst)
thfTypedConstToType (T0TC_THF_TypedConst_Par tcp) =  thfTypedConstToType tcp
thfTypedConstToType tc@(T0TC_Typed_Const c tlt) =
            maybe Nothing (\ t -> Just (t, c, tc))
                (thfTopLevelTypeToType tlt)

thfTopLevelTypeToType :: THFTopLevelType -> Maybe Type
thfTopLevelTypeToType tlt = case tlt of
    T0TLT_Defined_Type dt       -> thfDefinedTypeToType dt
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeToType bt
    T0TLT_Constant c            -> Just $ CType c
    T0TLT_System_Type st        -> Just $ SType st
    _                           -> Nothing

thfDefinedTypeToType :: DefinedType -> Maybe Type
thfDefinedTypeToType dt = case dt of
    DT_oType    -> Just OType
    DT_o        -> Just OType
    DT_iType    -> Just TType
    DT_i        -> Just IType
    DT_tType    -> Just TType
    _           -> Nothing

thfBinaryTypeToType :: THFBinaryType -> Maybe Type
thfBinaryTypeToType bt = case bt of
    TBT_THF_Mapping_Type []         -> Nothing
    TBT_THF_Mapping_Type (_ : [])   -> Nothing
    TBT_THF_Mapping_Type mt         -> thfMappingTypeToType mt
    T0BT_THF_Binary_Type_Par btp    -> thfBinaryTypeToType btp
    _                               -> Nothing

thfMappingTypeToType :: [THFUnitaryType] -> Maybe Type
thfMappingTypeToType [] = Nothing
thfMappingTypeToType (u : []) = thfUnitaryTypeToType u
thfMappingTypeToType (u : ru) =
    let k1 = thfUnitaryTypeToType u
        k2 = (thfMappingTypeToType ru)
    in if isJust k1 && isJust k2
       then Just $ MapType (fromJust k1) (fromJust k2)
       else Nothing

thfUnitaryTypeToType :: THFUnitaryType -> Maybe Type
thfUnitaryTypeToType ut = case ut of
    T0UT_THF_Binary_Type_Par bt -> thfBinaryTypeToType bt
    T0UT_Defined_Type dt        -> thfDefinedTypeToType dt
    T0UT_Constant c             -> Just $ CType c
    T0UT_System_Type st         -> Just $ SType st
    _                           -> Nothing

-- Questin is this a type too: c : $tType > $tType
isType :: THFFormula -> Bool
isType tf = case tf of
    T0F_THF_Typed_Const tc  -> thfTypedConstIsType tc
    _                       -> False

thfTypedConstIsType :: THFTypedConst -> Bool
thfTypedConstIsType tc = case tc of
    T0TC_THF_TypedConst_Par tcp -> thfTypedConstIsType tcp
    T0TC_Typed_Const _ tlt      -> thfTopLevelTypeIsType tlt

thfTopLevelTypeIsType :: THFTopLevelType -> Bool
thfTopLevelTypeIsType tlt = case tlt of
    T0TLT_Defined_Type dt       -> thfDefinedTypeIsType dt
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeIsType bt
    T0TLT_System_Type _         -> True
    _                           -> False

thfDefinedTypeIsType :: DefinedType -> Bool
thfDefinedTypeIsType dt = case dt of
    DT_tType    -> True
    _           -> False

thfBinaryTypeIsType :: THFBinaryType -> Bool
thfBinaryTypeIsType bt = case bt of
    TBT_THF_Mapping_Type []         -> False
    TBT_THF_Mapping_Type (_ : [])   -> False
    TBT_THF_Mapping_Type mt         -> thfMappingTypeIsType mt
    T0BT_THF_Binary_Type_Par btp    -> thfBinaryTypeIsType btp
    _                               -> False

thfMappingTypeIsType :: [THFUnitaryType] -> Bool
thfMappingTypeIsType mt = case mt of
    []          -> False
    (u : [])    -> thfUnitaryTypeIsType u
    (u : ru)    -> thfUnitaryTypeIsType u && thfMappingTypeIsType ru

thfUnitaryTypeIsType :: THFUnitaryType -> Bool
thfUnitaryTypeIsType ut = case ut of
    T0UT_Defined_Type dt        -> thfDefinedTypeIsType dt
    T0UT_THF_Binary_Type_Par bt -> thfBinaryTypeIsType bt
    T0UT_System_Type _          -> True
    _                           -> False
