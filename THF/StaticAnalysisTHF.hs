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

module THF.StaticAnalysisTHF (basicAnalysis,thfTopLevelTypeToType) where

import THF.As as As
import THF.Cons
import THF.Print ()
import THF.Sign

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign
import Common.Lib.State
import Common.DocUtils

import Control.Monad

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

--------------------------------------------------------------------------------
-- Questions:
--      * how to handle SysType in isTypeConsistent?
-- Todo:
--      * find out what fi_domain, fi_predicates and fi_functors are and try
--        to somehow support them
--------------------------------------------------------------------------------

-- The main method for the static analysis
basicAnalysis :: (BasicSpecTHF, SignTHF, GlobalAnnos) ->
        Result (BasicSpecTHF, ExtSign SignTHF SymbolTHF, [Named THFFormula])
basicAnalysis (bs@(BasicSpecTHF bs1), sig1, _) =
    let (diag1, bs2) = filterBS [] bs1
        (diag2, sig2, syms) = execState (fillSig bs2) (diag1, sig1, Set.empty)
        (diag3, ns) = getSentences bs2 (diag2, [])
    in Result (reverse diag3) $ Just (bs, ExtSign sig2 syms, ns)

-- This functions delets all Comments and Includes because they are not needed
-- for the static analysis
-- The diagnosis list has a reverted order!
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

-- Append the Signature by the Types and Constants given inside the basic spec
fillSig :: [TPTP_THF] -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
fillSig [] = return ()
fillSig bs = mapM_ fillSingleType bs >> mapM_ fillSingleConst bs
    where
        fillSingleType t = case t of
            TPTP_THF_Annotated_Formula n fr tf a -> case fr of
                Type    ->
                    when (isType tf) $ case makeKind tf of
                        Right d         -> appandDiag d
                        Left (k, c) -> insertType c n k a
                _       -> return ()
            _   -> return ()
        fillSingleConst t = case t of
            TPTP_THF_Annotated_Formula n fr tf a -> case fr of
                Type    ->
                    unless (isType tf) $ case makeType tf of
                        Right d             -> appandDiag d
                        Left (ty, c)    -> insertConst c n ty a
                _       -> return ()
            _ -> return ()

-- Append the Diagnosis-List by the given Diagnosis
-- The new diag will be put on top of the existing list.
appandDiag :: Diagnosis -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
appandDiag d = modify (\ (diag, s, syms) -> (d : diag, s, syms))

-- insert the given type into the Signature
insertType :: Constant -> As.Name -> Kind -> Annotations
                    -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
insertType c n k a = do
    (diag, sig, syms) <- get
    if sigHasConstSymbol c sig then appandDiag $ mkDiag Error
        "Duplicate definition a symbol as Type an Constant. Symbol: " c
     else
        if sigHasTypeSymbol c sig then
            unless (sigHasSameKind c k sig) $ appandDiag $
                mkDiag Error ("A Type with the same identifier"
                    ++ "but another Kind is already inside the signature") c
         else do -- everythign is fine
            let ti = TypeInfo { typeId = c, typeName = n, typeKind = k
                              , typeAnno = a }
                sym = Symbol { symId = c, symName = n, symType = ST_Type k }
            put (diag, sig { types = Map.insert c ti (types sig)
                           , symbols = Map.insert c sym (symbols sig) }
                , Set.insert sym syms)

-- insert the given constant into the Signature
insertConst :: Constant -> As.Name -> Type -> Annotations
                    -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
insertConst c n t a = do
    (diag, sig, syms) <- get
    if sigHasTypeSymbol c sig then appandDiag $ mkDiag Error
        "Duplicate definition a symbol as Type an Constant. Symbol: " c
     else case isTypeConsistent t sig of
        Just d  -> appandDiag d
        _       ->
            if sigHasConstSymbol c sig then
                unless (sigHasSameType c t sig) $ appandDiag $ mkDiag Error
                ("A Constant with the same identifier but another " ++
                 "Type is already inside the signature") c
            else do -- everything is fine
                let ci = ConstInfo { constId = c, constName = n, constType = t
                                   , constAnno = a }
                    sym = Symbol { symId = c, symName = n
                                 , symType = ST_Const t }
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
    ParType t1      -> isTypeConsistent t1 sig
    CType c         -> if sigHasTypeSymbol c sig then Nothing
                       else Just $ mkDiag Error "Unknown type: " c
    ProdType ts     -> let ds = map (\tp -> isTypeConsistent tp sig) ts
                       in case catMaybes ds of
                           []    -> Nothing
                           m : _ -> Just m
    SType _         -> Nothing -- how to handle these?
    _               -> Nothing

--------------------------------------------------------------------------------
-- Extract the sentences from the basic spec
--------------------------------------------------------------------------------

-- Get all sentences from the content of the BasicSpecTH
-- The diag list has a reverted order.
getSentences :: [TPTP_THF] -> ([Diagnosis], [Named THFFormula])
                           -> ([Diagnosis], [Named THFFormula])
getSentences [] dn = dn
getSentences (t : rt) dn@(d, ns) = case t of
    TPTP_THF_Annotated_Formula _ fr _ _ -> case fr of
        Type    -> getSentences rt dn
        Unknown         ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'unknown\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        Plain           ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'plain\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        Fi_Domain       ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'fi_domain\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        Fi_Functors     ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'fi_functors\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        Fi_Predicates   ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'fi_predicates\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        Assumption      ->
            let diag = (mkDiag Warning
                    "THFFormula with role \'assumption\' will be ignored." t)
            in getSentences rt (diag : d, ns)
        _               ->
            let (d1, ns1) = getSentences rt dn
            in (d1, tptpthfToNS t : ns1)
    _ -> getSentences rt dn

-- Precondition: The formulaRole must not be Type, Unknown, Plain, Fi_Domain
-- Fi_Functors, Fi_Predicates or Assumption
-- (They are filtered out in getSentences)
tptpthfToNS :: TPTP_THF -> Named THFFormula
tptpthfToNS t = case formulaRoleAF t of
    Definition          ->
           SenAttr { senAttr = show $ pretty $ nameAF t , isAxiom = True
                   , isDef = True, wasTheorem = False, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    Conjecture          ->
           SenAttr { senAttr = show $ pretty $ nameAF t, isAxiom = False
                   , isDef = False, wasTheorem = False, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    Negated_Conjecture  ->
           SenAttr { senAttr = show $ pretty $ nameAF t, isAxiom = False
                   , isDef = False, wasTheorem = False, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    Theorem             ->
           SenAttr { senAttr = show $ pretty $ nameAF t , isAxiom = True
                   , isDef = False, wasTheorem = True, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    Lemma               ->
           SenAttr { senAttr = show $ pretty $ nameAF t , isAxiom = True
                   , isDef = False, wasTheorem = True, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    Hypothesis          -> --isAxiom = false
           SenAttr { senAttr = show $ pretty $ nameAF t , isAxiom = False
                   , isDef = False, wasTheorem = False, simpAnno = Nothing
                   , attrOrigin = Nothing, sentence = thfFormulaAF t }
    _                   -> -- Axiom
           makeNamed (show $ pretty $ nameAF t) (thfFormulaAF t)


--------------------------------------------------------------------------------
-- Get the Kind of a type
--------------------------------------------------------------------------------

makeKind :: THFFormula -> Either (Kind, Constant) Diagnosis
makeKind t = maybe (Right $ mkDiag Error "Error while parsing the Kind of:" t)
                Left (thfFormulaToKind t)

thfFormulaToKind :: THFFormula -> Maybe (Kind, Constant)
thfFormulaToKind (T0F_THF_Typed_Const tc) = thfTypedConstToKind tc
thfFormulaToKind _  = Nothing

thfTypedConstToKind :: THFTypedConst -> Maybe (Kind, Constant)
thfTypedConstToKind (T0TC_THF_TypedConst_Par tcp) = thfTypedConstToKind tcp
thfTypedConstToKind (T0TC_Typed_Const c tlt) =
            maybe Nothing (\ k -> Just (k, c))
                (thfTopLevelTypeToKind tlt)

thfTopLevelTypeToKind :: THFTopLevelType -> Maybe Kind
thfTopLevelTypeToKind tlt = case tlt of
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeToKind bt
    T0TLT_Defined_Type _        -> Just Kind
    T0TLT_System_Type st        -> Just $ SysType st
    T0TLT_Variable v            -> Just $ VKind v
    _                           -> Nothing

thfBinaryTypeToKind :: THFBinaryType -> Maybe Kind
thfBinaryTypeToKind bt = case bt of
    TBT_THF_Mapping_Type []         -> Nothing
    TBT_THF_Mapping_Type (_ : [])   -> Nothing
    TBT_THF_Mapping_Type mt         -> thfMappingTypeToKind mt
    T0BT_THF_Binary_Type_Par btp    -> fmap ParKind (thfBinaryTypeToKind btp)
    TBT_THF_Xprod_Type []           -> Nothing
    TBT_THF_Xprod_Type (u : [])     -> thfUnitaryTypeToKind u
    TBT_THF_Xprod_Type us           -> let us' = map thfUnitaryTypeToKind us
                                       in if all isJust us' then
                                           (Just . ProdKind) $ map fromJust us'
                                          else Nothing
    _                               -> Nothing

thfMappingTypeToKind :: [THFUnitaryType] -> Maybe Kind
thfMappingTypeToKind [] = Nothing
thfMappingTypeToKind (u : []) = thfUnitaryTypeToKind u
thfMappingTypeToKind (u : ru) =
    let k1 = thfUnitaryTypeToKind u
        k2 = thfMappingTypeToKind ru
    in if isJust k1 && isJust k2
       then Just $ MapKind (fromJust k1) (fromJust k2)
       else Nothing

thfUnitaryTypeToKind :: THFUnitaryType -> Maybe Kind
thfUnitaryTypeToKind ut = case ut of
    T0UT_THF_Binary_Type_Par bt -> fmap ParKind (thfBinaryTypeToKind bt)
    T0UT_Defined_Type _         -> Just Kind
    T0UT_System_Type st         -> Just $ SysType st
    T0UT_Variable v             -> Just $ VKind v
    _                           -> Nothing


--------------------------------------------------------------------------------
-- Get the Type of a constant
--------------------------------------------------------------------------------

makeType :: THFFormula -> Either (Type, Constant) Diagnosis
makeType t = maybe (Right $ mkDiag Error "Error while parsing the Type of:" t)
                Left (thfFormulaToType t)

thfFormulaToType :: THFFormula -> Maybe (Type, Constant)
thfFormulaToType (T0F_THF_Typed_Const tc) = thfTypedConstToType tc
thfFormulaToType _  = Nothing

thfTypedConstToType :: THFTypedConst -> Maybe (Type, Constant)
thfTypedConstToType (T0TC_THF_TypedConst_Par tcp) =  thfTypedConstToType tcp
thfTypedConstToType (T0TC_Typed_Const c tlt) =
            maybe Nothing (\ t -> Just (t, c))
                (thfTopLevelTypeToType tlt)

thfTopLevelTypeToType :: THFTopLevelType -> Maybe Type
thfTopLevelTypeToType tlt = case tlt of
    T0TLT_Defined_Type dt       -> thfDefinedTypeToType dt
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeToType bt
    T0TLT_Constant c            -> Just $ CType c
    T0TLT_System_Type st        -> Just $ SType st
    T0TLT_Variable v            -> Just $ VType v
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
    T0BT_THF_Binary_Type_Par btp    -> fmap ParType (thfBinaryTypeToType btp)
    TBT_THF_Xprod_Type []           -> Nothing
    TBT_THF_Xprod_Type (u : [])     -> thfUnitaryTypeToType u
    TBT_THF_Xprod_Type us           -> let us' = map thfUnitaryTypeToType us
                                       in if all isJust us' then
                                           (Just . ProdType) $ map fromJust us'
                                          else Nothing
    _                               -> Nothing

thfMappingTypeToType :: [THFUnitaryType] -> Maybe Type
thfMappingTypeToType [] = Nothing
thfMappingTypeToType (u : []) = thfUnitaryTypeToType u
thfMappingTypeToType (u : ru) =
    let k1 = thfUnitaryTypeToType u
        k2 = thfMappingTypeToType ru
    in if isJust k1 && isJust k2
       then Just $ MapType (fromJust k1) (fromJust k2)
       else Nothing

thfUnitaryTypeToType :: THFUnitaryType -> Maybe Type
thfUnitaryTypeToType ut = case ut of
    T0UT_THF_Binary_Type_Par bt -> fmap ParType (thfBinaryTypeToType bt)
    T0UT_Defined_Type dt        -> thfDefinedTypeToType dt
    T0UT_Constant c             -> Just $ CType c
    T0UT_System_Type st         -> Just $ SType st
    T0UT_Variable v             -> Just $ VType v
    _                           -> Nothing


--------------------------------------------------------------------------------
-- Check if a THFFormula is a Type definition
--------------------------------------------------------------------------------

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
    TBT_THF_Xprod_Type []           -> False
    TBT_THF_Xprod_Type us           -> and $ map thfUnitaryTypeIsType us
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
