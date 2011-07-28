{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Static analysis for THF
Copyright   :  (c) A. Tsogias, DFKI Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Alexis.Tsogias@dfki.de
Stability   :  provisional
Portability :  portable

Instance of class Logic for THF.
NOTE: This implementation covers only THF0.
-}

module THF.StaticAnalysisTHF (basicAnalysis) where

import THF.As as As
import THF.Cons
import THF.Print ()
import THF.PrintTHF

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
QUESTION: how to treat fi_domain... int statAna
-}

-- it looks like the returned symbols inside the result are symbols that
-- were not "used" for the signature, so i propablly have to fix that.
basicAnalysis :: (BasicSpecTHF, SignTHF, GlobalAnnos) ->
        Result (BasicSpecTHF, ExtSign SignTHF SymbolTHF, [Named SentenceTHF])
basicAnalysis (BasicSpecTHF BSTHF _, _, _) =
    let err = mkDiag Error
            "Error: Static Analysis for general THF is not supported yet." ()
    in Result [err] Nothing
basicAnalysis (bs@(BasicSpecTHF BSTHF0 bs1), sig1, _) =
    let (diag1, bs2) = filterBS [] bs1
        (diag2, sig2) = execState (fillSig bs2) (diag1, sig1)
        (diag3, ns) = getSentences bs2 sig2 (diag2, [])
    in Result (reverse diag3)
            $ Just (bs, ExtSign sig2 (symbolMapToSet $ symbols sig2), ns)

symbolMapToSet :: SymbolMap -> Set.Set SymbolTHF
symbolMapToSet = Set.fromList . snd . unzip . Map.toList

-- IMPORTENT: the diag-list must have a reverted order
-- filter stuff not usefull things, like comments
fillSig :: [TPTP_THF] -> State ([Diagnosis], SignTHF) ()
fillSig [] = return ()
fillSig bs = do
    fillSigInitial bs
    (_, sig) <- get
    -- initial FinConstKindMap filled with the types
    let ickm = Map.map typeKind (types sig)
        cl = Map.elems (consts sig)
    foldM_ prepFinConst ickm cl

fillSigInitial :: [TPTP_THF] -> State ([Diagnosis], SignTHF) ()
fillSigInitial tl = mapM_ fillSingle tl
    where
        fillSingle t = case t of
            TPTP_THF_Annotated_Formula _ fr tf _ -> case fr of
                Type    -> case makeKind tf of
                    Right d         -> appandDiag d
                    Left (k, c, tc) ->
                        if isType tf
                            then insertType (Symbol c ST_Type) k c tc
                            else insertConst (Symbol c ST_Const) k c tc
                _       -> return ()
            _ -> return ()

appandDiag :: Diagnosis -> State ([Diagnosis], SignTHF) ()
appandDiag d = modify (\ (diag, s) -> (d : diag, s))

insertConst :: SymbolTHF -> Kind -> Constant -> THFTypedConst
                                 -> State ([Diagnosis], SignTHF) ()
insertConst sym k c tc = do
    (diag, sig) <- get
    if sigHasConst c sig
        then appandDiag $ mkDiag Warning
            "Constant is already contained inside the signature: " sym
        else do
            let ci = ConstInfo {constName = c, constKind = k, constDef = tc}
            put (diag, sig { consts = Map.insert c ci (consts sig)
                           , symbols = Map.insert c sym (symbols sig) })


insertType :: SymbolTHF -> Kind -> Constant -> THFTypedConst
                                -> State ([Diagnosis], SignTHF) ()
insertType sym k c tc = do
    (diag, sig) <- get
    if sigHasType c sig
        then appandDiag $ mkDiag Warning
                "Type is already contained inside the signature: " sym
        else do
            let ti = TypeInfo {typeName = c, typeKind = k, typeDef = tc}
            put (diag, sig { types = Map.insert c ti (types sig)
                           , symbols = Map.insert c sym (symbols sig) })

modConstKind :: Constant -> Kind -> State ([Diagnosis], SignTHF) ()
modConstKind c k = do
    (_, sig) <- get
    let ci = (consts sig Map.! c) {constKind = k}
    modify (\ (d, sig1) -> (d, sig1 {consts = Map.insert c ci (consts sig1)}))

sigHasType :: Constant -> SignTHF -> Bool
sigHasType c sig = Map.member c (types sig)

sigHasConst :: Constant -> SignTHF -> Bool
sigHasConst c sig = Map.member c (consts sig)

prepFinConst :: FinConstKindMap -> ConstInfo
                                -> State ([Diagnosis], SignTHF) FinConstKindMap
prepFinConst fckm ci = do
    (_, sig) <- get
    let fc = finConst (Set.singleton $ constName ci)
                (constKind ci) fckm (consts sig)
    case fc of
        Right diag      -> appandDiag diag >> return fckm
        Left (k, fckm1)  -> do
            modConstKind (constName ci) k
            let fckm2 = Map.insert (constName ci) k fckm1
            return fckm2

-- thought as collectin of finished kinds o ftheir Constants. used in finConst
type FinConstKindMap = Map.Map Constant Kind

-- assertion the constKindMap is filled with the content of (types sig)
finConst :: Set.Set Constant -> Kind -> FinConstKindMap -> ConstMap
                             -> Either (Kind, FinConstKindMap) Diagnosis
finConst sc k ckm cm = case k of
    FunKind k1 k2 r ->
        let fc1 = finConst sc k1 ckm cm
        in case fc1 of
            Right _         -> fc1
            Left (k11, ckm1)  ->
                let fc2 = finConst sc k2 ckm1 cm
                in case fc2 of
                    Right _             -> fc2
                    Left (k22, ckm2)    ->
                        Left (FunKind k11 k22 r, ckm2)
    Const c1    | Set.member c1 sc ->  Right $
                    mkDiag Error
                        "Circle detected while building Kind of Constant: " c1
                | Map.member c1 ckm -> Left (ckm Map.! c1, ckm)
                | Map.member c1 cm ->
                    let k1 = constKind (cm Map.! c1)
                    in if isFinishedKind k1
                       then Left (k1, Map.insert c1 k1 ckm)
                       else let fc = finConst (Set.insert c1 sc) k1 ckm cm
                            in case fc of
                                Right _ -> fc
                                Left (k2, ckm1) ->
                                    if isFinishedKind k2
                                    then Left (k2, Map.insert c1 k2 ckm1)
                                    else fc
                | otherwise -> Right $ mkDiag Error "Constant not defined: " c1
    _               -> Left (k, ckm)


{- Get all sentences from the content of the BasicSpecTHF-}
-- QUESTION: Are conjecures sentences?
getSentences :: [TPTP_THF] -> SignTHF -> ([Diagnosis], [Named SentenceTHF])
                                      -> ([Diagnosis], [Named SentenceTHF])
getSentences [] _ dn = dn
getSentences (t : rt) sig dn@(d, ns) = case t of
    TPTP_THF_Annotated_Formula _ fr _ _ -> case fr of
        Type    -> getSentences rt sig dn
        Unknown -> let diag = (mkDiag Warning
                        "THFFormula with type \'unknown\' will be ignored." t)
                   in getSentences rt sig (diag : d, ns)
        Plain   -> let diag = (mkDiag Warning
                        "THFFormula with type \'plain\' will be ignored." t)
                   in getSentences rt sig (diag : d, ns)
        _       -> let (d1, ns1) = getSentences rt sig dn
                   in (d1, tptpthfToNS t : ns1)
    _ -> getSentences rt sig dn

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

-- The diagnosis list has to be reverted.
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
    T0TLT_System_Type _         -> True
    T0TLT_THF_Binary_Type _     -> False
    T0TLT_Constant _            -> False
    _                           -> False

thfDefinedTypeIsType :: DefinedType -> Bool
thfDefinedTypeIsType dt = case dt of
    DT_tType    -> True
    _           -> False

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
    T0TLT_Constant c            -> Just $ Const c
    T0TLT_Defined_Type _        -> Just TType
    T0TLT_System_Type st        -> Just $ SysType st
    T0TLT_THF_Binary_Type bt    -> thfBinaryTypeToKind bt
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
       then Just $ FunKind (fromJust k1) (fromJust k2) nullRange
       else Nothing

thfUnitaryTypeToKind :: THFUnitaryType -> Maybe Kind
thfUnitaryTypeToKind ut = case ut of
    T0UT_Constant c             -> Just $ Const c
    T0UT_Defined_Type _         -> Just TType
    T0UT_System_Type st         -> Just $ SysType st
    T0UT_THF_Binary_Type_Par bt -> thfBinaryTypeToKind bt
    _                           -> Nothing

-- nameToId :: As.Name -> Id
-- nameToId = stringToId . show . printTHF

-- constantToId :: As.Constant -> Id
-- constantToId = stringToId . show . printTHF
