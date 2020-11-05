{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  ./THF/StaticAnalysisTHF.hs
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
import THF.Sign
import THF.Poly (type_check)
import THF.Utils (thfTopLevelTypeToType)

import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Common.ExtSign
import Common.Lib.State
import Common.DocUtils

import Control.Monad

import qualified Data.HashMap.Lazy as Map
import qualified Data.Set as Set

{- -----------------------------------------------------------------------------
Questions:
how to handle SysType in isTypeConsistent?
Todo:
find out what fi_domain, fi_predicates and fi_functors are and try
to somehow support them
----------------------------------------------------------------------------- -}

-- The main method for the static analysis
basicAnalysis :: (BasicSpecTHF, SignTHF, GlobalAnnos) ->
        Result (BasicSpecTHF, ExtSign SignTHF SymbolTHF, [Named THFFormula])
basicAnalysis (bs@(BasicSpecTHF bs1), sig1, _) =
    let (diag1, bs2) = filterBS [] bs1
        (diag2, sig2, syms) = execState (fillSig bs2) (diag1, sig1, Set.empty)
        (diag3, ns) = getSentences bs2 (diag2, [])
    in do
     type_check (types sig2) (consts sig2) ns
     Result (reverse diag3) $ Just (bs, ExtSign sig2 syms, ns)

{- This functions delets all Comments and Includes because they are not needed
for the static analysis
The diagnosis list has a reverted order! -}
filterBS :: [Diagnosis] -> [TPTP_THF] -> ([Diagnosis], [TPTP_THF])
filterBS d [] = (d, [])
filterBS d (t : rt) = case t of
    TPTP_Include i -> let ds = mkDiag Warning "Include will be ignored." i
                      in filterBS (ds : d) rt
    TPTP_Comment _ -> filterBS d rt
    TPTP_Defined_Comment _ -> filterBS d rt
    TPTP_System_Comment _ -> filterBS d rt
    TPTP_Header _ -> filterBS d rt
    _ -> let (diag, thf) = filterBS d rt
                               in (diag, t : thf)

-- Append the Signature by the Types and Constants given inside the basic spec
fillSig :: [TPTP_THF] -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
fillSig [] = return ()
fillSig bs = mapM_ fillSingleType bs >> mapM_ fillSingleConst bs
    where
        fillSingleType t = case t of
            TPTP_THF_Annotated_Formula n fr tf a -> case fr of
                Type ->
                    when (isKind tf) $ case makeKind tf of
                        Right d -> appandDiag d
                        Left (k, c) -> insertType c n k a
                _ -> return ()
            _ -> return ()
        fillSingleConst t = case t of
            TPTP_THF_Annotated_Formula n fr tf a -> case fr of
                Type ->
                    unless (isKind tf) $ case makeType tf of
                        Right d -> appandDiag d
                        Left (ty, c) -> insertConst c n ty a
                _ -> return ()
            _ -> return ()

{- Append the Diagnosis-List by the given Diagnosis
The new diag will be put on top of the existing list. -}
appandDiag :: Diagnosis -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
appandDiag d = modify (\ (diag, s, syms) -> (d : diag, s, syms))

-- insert the given type into the Signature
insertType :: Constant -> As.Name -> Kind -> Annotations
                    -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
insertType c n k a = do
    (diag, sig, syms) <- get
    if sigHasConstSymbol c sig then appandDiag $ mkDiag Error
        "Duplicate definition of a symbol as a type constant. Symbol: " c
     else
        if sigHasTypeSymbol c sig then
            unless (sigHasSameKind c k sig) $ appandDiag $
                mkDiag Error ("A type with the same identifier"
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
    (_, sig, _) <- get
    if sigHasTypeSymbol c sig then (appandDiag $ mkDiag Error
        "Duplicate definition of a symbol as a type constant. Symbol: " c)
    else do
          isTypeConsistent t
          if sigHasConstSymbol c sig then
               unless (sigHasSameType c t sig) $ appandDiag $ mkDiag Error
                 ("A constant with the same identifier but another " ++
                  "type is already inside the signature") c
           else -- everything is fine
                 let ci = ConstInfo { constId = c, constName = n, constType = t
                                    , constAnno = a }
                     sym = Symbol { symId = c, symName = n
                                  , symType = ST_Const t }
                 in do
                     (diag', sig', syms') <- get
                     put (diag', sig' { consts = Map.insert c ci (consts sig')
                                      , symbols = Map.insert c sym (symbols sig') }
                                      , Set.insert sym syms')

-- Check if a type symbol is already inside the sig
sigHasTypeSymbol :: Constant -> SignTHF -> Bool
sigHasTypeSymbol c sig = Map.member c (types sig)

{- This Method is ment to be used after sigHasTypeSymbol
Check if a type symbol with the same kind is inside the Sig
If this is not the case me have a problem! -}
sigHasSameKind :: Constant -> Kind -> SignTHF -> Bool
sigHasSameKind c k sig = typeKind (types sig Map.! c) == k

-- Check if a const symbol is already inside the sig
sigHasConstSymbol :: Constant -> SignTHF -> Bool
sigHasConstSymbol c sig = Map.member c (consts sig)

{- This Method is ment to be used after sigHasConstSymbol
Check if a const symbol with the same type is inside the Sig
If this is not the case me have a problem! -}
sigHasSameType :: Constant -> Type -> SignTHF -> Bool
sigHasSameType c t sig = constType (consts sig Map.! c) == t

{- check if all cTypes inside the given Type are elements of the signaure.
Nothing means that everything is fine, otherwise Just diag will be returned. -}
isTypeConsistent :: Type -> State ([Diagnosis], SignTHF, Set.Set SymbolTHF) ()
isTypeConsistent t = do
 (_, sig, _) <- get
 case t of
    MapType t1 t2 -> do
     isTypeConsistent t1
     isTypeConsistent t2
    ParType t1 -> isTypeConsistent t1
    CType c -> when (not (sigHasTypeSymbol c sig))
               (do
                 insertType c (N_Atomic_Word c) Kind Null
                 appandDiag $ mkDiag Warning "Unknown type: " c)
    ProdType ts -> mapM_ isTypeConsistent ts
    _ -> return ()
    -- SType _ -> ... -- how to handle these?

{- -----------------------------------------------------------------------------
Extract the sentences from the basic spec
----------------------------------------------------------------------------- -}

{- Get all sentences from the content of the BasicSpecTH
The diag list has a reverted order. -}
getSentences :: [TPTP_THF] -> ([Diagnosis], [Named THFFormula])
                           -> ([Diagnosis], [Named THFFormula])
getSentences [] dn = dn
getSentences (t : rt) dn@(d, ns) = case t of
    TPTP_THF_Annotated_Formula _ fr _ _ -> case fr of
        Type -> getSentences rt dn
        Unknown ->
            let diag = mkDiag Warning
                    "THFFormula with role \'unknown\' will be ignored." t
            in getSentences rt (diag : d, ns)
        Plain ->
            let diag = mkDiag Warning
                    "THFFormula with role \'plain\' will be ignored." t
            in getSentences rt (diag : d, ns)
        Fi_Domain ->
            let diag = mkDiag Warning
                    "THFFormula with role \'fi_domain\' will be ignored." t
            in getSentences rt (diag : d, ns)
        Fi_Functors ->
            let diag = mkDiag Warning
                    "THFFormula with role \'fi_functors\' will be ignored." t
            in getSentences rt (diag : d, ns)
        Fi_Predicates ->
            let diag = mkDiag Warning
                    "THFFormula with role \'fi_predicates\' will be ignored." t
            in getSentences rt (diag : d, ns)
        Assumption ->
            let diag = mkDiag Warning
                    "THFFormula with role \'assumption\' will be ignored." t
            in getSentences rt (diag : d, ns)
        _ ->
            let (d1, ns1) = getSentences rt dn
            in (d1, tptpthfToNS t : ns1)
    _ -> getSentences rt dn

{- Precondition: The formulaRole must not be Type, Unknown, Plain, Fi_Domain
Fi_Functors, Fi_Predicates or Assumption
(They are filtered out in getSentences) -}
tptpthfToNS :: TPTP_THF -> Named THFFormula
tptpthfToNS f =
  let s = makeNamed (show $ pretty $ nameAF f) (thfFormulaAF f)
      t = s { isAxiom = False }
      w = s { wasTheorem = True }
  in case formulaRoleAF f of
    Definition -> s { isDef = True }
    Conjecture -> t
    Negated_Conjecture -> t
    Theorem -> w
    Lemma -> w
    Hypothesis -> t
    _ -> s -- { isAxiom = True, isDef = False, wasTheorem = False }


{- -----------------------------------------------------------------------------
Get the Kind of a type
----------------------------------------------------------------------------- -}

makeKind :: THFFormula -> Either (Kind, Constant) Diagnosis
makeKind t = maybe (Right $ mkDiag Error "Error while parsing the kind of:" t)
                Left (thfFormulaToKind t)

thfFormulaToKind :: THFFormula -> Maybe (Kind, Constant)
thfFormulaToKind (T0F_THF_Typed_Const tc) = thfTypedConstToKind tc
thfFormulaToKind _ = Nothing

thfTypedConstToKind :: THFTypedConst -> Maybe (Kind, Constant)
thfTypedConstToKind (T0TC_THF_TypedConst_Par tcp) = thfTypedConstToKind tcp
thfTypedConstToKind (T0TC_Typed_Const c tlt) =
            maybe Nothing (\ k -> Just (k, c))
                (thfTopLevelTypeToKind tlt)

thfTopLevelTypeToKind :: THFTopLevelType -> Maybe Kind
thfTopLevelTypeToKind tlt = case tlt of
    T0TLT_THF_Binary_Type bt -> thfBinaryTypeToKind bt
    T0TLT_Defined_Type _ -> Just Kind
    _ -> Nothing

thfBinaryTypeToKind :: THFBinaryType -> Maybe Kind
thfBinaryTypeToKind bt = case bt of
    T0BT_THF_Binary_Type_Par btp -> thfBinaryTypeToKind btp
    _ -> Nothing

{- -----------------------------------------------------------------------------
Get the Type of a constant
----------------------------------------------------------------------------- -}

makeType :: THFFormula -> Either (Type, Constant) Diagnosis
makeType t = maybe (Right $ mkDiag Error "Error while parsing the type of:" t)
                Left (thfFormulaToType t)

thfFormulaToType :: THFFormula -> Maybe (Type, Constant)
thfFormulaToType (T0F_THF_Typed_Const tc) = thfTypedConstToType tc
thfFormulaToType _ = Nothing

thfTypedConstToType :: THFTypedConst -> Maybe (Type, Constant)
thfTypedConstToType (T0TC_THF_TypedConst_Par tcp) = thfTypedConstToType tcp
thfTypedConstToType (T0TC_Typed_Const c tlt) =
            maybe Nothing (\ t -> Just (t, c))
                (thfTopLevelTypeToType tlt)

{- -----------------------------------------------------------------------------
Check if a THFFormula is a Type definition
----------------------------------------------------------------------------- -}

isKind :: THFFormula -> Bool
isKind tf = case tf of
    T0F_THF_Typed_Const tc -> thfTypedConstIsKind tc
    _ -> False

thfTypedConstIsKind :: THFTypedConst -> Bool
thfTypedConstIsKind tc = case tc of
    T0TC_THF_TypedConst_Par tcp -> thfTypedConstIsKind tcp
    T0TC_Typed_Const _ tlt -> thfTopLevelTypeIsKind tlt

thfTopLevelTypeIsKind :: THFTopLevelType -> Bool
thfTopLevelTypeIsKind tlt = case tlt of
    T0TLT_THF_Binary_Type bt -> thfBinaryTypeIsKind bt
    T0TLT_Defined_Type dt -> thfDefinedTypeIsKind dt
    _ -> False

thfDefinedTypeIsKind :: DefinedType -> Bool
thfDefinedTypeIsKind dt = case dt of
    DT_tType -> True
    _ -> False

thfBinaryTypeIsKind :: THFBinaryType -> Bool
thfBinaryTypeIsKind bt = case bt of
    T0BT_THF_Binary_Type_Par btp -> thfBinaryTypeIsKind btp
    _ -> False
