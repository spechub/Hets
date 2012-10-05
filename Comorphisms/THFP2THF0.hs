{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from THFP to THF0
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  J. von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The comorphism from THFP to THF0.
-}

module Comorphisms.THFP2THF0 where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Id (Token(..),nullRange)
import Common.AS_Annotation (Named,SenAttr(..))

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.StaticAnalysisTHF (thfTopLevelTypeToType)

import qualified Data.Map as Map

data THFP2THF0 = THFP2THF0 deriving Show

instance Language THFP2THF0

instance Comorphism THFP2THF0
                THF SL.THFSl
                BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF SentenceTHF () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP2THF0 = THF
    sourceSublogic THFP2THF0 = SL.THFP
    targetLogic THFP2THF0 = THF
    mapSublogic THFP2THF0 _ = Just SL.THF0
    map_theory THFP2THF0 = trans_theory
    has_model_expansion THFP2THF0 = True

trans_theory :: (SignTHF,[Named SentenceTHF])
                -> Result (SignTHF,[Named SentenceTHF])
trans_theory (sig, sentences1) = do
 let (tp_trans,cs_trans,sig1)  = head . filter (\(tp_t,_,Sign tps cs _) -> 
                                     not (any hasProdK $ Map.elems tps)
                                  && not (any (hasProdT tp_t) $ Map.elems cs)) $
                 iterate makeExplicitProducts (Map.empty, Map.empty, sig)
     sig2 = sig1 {consts =
      Map.map (\c -> c {constType = curryConstType tp_trans
                                 (constType c)}) $ consts sig1}
     sentences = rewriteSen tp_trans cs_trans sentences1
 return (recreateSymbols sig2,sentences)

recreateSymbols :: SignTHF -> SignTHF
recreateSymbols (Sign tps cs _) =
 let name = N_Atomic_Word
     symbs1 = foldl (\m (c,t) -> Map.insert c
                      (Symbol c (name c) (ST_Type $ typeKind t)) m)
              Map.empty $ Map.toList tps
     symbs  = foldl (\m (c,k) -> Map.insert c
                      (Symbol c (name c) (ST_Const $ constType k)) m)
              symbs1 $ Map.toList cs
 in Sign tps cs symbs

type TransMap = Map.Map Constant [Constant]

-- note: does not do anything on non-map-types
curryConstType :: TransMap -> Type -> Type
curryConstType m (MapType t1 t2) = prodToMapType m t1 t2
curryConstType m (ParType t)     = ParType (curryConstType m t)
curryConstType _ t               = t

prodToMapType :: TransMap -> Type -> Type -> Type
prodToMapType m t1 t2 = case t1 of
 MapType _ _ -> MapType (curryConstType m t1) t2
 ProdType ts -> let ts' = map (curryConstType m) ts
                in foldl (\t1' t2' -> MapType t2' t1') t2 ts'
 CType c     -> let cs = map CType $ curryConst m c
                in foldl (\t1' t2' -> MapType t2' t1') t2 cs
 ParType t   -> prodToMapType m t t2
 _           -> MapType t1 t2
 
curryConst :: TransMap -> Constant -> [Constant]
curryConst m c = case Map.lookup c m of
 Just cs -> concat $ map (curryConst m) cs
 Nothing -> [c]

rewriteSen :: TransMap -> TransMap -> [Named SentenceTHF] -> [Named SentenceTHF]
rewriteSen tp_trans cs_trans = concat . map (rewriteSen' tp_trans cs_trans)

rewriteSen' :: TransMap -> TransMap -> Named SentenceTHF -> [Named SentenceTHF]
rewriteSen' tp_trans cs_trans sen =
 let sen_ = sentence sen
     sen' = case senFormula . sentence $ sen of
             TF_THF_Logic_Formula lf -> TF_THF_Logic_Formula $
               rewriteLogicFormula tp_trans cs_trans lf
             T0F_THF_Typed_Const  tc -> T0F_THF_Typed_Const $
               rewriteTypedConst tp_trans cs_trans tc
             TF_THF_Sequent _ ->
              error "THFP2THF0.rewriteSen: Sequents are not in THF0!"
 in [sen { sentence = sen_ { senFormula = sen' } }]

rewriteLogicFormula :: TransMap -> TransMap
                       -> THFLogicFormula -> THFLogicFormula
rewriteLogicFormula tp_trans cs_trans lf = case lf of
 TLF_THF_Binary_Formula bf ->
  case rewriteBinaryFormula tp_trans cs_trans bf of
   Left bf' -> TLF_THF_Binary_Formula bf'
   Right uf -> TLF_THF_Unitary_Formula uf
 TLF_THF_Unitary_Formula uf -> TLF_THF_Unitary_Formula $
   rewriteUnitaryFormula tp_trans cs_trans uf
 TLF_THF_Type_Formula _ ->
  error "THFP2THF0.rewriteLogicFormula: TLF_THF_Type_Formula is not in THF0!"
 TLF_THF_Sub_Type _ ->
  error "THFP2THF0.rewriteLogicFormula: TLF_THF_Sub_Type is not in THF0!"

rewriteTypedConst :: TransMap -> TransMap
                     -> THFTypedConst -> THFTypedConst
rewriteTypedConst tp_trans cs_trans tc = case tc of
 T0TC_Typed_Const c tlf ->
  case thfTopLevelTypeToType tlf of
    Just _ -> error "THFP2THF0.rewriteTypedConst: Not yet implemented!"
    Nothing ->
     error $ "THFP2THF0.rewriteTypedConst: Couldn't interpret type for " ++
           "Constant " ++ show c
 T0TC_THF_TypedConst_Par tc' ->
   T0TC_THF_TypedConst_Par $ rewriteTypedConst tp_trans cs_trans tc'

rewriteBinaryFormula :: TransMap -> TransMap -> THFBinaryFormula
                        -> Either THFBinaryFormula THFUnitaryFormula
rewriteBinaryFormula tp_trans cs_trans bf = case bf of
 TBF_THF_Binary_Type _ ->
  error "THFP2THF0.rewriteBinaryFormula: TBF_THF_Binary_Type is not in THF0!"
 TBF_THF_Binary_Pair uf1 cn uf2 ->
  let uf1' = rewriteUnitaryFormula tp_trans cs_trans uf1
      uf2' = rewriteUnitaryFormula tp_trans cs_trans uf2
  in case (toTuple uf1',cn,toTuple uf2') of
      (Just (TUF_THF_Tuple t1), Infix_Equality, 
       Just (TUF_THF_Tuple t2)) -> if length t1 == length t2
        then Left $ TBF_THF_Binary_Tuple $ TBT_THF_And_Formula $
              map (\(t1',t2') ->
               TUF_THF_Logic_Formula_Par $ TLF_THF_Binary_Formula $
                TBF_THF_Binary_Pair (logicFormula2UnitaryFormula t1')
                 cn (logicFormula2UnitaryFormula t2')) (zip t1 t2)
        else error $ "THFP2THF0.rewriteBinaryFormula: Equality on tuples of " ++
                   "different size!"
      _ -> Left $ TBF_THF_Binary_Pair uf1' cn uf2'
 TBF_THF_Binary_Tuple bt -> rewriteBinaryTuple tp_trans cs_trans bt

toTuple :: THFUnitaryFormula -> Maybe THFUnitaryFormula
toTuple u@(TUF_THF_Tuple _) = Just u
toTuple (TUF_THF_Logic_Formula_Par
  (TLF_THF_Unitary_Formula u)) = Just u
toTuple _ = Nothing

logicFormula2UnitaryFormula :: THFLogicFormula -> THFUnitaryFormula
logicFormula2UnitaryFormula l = case l of
 TLF_THF_Unitary_Formula uf -> uf
 _ -> TUF_THF_Logic_Formula_Par l

rewriteBinaryTuple :: TransMap -> TransMap -> THFBinaryTuple
                      -> Either THFBinaryFormula THFUnitaryFormula
rewriteBinaryTuple tp_trans cs_trans bt = case bt of
 TBT_THF_Or_Formula ufs -> Left $ TBF_THF_Binary_Tuple $ TBT_THF_Or_Formula $
  map (rewriteUnitaryFormula tp_trans cs_trans) ufs
 TBT_THF_And_Formula ufs -> Left $ TBF_THF_Binary_Tuple $ TBT_THF_And_Formula $
  map (rewriteUnitaryFormula tp_trans cs_trans) ufs
 TBT_THF_Apply_Formula ufs ->
  let ufs' = map (rewriteUnitaryFormula tp_trans cs_trans) ufs
  in case ufs' of
      []   -> error "THFP2THF0.rewriteBinaryTuple: Illegal Application!"
      _:[] -> error "THFP2THF0.rewriteBinaryTuple: Illegal Application!"
      fn:args -> case removeParensUnitaryFormula fn of
       (TUF_THF_Atom (T0A_Constant c)) ->
         case show . toToken $ c of
           'p':'r':'_':i ->
              case args of
               tuple:[] ->
                let i' = read i :: Int
                in unpack_tuple tuple i'
               _ -> error $ "THFP2THF0.rewriteBinaryTuple: Invalid argument " ++
                            "for projection: " ++ show args
           _ -> Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
                 fn:(flattenTuples args)
       TUF_THF_Tuple lfs -> Right . rewriteUnitaryFormula tp_trans cs_trans .
        TUF_THF_Tuple $
         map (\l -> case rewriteBinaryTuple tp_trans cs_trans .
              TBT_THF_Apply_Formula $
              (TUF_THF_Logic_Formula_Par l):args of
               Left bf  -> TLF_THF_Binary_Formula bf
               Right uf -> TLF_THF_Unitary_Formula uf) lfs
       _ -> Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
             fn:(flattenTuples args)

flattenTuples :: [THFUnitaryFormula] -> [THFUnitaryFormula]
flattenTuples ufs = concat . map flattenTuple $ ufs

flattenTuple :: THFUnitaryFormula -> [THFUnitaryFormula]
flattenTuple u = case removeParensUnitaryFormula u of
 TUF_THF_Tuple lfs ->
  concat . map (flattenTuple . TUF_THF_Logic_Formula_Par) $ lfs
 _ -> [u]

unpack_tuple :: THFUnitaryFormula -> Int
                -> Either THFBinaryFormula THFUnitaryFormula
unpack_tuple uf i = case removeParensUnitaryFormula uf of
 TUF_THF_Tuple lfs -> if i > length lfs
  then error "THFP2THF0.unpack_tuple: Tuple has too few elements!"
  else case lfs!!(i-1) of
        TLF_THF_Binary_Formula bf -> Left bf
        TLF_THF_Unitary_Formula uf' -> Right uf'
        lf -> error $ "THFP2THF0.unpack_tuple: " ++ show lf ++ " is not in THF0!"
 _ -> error $ "THFP2THF0.unpack_tuple: " ++ show uf ++ " is not a tuple!"

removeParensUnitaryFormula :: THFUnitaryFormula -> THFUnitaryFormula
removeParensUnitaryFormula (TUF_THF_Logic_Formula_Par
 (TLF_THF_Unitary_Formula uf)) = uf
removeParensUnitaryFormula uf = uf

rewriteUnitaryFormula :: TransMap -> TransMap
                         -> THFUnitaryFormula -> THFUnitaryFormula
rewriteUnitaryFormula tp_trans cs_trans uf = case uf of
 TUF_THF_Conditional _ _ _ ->
  error "THFP2THF0.rewriteUnitaryFormula: TUF_THF_Conditional is not in THF0!"
 TUF_THF_Quantified_Formula qf -> case qf of
  TQF_THF_Quantified_Formula q vs uf' -> TUF_THF_Quantified_Formula $
   TQF_THF_Quantified_Formula q
    (rewriteVariableList tp_trans cs_trans vs)
    (rewriteUnitaryFormula tp_trans cs_trans uf')
  T0QF_THF_Quantified_Var q vs uf' -> TUF_THF_Quantified_Formula $
   T0QF_THF_Quantified_Var q
    (rewriteVariableList tp_trans cs_trans vs)
    (rewriteUnitaryFormula tp_trans cs_trans uf')
  T0QF_THF_Quantified_Novar _ _ -> 
   error $ "THFP2THF0.rewriteUnitaryFormula: T0QF_THF_Quantified_Novar not " ++
           "yet implemented!"
 TUF_THF_Unary_Formula c lf -> TUF_THF_Unary_Formula c $
  rewriteLogicFormula tp_trans cs_trans lf
 TUF_THF_Atom a -> rewriteAtom tp_trans cs_trans a
 TUF_THF_Tuple t -> TUF_THF_Tuple $
                     map (rewriteLogicFormula tp_trans cs_trans) t
 TUF_THF_Logic_Formula_Par lf -> TUF_THF_Logic_Formula_Par $
  rewriteLogicFormula tp_trans cs_trans lf
 T0UF_THF_Abstraction vs uf' -> T0UF_THF_Abstraction
  (rewriteVariableList tp_trans cs_trans vs)
  (rewriteUnitaryFormula tp_trans cs_trans uf')

rewriteVariableList :: TransMap -> TransMap
                       -> [THFVariable] -> [THFVariable]
rewriteVariableList tp_trans cs_trans vs = concat $
 map (\v -> case v of
             TV_THF_Typed_Variable t tp ->
              case thfTopLevelTypeToType tp of
               Just tp' -> let cs = constMakeExplicitProduct tp_trans
                                     (A_Lower_Word t) tp'
                           in map (\(c,tp'') ->
                               TV_THF_Typed_Variable (toToken c)
                                 (typeToTopLevelType
                                  (curryConstType tp_trans tp''))) cs
               Nothing -> error $ "THFP2THF0.rewriteVariableList: Couldn't " ++
                                  "type " ++ show tp
             TV_Variable t -> case transToken cs_trans t of
                               [_] -> [v]
                               t' -> map TV_Variable t') vs

rewriteAtom :: TransMap -> TransMap
               -> THFAtom -> THFUnitaryFormula
rewriteAtom _ cs_trans a = case a of
 TA_Term _ -> error "THFP2THF0.rewriteAtom: TA_Term is not in THF0!"
 TA_THF_Conn_Term c -> case c of
  TCT_THF_Pair_Connective _ -> error $ "THFP2THF0.rewriteAtom: " ++
                                      "TC_THF_Pair_Connective is not in THF0!"
  TCT_Assoc_Connective _ -> TUF_THF_Atom a
  TCT_THF_Unary_Connective _ -> TUF_THF_Atom a
  T0CT_THF_Quantifier _ -> TUF_THF_Atom a
 TA_Defined_Type _ -> error $ "THFP2THF0.rewriteAtom: TA_Defined_Type " ++
                              "is not in THF0!"
 TA_Defined_Plain_Formula _ -> error $ "THFP2THF0.rewriteAtom: " ++
                                      "TA_Defined_Plain_Formula is not in THF0!"
 TA_System_Type _ -> error $ "THFP2THF0.rewriteAtom: TA_System_Type " ++
                             "is not in THF0!"
 TA_System_Atomic_Formula _ -> error $ "THFP2THF0.rewriteAtom: " ++
                                       "TA_System_Atomic_Formula " ++
                                       "is not in THF0!"
 T0A_Constant c -> transConst cs_trans c
 T0A_Defined_Constant _ -> TUF_THF_Atom a
 T0A_System_Constant _ -> TUF_THF_Atom a
 T0A_Variable _ -> TUF_THF_Atom a

typeToTopLevelType :: Type -> THFTopLevelType
typeToTopLevelType t = case t of
 TType -> T0TLT_Defined_Type (DT_tType)
 OType -> T0TLT_Defined_Type (DT_oType)
 IType -> T0TLT_Defined_Type (DT_iType)
 MapType t1 t2 -> T0TLT_THF_Binary_Type (TBT_THF_Mapping_Type
                   [typeToUnitaryType t1,typeToUnitaryType t2])
 ProdType ts   -> T0TLT_THF_Binary_Type (TBT_THF_Xprod_Type $
                   map typeToUnitaryType ts)
 CType c       -> T0TLT_Constant c
 SType t'      -> T0TLT_System_Type t'
 VType t'      -> T0TLT_Variable t'
 ParType t'    -> T0TLT_THF_Binary_Type $ T0BT_THF_Binary_Type_Par $
                   typeToBinaryType t'

typeToUnitaryType :: Type -> THFUnitaryType
typeToUnitaryType t = case typeToTopLevelType t of
                       T0TLT_Constant c        -> T0UT_Constant c
                       T0TLT_Variable t'       -> T0UT_Variable t'
                       T0TLT_Defined_Type d    -> T0UT_Defined_Type d
                       T0TLT_System_Type t'    -> T0UT_System_Type t'
                       T0TLT_THF_Binary_Type b -> T0UT_THF_Binary_Type_Par b
                       TTLT_THF_Logic_Formula _ ->
                        error "This shouldn't happen!"

typeToBinaryType :: Type -> THFBinaryType
typeToBinaryType t = case typeToTopLevelType t of
                      T0TLT_THF_Binary_Type b -> b
                      _ -> error $ "Cannot represent type " ++ show t ++
                                   "as THFBinaryType!"

toToken :: Constant -> Token
toToken (A_Lower_Word t)    = t
toToken (A_Single_Quoted t) = t

transToken :: TransMap -> Token -> [Token]
transToken m t = case Map.toList $
  Map.filterWithKey (\c _ -> (toToken c) == t) m of
                   (_,cs):_ -> concat $ map (transToken m . toToken) cs
                   [] -> [t]

transConst :: TransMap -> Constant -> THFUnitaryFormula
transConst m c = case transConst' m c of
 [] -> TUF_THF_Atom (T0A_Constant c)
 lfs -> TUF_THF_Tuple lfs

transConst' :: TransMap -> Constant -> [THFLogicFormula]
transConst' m c = case Map.toList $
  Map.filterWithKey (\c' _ -> c == c') m of
   (_,cs):_ -> map (\c' -> case transConst' m c' of
                           [] -> TLF_THF_Unitary_Formula .
                                 TUF_THF_Atom . T0A_Constant $ c'
                           lfs -> TLF_THF_Unitary_Formula .
                                  TUF_THF_Tuple $ lfs) cs
   [] -> []

constMakeExplicitProduct :: TransMap -> Constant -> Type -> [(Constant,Type)]
constMakeExplicitProduct tp_trans c t =
 let (_,_,Sign _ cs _) = head . filter (\(tp_t,_,Sign _ cs' _) -> 
                          not (any (hasProdT tp_t) $ Map.elems cs')) $
      iterate makeExplicitProducts
      (tp_trans,Map.empty, Sign Map.empty (Map.fromList [(c,
        ConstInfo {constId = c, constName = N_Atomic_Word c,
                   constType = t, constAnno = Null})]) Map.empty)
 in map (\i -> (constId i,constType i)) $ Map.elems cs

{- Note: Type definitions are non-recursive -}
makeExplicitProducts :: (TransMap, TransMap, SignTHF) ->
 (TransMap, TransMap, SignTHF)
makeExplicitProducts (tp_trans1, cs_trans1, sig) =
 let (tp_trans,tps) = mkExplicitProductsK tp_trans1 (types sig)
     (cs_trans,cs)  = mkExplicitProductsT cs_trans1 tp_trans (consts sig)
 in (tp_trans, cs_trans, sig {types = tps, consts = cs})

mkExplicitProductsT :: TransMap -> TransMap -> Map.Map Constant ConstInfo
                       -> (TransMap,Map.Map Constant ConstInfo)
mkExplicitProductsT cs_trans1 tp_trans cs1 = Map.fold
 (\c (trans,cs) -> prodTToTuple trans tp_trans cs (constId c) (constName c)
                     (constType c)) (cs_trans1,cs1) cs1

prodTToTuple :: TransMap -> TransMap -> Map.Map Constant ConstInfo -> Constant
                -> Name -> Type -> (TransMap, Map.Map Constant ConstInfo)
prodTToTuple trans tp_trans cs c n t = case t of
 MapType t1 t2 -> 
  let (_,cs') = prodTToTuple Map.empty tp_trans Map.empty c n t2
      cs'' = Map.delete c cs
      tuple = Map.elems cs'
      names = mkNames c n $ length tuple
  in if length tuple == 0 then (trans,cs) else
     (Map.insert c (map fst names) trans,
      foldr (\((n1,n2),ci) cs''' -> Map.insert n1
                ci {constName = n2,
                    constId = n1,
                    constType = MapType t1 (constType ci)} cs''')
            cs'' (zip names tuple)) 
 ProdType ts -> let cs' = Map.delete c cs
                    names = mkNames c n $ length ts
                in (Map.insert c (map fst names) trans,
                    foldr (\((n1,n2),tp) cs'' -> Map.insert n1
                              ConstInfo {constType = tp,
                                        constName = n2,
                                        constId = n1,
                                        constAnno = Null} cs'')
                          cs' (zip names ts))
 CType c' -> case Map.lookup c' tp_trans of
              Just cs_ -> let names = mkNames c n $ length cs_
                              cs' = Map.delete c cs
                          in (Map.insert c (map fst names) trans,
                              foldr (\((n1,n2),c'') cs'' -> Map.insert n1
                                        ConstInfo {constType = CType c'',
                                                  constName = n2,
                                                  constId = n1,
                                                  constAnno = Null} cs'')
                                    cs' (zip names cs_))
              Nothing  -> (trans,cs)
 ParType tp -> prodTToTuple trans tp_trans cs c n tp
 _ -> (trans,cs)

mkExplicitProductsK :: TransMap -> Map.Map Constant TypeInfo
                       -> (TransMap,Map.Map Constant TypeInfo)
mkExplicitProductsK tp_trans1 tps1 = Map.fold
 (\tp (trans,tps) -> if hasProdK tp
                     then prodKToTuple trans tps (typeId tp) (typeName tp)
                           (typeKind tp)
                     else (trans,tps))
 (tp_trans1,tps1) tps1

prodKToTuple :: TransMap -> Map.Map Constant TypeInfo -> Constant -> Name
                -> Kind -> (TransMap, Map.Map Constant TypeInfo)
prodKToTuple trans tps c n k = case k of
 ParKind k1 -> prodKToTuple trans tps c n k1
 ProdKind ks -> let tps' = Map.delete c tps
                    names = mkNames c n $ length ks
                in (Map.insert c (map fst names) trans,
                    foldr (\((n1,n2),kd) tps'' -> Map.insert n1 
                              TypeInfo {typeKind = kd,
                                        typeName = n2,
                                        typeId   = n1,
                                        typeAnno = Null} tps'')
                          tps' (zip names ks))
 MapKind k1 k2 ->
  let (_, tps') = prodKToTuple Map.empty Map.empty c n k2
      tps'' = Map.delete c tps
      tuple = Map.elems tps'
      names = mkNames c n $ length tuple
  in (Map.insert c (map fst names) trans,
      foldr (\((n1,n2),tpi) tps''' -> Map.insert n1
                tpi {typeName = n2,
                     typeId = n1,
                     typeKind = MapKind k1 (typeKind tpi)} tps''')
            tps'' (zip names tuple))
 _ -> error "Invalid call to prodKToTuple"
                          

mkNames :: Constant -> Name -> Int -> [(Constant,Name)]
mkNames c n i =
 let (mkC,t1) = case c of
       A_Lower_Word t    -> (A_Lower_Word,t)
       A_Single_Quoted t -> (A_Single_Quoted,t)
     (mkN,t2) = case n of
                 N_Atomic_Word a -> case a of
                  A_Lower_Word t    -> (N_Atomic_Word . A_Lower_Word,t)
                  A_Single_Quoted t -> (N_Atomic_Word . A_Single_Quoted,t)
                 N_Integer t -> (N_Atomic_Word . A_Lower_Word,
                                 Token ("i"++show t) nullRange)
                 T0N_Unsigned_Integer t ->
                  (N_Atomic_Word . A_Lower_Word,Token ("i"++show t) nullRange)
 in zip (map (\i' -> mkC $ Token (show t1 ++ "_" ++ show i') nullRange) [1..i])
        (map (\i' -> mkN $ Token (show t2 ++ "_" ++ show i') nullRange) [1..i])

hasProdK :: TypeInfo -> Bool
hasProdK = isProdK . typeKind

isProdK :: Kind -> Bool
isProdK Kind            = False
isProdK (MapKind _ k2)  = isProdK k2
isProdK (ProdKind _)    = True
isProdK (SysType _)     = False
isProdK (VKind _)       = False
isProdK (ParKind k)     = isProdK k

hasProdT :: TransMap -> ConstInfo -> Bool
hasProdT t = isProdT t . constType

isProdT :: TransMap -> Type -> Bool
isProdT _ TType          = False
isProdT _ OType          = False
isProdT _ IType          = False
isProdT m (MapType _ t2) = isProdT m t2
isProdT _ (ProdType _)   = True
isProdT m (CType c)      = case Map.lookup c m of
                            Just _ -> True
                            Nothing -> False
isProdT _ (SType _)      = False
isProdT _ (VType _)      = False
isProdT m (ParType t)    = isProdT m t
