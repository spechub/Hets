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

module Comorphisms.THFP_ST2THF0_ST where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Id (Token(..))
import Common.AS_Annotation (Named)

import THF.Logic_THF
import THF.Cons
import THF.Sign
import qualified THF.Sublogic as SL
import THF.As
import THF.Utils

import qualified Data.Map as Map

data THFP_ST2THF0_ST = THFP_ST2THF0_ST deriving Show

instance Language THFP_ST2THF0_ST

instance Comorphism THFP_ST2THF0_ST
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree where
    sourceLogic THFP_ST2THF0_ST = THF
    sourceSublogic THFP_ST2THF0_ST = SL.tHFP_ST
    targetLogic THFP_ST2THF0_ST = THF
    mapSublogic THFP_ST2THF0_ST _ = Just SL.tHF0_ST
    map_theory THFP_ST2THF0_ST = trans_theory
    has_model_expansion THFP_ST2THF0_ST = True

trans_theory :: (SignTHF,[Named THFFormula])
                -> Result (SignTHF,[Named THFFormula])
trans_theory (sig, sentences1) = do
 let (tp_trans,cs_trans,sig1)  = head . filter (\(tp_t,_,Sign tps cs _) -> 
                                     not (any hasProdK $ Map.elems tps)
                                  && not (any (hasProdT tp_t) $ Map.elems cs)) $
                 iterate makeExplicitProducts (Map.empty, Map.empty, sig)
     sig2 = sig1 {consts =
      Map.map (\c -> c {constType = curryConstType tp_trans
                                 (constType c)}) $ consts sig1}
 sentences <- rewriteSen tp_trans cs_trans sentences1
 return (recreateSymbols sig2,sentences)

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
                in foldl (\t1' t2' -> MapType t2' t1') t2 (reverse ts')
 CType c     -> let cs = map CType $ curryConst m c
                in foldl (\t1' t2' -> MapType t2' t1') t2 (reverse cs)
 ParType t   -> prodToMapType m t t2
 _           -> MapType t1 t2
 
curryConst :: TransMap -> Constant -> [Constant]
curryConst m c = case Map.lookup c m of
 Just cs -> concat $ map (curryConst m) cs
 Nothing -> [c]

rewriteSen :: TransMap -> TransMap -> [Named THFFormula]
               -> Result [Named THFFormula]
rewriteSen tp_trans cs_trans = mapR (rewriteSen' tp_trans cs_trans)

rewriteFns :: RewriteFuns (TransMap,TransMap)
rewriteFns = rewriteTHF0 {
 rewriteLogicFormula = rewriteLogicFormula',
 rewriteBinaryFormula =
  \ _ bf -> mkError "This function shouldn't be called!" bf,
 rewriteBinaryTuple =
  \ _ bt -> mkError "This function shouldn't be called!" bt,
 rewriteVariableList = rewriteVariableList',
 rewriteConst = rewriteConst'
}

rewriteSen' :: TransMap -> TransMap -> Named THFFormula
               -> Result (Named THFFormula)
rewriteSen' tp_trans cs_trans = rewriteSenFun (rewriteFns,(tp_trans,cs_trans))

rewriteLogicFormula' :: (RewriteFuns (TransMap,TransMap),(TransMap, TransMap))
                       -> THFLogicFormula -> Result THFLogicFormula
rewriteLogicFormula' d lf = case lf of
 TLF_THF_Binary_Formula bf -> do
  bf' <- rewriteBinaryFormula' d bf
  case bf' of
   Left bf'' -> return $ TLF_THF_Binary_Formula bf''
   Right uf -> return $ TLF_THF_Unitary_Formula uf
 _ -> (rewriteLogicFormula rewriteTHF0) d lf

rewriteBinaryFormula' :: (RewriteFuns (TransMap,TransMap),(TransMap, TransMap))
                        -> THFBinaryFormula
                        -> Result (Either THFBinaryFormula THFUnitaryFormula)
rewriteBinaryFormula' d@(fns,_) bf = case bf of
 TBF_THF_Binary_Pair uf1 cn uf2 -> do
  uf1' <- (rewriteUnitaryFormula fns) d uf1
  uf2' <- (rewriteUnitaryFormula fns) d uf2
  case (toTuple uf1',cn,toTuple uf2') of
      (Just (TUF_THF_Tuple t1), Infix_Equality, 
       Just (TUF_THF_Tuple t2)) -> if length t1 == length t2
        then return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_And_Formula $
              map (\(t1',t2') ->
               TUF_THF_Logic_Formula_Par $ TLF_THF_Binary_Formula $
                TBF_THF_Binary_Pair (logicFormula2UnitaryFormula t1')
                 cn (logicFormula2UnitaryFormula t2')) (zip t1 t2)
        else mkError ("THFP2THF0.rewriteBinaryFormula: Equality on tuples " ++
                      "of different size!") bf
      _ -> return $ Left $ TBF_THF_Binary_Pair uf1' cn uf2'
 TBF_THF_Binary_Tuple bt -> rewriteBinaryTuple' d bt
 _ -> (rewriteBinaryFormula rewriteTHF0) d bf
  >>= return . Left

toTuple :: THFUnitaryFormula -> Maybe THFUnitaryFormula
toTuple u@(TUF_THF_Tuple _) = Just u
toTuple (TUF_THF_Logic_Formula_Par
  (TLF_THF_Unitary_Formula u)) = Just u
toTuple _ = Nothing

logicFormula2UnitaryFormula :: THFLogicFormula -> THFUnitaryFormula
logicFormula2UnitaryFormula l = case l of
 TLF_THF_Unitary_Formula uf -> uf
 _ -> TUF_THF_Logic_Formula_Par l

rewriteBinaryTuple' :: (RewriteFuns (TransMap,TransMap),(TransMap, TransMap))
                        -> THFBinaryTuple
                        -> Result (Either THFBinaryFormula THFUnitaryFormula)
rewriteBinaryTuple' d@(fns,_) bt = case bt of
 TBT_THF_Apply_Formula ufs -> do
  ufs' <- mapR ((rewriteUnitaryFormula fns) d) ufs
  case ufs' of
      []   -> mkError "THFP2THF0.rewriteBinaryTuple: Illegal Application!" bt
      _:[] -> mkError "THFP2THF0.rewriteBinaryTuple: Illegal Application!" bt
      fn:args -> case removeParensUnitaryFormula fn of
       (TUF_THF_Atom (T0A_Constant c)) ->
         case show . toToken $ c of
           'p':'r':'_':i ->
              case args of
               tuple:[] ->
                let i' = read i :: Int
                in unpack_tuple tuple i'
               _ -> mkError ("THFP2THF0.rewriteBinaryTuple: Invalid " ++
                            "argument for projection: " ++ show args) ufs
           _ -> return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
                 fn:(flattenTuples args)
       TUF_THF_Tuple lfs ->
         mapR (\l -> do app' <- rewriteBinaryTuple' d .
                                 TBT_THF_Apply_Formula $
                                  (TUF_THF_Logic_Formula_Par l):args
                        return $ case app' of
                          Left bf  -> TLF_THF_Binary_Formula bf
                          Right uf -> TLF_THF_Unitary_Formula uf) lfs
          >>= ((rewriteUnitaryFormula fns) d) . TUF_THF_Tuple
          >>= return . Right
       _ -> return $ Left $ TBF_THF_Binary_Tuple $ TBT_THF_Apply_Formula $
             fn:(flattenTuples args)
 _ -> (rewriteBinaryTuple rewriteTHF0) d bt
  >>= return . Left . TBF_THF_Binary_Tuple

flattenTuples :: [THFUnitaryFormula] -> [THFUnitaryFormula]
flattenTuples ufs = concat . map flattenTuple $ ufs

flattenTuple :: THFUnitaryFormula -> [THFUnitaryFormula]
flattenTuple u = case removeParensUnitaryFormula u of
 TUF_THF_Tuple lfs ->
  concat . map (flattenTuple . TUF_THF_Logic_Formula_Par) $ lfs
 _ -> [u]

unpack_tuple :: THFUnitaryFormula -> Int
                -> Result (Either THFBinaryFormula THFUnitaryFormula)
unpack_tuple uf i = case removeParensUnitaryFormula uf of
 TUF_THF_Tuple lfs -> if i > length lfs
  then mkError "THFP2THF0.unpack_tuple: Tuple has too few elements!" uf
  else case lfs!!(i-1) of
        TLF_THF_Binary_Formula bf -> return $ Left bf
        TLF_THF_Unitary_Formula uf' -> return $ Right uf'
        lf -> mkError ("THFP2THF0.unpack_tuple: " ++ show lf
                       ++ " is not in THF0!") uf
 _ -> mkError ("THFP2THF0.unpack_tuple: " ++ show uf ++ " is not a tuple!") uf

removeParensUnitaryFormula :: THFUnitaryFormula -> THFUnitaryFormula
removeParensUnitaryFormula (TUF_THF_Logic_Formula_Par
 (TLF_THF_Unitary_Formula uf)) = uf
removeParensUnitaryFormula uf = uf

rewriteVariableList' :: (RewriteFuns (TransMap,TransMap),(TransMap,TransMap))
                       -> [THFVariable] -> Result [THFVariable]
rewriteVariableList' (_,(tp_trans,cs_trans)) vs = do
 vs' <- mapR (\v -> case v of
             TV_THF_Typed_Variable t tp ->
              case thfTopLevelTypeToType tp of
               Just tp' -> let cs = constMakeExplicitProduct tp_trans
                                     (A_Lower_Word t) tp'
                           in mapM (\(c,tp'') ->
                                 (typeToTopLevelType
                                  (curryConstType tp_trans tp''))
                                  >>= return . TV_THF_Typed_Variable
                                       (toToken c)) cs
               Nothing ->
                mkError ("THFP2THF0.rewriteVariableList: Couldn't " ++
                         "type " ++ show tp) tp
             TV_Variable t -> case transToken cs_trans t of
                               [_] -> return [v]
                               t' -> return $ map TV_Variable t') vs
 return $ concat vs'

transToken :: TransMap -> Token -> [Token]
transToken m t = case Map.toList $
  Map.filterWithKey (\c _ -> (toToken c) == t) m of
                   (_,cs):_ -> concat $ map (transToken m . toToken) cs
                   [] -> [t]

rewriteConst' :: (RewriteFuns (TransMap,TransMap),(TransMap, TransMap))
                  -> Constant -> Result THFUnitaryFormula
rewriteConst' (_,(_,m)) c = case transConst' m c of
 [] -> return $ TUF_THF_Atom (T0A_Constant c)
 lfs -> return $ TUF_THF_Tuple lfs

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
