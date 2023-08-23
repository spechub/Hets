{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  ./THF/Utils.hs
Description :  A couple helper functions
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

-}
module THF.Utils (
 Unique (..),
 UniqueT,
 fresh,
 evalUniqueT,
 evalUnique,
 numbered,
 numberedTok,
 mkNames,
 addSuffix,
 recreateSymbols,
 thfTopLevelTypeToType,
 typeToTopLevelType,
 typeToUnitaryType,
 typeToBinaryType,
 toToken,
 toId,
 RewriteFuns (..),
 rewriteSenFun,
 rewriteTHF0,
 AnaFuns (..),
 anaSenFun,
 anaTHF0
) where

import THF.As
import THF.Sign
import THF.Cons
import THF.Print ()

import Common.Id (Token (..), Id, mkId, nullRange)
import Common.AS_Annotation (Named, SenAttr (..))
import Common.Result

import Control.Applicative ()
import Control.Monad.State
import Control.Monad.Identity

import qualified Data.Map as Map
import Data.Maybe (fromJust, isJust)

-- taken from http://www.haskell.org/haskellwiki/New_monads/MonadUnique
newtype UniqueT m a = UniqueT (StateT Integer m a)
    deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

newtype Unique a = Unique (UniqueT Identity a)
    deriving (Functor, Applicative, Monad, MonadUnique)

class Monad m => MonadUnique m where
    fresh :: m Integer

instance (Monad m) => MonadUnique (UniqueT m) where
    fresh = UniqueT $ do
                n <- get
                put (succ n)
                return n

evalUniqueT :: Monad m => UniqueT m a -> m a
evalUniqueT (UniqueT s) = evalStateT s 1

evalUnique :: Unique a -> a
evalUnique (Unique s) = runIdentity (evalUniqueT s)

addSuffix :: String -> AtomicWord -> AtomicWord
addSuffix s a = case a of
  A_Lower_Word t -> A_Lower_Word $ rename t
  A_Single_Quoted t -> A_Single_Quoted $ rename t
 where rename t = t { tokStr = tokStr t ++ s }

addSuffixN :: String -> Name -> Name
addSuffixN s n = case n of
  N_Atomic_Word a -> N_Atomic_Word $ addSuffix s a
  N_Integer t -> rename s t
  T0N_Unsigned_Integer t -> rename s t
 where rename sf t = N_Atomic_Word $ addSuffix sf
                      (A_Lower_Word $ t { tokStr = 'i' : show t })

numbered :: Monad m => AtomicWord -> UniqueT m AtomicWord
numbered a = do
 f <- fresh
 return (addSuffix ('_' : show f) a)

numberedTok :: Monad m => Token -> UniqueT m Token
numberedTok = liftM toToken . numbered . A_Single_Quoted

mkNames :: Constant -> Name -> Int -> [(Constant, Name)]
mkNames c n i = evalUnique $ replicateM i $ do
 f <- fresh
 let s = '_' : show f
 return (addSuffix s c, addSuffixN s n)

recreateSymbols :: SignTHF -> SignTHF
recreateSymbols (Sign tps cs _) =
 let name = N_Atomic_Word
     symbs1 = foldl (\ m (c, t) -> Map.insert c
                      (Symbol c (name c) (ST_Type $ typeKind t)) m)
              Map.empty $ Map.toList tps
     symbs = foldl (\ m (c, k) -> Map.insert c
                      (Symbol c (name c) (ST_Const $ constType k)) m)
              symbs1 $ Map.toList cs
 in Sign tps cs symbs

toToken :: Constant -> Token
toToken (A_Lower_Word t) = t
toToken (A_Single_Quoted t) = t

toId :: Constant -> Id
toId c = mkId [toToken c]

thfTopLevelTypeToType :: THFTopLevelType -> Maybe Type
thfTopLevelTypeToType tlt = case tlt of
    T0TLT_Defined_Type dt -> thfDefinedTypeToType dt
    T0TLT_THF_Binary_Type bt -> thfBinaryTypeToType bt
    T0TLT_Constant c -> Just $ CType c
    T0TLT_System_Type st -> Just $ SType st
    T0TLT_Variable v -> Just $ VType v
    _ -> Nothing

thfDefinedTypeToType :: DefinedType -> Maybe Type
thfDefinedTypeToType dt = case dt of
    DT_oType -> Just OType
    DT_o -> Just OType
    DT_iType -> Just IType
    DT_i -> Just IType
    DT_tType -> Just TType
    _ -> Nothing

thfBinaryTypeToType :: THFBinaryType -> Maybe Type
thfBinaryTypeToType bt = case bt of
    TBT_THF_Mapping_Type [] -> Nothing
    TBT_THF_Mapping_Type (_ : []) -> Nothing
    TBT_THF_Mapping_Type mt -> thfMappingTypeToType mt
    T0BT_THF_Binary_Type_Par btp -> fmap ParType (thfBinaryTypeToType btp)
    TBT_THF_Xprod_Type [] -> Nothing
    TBT_THF_Xprod_Type (u : []) -> thfUnitaryTypeToType u
    TBT_THF_Xprod_Type us -> let us' = map thfUnitaryTypeToType us
                                       in if all isJust us' then
                                           (Just . ProdType) $ map fromJust us'
                                          else Nothing
    _ -> Nothing

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
    T0UT_Defined_Type dt -> thfDefinedTypeToType dt
    T0UT_Constant c -> Just $ CType c
    T0UT_System_Type st -> Just $ SType st
    T0UT_Variable v -> Just $ VType v
    _ -> Nothing

typeToTopLevelType :: Type -> Result THFTopLevelType
typeToTopLevelType t = case t of
 TType -> return $ T0TLT_Defined_Type DT_tType
 OType -> return $ T0TLT_Defined_Type DT_oType
 IType -> return $ T0TLT_Defined_Type DT_iType
 MapType t1 t2 -> liftM (T0TLT_THF_Binary_Type . TBT_THF_Mapping_Type)
                        (mapM typeToUnitaryType [t1, t2])
 ProdType ts -> liftM (T0TLT_THF_Binary_Type . TBT_THF_Xprod_Type)
                      (mapM typeToUnitaryType ts)
 CType c -> return $ T0TLT_Constant c
 SType t' -> return $ T0TLT_System_Type t'
 VType t' -> return $ T0TLT_Variable t'
 ParType t' -> liftM (T0TLT_THF_Binary_Type . T0BT_THF_Binary_Type_Par)
                     (typeToBinaryType t')

typeToUnitaryType :: Type -> Result THFUnitaryType
typeToUnitaryType t = do
 tl <- typeToTopLevelType t
 case tl of
  T0TLT_Constant c -> return $ T0UT_Constant c
  T0TLT_Variable t' -> return $ T0UT_Variable t'
  T0TLT_Defined_Type d -> return $ T0UT_Defined_Type d
  T0TLT_System_Type t' -> return $ T0UT_System_Type t'
  T0TLT_THF_Binary_Type b -> return $ T0UT_THF_Binary_Type_Par b
  TTLT_THF_Logic_Formula _ -> mkError "Not yet implemented!" nullRange

typeToBinaryType :: Type -> Result THFBinaryType
typeToBinaryType t = do
 tl <- typeToTopLevelType t
 case tl of
  T0TLT_THF_Binary_Type b -> return b
  _ -> mkError ("Cannot represent type " ++ show t ++
                "as THFBinaryType!") nullRange

data RewriteFuns a = RewriteFuns {
 rewriteLogicFormula :: (RewriteFuns a, a) -> THFLogicFormula
  -> Result THFLogicFormula,
 rewriteBinaryFormula :: (RewriteFuns a, a) -> THFBinaryFormula
  -> Result THFBinaryFormula,
 rewriteUnitaryFormula :: (RewriteFuns a, a) -> THFUnitaryFormula
  -> Result THFUnitaryFormula,
 rewriteBinaryPair :: (RewriteFuns a, a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula)
                       -> Result THFBinaryFormula,
 rewriteBinaryTuple :: (RewriteFuns a, a) -> THFBinaryTuple
                        -> Result THFBinaryTuple,
 rewriteQuantifiedFormula :: (RewriteFuns a, a) -> THFQuantifiedFormula
                              -> Result THFQuantifiedFormula,
 rewriteAtom :: (RewriteFuns a, a) -> THFAtom -> Result THFUnitaryFormula,
 rewriteVariableList :: (RewriteFuns a, a) -> [THFVariable]
                         -> Result [THFVariable],
 rewriteConst :: (RewriteFuns a, a) -> Constant -> Result THFUnitaryFormula,
 rewriteConnTerm :: (RewriteFuns a, a) -> THFConnTerm -> Result THFConnTerm }

rewriteTHF0 :: RewriteFuns a
rewriteTHF0 = RewriteFuns {
 rewriteLogicFormula = rewriteLogicFormula',
 rewriteBinaryFormula = rewriteBinaryFormula',
 rewriteUnitaryFormula = rewriteUnitaryFormula',
 rewriteBinaryPair = rewriteBinaryPair',
 rewriteBinaryTuple = rewriteBinaryTuple',
 rewriteQuantifiedFormula = rewriteQuantifiedFormula',
 rewriteAtom = rewriteAtom',
 rewriteVariableList = rewriteVariableList',
 rewriteConst = rewriteConst',
 rewriteConnTerm = rewriteConnTerm' }

rewriteSenFun :: (RewriteFuns a, a) -> Named THFFormula
               -> Result (Named THFFormula)
rewriteSenFun (fns, d) sen = do
 sen' <- case sentence sen of
             TF_THF_Logic_Formula lf ->
              liftM TF_THF_Logic_Formula (rewriteLogicFormula fns (fns, d) lf)
             T0F_THF_Typed_Const tc ->
              mkError "THF.Utils.rewriteSen: Typed constants are not in THF0! "
               tc
             TF_THF_Sequent s ->
              mkError "THF.Utils.rewriteSen: Sequents are not in THF0!" s
 return $ sen { sentence = sen' }

rewriteLogicFormula' :: (RewriteFuns a, a) -> THFLogicFormula
                        -> Result THFLogicFormula
rewriteLogicFormula' (fns, d) lf = case lf of
 TLF_THF_Binary_Formula bf -> liftM TLF_THF_Binary_Formula $
  rewriteBinaryFormula fns (fns, d) bf
 TLF_THF_Unitary_Formula uf -> liftM TLF_THF_Unitary_Formula $
  rewriteUnitaryFormula fns (fns, d) uf
 TLF_THF_Type_Formula _ ->
  mkError "THF.Utils.rewriteLogicFormula: Type Formula not in THF0!" lf
 TLF_THF_Sub_Type _ ->
  mkError "THF.Utils.rewriteLogicFormula: Sub Type Formula not in THF0!" lf

rewriteBinaryFormula' :: (RewriteFuns a, a) -> THFBinaryFormula
                          -> Result THFBinaryFormula
rewriteBinaryFormula' (fns, d) bf = case bf of
 TBF_THF_Binary_Type _ -> mkError
  "THF.Utils.rewriteBinaryFormula: Binary Type not in THF0!" bf
 TBF_THF_Binary_Pair uf1 cn uf2 ->
  rewriteBinaryPair fns (fns, d) (uf1, cn, uf2)
 TBF_THF_Binary_Tuple bt -> liftM TBF_THF_Binary_Tuple $
  rewriteBinaryTuple fns (fns, d) bt

rewriteBinaryPair' :: (RewriteFuns a, a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula)
                       -> Result THFBinaryFormula
rewriteBinaryPair' (fns, d) (uf1, cn, uf2) = do
 uf1' <- rewriteUnitaryFormula fns (fns, d) uf1
 uf2' <- rewriteUnitaryFormula fns (fns, d) uf2
 return $ TBF_THF_Binary_Pair uf1' cn uf2'

rewriteBinaryTuple' :: (RewriteFuns a, a) -> THFBinaryTuple
                        -> Result THFBinaryTuple
rewriteBinaryTuple' (fns, d) bt = case bt of
 TBT_THF_Or_Formula ufs -> liftM TBT_THF_Or_Formula $
  mapR (rewriteUnitaryFormula fns (fns, d)) ufs
 TBT_THF_And_Formula ufs -> liftM TBT_THF_And_Formula $
  mapR (rewriteUnitaryFormula fns (fns, d)) ufs
 TBT_THF_Apply_Formula ufs -> liftM TBT_THF_Apply_Formula $
  mapR (rewriteUnitaryFormula fns (fns, d)) ufs

rewriteUnitaryFormula' :: (RewriteFuns a, a) -> THFUnitaryFormula
                           -> Result THFUnitaryFormula
rewriteUnitaryFormula' (fns, d) uf = case uf of
 TUF_THF_Conditional {} ->
  mkError ("THF.Utils.rewriteUnitaryFOrmula: " ++
           "Conditional not in THF0!") uf
 TUF_THF_Quantified_Formula qf -> liftM TUF_THF_Quantified_Formula $
  rewriteQuantifiedFormula fns (fns, d) qf
 TUF_THF_Unary_Formula c lf -> liftM (TUF_THF_Unary_Formula c) $
  rewriteLogicFormula fns (fns, d) lf
 TUF_THF_Atom a -> rewriteAtom fns (fns, d) a
 TUF_THF_Tuple t -> liftM TUF_THF_Tuple $
  mapR (rewriteLogicFormula fns (fns, d)) t
 TUF_THF_Logic_Formula_Par lf -> liftM TUF_THF_Logic_Formula_Par $
  rewriteLogicFormula fns (fns, d) lf
 T0UF_THF_Abstraction vs uf' -> do
  vs' <- rewriteVariableList fns (fns, d) vs
  uf'' <- rewriteUnitaryFormula fns (fns, d) uf'
  return $ T0UF_THF_Abstraction vs' uf''

rewriteQuantifiedFormula' :: (RewriteFuns a, a) -> THFQuantifiedFormula
                             -> Result THFQuantifiedFormula
rewriteQuantifiedFormula' (fns, d) qf = case qf of
 TQF_THF_Quantified_Formula q vs uf -> do
  vs' <- rewriteVariableList fns (fns, d) vs
  uf' <- rewriteUnitaryFormula fns (fns, d) uf
  return $ TQF_THF_Quantified_Formula q vs' uf'
 T0QF_THF_Quantified_Var q vs uf -> do
  vs' <- rewriteVariableList fns (fns, d) vs
  uf' <- rewriteUnitaryFormula fns (fns, d) uf
  return $ T0QF_THF_Quantified_Var q vs' uf'
 T0QF_THF_Quantified_Novar _ _ ->
  mkError "THF.Utils.rewriteQuantifiedFormula: Quantified Novar not in THF0!" qf

rewriteVariableList' :: (RewriteFuns a, a) -> [THFVariable]
                         -> Result [THFVariable]
rewriteVariableList' _ = return

rewriteAtom' :: (RewriteFuns a, a) -> THFAtom -> Result THFUnitaryFormula
rewriteAtom' (fns, d) a = case a of
 TA_Term _ -> mkError "THF.Utils.rewriteAtom: Term not in THF0!" a
 TA_THF_Conn_Term c -> liftM (TUF_THF_Atom . TA_THF_Conn_Term) $
  rewriteConnTerm fns (fns, d) c
 TA_Defined_Type _ ->
  mkError "THF.Utils.rewriteAtom: Defined Type not in THF0!" a
 TA_Defined_Plain_Formula _ ->
  mkError "THF.Utils.rewriteAtom: Defined Plain Formula not in THF0!" a
 TA_System_Type _ ->
  mkError "THF.Utils.rewriteAtom: System Type not in THF0!" a
 TA_System_Atomic_Formula _ ->
  mkError "THF.Utils.rewriteAtom: System Atomic Formula not in THF0!" a
 T0A_Constant c -> rewriteConst fns (fns, d) c
 T0A_Defined_Constant _ -> return $ TUF_THF_Atom a
 T0A_System_Constant _ -> return $ TUF_THF_Atom a
 T0A_Variable v -> do
  v' <- rewriteVariableList fns (fns, d) [TV_Variable v]
  case v' of
   TV_Variable t : _ -> return $ TUF_THF_Atom $ T0A_Variable t
   _ -> mkError "THF.Utils.rewriteAtom: Invalid rewrite!" v

rewriteConst' :: (RewriteFuns a, a) -> Constant -> Result THFUnitaryFormula
rewriteConst' _ = return . TUF_THF_Atom . T0A_Constant

rewriteConnTerm' :: (RewriteFuns a, a) -> THFConnTerm -> Result THFConnTerm
rewriteConnTerm' _ c = return c

data AnaFuns a b = AnaFuns {
 anaLogicFormula :: (AnaFuns a b, a) -> THFLogicFormula -> Result [b],
 anaBinaryFormula :: (AnaFuns a b, a) -> THFBinaryFormula -> Result [b],
 anaUnitaryFormula :: (AnaFuns a b, a) -> THFUnitaryFormula -> Result [b],
 anaBinaryPair :: (AnaFuns a b, a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula) -> Result [b],
 anaBinaryTuple :: (AnaFuns a b, a) -> THFBinaryTuple -> Result [b],
 anaQuantifiedFormula :: (AnaFuns a b, a) -> THFQuantifiedFormula -> Result [b],
 anaAtom :: (AnaFuns a b, a) -> THFAtom -> Result [b],
 anaVariableList :: (AnaFuns a b, a) -> [THFVariable] -> Result [b],
 anaConst :: (AnaFuns a b, a) -> Constant -> Result [b],
 anaConnTerm :: (AnaFuns a b, a) -> THFConnTerm -> Result [b] }

anaTHF0 :: AnaFuns a b
anaTHF0 = AnaFuns {
 anaLogicFormula = anaLogicFormula',
 anaBinaryFormula = anaBinaryFormula',
 anaUnitaryFormula = anaUnitaryFormula',
 anaBinaryPair = anaBinaryPair',
 anaBinaryTuple = anaBinaryTuple',
 anaQuantifiedFormula = anaQuantifiedFormula',
 anaAtom = anaAtom',
 anaVariableList = anaVariableList',
 anaConst = anaConst',
 anaConnTerm = anaConnTerm' }

anaSenFun :: (AnaFuns a b, a) -> Named THFFormula -> Result [b]
anaSenFun (fns, d) sen = case sentence sen of
 TF_THF_Logic_Formula lf -> anaLogicFormula fns (fns, d) lf
 T0F_THF_Typed_Const tc ->
  mkError "THF.Utils.anaSen: Typed constants are not in THF0! " tc
 TF_THF_Sequent s ->
  mkError "THF.Utils.anaSen: Sequents are not in THF0!" s

anaLogicFormula' :: (AnaFuns a b, a) -> THFLogicFormula -> Result [b]
anaLogicFormula' (fns, d) lf = case lf of
 TLF_THF_Binary_Formula bf -> anaBinaryFormula fns (fns, d) bf
 TLF_THF_Unitary_Formula uf -> anaUnitaryFormula fns (fns, d) uf
 TLF_THF_Type_Formula _ ->
  mkError "THF.Utils.anaLogicFormula: Type Formula not in THF0!" lf
 TLF_THF_Sub_Type _ ->
  mkError "THF.Utils.anaLogicFormula: Sub Type Formula not in THF0!" lf

anaBinaryFormula' :: (AnaFuns a b, a) -> THFBinaryFormula -> Result [b]
anaBinaryFormula' (fns, d) bf = case bf of
 TBF_THF_Binary_Type _ -> mkError
  "THF.Utils.anaBinaryFormula: Binary Type not in THF0!" bf
 TBF_THF_Binary_Pair uf1 cn uf2 ->
  anaBinaryPair fns (fns, d) (uf1, cn, uf2)
 TBF_THF_Binary_Tuple bt -> anaBinaryTuple fns (fns, d) bt

anaBinaryPair' :: (AnaFuns a b, a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula)
                       -> Result [b]
anaBinaryPair' (fns, d) (uf1, _, uf2) = do
 l1 <- anaUnitaryFormula fns (fns, d) uf1
 l2 <- anaUnitaryFormula fns (fns, d) uf2
 return $ l1 ++ l2

anaBinaryTuple' :: (AnaFuns a b, a) -> THFBinaryTuple -> Result [b]
anaBinaryTuple' (fns, d) bt = case bt of
 TBT_THF_Or_Formula ufs -> do
  r <- mapR (anaUnitaryFormula fns (fns, d)) ufs
  return $ concat r
 TBT_THF_And_Formula ufs -> do
  r <- mapR (anaUnitaryFormula fns (fns, d)) ufs
  return $ concat r
 TBT_THF_Apply_Formula ufs -> do
  r <- mapR (anaUnitaryFormula fns (fns, d)) ufs
  return $ concat r

anaUnitaryFormula' :: (AnaFuns a b, a) -> THFUnitaryFormula -> Result [b]
anaUnitaryFormula' (fns, d) uf = case uf of
 TUF_THF_Conditional {} ->
  mkError ("THF.Utils.anaUnitaryFOrmula: " ++
           "Conditional not in THF0!") uf
 TUF_THF_Quantified_Formula qf -> anaQuantifiedFormula fns (fns, d) qf
 TUF_THF_Unary_Formula _ lf -> anaLogicFormula fns (fns, d) lf
 TUF_THF_Atom a -> anaAtom fns (fns, d) a
 TUF_THF_Tuple t -> do
  r <- mapR (anaLogicFormula fns (fns, d)) t
  return $ concat r
 TUF_THF_Logic_Formula_Par lf -> anaLogicFormula fns (fns, d) lf
 T0UF_THF_Abstraction vs uf' -> do
  l1 <- anaVariableList fns (fns, d) vs
  l2 <- anaUnitaryFormula fns (fns, d) uf'
  return $ l1 ++ l2

anaQuantifiedFormula' :: (AnaFuns a b, a) -> THFQuantifiedFormula
                             -> Result [b]
anaQuantifiedFormula' (fns, d) qf = case qf of
 TQF_THF_Quantified_Formula _ vs uf -> do
  l1 <- anaVariableList fns (fns, d) vs
  l2 <- anaUnitaryFormula fns (fns, d) uf
  return $ l1 ++ l2
 T0QF_THF_Quantified_Var _ vs uf -> do
  l1 <- anaVariableList fns (fns, d) vs
  l2 <- anaUnitaryFormula fns (fns, d) uf
  return $ l1 ++ l2
 T0QF_THF_Quantified_Novar _ _ ->
  mkError "THF.Utils.anaQuantifiedFormula: Quantified Novar not in THF0!" qf

anaVariableList' :: (AnaFuns a b, a) -> [THFVariable] -> Result [b]
anaVariableList' _ _ = return []

anaAtom' :: (AnaFuns a b, a) -> THFAtom -> Result [b]
anaAtom' (fns, d) a = case a of
 TA_Term _ -> mkError "THF.Utils.anaAtom: Term not in THF0!" a
 TA_THF_Conn_Term c -> anaConnTerm fns (fns, d) c
 TA_Defined_Type _ ->
  mkError "THF.Utils.anaAtom: Defined Type not in THF0!" a
 TA_Defined_Plain_Formula _ ->
  mkError "THF.Utils.anaAtom: Defined Plain Formula not in THF0!" a
 TA_System_Type _ ->
  mkError "THF.Utils.anaAtom: System Type not in THF0!" a
 TA_System_Atomic_Formula _ ->
  mkError "THF.Utils.anaAtom: System Atomic Formula not in THF0!" a
 T0A_Constant c -> anaConst fns (fns, d) c
 T0A_Defined_Constant _ -> return []
 T0A_System_Constant _ -> return []
 T0A_Variable v -> anaVariableList fns (fns, d) [TV_Variable v]

anaConst' :: (AnaFuns a b, a) -> Constant -> Result [b]
anaConst' _ _ = return []

anaConnTerm' :: (AnaFuns a b, a) -> THFConnTerm -> Result [b]
anaConnTerm' _ _ = return []
