{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{- |
Module      :  $Header$
Description :  A couple helper functions
Copyright   :  (c) J. von Schroeder, DFKI Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <j.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable

-}
module THF.Utils (
 Unique,
 evalUnique,
 numbered,
 mkNames,
 recreateSymbols,
 typeToTopLevelType,
 typeToUnitaryType,
 typeToBinaryType,
 toToken,
 RewriteFuns(..),
 rewriteSenFun,
 rewriteTHF0
) where

import THF.As
import THF.Sign
import THF.Cons
import THF.Print()

import Common.Id (Token(..),nullRange)
import Common.AS_Annotation (Named,SenAttr(..))
import Common.Result

import Control.Monad.State
import Control.Monad.Identity
import Control.Monad (mapM)

import qualified Data.Map as Map

{- taken from http://www.haskell.org/haskellwiki/New_monads/MonadUnique -}
newtype UniqueT m a = UniqueT (StateT Integer m a)
    deriving (Functor, Monad, MonadTrans, MonadIO)
 
newtype Unique a = Unique (UniqueT Identity a)
    deriving (Functor, Monad, MonadUnique)
 
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
  A_Lower_Word t    -> A_Lower_Word $ rename t
  A_Single_Quoted t -> A_Single_Quoted $ rename t
 where rename = (\t -> t { tokStr = (tokStr t) ++ s})

addSuffixN :: String -> Name -> Name
addSuffixN s n = case n of
  N_Atomic_Word a -> N_Atomic_Word $ addSuffix s a
  N_Integer t -> rename s t
  T0N_Unsigned_Integer t -> rename s t
 where rename = \sf t -> N_Atomic_Word $ addSuffix sf
                         (A_Lower_Word $ t { tokStr = "i"++show t })

numbered :: AtomicWord -> Unique AtomicWord
numbered a = do
 f <- fresh
 return (addSuffix ("_"++show f) a)

mkNames :: Constant -> Name -> Int -> [(Constant,Name)]
mkNames c n i = evalUnique $ replicateM i $ do
 f <- fresh
 let s = "_"++show f
 return (addSuffix s c,addSuffixN s n)

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

toToken :: Constant -> Token
toToken (A_Lower_Word t)    = t
toToken (A_Single_Quoted t) = t

typeToTopLevelType :: Type -> Result THFTopLevelType
typeToTopLevelType t = case t of
 TType -> return $ T0TLT_Defined_Type (DT_tType)
 OType -> return $ T0TLT_Defined_Type (DT_oType)
 IType -> return $ T0TLT_Defined_Type (DT_iType)
 MapType t1 t2 -> mapM typeToUnitaryType [t1,t2] >>=
  return . T0TLT_THF_Binary_Type . TBT_THF_Mapping_Type
 ProdType ts   -> mapM typeToUnitaryType ts >>=
  return . T0TLT_THF_Binary_Type . TBT_THF_Xprod_Type
 CType c       -> return $ T0TLT_Constant c
 SType t'      -> return $ T0TLT_System_Type t'
 VType t'      -> return $ T0TLT_Variable t'
 ParType t'    -> typeToBinaryType t' >>=
  return . T0TLT_THF_Binary_Type . T0BT_THF_Binary_Type_Par

typeToUnitaryType :: Type -> Result THFUnitaryType
typeToUnitaryType t = do
 tl <- typeToTopLevelType t
 case tl of
  T0TLT_Constant c        -> return $ T0UT_Constant c
  T0TLT_Variable t'       -> return $ T0UT_Variable t'
  T0TLT_Defined_Type d    -> return $ T0UT_Defined_Type d
  T0TLT_System_Type t'    -> return $ T0UT_System_Type t'
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
 rewriteLogicFormula :: (RewriteFuns a,a) -> THFLogicFormula
  -> Result THFLogicFormula,
 rewriteBinaryFormula :: (RewriteFuns a,a) -> THFBinaryFormula
  -> Result THFBinaryFormula,
 rewriteUnitaryFormula :: (RewriteFuns a,a) -> THFUnitaryFormula
  -> Result THFUnitaryFormula,
 rewriteBinaryPair :: (RewriteFuns a,a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula)
                       -> Result THFBinaryFormula,
 rewriteBinaryTuple :: (RewriteFuns a,a) -> THFBinaryTuple
                        -> Result THFBinaryTuple,
 rewriteQuantifiedFormula :: (RewriteFuns a,a) -> THFQuantifiedFormula
                              -> Result THFQuantifiedFormula,
 rewriteAtom :: (RewriteFuns a,a) -> THFAtom -> Result THFUnitaryFormula,
 rewriteVariableList :: (RewriteFuns a,a) -> [THFVariable]
                         -> Result [THFVariable],
 rewriteConst :: (RewriteFuns a,a) -> Constant -> Result THFUnitaryFormula,
 rewriteConnTerm :: (RewriteFuns a,a) -> THFConnTerm -> Result THFConnTerm }

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
rewriteSenFun (fns,d) sen = do
 sen' <- case sentence $ sen of
             TF_THF_Logic_Formula lf ->
              rewriteLogicFormula fns (fns,d) lf
               >>= return . TF_THF_Logic_Formula
             T0F_THF_Typed_Const tc ->
              mkError "THF.Utils.rewriteSen: Typed constants are not in THF0! "
               tc
             TF_THF_Sequent s ->
              mkError "THF.Utils.rewriteSen: Sequents are not in THF0!" s
 return $ sen { sentence = sen' }

rewriteLogicFormula' :: (RewriteFuns a, a) -> THFLogicFormula
                        -> Result THFLogicFormula
rewriteLogicFormula' (fns,d) lf = case lf of
 TLF_THF_Binary_Formula bf ->
  (rewriteBinaryFormula fns) (fns,d) bf
   >>= return . TLF_THF_Binary_Formula
 TLF_THF_Unitary_Formula uf ->
  (rewriteUnitaryFormula fns) (fns,d) uf
   >>= return . TLF_THF_Unitary_Formula
 TLF_THF_Type_Formula _ ->
  mkError "THF.Utils.rewriteLogicFormula: Type Formula not in THF0!" lf
 TLF_THF_Sub_Type _ ->
  mkError "THF.Utils.rewriteLogicFormula: Sub Type Formula not in THF0!" lf

rewriteBinaryFormula' :: (RewriteFuns a, a) -> THFBinaryFormula
                          -> Result THFBinaryFormula
rewriteBinaryFormula' (fns,d) bf = case bf of
 TBF_THF_Binary_Type _ -> mkError
  "THF.Utils.rewriteBinaryFormula: Binary Type not in THF0!" bf
 TBF_THF_Binary_Pair uf1 cn uf2 ->
  (rewriteBinaryPair fns) (fns,d) (uf1,cn,uf2)
 TBF_THF_Binary_Tuple bt ->
  (rewriteBinaryTuple fns) (fns,d) bt
   >>= return . TBF_THF_Binary_Tuple

rewriteBinaryPair' :: (RewriteFuns a, a) -> (THFUnitaryFormula,
                       THFPairConnective, THFUnitaryFormula)
                       -> Result THFBinaryFormula
rewriteBinaryPair' (fns,d) (uf1,cn,uf2) = do
 uf1' <- (rewriteUnitaryFormula fns) (fns,d) uf1
 uf2' <- (rewriteUnitaryFormula fns) (fns,d) uf2
 return $ TBF_THF_Binary_Pair uf1' cn uf2'

rewriteBinaryTuple' :: (RewriteFuns a, a) -> THFBinaryTuple
                        -> Result THFBinaryTuple
rewriteBinaryTuple' (fns,d) bt = case bt of
 TBT_THF_Or_Formula ufs ->
  mapR ((rewriteUnitaryFormula fns) (fns,d)) ufs
   >>= return . TBT_THF_Or_Formula
 TBT_THF_And_Formula ufs ->
  mapR ((rewriteUnitaryFormula fns) (fns,d)) ufs
   >>= return . TBT_THF_And_Formula
 TBT_THF_Apply_Formula ufs ->
  mapR ((rewriteUnitaryFormula fns) (fns,d)) ufs
   >>= return . TBT_THF_Apply_Formula

rewriteUnitaryFormula' :: (RewriteFuns a, a) -> THFUnitaryFormula
                           -> Result THFUnitaryFormula
rewriteUnitaryFormula' (fns,d) uf = case uf of
 TUF_THF_Conditional _ _ _ ->
  mkError ("THF.Utils.rewriteUnitaryFOrmula: "++
           "Conditional not in THF0!") uf
 TUF_THF_Quantified_Formula qf ->
  (rewriteQuantifiedFormula fns) (fns,d) qf
   >>= return . TUF_THF_Quantified_Formula
 TUF_THF_Unary_Formula c lf ->
  (rewriteLogicFormula fns) (fns,d) lf
   >>= return . (TUF_THF_Unary_Formula c)
 TUF_THF_Atom a ->
  (rewriteAtom fns) (fns,d) a
 TUF_THF_Tuple t ->
  mapR ((rewriteLogicFormula fns) (fns, d)) t
   >>= return . TUF_THF_Tuple
 TUF_THF_Logic_Formula_Par lf ->
  (rewriteLogicFormula fns) (fns,d) lf
   >>= return . TUF_THF_Logic_Formula_Par
 T0UF_THF_Abstraction vs uf' -> do
  vs' <- (rewriteVariableList fns) (fns, d) vs
  uf'' <- (rewriteUnitaryFormula fns) (fns, d) uf'
  return $ T0UF_THF_Abstraction vs' uf''

rewriteQuantifiedFormula' :: (RewriteFuns a, a) -> THFQuantifiedFormula
                             -> Result THFQuantifiedFormula
rewriteQuantifiedFormula' (fns,d) qf = case qf of
 TQF_THF_Quantified_Formula q vs uf -> do
  vs' <- (rewriteVariableList fns) (fns,d) vs
  uf' <- (rewriteUnitaryFormula fns) (fns,d) uf
  return $ TQF_THF_Quantified_Formula q vs' uf'
 T0QF_THF_Quantified_Var q vs uf -> do
  vs' <- (rewriteVariableList fns) (fns,d) vs
  uf' <- (rewriteUnitaryFormula fns) (fns,d) uf
  return $ T0QF_THF_Quantified_Var q vs' uf'
 T0QF_THF_Quantified_Novar _ _ ->
  mkError "THF.Utils.rewriteQuantifiedFormula: Quantified Novar not in THF0!" qf

rewriteVariableList' :: (RewriteFuns a, a) -> [THFVariable]
                         -> Result [THFVariable]
rewriteVariableList' _ = return

rewriteAtom' :: (RewriteFuns a, a) -> THFAtom -> Result THFUnitaryFormula
rewriteAtom' (fns,d) a = case a of
 TA_Term _ -> mkError "THF.Utils.rewriteAtom: Term not in THF0!" a
 TA_THF_Conn_Term c ->
  (rewriteConnTerm fns) (fns,d) c
   >>= return . TUF_THF_Atom . TA_THF_Conn_Term
 TA_Defined_Type _ ->
  mkError "THF.Utils.rewriteAtom: Defined Type not in THF0!" a
 TA_Defined_Plain_Formula _ ->
  mkError "THF.Utils.rewriteAtom: Defined Plain Formula not in THF0!" a
 TA_System_Type _ ->
  mkError "THF.Utils.rewriteAtom: System Type not in THF0!" a
 TA_System_Atomic_Formula _ ->
  mkError "THF.Utils.rewriteAtom: System Atomic Formula not in THF0!" a
 T0A_Constant c -> (rewriteConst fns) (fns,d) c
 T0A_Defined_Constant _ -> return $ TUF_THF_Atom a
 T0A_System_Constant _ -> return $ TUF_THF_Atom a
 T0A_Variable _ -> return $ TUF_THF_Atom a

rewriteConst' :: (RewriteFuns a, a) -> Constant -> Result THFUnitaryFormula
rewriteConst' _ = return . TUF_THF_Atom . T0A_Constant

rewriteConnTerm' :: (RewriteFuns a, a) -> THFConnTerm -> Result THFConnTerm
rewriteConnTerm' _ c = case c of
 TCT_THF_Pair_Connective _ ->
  mkError "THF.Utils.rewriteConnTerm: Pair Connective not in THF0!" c
 _ -> return c
