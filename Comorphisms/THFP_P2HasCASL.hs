{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/THFP_P2HasCASL.hs
Description :  Comorphism from THFP to HasCASL
Copyright   :  (c) Jonathan von Schroeder, DFKI Bremen 2013
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Jonathan von Schroeder <jonathan.von_schroeder@dfki.de>
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The embedding comorphism from THFP to HasCASL.
-}

module Comorphisms.THFP_P2HasCASL where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Id
import Common.AS_Annotation

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
import THF.Utils (thfTopLevelTypeToType)
import qualified THF.Sublogic as SL

import Control.Monad

import qualified Data.HashMap.Strict as Map
import qualified Data.Set as Set

data THFP_P2HasCASL = THFP_P2HasCASL deriving Show

instance Language THFP_P2HasCASL

instance Comorphism THFP_P2HasCASL
                THF SL.THFSl
                BasicSpecTHF THFFormula () ()
                SignTHF MorphismTHF SymbolTHF () ProofTree
                HasCASL Sublogic
                BasicSpec Sentence SymbItems SymbMapItems
                Env Morphism Symbol RawSymbol () where
    sourceLogic THFP_P2HasCASL = THF
    sourceSublogic THFP_P2HasCASL = SL.tHFP_P
    targetLogic THFP_P2HasCASL = HasCASL
    mapSublogic THFP_P2HasCASL _ = Just reqSubLogicForTHFP
    map_theory THFP_P2HasCASL = transTheory
    map_symbol THFP_P2HasCASL _ s = propagateErrors "" $ transSymbol s
    has_model_expansion THFP_P2HasCASL = True

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

transTheory :: (SignTHF, [Named THFFormula]) -> Result (Env, [Named Sentence])
transTheory (s@(Sign t c _), nfs) =
 let typeMap_ = Map.fromList $ map (\ (_, THFSign.TypeInfo i _ k _) ->
      let id' = case i of
                A_Lower_Word tok -> tok
                A_Single_Quoted tok -> tok
      in case k of
          Kind -> (mkId [id'], HCLe.TypeInfo {
           HCLe.typeKind = ClassKind (), -- the only supported kind right now
           otherTypeKinds = Set.empty,
           superTypes = Set.empty,
           typeDefn = NoTypeDefn
           })) (Map.toList t)
     assumps_ = Map.fromList $ map (\ (_, THFSign.ConstInfo i _ t' _) ->
      let id' = case i of
                A_Lower_Word tok -> tok
                A_Single_Quoted tok -> tok
      in (mkId [id'], Set.singleton OpInfo {
           opType = TypeScheme [] (toHCType t') (getRange t'),
           opAttrs = Set.empty,
           opDefn = NoOpDefn HCAs.Fun
          })) (Map.toList c)
     env = preEnv { typeMap = typeMap_,
                         assumps = assumps_ }
 in do
    nfs' <- mapM (transNamedFormula s) nfs
    return (env, nfs')

transNamedFormula :: SignTHF -> Named THFFormula -> Result (Named Sentence)
transNamedFormula sig ns = do
 s' <- transFormula sig $ sentence ns
 return $ ns { sentence = Formula s' }

transFormula :: SignTHF -> THFFormula -> Result HCAs.Term
transFormula sig (TF_THF_Logic_Formula lf) = case lf of
 TLF_THF_Binary_Formula bf -> transBinaryFormula sig bf
 TLF_THF_Unitary_Formula uf -> transUnitaryFormula sig uf
 _ -> fatal_error "Not yet implemented!" nullRange
transFormula _ _ = fatal_error "Not yet implemented!" nullRange

transBinaryFormula :: SignTHF -> THFBinaryFormula -> Result HCAs.Term
transBinaryFormula sig bf = case bf of
 TBF_THF_Binary_Pair uf1 cn uf2 -> do
  uf1' <- transUnitaryFormula sig uf1
  uf2' <- transUnitaryFormula sig uf2
  let tm id' = mkLogTerm id' (getRange bf) uf1' uf2'
  case cn of
   Infix_Equality -> return $ tm eqId
   Infix_Inequality -> return $ mkTerm notId notType [] (getRange bf) $ tm eqId
   Equivalent -> return $ tm eqvId
   Implication -> return $ tm implId
   IF -> fatal_error "Not yet implemented!" nullRange
    -- mkEqTerm implId (getRange bf) uf2' uf1'
   XOR -> fatal_error "Not yet implemented!" nullRange
   NOR -> fatal_error "Not yet implemented!" nullRange
   NAND -> fatal_error "Not yet implemented!" nullRange
 TBF_THF_Binary_Tuple bt -> case bt of
   TBT_THF_Or_Formula ufs -> do
    (u : ufs') <- mapM (transUnitaryFormula sig) ufs
    foldM (\ a b -> return $ mkLogTerm orId nullRange a b) u ufs'
   TBT_THF_And_Formula ufs -> do
    (u : ufs') <- mapM (transUnitaryFormula sig) ufs
    foldM (\ a b -> return $ mkLogTerm orId nullRange a b) u ufs'
   TBT_THF_Apply_Formula (u : ufs) -> do
    u' <- transUnitaryFormula sig u
    ufs' <- mapM (transUnitaryFormula sig) ufs
    return $ mkApplTerm u' ufs'
   _ -> fatal_error "Translation not possible!" nullRange
 _ -> fatal_error "Not yet implemented!" nullRange

transUnitaryFormula :: SignTHF -> THFUnitaryFormula -> Result HCAs.Term
transUnitaryFormula sig uf = case uf of
 TUF_THF_Quantified_Formula qf -> do
  (quantifier, vs, uf') <- case qf of
    TQF_THF_Quantified_Formula qf' vs uf' -> case qf' of
     TQ_ForAll -> return (Universal, vs, uf')
     TQ_Exists -> return (Existential, vs, uf')
     _ -> fatal_error "Not yet implemented!" nullRange
    T0QF_THF_Quantified_Var q vs uf' -> case q of
     T0Q_ForAll -> return (Universal, vs, uf')
     T0Q_Exists -> return (Existential, vs, uf')
    _ -> fatal_error "Not yet implemented!" nullRange
  uf'' <- transUnitaryFormula sig uf'
  let vs' = map variable2VarDecl vs
  return (QuantifiedTerm quantifier vs' uf'' (getRange uf))
 TUF_THF_Unary_Formula c lf -> do
  lf' <- transFormula sig (TF_THF_Logic_Formula lf)
  case c of
   Negation -> return $ mkTerm notId notType [] (getRange lf) lf'
   _ -> fatal_error "Not yet implemented!" nullRange
 TUF_THF_Atom a -> case a of
  TA_THF_Conn_Term _ -> fatal_error ("Not directly translatable! - " ++
                             "Maybe the term is malformed?") nullRange
  T0A_Constant c ->
   let id' = case c of
           A_Lower_Word tok -> mkId [tok]
           A_Single_Quoted tok -> mkId [tok]
       t = case Map.lookup c (consts sig) of
            Just ci -> TypeScheme [] (toHCType $ constType ci) nullRange
            Nothing -> TypeScheme [TypeArg (stringToId "tmp") NonVar
              (VarKind (ClassKind (stringToId "tmp"))) (ClassKind ()) 0 Comma nullRange]
             (TypeName (stringToId "tmp") (ClassKind ()) (-1)) nullRange
   in return $ QualOp HCAs.Fun (PolyId id' [] (getRange c)) t [] Infer nullRange
  T0A_Variable v -> return $ QualVar $ VarDecl (stringToId $ show v)
                             (TypeName (stringToId $ show v)
                               (ClassKind ()) (-1)) Comma nullRange
   -- what type should we give a (bound) variable?
  _ -> fatal_error "Not yet implemented!" nullRange
 TUF_THF_Tuple t -> do
  t' <- mapM (transFormula sig . TF_THF_Logic_Formula) t
  return $ TupleTerm t' (getRange t)
 TUF_THF_Logic_Formula_Par lf -> transFormula sig (TF_THF_Logic_Formula lf)
 T0UF_THF_Abstraction vs uf' -> do
  vs' <- mapM variable2Term vs
  uf'' <- transUnitaryFormula sig uf'
  return $ LambdaTerm vs' Total uf'' (getRange uf)
 _ -> fatal_error "Not yet implemented!" nullRange

variable2Term :: THFVariable -> Result HCAs.Term
variable2Term v@(TV_Variable _) = case variable2VarDecl v of
 GenVarDecl vdecl -> return $ QualVar vdecl
 _ -> fatal_error "This shouldn't happen!" nullRange
variable2Term (TV_THF_Typed_Variable t tp) =
 case thfTopLevelTypeToType tp of
   Just tp' -> do
    t' <- variable2Term (TV_Variable t)
    return $ TypedTerm t' OfType (toHCType tp') nullRange
   Nothing -> variable2Term (TV_Variable t)

variable2VarDecl :: THFVariable -> GenVarDecl
variable2VarDecl (TV_Variable t) = GenTypeVarDecl $ TypeArg
 (mkId [t]) NonVar (VarKind (ClassKind (mkId [t]))) (ClassKind ()) 0 Comma
 (getRange t)
variable2VarDecl (TV_THF_Typed_Variable t tp) =
 case thfTopLevelTypeToType tp of
  Just tp' -> GenVarDecl $ VarDecl (mkId [t]) (toHCType tp') Comma
               (getRange t)
  Nothing -> variable2VarDecl (TV_Variable t)

transSymbol :: SymbolTHF -> Result (Set.Set Symbol)
transSymbol (THFCons.Symbol i _ t) =
 let id' = case i of
           A_Lower_Word tok -> mkId [tok]
           A_Single_Quoted tok -> mkId [tok]
 in case t of
  (ST_Type Kind) -> return $ Set.singleton $ HCLe.Symbol id' $
   TypeAsItemType $ ClassKind ()
  (ST_Const t_) -> {- currently only "simple" kinds are allowed in thf so this
                     must be the type of an operator -}
    case tailType t_ of
     (t', Just OType) -> return $ Set.singleton $ HCLe.Symbol id' $
      PredAsItemType $ TypeScheme [] (toHCType t') (getRange t')
     _ -> return $ Set.singleton $ HCLe.Symbol id' $
      OpAsItemType $ TypeScheme [] (toHCType t_) (getRange t_)

tailType :: THFCons.Type -> (THFCons.Type, Maybe THFCons.Type)
tailType (MapType t1 t2) = case t2 of
 MapType _ _ ->
  let (t2', tailT) = tailType t2
  in (MapType t1 t2', tailT)
 _ -> (t1, Just t2)
tailType t = (t, Nothing)

toHCType :: THFCons.Type -> HCAs.Type
toHCType IType = toType $ stringToId "$i"
toHCType TType = toType $ stringToId "$t"
toHCType OType = unitType
toHCType (MapType t1 t2) = mkFunArrType (toHCType t1) FunArr (toHCType t2)
toHCType (ProdType ts) = mkProductType $ map toHCType ts
toHCType (CType c) = toType $ stringToId $ show c
toHCType (SType _) = error "not implemented" {- currently not in use
open issue: is the integer argument required
   to be unique for each typ var? -}
toHCType (VType t) = TypeName (stringToId $ show t) (ClassKind ()) (-1)
toHCType (ParType t) = toHCType t
