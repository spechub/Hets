{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/HPAR2CASL.hs
Description :  encoding of HPAR to FOL
Copyright   :  (c) M. Codescu, IMAR, 2018
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  mscodescu@gmail.com
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

The encoding comorphism from HPAR to FOL.

-}

module Comorphisms.HPAR2CASL where

import Logic.Logic
import Logic.Comorphism
import qualified Data.Set as Set
import qualified Data.Map as Map
import Common.ProofTree
import Common.Result
import Common.AS_Annotation
import Common.Id
import qualified Common.Lib.MapSet as MapSet


import Control.Monad (foldM)
import Data.List(partition)

-- HPAR
import qualified HPAR.Logic_HPAR as HLogic
import qualified HPAR.AS_Basic_HPAR as HBasic
import qualified HPAR.Sign as HSign
import qualified RigidCASL.Sign as RSign
import qualified HPAR.Morphism as HMorphism
import qualified HPAR.StaticAna as HAna

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor
import CASL.Sublogic 
import qualified CASL.Induction as CInd

-- base comorphism
import qualified Comorphisms.CASL2SubCFOL as BaseCom

import Debug.Trace

-- | The identity of the comorphism
data HPAR2CASL = HPAR2CASL deriving (Show)

instance Language HPAR2CASL

instance Comorphism HPAR2CASL
               HLogic.HPAR ()
               HBasic.H_BASIC_SPEC HBasic.HFORMULA HBasic.H_SYMB_ITEMS 
               CBasic.SYMB_MAP_ITEMS
               HSign.HSign HMorphism.HMorphism CSign.Symbol CMor.RawSymbol () 
               CLogic.CASL CASL_Sublogics
               CLogic.CASLBasicSpec CBasic.CASLFORMULA CBasic.SYMB_ITEMS CBasic.SYMB_MAP_ITEMS
               CSign.CASLSign
               CMor.CASLMor
               CSign.Symbol CMor.RawSymbol ProofTree where
    sourceLogic HPAR2CASL = HLogic.HPAR
    sourceSublogic HPAR2CASL = ()
    targetLogic HPAR2CASL = CLogic.CASL
    mapSublogic HPAR2CASL _ = Just cFol
    map_theory HPAR2CASL = mapTheory
    map_morphism HPAR2CASL = undefined
    map_sentence HPAR2CASL =  undefined
    map_symbol HPAR2CASL _ = undefined
    -- has_model_expansion HPAR2CASL = True 
    -- @Till: this makes proofs by translation available, but on a weird path

mapTheory :: (HSign.HSign, [Named HBasic.HFORMULA]) ->
             Result (CSign.CASLSign, [Named CBasic.CASLFORMULA])
mapTheory (hsig, nhsens) = -- trace ("nhsens:" ++ show nhsens) $ 
                           do 
  (csig, csens) <- map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) $ (RSign.caslSign $ HSign.baseSig $ hsig, []) 
  let st = genName "ST"
      v = genToken "X"
      domain = genName "domain"
      cvars = foldl (\vars asen -> getVarSorts vars $ sentence asen) Set.empty csens -- variables in \Gamma_\Sigma
      csens' = -- trace ("cvars:" ++ show cvars) $ 
               map (\f -> f { sentence = CBasic.Quantification CBasic.Universal [CBasic.Var_decl [v] st nullRange] (addX v $ sentence f) nullRange} ) csens
  stsig <- CSign.addSymbToSign (CSign.emptySign ()) $ CSign.Symbol st CSign.SortAsItemType -- this one has gn_ST
  sortsig <- foldM (\aSig x -> CSign.addSymbToSign aSig $ CSign.Symbol x CSign.SortAsItemType) 
                   stsig $ Set.toList $ CSign.sortSet csig         -- this one has [S_\Sigma]
  nomsig <- foldM (\aSig x -> CSign.addSymbToSign aSig $ CSign.Symbol x $ CSign.OpAsItemType $ CSign.OpType CBasic.Total [] st) 
                  sortsig $ HSign.noms hsig -- this one has \overline{Nom}
  opsig <- foldM (\aSig (i, CSign.OpType k w s) -> CSign.addSymbToSign aSig $ CSign.Symbol i $ CSign.OpAsItemType $ CSign.OpType k (st:w) s)
                 nomsig $ MapSet.toPairList $ CSign.opMap csig -- this one has [F_\Sigma]
  let domsens = 
                foldl (\sens (f, o@(CSign.OpType _ w s)) -> 
                          let ydecl = CBasic.mkVarDecl (genToken "w") st
                              xsdecl = map (\(si, ii) -> CBasic.mkVarDecl (genToken $ "x" ++ show ii) si) $ zip w [1::Int ..]
                              df = CBasic.mkForall [ydecl] $
                                   CBasic.mkForall xsdecl $
                                   CBasic.mkImpl 
                                    (CBasic.conjunct $ map (\xidecl -> case xidecl of 
                                                                         CBasic.Var_decl [xi] si _ -> 
                                                                           CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, si] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w") st nullRange,
                                                                                                 CBasic.Qual_var xi si nullRange]
                                                                         _ -> error "domsens"
                                                           ) xsdecl
                                    ) 
                                    (CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange) 
                                                          [CBasic.Qual_var (genToken "w") st nullRange,
                                                           CBasic.mkAppl (CBasic.Qual_op_name f (addSortToOpType $ CSign.toOP_TYPE o) nullRange) 
                                                                         (map CBasic.toQualVar $ ydecl:xsdecl) 
                                                          ]
                                    )
                          in (makeNamed ("ga_domain_"++show f) df):sens
                      ) 
                      [] $ MapSet.toPairList $ CSign.opMap csig -- this is D_F_\Sigma
  predsig <- foldM (\aSig (i, CSign.PredType w) -> CSign.addSymbToSign aSig $ CSign.Symbol i $ CSign.PredAsItemType $ CSign.PredType (st:w))
                   opsig $ MapSet.toPairList $ CSign.predMap csig -- this one has [P_\Sigma]
  domsig <- foldM (\aSig s -> CSign.addSymbToSign aSig $ CSign.Symbol domain $ CSign.PredAsItemType $ CSign.PredType [st, s])
            predsig $ Set.toList $ CSign.sortSet csig -- this one has D_s
  lamsig <- foldM (\aSig (l, x) -> CSign.addSymbToSign aSig $ CSign.Symbol l $ CSign.PredAsItemType $ CSign.PredType $ take x $ repeat st)
            domsig $ Map.toList $ HSign.mods hsig -- this one has \overline{\Lambda}
  let ncsens = map (mapNamedSentence hsig) nhsens
      constrsens = constrsToSens hsig $ sem_constr HLogic.HPAR
      makeVSen s = makeNamed ("ga_V_"++show s)
                   $ CBasic.mkForall [CBasic.mkVarDecl (genToken "w") st, CBasic.mkVarDecl (genToken "x") s] 
                   $ CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w") st nullRange,
                                                                                                 CBasic.Qual_var (genToken "x") s nullRange]
      vsens = map makeVSen $ Set.toList cvars -- this is V(\Gamma_Sigma)
  trace (concatMap (\x -> show x ++ "\n") ncsens) $ return (lamsig, csens' ++ vsens ++ domsens ++ ncsens ++ constrsens)

getVarSorts :: Set.Set CBasic.SORT -> CBasic.CASLFORMULA -> Set.Set CBasic.SORT
getVarSorts oldS sen = 
 case sen of
  CBasic.Quantification _ vdecls f _ -> Set.union (Set.fromList $ map (\(CBasic.Var_decl _ s _) -> s) vdecls) $ getVarSorts oldS f
  CBasic.Junction _ fs _ -> foldl (\s f -> getVarSorts s f) oldS fs
  CBasic.Relation f1 _ f2 _ -> Set.union (getVarSorts oldS f1) (getVarSorts oldS f2)
  CBasic.Negation f _ -> getVarSorts oldS f
  CBasic.Atom _ _ -> oldS
  CBasic.Definedness _ _ -> oldS
  CBasic.Predication _ _ _ -> oldS
  CBasic.Equation _ _ _ _ -> oldS
  _ -> error $ "Illegal argument for getVarSorts in HPAR2CASL.hs: " ++  show sen

constrsToSens :: HSign.HSign -> [SemanticConstraint] -> [Named CBasic.CASLFORMULA]
constrsToSens hsig cs = concatMap (constrToSens hsig) cs

constrToSens :: HSign.HSign -> SemanticConstraint -> [Named CBasic.CASLFORMULA]
constrToSens hsig sc = 
  let 
    rsig = HSign.baseSig hsig
    st = genName "ST"
    domain = genName "domain"
    defined = genName "defined"
    (totals, partials) = partition (\(_, ot) -> CSign.opKind ot == CBasic.Total) $ MapSet.toPairList $ RSign.rigidOps $ CSign.extendedInfo rsig
  in 
  case sc of 
   SameInterpretation "rigid sort" -> 
     map (\s -> makeNamed ("ga_sem_constr_"++show s)
                $ CBasic.mkForall [CBasic.mkVarDecl (genToken "w1") st, 
                                 CBasic.mkVarDecl (genToken "w2") st, 
                                 CBasic.mkVarDecl (genToken "x") s]
                                 $ CBasic.mkEqv 
                                    (CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w1") st nullRange,
                                                                                                 CBasic.Qual_var (genToken "x") s nullRange])
                                    (CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, s] nullRange)
                                                                                                [CBasic.Qual_var (genToken "w2") st nullRange,
                                                                                                 CBasic.Qual_var (genToken "x") s nullRange]) 
          ) 
                $ Set.toList $ RSign.rigidSorts $ CSign.extendedInfo rsig
   SameInterpretation "rigid op" ->
    let
      xs ot = zip (CSign.opArgs ot) [1::Int ..]
      extOt i ot = CBasic.Qual_op_name i (CBasic.Op_type CBasic.Total (st:CSign.opArgs ot) (CSign.opRes ot) nullRange) nullRange
    in
     map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ CBasic.mkForall 
                                ( [CBasic.mkVarDecl (genToken "w1") st, 
                                   CBasic.mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> CBasic.mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ CBasic.mkStEq 
                                      (CBasic.mkAppl (extOt i ot) $ map (\(a,b) -> CBasic.mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
                                      (CBasic.mkAppl (extOt i ot) $ map (\(a,b) -> CBasic.mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
          ) 
                totals
   SameDomain True -> let
      xs ot = zip (CSign.opArgs ot) [1::Int ..]
      extOt i ot = CBasic.Qual_op_name i (CBasic.Op_type CBasic.Total (st:CSign.opArgs ot) (CSign.opRes ot) nullRange) nullRange
    in
     map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ CBasic.mkForall 
                                ( [CBasic.mkVarDecl (genToken "w1") st, 
                                   CBasic.mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> CBasic.mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ CBasic.mkEqv 
                                      (CBasic.mkPredication (CBasic.mkQualPred defined $ CBasic.Pred_type [st, CSign.opRes ot] nullRange) $ 
                                       [CBasic.mkVarTerm (genToken "w1") st,
                                        CBasic.mkAppl (extOt i ot) $ map (\(a,b) -> CBasic.mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
                                      (CBasic.mkPredication (CBasic.mkQualPred defined $ CBasic.Pred_type [st, CSign.opRes ot] nullRange) $ 
                                       [CBasic.mkVarTerm (genToken "w2") st,
                                        CBasic.mkAppl (extOt i ot) $ map (\(a,b) -> CBasic.mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
          ) 
                partials 
   _ -> error $ "unexpected semantic constraint: " ++ show sc

addSortToOpType :: CBasic.OP_TYPE -> CBasic.OP_TYPE
addSortToOpType (CBasic.Op_type k w s r1) = CBasic.Op_type k (genName "ST":w) s r1

addSortToPredType :: CBasic.PRED_TYPE -> CBasic.PRED_TYPE
addSortToPredType (CBasic.Pred_type w r1) = CBasic.Pred_type (genName "ST" : w) r1

addVarToTerm :: CBasic.VAR -> CBasic.TERM () -> CBasic.TERM ()
addVarToTerm v t = case t of
 CBasic.Qual_var _ _ _ -> t
 CBasic.Application (CBasic.Qual_op_name f o r2) args r -> 
   CBasic.Application (CBasic.Qual_op_name f (addSortToOpType o) r2) ((CBasic.Qual_var v (genName "ST") nullRange):(map (addVarToTerm v) args)) r
 _ -> error $ "HPAR2CASL: can't add var to term " ++ show t

addX :: CBasic.VAR -> CBasic.CASLFORMULA -> CBasic.CASLFORMULA
addX v sen = case sen of
  CBasic.Quantification q vdecls f r -> CBasic.Quantification q vdecls (addX v f) r
  CBasic.Junction j fs r -> CBasic.Junction j (map (addX v) fs) r
  CBasic.Relation f1 rel f2 r -> CBasic.Relation (addX v f1) rel (addX v f2) r
  CBasic.Negation f r -> CBasic.Negation (addX v f) r
  CBasic.Atom _ _ -> sen
  CBasic.Definedness t r -> CBasic.Definedness (addVarToTerm v t) r
  CBasic.Predication (CBasic.Qual_pred_name p t r2) terms r -> 
    CBasic.Predication (CBasic.Qual_pred_name p (addSortToPredType t) r2) ((CBasic.Qual_var v (genName "ST") nullRange):(map (addVarToTerm v) terms)) r
  CBasic.Equation t1 eq t2 r -> CBasic.Equation (addVarToTerm v t1) eq (addVarToTerm v t2) r
  _ -> error $ "Illegal argument for addX in HPAR2CASL.hs: " ++  show sen

substituteInHSen :: CBasic.VAR -> CBasic.SORT -> CBasic.TERM () -> HBasic.HFORMULA -> HBasic.HFORMULA
substituteInHSen v s t hf = 
 case hf of
  HBasic.Base_formula f r -> HBasic.Base_formula (CInd.substitute v s t f) r
  HBasic.Negation hf' r -> HBasic.Negation (substituteInHSen v s t hf') r 
  HBasic.Conjunction hfs r -> HBasic.Conjunction (map (substituteInHSen v s t) hfs) r
  HBasic.Disjunction hfs r -> HBasic.Disjunction (map (substituteInHSen v s t) hfs) r
  HBasic.Implication hf1 hf2 r -> HBasic.Implication (substituteInHSen v s t hf1) (substituteInHSen v s t hf2) r
  HBasic.Equivalence hf1 hf2 r -> HBasic.Equivalence (substituteInHSen v s t hf1) (substituteInHSen v s t hf2) r
  HBasic.AtState nom hf' r -> HBasic.AtState nom (substituteInHSen v s t hf') r 
  HBasic.BoxFormula md hf' r -> HBasic.BoxFormula md (substituteInHSen v s t hf') r
  HBasic.DiamondFormula md hf' r -> HBasic.DiamondFormula md (substituteInHSen v s t hf') r
  HBasic.QuantNominals q noms hf' r -> HBasic.QuantNominals q noms (substituteInHSen v s t hf') r
  HBasic.QuantRigidVars q vdecls hf' r -> HBasic.QuantRigidVars q vdecls (substituteInHSen v s t hf') r
  _ -> hf

replaceInHSen :: CBasic.VAR -> CBasic.SORT -> HBasic.HFORMULA -> HBasic.HFORMULA
replaceInHSen v s hf = 
 case hf of
  HBasic.Base_formula f r -> HBasic.Base_formula (replaceVarAppls v s f) r
  HBasic.Negation hf' r -> HBasic.Negation (replaceInHSen v s hf') r 
  HBasic.Conjunction hfs r -> HBasic.Conjunction (map (replaceInHSen v s) hfs) r
  HBasic.Disjunction hfs r -> HBasic.Disjunction (map (replaceInHSen v s) hfs) r
  HBasic.Implication hf1 hf2 r -> HBasic.Implication (replaceInHSen v s hf1) (replaceInHSen v s hf2) r
  HBasic.Equivalence hf1 hf2 r -> HBasic.Equivalence (replaceInHSen v s hf1) (replaceInHSen v s hf2) r
  HBasic.AtState nom hf' r -> HBasic.AtState nom (replaceInHSen v s hf') r 
  HBasic.BoxFormula md hf' r -> HBasic.BoxFormula md (replaceInHSen v s hf') r
  HBasic.DiamondFormula md hf' r -> HBasic.DiamondFormula md (replaceInHSen v s hf') r
  HBasic.QuantNominals q noms hf' r -> HBasic.QuantNominals q noms (replaceInHSen v s hf') r
  HBasic.QuantRigidVars q vdecls hf' r -> HBasic.QuantRigidVars q vdecls (replaceInHSen v s hf') r
  _ -> hf

replaceVarAppls :: CBasic.VAR -> CBasic.SORT -> CBasic.CASLFORMULA -> CBasic.CASLFORMULA
replaceVarAppls v s sen = case sen of
  CBasic.Quantification q vdecls f r -> CBasic.Quantification q vdecls (replaceVarAppls v s f) r
  CBasic.Junction j fs r -> CBasic.Junction j (map (replaceVarAppls v s) fs) r
  CBasic.Relation f1 rel f2 r -> CBasic.Relation (replaceVarAppls v s f1) rel (replaceVarAppls v s f2) r
  CBasic.Negation f r -> CBasic.Negation (replaceVarAppls v s f) r
  CBasic.Atom _ _ -> sen
  CBasic.Definedness t r -> CBasic.Definedness (replTermWithVar v s t) r
  CBasic.Predication p terms r -> CBasic.Predication p (map (replTermWithVar v s) terms) r
  CBasic.Equation t1 eq t2 r -> CBasic.Equation (replTermWithVar v s t1) eq (replTermWithVar v s t2) r
  _ -> error $ "Illegal argument for addX in HPAR2CASL.hs: " ++  show sen

replTermWithVar :: CBasic.VAR -> CBasic.SORT -> CBasic.TERM () -> CBasic.TERM ()
replTermWithVar v s t = case t of 
  CBasic.Application op@(CBasic.Qual_op_name f _o _r2) args r -> 
     if simpleIdToId v == f 
        then CBasic.Qual_var v s nullRange
        else CBasic.Application op (map (replTermWithVar v s) args) r                   
  _ -> t

mapNamedSentence :: HSign.HSign -> Named HBasic.HFORMULA -> Named CBasic.CASLFORMULA
mapNamedSentence hsig nsen = nsen {sentence = mapSentence hsig $ sentence nsen}

mapSentence :: HSign.HSign -> HBasic.HFORMULA -> CBasic.CASLFORMULA
mapSentence hsig sen = -- trace ("mapping:" ++ show sen) $ 
 let 
  x = genToken "X"
  st = genName "ST"
  hth = HAna.HTheoryAna hsig Set.empty [] Map.empty []
 in CBasic.mkForall [CBasic.mkVarDecl x st] $ 
       mapSentenceAux hth x st sen

mapSentenceAux :: HAna.HTheoryAna -> CBasic.VAR -> CBasic.SORT -> HBasic.HFORMULA -> CBasic.CASLFORMULA
mapSentenceAux hth x st sen = case sen of
 HBasic.Nominal b i _ -> CBasic.mkStEq 
                          (CBasic.Qual_var x st nullRange) $ 
                          if b then CBasic.Qual_var i st nullRange
                          else CBasic.Application (CBasic.mkQualOp (simpleIdToId i) $ CBasic.Op_type CBasic.Total [] st nullRange) [] nullRange
 HBasic.Base_formula f _ -> let
   hsig = HAna.hSign hth 
   Result ds f' = map_sentence (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) (RSign.caslSign $ HSign.baseSig hsig) f
  in case f' of
      Nothing  -> error $ "can't translate sentence " ++ show f ++ " msg:" ++ show ds
      Just f'' -> addX x f''
 HBasic.Negation hf _ -> CBasic.Negation (mapSentenceAux hth x st hf) nullRange
 HBasic.Conjunction hfs _ -> CBasic.Junction CBasic.Con (map (mapSentenceAux hth x st) hfs) nullRange
 HBasic.Disjunction hfs _ -> CBasic.Junction CBasic.Dis (map (mapSentenceAux hth x st) hfs) nullRange
 HBasic.Implication hf1 hf2 _ -> CBasic.Relation (mapSentenceAux hth x st hf1) CBasic.Implication (mapSentenceAux hth x st hf2) nullRange
 HBasic.Equivalence hf1 hf2 _ -> CBasic.Relation (mapSentenceAux hth x st hf1) CBasic.Equivalence (mapSentenceAux hth x st hf2) nullRange
 HBasic.AtState nom hf _ -> let cf = mapSentenceAux hth x st hf 
                                t = if nom `elem` (Map.keys $ HAna.hVars hth) then CBasic.Qual_var nom st nullRange else 
                                      CBasic.mkAppl (CBasic.mkQualOp (simpleIdToId nom) $ CBasic.Op_type CBasic.Total [] st nullRange) []
                            in CInd.substitute x st t cf 
                         -- mapSentenceAux i st sen does not work, because i should not be a var. apply a substitution of x with i instead 
 HBasic.BoxFormula md hf _ -> CBasic.mkForall [CBasic.mkVarDecl (genToken "Y") st] $ 
                                               CBasic.mkImpl 
                                                 (CBasic.mkPredication (CBasic.mkQualPred (simpleIdToId md) $ CBasic.Pred_type [st,st] nullRange) 
                                                                       [CBasic.Qual_var x st nullRange, CBasic.Qual_var (genToken "Y") st nullRange]) $ 
                                                 mapSentenceAux hth (genToken "Y") st hf
 HBasic.DiamondFormula md hf _ -> CBasic.mkExist [CBasic.mkVarDecl (genToken "Y") st] $ 
                                               CBasic.Junction CBasic.Con 
                                                 [CBasic.mkPredication (CBasic.mkQualPred (simpleIdToId md) $ CBasic.Pred_type [st,st] nullRange) 
                                                                       [CBasic.Qual_var x st nullRange, CBasic.Qual_var (genToken "Y") st nullRange],
                                                  mapSentenceAux hth (genToken "Y") st hf]
                                                 nullRange
 HBasic.QuantNominals q noms hf _ -> (case q of 
                                          HBasic.HUniversal -> CBasic.mkForall
                                          HBasic.HExistential -> CBasic.mkExist) 
                                      (map (\n -> CBasic.mkVarDecl n st) noms)
                                      $ mapSentenceAux (hth{HAna.hVars = foldl (\f n -> Map.insert n st f) (HAna.hVars hth) noms}) x st hf 
                                      -- here we must make sure that noms are known to be variables and not nominals!
 HBasic.QuantRigidVars q vdecls hf _ -> 
  let
   hsig = HAna.hSign hth
   domainSen xi si = CBasic.mkPredication (CBasic.mkQualPred (genName "domain") $ CBasic.Pred_type [st, si] nullRange)
                                           [CBasic.Qual_var x st nullRange,
                                            CBasic.mkAppl (CBasic.Qual_op_name (simpleIdToId xi) (addSortToOpType $ CBasic.Op_type CBasic.Total [] si nullRange) nullRange) 
                                                           [CBasic.Qual_var x st nullRange]]
   baseSig = RSign.caslSign $ HSign.baseSig $ hsig
   Result ds resTh = map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) $ (baseSig, [])
   (_, csens) = case resTh of
                  Nothing -> error $ "could not translate theory:" ++ show ds
                  Just th -> th
   addVarAsConst xi si = 
    let Result ds' resTh' = CSign.addSymbToSign baseSig $ CSign.Symbol (simpleIdToId xi) $ CSign.OpAsItemType $ CSign.OpType CBasic.Total [] si 
    in case resTh' of 
         Nothing ->  error $ "could not add variable as constant:" ++ show ds'
         Just th -> th
   getCSens xi si = let
     Result ds'' resTh'' = map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) $ (addVarAsConst xi si, [])
    in case resTh'' of
         Nothing -> error $ "could not translate theory with added variable:" ++ show ds''
         Just (_, sens) -> sens
   --  keep the sentences that appear only in the second list of sentences
   gamma_xi xi si = map (\f -> f { sentence = CBasic.Quantification CBasic.Universal [CBasic.Var_decl [genToken "w"] st nullRange] (addX (genToken "w") $ sentence f) nullRange} )
                     $ filter (\s -> not (s `elem` csens)) $ getCSens xi si
   allVars = concatMap (\(CBasic.Var_decl vs si _ ) -> map (\v -> (v, si)) vs) vdecls
   baseSigXi bSig xi si = let Result ds''' resSig = CSign.addSymbToSign bSig $ CSign.Symbol (simpleIdToId xi) $ CSign.OpAsItemType $ CSign.OpType CBasic.Total [] si
                          in case resSig of 
                              Nothing -> error $ show ds'''
                              Just sig -> sig
   baseSigWithVars = foldl (\bSig (xi, si) -> baseSigXi bSig xi si) (HSign.baseSig $ hsig) allVars
   hsig' = hsig {HSign.baseSig = baseSigWithVars}
   hf' = foldl (\f (xi, si) -> substituteInHSen xi si (CBasic.mkAppl (CBasic.mkQualOp (simpleIdToId xi) $ CBasic.Op_type CBasic.Total [] si nullRange) []) f) hf allVars
   senWithVarAppl = CBasic.mkImpl 
                     (CBasic.Junction CBasic.Con (
                                      (map sentence $ 
                                          concatMap (\(xi,si)-> gamma_xi xi si) allVars
                                      ) ++ (map (\(xi,si) -> domainSen xi si) allVars)
                                   ) nullRange)
                    $ mapSentenceAux (hth {HAna.hSign = hsig'}) x st hf'
   senRepl = foldl (\csen (xi,si) -> replaceVarAppls xi si csen) senWithVarAppl allVars
  in -- trace ("hf':" ++ show hf') $ 
       (case q of 
         HBasic.HUniversal -> CBasic.mkForall
         HBasic.HExistential -> CBasic.mkExist) vdecls senRepl
       

    {- (case q of 
                                          HBasic.HUniversal -> CBasic.mkForall
                                          HBasic.HExistential -> CBasic.mkExist) 
                                 vdecls 
                                 $ CBasic.mkImpl 
                                     (CBasic.mkForall [CBasic.mkVarDecl (genToken "Y") st] $
                                                      CBasic.Junction CBasic.Con 
                                                                      (concatMap (\(CBasic.Var_decl vs s _) -> 
                                                                                    map (\v -> CBasic.mkPredication (CBasic.mkQualPred (genName "domain") $ CBasic.Pred_type [st, s] nullRange) 
                                                                                                                     [CBasic.Qual_var (genToken "Y") st nullRange,
                                                                                                                      CBasic.Qual_var v s nullRange]) 
                                                                                    vs    
                                                                                 ) vdecls
                                                                       ) 
                                                                      nullRange
                                     )
                                     $ mapSentenceAux hsig x st hf   -}

{-

QuantRigidVars q vdecls hf _ ->
  let 
    domainSen xi si = CBasic.mkPredication (CBasic.mkQualPred domain $ CBasic.Pred_type [st, si] nullRange)
                                           [CBasic.Qual_var x st nullRange,
                                            CBasic.Qual_var xi si nullRange]
  --  translate hsig to CASL
    baseSig = RSign.caslSign $ HSign.baseSig $ hsig
  (csig, csens) <- map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) $ (baseSig, [])
  baseSigXi <- CSign.addSymbToSign baseSig $ CSign.Symbol xi $ CSign.OpAsItemType $ CSign.OpType CBasic.Total [] si
  hsig' = hsig {HSign.baseSig = addSymb (xi as constant) $ baseSig hsig}
  --  translate hsig + x to CASL
  (csig', csens') <- map_theory (BaseCom.CASL2SubCFOL True BaseCom.NoMembershipOrCast) $ (baseSigXi, [])
  --  keep the sentences that appear only in the second list of sentences
  let gamma_xi = map (\f -> f { sentence = CBasic.Quantification CBasic.Universal [CBasic.Var_decl [v] st nullRange] (addX v $ sentence f) nullRange} ) csens 
                 $ filter (\s -> not (s `elem` csens)) csens' 
  in CBasic.mkImpl
       (CBasic.Junction CBasic.Con $ map domainSen $ vdecls)
       $ mapSentenceAux hsig' x st f

-}

{-

mapTheory :: (RSign.RSign, [Named CBasic.CASLFORMULA]) ->
             Result (HSign.HSign, [Named HBasic.HFORMULA])
mapTheory (sig, nsens) = do
 let tsig = HSign.HSign {HSign.baseSig = sig,
                         HSign.noms = Set.singleton $ genName "i",
                         HSign.mods = Map.empty}
     tsens = map mapNamedSen nsens
 return (tsig, tsens)

mapNamedSen :: Named CBasic.CASLFORMULA -> Named HBasic.HFORMULA
mapNamedSen nsen = let
 sen = sentence nsen
 trans = HBasic.AtState (genToken "i") (HBasic.Base_formula sen) nullRange
                    in
 nsen {sentence = trans}

-}
