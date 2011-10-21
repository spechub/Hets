{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

Translating comorphism from Common Logic (compact, that is without sequence markers) to CASL

-}

module Comorphisms.CommonLogic2CASLCompact
   (
     CommonLogic2CASLCompact (..)
   )
   where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation as AS_Anno
import Common.Lib.MapSet (MapSet)
import Common.DocUtils (pretty)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Common.Id as Id

import Data.List (partition, intersect)
import qualified Data.Set as Set
import qualified Data.Map as Map

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as Cl
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSl

import Comorphisms.CommonLogicModuleElimination (eliminateModules)

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

data CommonLogic2CASLCompact = CommonLogic2CASLCompact deriving Show

instance Language CommonLogic2CASLCompact where
  language_name CommonLogic2CASLCompact = "CommonLogic2CASLCompact"

instance Comorphism
    CommonLogic2CASLCompact -- comorphism
    ClLogic.CommonLogic     -- lid domain
    ClSl.CommonLogicSL      -- sublogics codomain
    Cl.BASIC_SPEC           -- Basic spec domain
    Cl.TEXT_META            -- sentence domain
    Cl.SYMB_ITEMS           -- symbol items domain
    Cl.SYMB_MAP_ITEMS       -- symbol map items domain
    ClSign.Sign             -- signature domain
    ClMor.Morphism          -- morphism domain
    ClSymbol.Symbol         -- symbol domain
    ClSymbol.Symbol         -- rawsymbol domain
    ProofTree               -- proof tree codomain
    CLogic.CASL             -- lid codomain
    CSL.CASL_Sublogics      -- sublogics codomain
    CLogic.CASLBasicSpec    -- Basic spec codomain
    CBasic.CASLFORMULA      -- sentence codomain
    CBasic.SYMB_ITEMS       -- symbol items codomain
    CBasic.SYMB_MAP_ITEMS   -- symbol map items codomain
    CSign.CASLSign          -- signature codomain
    CMor.CASLMor            -- morphism codomain
    CSign.Symbol            -- symbol codomain
    CMor.RawSymbol          -- rawsymbol codomain
    ProofTree               -- proof tree domain
    where
      sourceLogic CommonLogic2CASLCompact = ClLogic.CommonLogic
      sourceSublogic CommonLogic2CASLCompact = ClSl.compactsl
      targetLogic CommonLogic2CASLCompact = CLogic.CASL
      mapSublogic CommonLogic2CASLCompact = Just . mapSub
      map_theory CommonLogic2CASLCompact = mapTheory
      map_morphism CommonLogic2CASLCompact = mapMor
      map_sentence CommonLogic2CASLCompact = mapSentence
      has_model_expansion CommonLogic2CASLCompact = True

data Q_TYPE = Universal | Existential deriving (Eq, Ord, Show)
data Pred_Or_Func = Pred | Func deriving (Eq, Ord, Show)
data TextInfo = TextInfo {
    vars :: Set.Set String
  , props :: Set.Set String
  , arityPred :: MapSet String Int
  , arityFunc :: MapSet String Int
  } deriving (Eq, Ord, Show)

emptyTI :: TextInfo
emptyTI = TextInfo { vars = Set.empty
                   , props = Set.empty
                   , arityPred = MapSet.empty
                   , arityFunc = MapSet.empty
                   }

unionTI :: TextInfo -> TextInfo -> TextInfo
unionTI s t = TextInfo { vars = Set.union (vars s) (vars t)
                       , props = Set.union (props s) (props t)
                       , arityPred = MapSet.union (arityPred s) (arityPred t)
                       , arityFunc = MapSet.union (arityFunc s) (arityFunc t)
                       }

unionsTI :: [TextInfo] -> TextInfo
unionsTI = foldr (\ti r -> unionTI r ti) emptyTI

removeFromTI :: String -> TextInfo -> TextInfo
removeFromTI n ti = ti { vars = Set.delete n $ vars ti
                       , props = Set.delete n $ props ti
                       , arityPred = MapSet.fromMap $
                                      Map.delete n $ MapSet.toMap $ arityPred ti
                       , arityFunc = MapSet.fromMap $
                                      Map.delete n $ MapSet.toMap $ arityFunc ti
                       }



mapSub :: ClSl.CommonLogicSL -> CSL.CASL_Sublogics
mapSub _ = CSL.caslTop
        { CSL.cons_features = CSL.emptyMapConsFeature
        , CSL.sub_features = CSL.NoSub }

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor mor = Result [] $ Just (CMor.embedMorphism ()
  (mapSig emptyTI $ ClMor.source mor) $ mapSig emptyTI $ ClMor.target mor)
  { CMor.pred_map = trMor $ ClMor.propMap mor }

-- | Helper for map mor
trMor :: Map.Map Id.Id Id.Id -> Map.Map (Id.Id, CSign.PredType) Id.Id
trMor mp =
    let
        pt = CSign.PredType {CSign.predArgs = []}
    in
      Map.foldWithKey
             (\ k a ->
              Map.insert (k, pt) a
             )
      Map.empty
      mp

-- |
mapTheory :: (ClSign.Sign, [AS_Anno.Named Cl.TEXT_META])
              -> Result (CSign.CASLSign, [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) =
  let ti = unionsTI $ map (collectTextInfo . AS_Anno.sentence) form
  in  Result [] $ Just (mapSig ti sig, map trNamedForm form)

mapSig :: TextInfo -> ClSign.Sign -> CSign.CASLSign
mapSig ti _ =
  let constOpMap = Set.fold (\n res ->
          MapSet.insert (Id.stringToId n) (opTypeSign 0) res
        ) MapSet.empty (vars ti)
      constPredMap = Set.fold (\n res ->
          MapSet.insert (Id.stringToId n) (predTypeSign 0) res
        ) MapSet.empty (props ti)
      opMap = MapSet.foldWithKey (\n ar ops ->
          MapSet.insert (Id.stringToId n) (opTypeSign ar) ops
        ) MapSet.empty (arityFunc ti)
      predMap = MapSet.foldWithKey (\n ar preds ->
          MapSet.insert (Id.stringToId n) (predTypeSign ar) preds
        ) MapSet.empty (arityPred ti)
  in  CSign.uniteCASLSign (
          (CSign.emptySign ()) {
              CSign.opMap = MapSet.union constOpMap opMap
            , CSign.predMap = MapSet.union constPredMap predMap
            }
        ) caslSig

opTypeSign :: Int -> CSign.OpType
opTypeSign ar = CSign.mkTotOpType (replicate ar individual) individual

predTypeSign :: Int -> CSign.PredType
predTypeSign ar = CSign.PredType {CSign.predArgs = replicate ar individual}


-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet $ Set.fromList [individual] }

individual :: Id.Id
individual = Id.stringToId "individual"
-- -}
-- todo maybe input here axioms
trNamedForm :: AS_Anno.Named (Cl.TEXT_META)
            -> AS_Anno.Named (CBasic.CASLFORMULA)
trNamedForm form = AS_Anno.mapNamed (trFormMeta . eliminateModules) form

mapSentence :: ClSign.Sign -> Cl.TEXT_META -> Result CBasic.CASLFORMULA
mapSentence _ form = Result [] $ Just $ trFormMeta (eliminateModules form)

-- ignores importations
trFormMeta ::  Cl.TEXT_META -> CBasic.CASLFORMULA
trFormMeta tm = trForm $ Cl.getText tm

trForm ::Cl.TEXT -> CBasic.CASLFORMULA
trForm form =
   case form of
     Cl.Text phrs rn ->
        let ps = filter nonImportAndNonEmpty phrs in
        if null ps then CBasic.True_atom Id.nullRange else
        CBasic.Conjunction (map phraseForm ps) rn
     Cl.Named_text _ t _ -> trForm t
   where nonImportAndNonEmpty :: Cl.PHRASE -> Bool
         nonImportAndNonEmpty p = case p of
            Cl.Importation _ -> False
            Cl.Comment_text _ t _ -> not $ isTextEmpty t
            _ -> True
         isTextEmpty :: Cl.TEXT -> Bool
         isTextEmpty txt = case txt of
            Cl.Named_text _ t _ -> isTextEmpty t
            Cl.Text [] _ -> True
            _ -> False

phraseForm :: Cl.PHRASE -> CBasic.CASLFORMULA
phraseForm phr = case phr of
  Cl.Module _ -> undefined -- cannot occur because module elimination applied
  Cl.Sentence s -> senForm Set.empty s
  Cl.Importation _ -> undefined -- cannot occur, because filtered
  Cl.Comment_text _ t _ -> trForm t

senForm :: Set.Set Cl.NAME -> Cl.SENTENCE -> CBasic.CASLFORMULA
senForm bndVars form = case form of
  Cl.Bool_sent bs rn -> case bs of
      Cl.Negation s -> CBasic.Negation (senForm bndVars s) rn
      Cl.Conjunction [] -> CBasic.True_atom Id.nullRange
      Cl.Disjunction [] -> CBasic.True_atom Id.nullRange
      Cl.Conjunction ss -> CBasic.Conjunction (map (senForm bndVars) ss) rn
      Cl.Disjunction ss -> CBasic.Disjunction (map (senForm bndVars) ss) rn
      Cl.Implication s1 s2 ->
          CBasic.Implication
            (senForm bndVars s1)
            (senForm bndVars s2)
            True rn
      Cl.Biconditional s1 s2 ->
          CBasic.Equivalence
            (senForm bndVars s1)
            (senForm bndVars s2)
            rn
  Cl.Quant_sent qs rn -> case qs of
      Cl.Universal bs s -> quantSentForm Universal rn bndVars bs s
      Cl.Existential bs s -> quantSentForm Existential rn  bndVars bs s
  Cl.Atom_sent at rn -> case at of
      Cl.Equation trm1 trm2 ->
          CBasic.Strong_equation
            (termForm bndVars $ uncurryTerm trm1)
            (termForm bndVars $ uncurryTerm trm2) rn
      Cl.Atom trm tseqs ->
          CBasic.Predication
            (termFormPrd (uncurryTerm trm) (length tseqs))
            (map (termSeqForm bndVars) tseqs) rn
  Cl.Comment_sent _ s _ -> senForm bndVars s
  Cl.Irregular_sent s _ -> senForm bndVars s

-- checks for second order quantification
quantSentForm :: Q_TYPE -> Id.Range -> Set.Set Cl.NAME -> [Cl.NAME_OR_SEQMARK]
                 -> Cl.SENTENCE -> CBasic.CASLFORMULA
quantSentForm qt rn bndVars bs sen =
  let ti = colTi_sen sen
      bSs = map nosStrnig bs
      (predSs, opsVars) = partition
          (\n -> Map.member n $ MapSet.toMap $ arityPred ti) bSs
      (opSs, predsVars) = partition
          (\n -> Map.member n $ MapSet.toMap $ arityFunc ti) bSs
      vs = map (Cl.Name . Id.mkSimpleId) $ intersect opsVars predsVars
      preds = MapSet.filterWithKey (\s _ -> elem s predSs) $ arityPred ti
      ops = MapSet.filterWithKey (\s _ -> elem s opSs) $ arityFunc ti
      quantifier = case qt of
          Universal -> CBasic.Universal
          Existential -> CBasic.Existential
      folSen =
        if null vs
        then senForm bndVars sen
        else CBasic.Quantification quantifier
                  [CBasic.Var_decl (map bindingSeq bs) individual Id.nullRange]
                  (senForm (bndVarsToSet bndVars vs) sen) rn
      predSen = MapSet.foldWithKey (\prd ar s ->
          CBasic.QuantPred (Id.stringToId prd) (predType ar) s
        ) folSen preds
      opSen = MapSet.foldWithKey (\op ar s ->
          CBasic.QuantOp (Id.stringToId op) (opType ar) s
        ) predSen ops
  in  opSen

opType :: Int -> CBasic.OP_TYPE
opType ar =
  CBasic.Op_type CBasic.Total (replicate ar individual) individual Id.nullRange

predType :: Int -> CBasic.PRED_TYPE
predType ar = CBasic.Pred_type (replicate ar individual) Id.nullRange

bndVarsToSet :: Set.Set Cl.NAME -> [Cl.NAME_OR_SEQMARK] -> Set.Set Cl.NAME
bndVarsToSet bndVars bs = foldr Set.insert bndVars
  $ map (\nos -> case nos of
                  Cl.Name n -> n
                  Cl.SeqMark s -> error $ errSeqMark s)
        bs

termForm :: Set.Set Cl.NAME -> Cl.TERM -> CBasic.TERM a
termForm bndVars trm = case trm of
  Cl.Name_term n ->
      if Set.member n bndVars
      then CBasic.Qual_var n individual Id.nullRange
      else CBasic.Application (termFormApp trm 0) [] Id.nullRange
  Cl.Funct_term term tseqs rn ->
      CBasic.Application
        (termFormApp term (length tseqs))
        (map (termSeqForm bndVars) tseqs) rn
  Cl.Comment_term term _ _ -> termForm bndVars (uncurryTerm term)

termFormApp :: Cl.TERM -> Int -> CBasic.OP_SYMB
termFormApp trm ar = case trm of
  Cl.Name_term n -> CBasic.Qual_op_name (Id.mkId [n]) (opType ar) Id.nullRange
  Cl.Comment_term t _ _ -> termFormApp t ar
  _ -> error errCurriedFunctionS

termFormPrd :: Cl.TERM -> Int -> CBasic.PRED_SYMB
termFormPrd trm ar = case trm of
  Cl.Name_term n ->
      CBasic.Qual_pred_name (Id.mkId [n]) (predType ar) Id.nullRange
  Cl.Comment_term t _ _ -> termFormPrd t ar
  Cl.Funct_term _ _ _ -> error $ errFunctionReturnedPredicateS trm

termSeqForm :: Set.Set Cl.NAME -> Cl.TERM_SEQ -> CBasic.TERM a
termSeqForm bndVars tseq = case tseq of
  Cl.Term_seq trm -> termForm bndVars $ uncurryTerm trm
  Cl.Seq_marks s -> error $ errSeqMark s

bindingSeq :: Cl.NAME_OR_SEQMARK -> CBasic.VAR
bindingSeq bs = case bs of
  Cl.Name n -> n
  Cl.SeqMark s -> error $ errSeqMark s

collectTextInfo :: Cl.TEXT_META -> TextInfo
collectTextInfo tm = colTi_txt $ Cl.getText tm

colTi_txt :: Cl.TEXT -> TextInfo
colTi_txt txt = case txt of
  Cl.Named_text _ t _ -> colTi_txt t
  Cl.Text ps _ -> unionsTI $ map colTi_phr ps

colTi_phr :: Cl.PHRASE -> TextInfo
colTi_phr p = case p of
  Cl.Module (Cl.Mod _ t _) -> colTi_txt t
  Cl.Module (Cl.Mod_ex _ _ t _) -> colTi_txt t
  Cl.Importation _ -> emptyTI
  Cl.Comment_text _ t _ -> colTi_txt t
  Cl.Sentence s -> colTi_sen s

colTi_sen :: Cl.SENTENCE -> TextInfo
colTi_sen sen = case sen of
  Cl.Quant_sent q _ -> case q of
      Cl.Universal noss s ->
          foldr (\n r -> removeFromTI n r) (colTi_sen s) (map nosStrnig noss)
      Cl.Existential noss s ->
          foldr (\n r -> removeFromTI n r) (colTi_sen s) (map nosStrnig noss)
  Cl.Bool_sent b _ -> case b of
      Cl.Conjunction sens -> unionsTI $ map colTi_sen sens
      Cl.Disjunction sens -> unionsTI $ map colTi_sen sens
      Cl.Negation s -> colTi_sen s
      Cl.Implication s1 s2 -> unionsTI $ map colTi_sen [s1,s2]
      Cl.Biconditional s1 s2 -> unionsTI $ map colTi_sen [s1,s2]
  Cl.Atom_sent a _ -> case a of
      Cl.Equation t1 t2 -> unionsTI $ map (colTi_trm_var . uncurryTerm) [t1, t2]
      Cl.Atom t [] -> colTi_trm_prop $ uncurryTerm t
      Cl.Atom t tseqs -> colTi_addArity Pred (uncurryTerm t) tseqs
  Cl.Comment_sent _ s _ -> colTi_sen s
  Cl.Irregular_sent s _ -> colTi_sen s

nosStrnig :: Cl.NAME_OR_SEQMARK -> String
nosStrnig nos = case nos of
  Cl.Name n -> Id.tokStr n
  Cl.SeqMark s -> error $ errSeqMark s

colTi_trm_var :: Cl.TERM -> TextInfo
colTi_trm_var trm = case trm of
  Cl.Name_term n -> emptyTI {vars = Set.singleton (Id.tokStr n)}
  Cl.Comment_term t _ _ -> colTi_trm_var t
  _ -> colTi_trm $ uncurryTerm trm

colTi_trm_prop :: Cl.TERM -> TextInfo
colTi_trm_prop trm = case trm of
  Cl.Name_term n -> emptyTI {props = Set.singleton (Id.tokStr n)}
  Cl.Comment_term t _ _ -> colTi_trm_prop t
  _ -> colTi_trm $ uncurryTerm trm

colTi_trm :: Cl.TERM -> TextInfo
colTi_trm trm = case trm of
  Cl.Name_term _ -> emptyTI
  Cl.Funct_term t tseqs _ -> colTi_addArity Func t tseqs
  Cl.Comment_term t _ _ -> colTi_trm $ uncurryTerm t

colTi_trmSeq :: Cl.TERM_SEQ -> TextInfo
colTi_trmSeq tseq = case tseq of
  Cl.Term_seq trm -> colTi_trm_var trm
  Cl.Seq_marks s -> error $ errSeqMark s

colTi_addArity :: Pred_Or_Func -> Cl.TERM -> [Cl.TERM_SEQ] -> TextInfo
colTi_addArity ty trm tseqs = case trm of
  Cl.Name_term n ->
      unionsTI $ (if ty == Pred
                  then emptyTI { arityPred = MapSet.insert
                                  (Id.tokStr n) (length tseqs) MapSet.empty}
                  else emptyTI { arityFunc = MapSet.insert
                                  (Id.tokStr n) (length tseqs) MapSet.empty}
                  ) : map colTi_trmSeq tseqs
  Cl.Funct_term _ _ _ -> colTi_trm $ uncurryTerm trm -- FIX predicate "(f x) y"
  Cl.Comment_term t _ _ -> colTi_addArity ty t tseqs

-- If curried, uncurries term. Otherwise original term returned
-- removes comments
uncurryTerm :: Cl.TERM -> Cl.TERM
uncurryTerm trm = case trm of
  Cl.Funct_term t tseqs rn ->
      let (nt, args) = uncurryTermWithArgs t tseqs in
      Cl.Funct_term nt args rn
  Cl.Comment_term t _ _ -> uncurryTerm t
  _ -> trm

uncurryTermWithArgs :: Cl.TERM -> [Cl.TERM_SEQ] -> (Cl.TERM, [Cl.TERM_SEQ])
uncurryTermWithArgs trm tseqs = case trm of
  Cl.Funct_term t ts _ -> uncurryTermWithArgs t (ts ++ tseqs)
  Cl.Comment_term t _ _ -> uncurryTermWithArgs t tseqs
  _ -> (trm, tseqs)

errSeqMark :: Cl.SEQ_MARK -> String
errSeqMark s = "Sequence marks not allowed in this comorphism. Found: " ++ Id.tokStr s

errCurriedFunctionS :: String
errCurriedFunctionS = "Found curried function"

errFunctionReturnedPredicateS :: Cl.TERM -> String
errFunctionReturnedPredicateS t = "Function returned predicate "++ (show $ pretty t)
