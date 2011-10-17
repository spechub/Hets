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
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Common.Id as Id

import qualified Data.Set as Set
import qualified Data.Map as Map

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as Cl
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSl

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

data TYPE = Pred | Func deriving (Eq, Ord, Show)
type ArityMap = MapSet (String, TYPE) Int

unionsMS :: (Ord a, Ord b) => [MapSet a b] -> MapSet a b
unionsMS ts =  foldl MapSet.union MapSet.empty ts

mapSub :: ClSl.CommonLogicSL -> CSL.CASL_Sublogics
mapSub _ = CSL.caslTop
        { CSL.cons_features = CSL.emptyMapConsFeature
        , CSL.sub_features = CSL.NoSub }

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor mor = Result [] $ Just (CMor.embedMorphism ()
  (mapSig MapSet.empty $ ClMor.source mor) $ mapSig MapSet.empty $ ClMor.target mor)
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
  let arities = unionsMS $ map (collectArities . AS_Anno.sentence) form
  in  Result [] $ Just (mapSig arities sig, map (trNamedForm sig) form)

mapSig :: ArityMap -> ClSign.Sign -> CSign.CASLSign
mapSig arities sign =
  let constOpMap = Set.fold (\x res -> -- get constants
          MapSet.insert x (CSign.mkTotOpType [] individual) res
        ) MapSet.empty $ ClSign.items sign
      (pm, om) = MapSet.foldWithKey (\(n,t) ar (preds, ops) ->
          case t of
            Pred -> ( MapSet.insert -- get non-nullary predicats
                        (Id.mkId [Id.mkSimpleId n])
                        (CSign.PredType {
                          CSign.predArgs = replicate ar individual})
                        preds
                    , ops
                    )
            Func -> ( preds -- get non-nullary functions
                    , MapSet.insert
                        (Id.mkId [Id.mkSimpleId n])
                        (CSign.mkTotOpType
                          (replicate ar individual)
                          individual)
                        ops
                    )
          ) (MapSet.empty, constOpMap) arities
  in  CSign.uniteCASLSign ((CSign.emptySign ()) { CSign.opMap = om
                                                , CSign.predMap = pm
                                                }) caslSig

-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet $ Set.fromList [individual] }

individual :: Id.Id
individual = Id.stringToId "individual"
-- -}
-- todo maybe input here axioms
trNamedForm :: ClSign.Sign -> AS_Anno.Named (Cl.TEXT_META)
            -> AS_Anno.Named (CBasic.CASLFORMULA)
trNamedForm _ form = AS_Anno.mapNamed trFormMrs form

mapSentence :: ClSign.Sign -> Cl.TEXT_META -> Result CBasic.CASLFORMULA
mapSentence _ form = Result [] $ Just $ trFormMrs form

-- ignores importations
trFormMrs :: Cl.TEXT_META -> CBasic.CASLFORMULA
trFormMrs tm = trForm $ Cl.getText tm

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
phraseForm phr =
   case phr of
     Cl.Module m -> moduleForm m
     Cl.Sentence s -> senForm s
     Cl.Importation _ -> undefined -- cannot occur, because filtered
     Cl.Comment_text _ t _ -> trForm t

moduleForm :: Cl.MODULE -> CBasic.CASLFORMULA
moduleForm m = case m of
   Cl.Mod _ txt _ -> trForm txt
   Cl.Mod_ex _ _ txt _ -> trForm txt --what to do with the exclusions?

senForm :: Cl.SENTENCE -> CBasic.CASLFORMULA
senForm form = case form of
  Cl.Bool_sent bs rn -> case bs of
      Cl.Negation s -> CBasic.Negation (senForm s) rn
      Cl.Conjunction [] -> CBasic.True_atom Id.nullRange
      Cl.Disjunction [] -> CBasic.True_atom Id.nullRange
      Cl.Conjunction ss -> CBasic.Conjunction (map (senForm) ss) rn
      Cl.Disjunction ss -> CBasic.Disjunction (map (senForm) ss) rn
      Cl.Implication s1 s2 ->
          CBasic.Implication (senForm s1) (senForm s2) True rn
      Cl.Biconditional s1 s2 ->
          CBasic.Equivalence (senForm s1) (senForm s2) rn
  Cl.Quant_sent qs rn -> case qs of
      Cl.Universal bs s ->
          CBasic.Quantification CBasic.Universal
            [CBasic.Var_decl (map bindingSeq bs) individual Id.nullRange]
            (senForm s) rn
      Cl.Existential bs s ->
          CBasic.Quantification CBasic.Existential
            [CBasic.Var_decl (map bindingSeq bs) individual Id.nullRange]
            (senForm s) rn
  Cl.Atom_sent at rn -> case at of
      Cl.Equation trm1 trm2 ->
          CBasic.Strong_equation (termForm trm1) (termForm trm2) rn
      Cl.Atom trm tseqs -> 
          CBasic.Predication (termFormPrd trm) (map termSeqForm tseqs) rn
  Cl.Comment_sent _ s _ -> senForm s
  Cl.Irregular_sent s _ -> senForm s

termForm :: Cl.TERM -> CBasic.TERM a
termForm trm = case trm of
  Cl.Name_term _ -> CBasic.Application (termFormApp trm) [] Id.nullRange
  Cl.Funct_term term tseqs rn ->
      CBasic.Application (termFormApp term) (map termSeqForm tseqs) rn
  Cl.Comment_term term _ _ -> termForm term

termFormApp :: Cl.TERM -> CBasic.OP_SYMB
termFormApp trm = case trm of
  Cl.Name_term n -> CBasic.Op_name $ Id.mkId [n]
  _ -> error errHigherOrderFunctionS

termFormPrd :: Cl.TERM -> CBasic.PRED_SYMB
termFormPrd trm = case trm of
  Cl.Name_term n -> CBasic.Pred_name $ Id.mkId [n]
  _ -> error errFunctionReturnedPredicateS

termSeqForm :: Cl.TERM_SEQ -> CBasic.TERM a
termSeqForm tseq = case tseq of
  Cl.Term_seq trm -> termForm trm
  Cl.Seq_marks s -> error $ errSeqMark s

bindingSeq :: Cl.NAME_OR_SEQMARK -> CBasic.VAR
bindingSeq bs = case bs of
  Cl.Name n -> n
  Cl.SeqMark s -> error $ errSeqMark s

collectArities :: Cl.TEXT_META -> ArityMap
collectArities tm = colAr_txt $ Cl.getText tm

colAr_txt :: Cl.TEXT -> ArityMap
colAr_txt txt = case txt of
  Cl.Named_text _ t _ -> colAr_txt t
  Cl.Text ps _ -> unionsMS $ map colAr_phr ps

colAr_phr :: Cl.PHRASE -> ArityMap
colAr_phr p = case p of
  Cl.Module (Cl.Mod _ t _) -> colAr_txt t
  Cl.Module (Cl.Mod_ex _ _ t _) -> colAr_txt t
  Cl.Importation _ -> MapSet.empty
  Cl.Comment_text _ t _ -> colAr_txt t
  Cl.Sentence s -> colAr_sen s

colAr_sen :: Cl.SENTENCE -> ArityMap
colAr_sen sen = case sen of
  Cl.Quant_sent q _ -> case q of
      Cl.Universal [] s -> colAr_sen s
      Cl.Existential [] s -> colAr_sen s
      Cl.Universal noss s -> unionsMS $ colAr_sen s : (map colAr_nos noss)
      Cl.Existential noss s -> unionsMS $ colAr_sen s : (map colAr_nos noss)
  Cl.Bool_sent b _ -> case b of
      Cl.Conjunction sens -> unionsMS $ map colAr_sen sens
      Cl.Disjunction sens -> unionsMS $ map colAr_sen sens
      Cl.Negation s -> colAr_sen s
      Cl.Implication s1 s2 -> unionsMS $ map colAr_sen [s1,s2]
      Cl.Biconditional s1 s2 -> unionsMS $ map colAr_sen [s1,s2]
  Cl.Atom_sent a _ -> case a of
      Cl.Equation t1 t2 -> unionsMS $ map colAr_trm [t1,t2]
      Cl.Atom t [] -> colAr_trm t
      Cl.Atom t tseqs -> colAr_Add Pred t tseqs
  Cl.Comment_sent _ s _ -> colAr_sen s
  Cl.Irregular_sent s _ -> colAr_sen s

colAr_nos :: Cl.NAME_OR_SEQMARK -> ArityMap
colAr_nos nos = case nos of
  Cl.Name _ -> MapSet.empty
  Cl.SeqMark s -> error $ errSeqMark s

colAr_trm :: Cl.TERM -> ArityMap
colAr_trm trm = case trm of
  Cl.Name_term _ -> MapSet.empty
  Cl.Funct_term t tseqs _ -> colAr_Add Func t tseqs
  Cl.Comment_term t _ _ -> colAr_trm t

colAr_trmSeq :: Cl.TERM_SEQ -> ArityMap
colAr_trmSeq tseq = case tseq of
  Cl.Term_seq t -> colAr_trm t
  Cl.Seq_marks s -> error $ errSeqMark s

colAr_Add :: TYPE -> Cl.TERM -> [Cl.TERM_SEQ] -> ArityMap
colAr_Add ty trm tseqs = case trm of
  Cl.Name_term n ->
      unionsMS $ MapSet.insert (Id.tokStr n,ty) (length tseqs) MapSet.empty
                    : colAr_trm trm
                    : map colAr_trmSeq tseqs
  Cl.Funct_term _ _ _ ->
    unionsMS [ colAr_trm trm
             -- , undefined -- TODO: implement correct handling for higher order functions
             ]
  Cl.Comment_term t _ _ -> colAr_Add ty t tseqs

errSeqMark :: Cl.SEQ_MARK -> String
errSeqMark s = "Sequence marks not allowed in this comorphism. Found: " ++ Id.tokStr s

errHigherOrderFunctionS :: String
errHigherOrderFunctionS = "Found higher order function"

errFunctionReturnedPredicateS :: String
errFunctionReturnedPredicateS = "Function returned predicate"
