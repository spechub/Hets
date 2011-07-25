{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c) Uni Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  kluc@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

Translating comorphism from Common Logic to CASL

-}

module Comorphisms.CommonLogic2CASL
   (
     CommonLogic2CASL (..)
   )
   where

import Comorphisms.GetPreludeLib

import System.IO.Unsafe

import Static.GTheory

import Logic.Prover
import Logic.Coerce
import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation as AS_Anno
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Common.Id as Id

import qualified Data.Set as Set
import qualified Data.Map as Map

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as ClBasic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor

data CommonLogic2CASL = CommonLogic2CASL deriving Show

instance Language CommonLogic2CASL where
  language_name CommonLogic2CASL = "CommonLogic2CASL"

instance Comorphism
    CommonLogic2CASL        -- comorphism
    ClLogic.CommonLogic     -- lid domain
    ()                      -- sublogics domain
    ClBasic.BASIC_SPEC              -- Basic spec domain
    ClBasic.TEXT                    -- sentence domain
    ClBasic.NAME                    -- symbol items domain
    ClBasic.SYMB_MAP_ITEMS          -- symbol map items domain
    ClSign.Sign            -- signature domain
    ClMor.Morphism         -- morphism domain
    ClSymbol.Symbol        -- symbol domain
    ClSymbol.Symbol        -- rawsymbol domain
    ProofTree              -- proof tree codomain
    CLogic.CASL            -- lid codomain
    CSL.CASL_Sublogics     -- sublogics codomain
    CLogic.CASLBasicSpec   -- Basic spec codomain
    CBasic.CASLFORMULA     -- sentence codomain
    CBasic.SYMB_ITEMS      -- symbol items codomain
    CBasic.SYMB_MAP_ITEMS  -- symbol map items codomain
    CSign.CASLSign         -- signature codomain
    CMor.CASLMor           -- morphism codomain
    CSign.Symbol           -- symbol codomain
    CMor.RawSymbol         -- rawsymbol codomain
    ProofTree              -- proof tree domain
    where
      sourceLogic CommonLogic2CASL = ClLogic.CommonLogic
      sourceSublogic CommonLogic2CASL = ()
      targetLogic CommonLogic2CASL = CLogic.CASL
      mapSublogic CommonLogic2CASL = Just . mapSub -- Just . mapSub
      map_theory CommonLogic2CASL = mapTheory -- TODO
      map_morphism CommonLogic2CASL = mapMor  -- TODO prop
      map_sentence CommonLogic2CASL = mapSentence
      has_model_expansion CommonLogic2CASL = True

-- | Creates CASL Sig
baseCASLSig :: [AS_Anno.Named CBasic.CASLFORMULA]
baseCASLSig =
     let lib = head $ unsafePerformIO $ readLib "CommonLogic/CommonLogic.casl"
     in case lib of
        G_theory lid _ _ thSens _ -> let sens = toNamedList thSens
                                     in do
                                         sens' <- coerceSens lid CLogic.CASL ""
                                                    sens
                                         -- filter (not . ctorCons) sens'
                                         sens'

mapSub :: () -> CSL.CASL_Sublogics
mapSub _ = CSL.caslTop
        { CSL.cons_features = CSL.emptyMapConsFeature
        , CSL.sub_features = CSL.NoSub }

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor mor = Result [] $ Just (CMor.embedMorphism ()
    (mapSig $ ClMor.source mor) $ mapSig $ ClMor.target mor)
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
mapTheory :: (ClSign.Sign,
              [AS_Anno.Named ClBasic.TEXT])
              -> Result
                  (CSign.CASLSign,
                   [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) = Result [] $ Just (mapSig sig, baseCASLSig ++ (map
           (trNamedForm sig) form))

mapSig :: ClSign.Sign -> CSign.CASLSign
mapSig sign = CSign.uniteCASLSign ((CSign.emptySign ()) {
               CSign.opMap = Set.fold (\ x -> MapSet.insert x
                                $ CSign.mkTotOpType [] individual)
                                MapSet.empty $ ClSign.items sign
               }) caslSig

-- | setting casl sign: sorts, cons, fun, nil, pred
caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortRel = Rel.fromKeysSet
                   $ Set.fromList [list, individual]
               , CSign.opMap = MapSet.fromList
                         [ (cons, [CSign.mkTotOpType
                                   [individual, list]
                                   list])
                         , (fun, [CSign.mkTotOpType
                                  [individual, list]
                                  individual])
                         , (nil, [CSign.mkTotOpType [] list])]
               , CSign.predMap = MapSet.fromList
                [(rel, [CSign.PredType [individual, list]])]
               }

list :: Id.Id
list = Id.stringToId "list"

individual :: Id.Id
individual = Id.stringToId "individual"

rel :: Id.Id
rel = Id.stringToId "rel"

fun :: Id.Id
fun = Id.stringToId "fun"

cons :: Id.Id
cons = Id.stringToId "cons"

nil :: Id.Id
nil = Id.stringToId "nil"

-- todo maybe input here axioms
trNamedForm :: ClSign.Sign -> AS_Anno.Named (ClBasic.TEXT)
            -> AS_Anno.Named (CBasic.CASLFORMULA)
trNamedForm sig form = AS_Anno.mapNamed (trForm sig) form

mapSentence :: ClSign.Sign -> ClBasic.TEXT -> Result CBasic.CASLFORMULA
mapSentence sig form = Result [] $ Just $ trForm sig form

-- ignores importations
trForm :: ClSign.Sign -> ClBasic.TEXT -> CBasic.CASLFORMULA
trForm sig form =
   case form of
     ClBasic.Text phrs rn ->
        CBasic.Conjunction (map (phraseForm sig) (filter nonImport phrs)) rn
     ClBasic.Named_text _ t _ -> trForm sig t
   where nonImport :: ClBasic.PHRASE -> Bool
         nonImport p = case p of
            ClBasic.Importation _ -> False
            _ -> True

phraseForm :: ClSign.Sign -> ClBasic.PHRASE -> CBasic.CASLFORMULA
phraseForm sig phr =
   case phr of
     ClBasic.Module m -> moduleForm sig m
     ClBasic.Sentence s -> senForm sig s
     ClBasic.Importation i -> undefined -- cannot occur, because filtered
     ClBasic.Comment_text _ t _ -> trForm sig t

moduleForm :: ClSign.Sign -> ClBasic.MODULE -> CBasic.CASLFORMULA
moduleForm sig m = case m of
   ClBasic.Mod _ txt _ -> trForm sig txt
   ClBasic.Mod_ex _ exs txt _ -> trForm sig txt --what to do with the exclusions?

senForm :: ClSign.Sign -> ClBasic.SENTENCE -> CBasic.CASLFORMULA
senForm sig form =
   case form of
     ClBasic.Bool_sent bs rn
        -> case bs of
             ClBasic.Negation s -> CBasic.Negation (senForm sig s) rn
             ClBasic.Conjunction ss ->
                CBasic.Conjunction (map (senForm sig) ss) rn
             ClBasic.Disjunction ss ->
                CBasic.Disjunction (map (senForm sig) ss) rn
             ClBasic.Implication s1 s2 ->
                CBasic.Implication (senForm sig s1) (senForm sig s2) True rn
             ClBasic.Biconditional s1 s2 -> CBasic.Equivalence
                                             (senForm sig s1) (senForm sig s2) rn
     ClBasic.Quant_sent qs rn
        -> case qs of
             ClBasic.Universal bs s ->
               CBasic.Quantification CBasic.Universal
               [CBasic.Var_decl (map bindingSeq bs) individual Id.nullRange]
               (senForm sig s) rn -- FIX
             ClBasic.Existential bs s ->
               CBasic.Quantification CBasic.Existential
               [CBasic.Var_decl (map bindingSeq bs) individual Id.nullRange]
               (senForm sig s) rn -- FIX
     ClBasic.Atom_sent at rn
        -> case at of
             ClBasic.Equation trm1 trm2 ->
                CBasic.Strong_equation (termForm trm1) (termForm trm2) rn
             ClBasic.Atom trm ts -> CBasic.Predication
                                       (CBasic.Qual_pred_name rel
                                       (CBasic.Pred_type [individual, list]
                                        Id.nullRange)
                                        Id.nullRange) ([termForm trm] ++
                                    (consSeq sig ts) : []) Id.nullRange
     ClBasic.Comment_sent _ s _ -> senForm sig s -- FIX
     ClBasic.Irregular_sent s _ -> senForm sig s -- FIX

termForm :: ClBasic.TERM -> CBasic.TERM a
termForm trm = case trm of
                 ClBasic.Name_term name -> CBasic.Application
                     (CBasic.Qual_op_name (Id.simpleIdToId name)
                       (CBasic.Op_type CBasic.Total [] individual Id.nullRange)
                       Id.nullRange)
                     [] $ Id.tokPos name
                 -- ClBasic.Name_term name -> CBasic.Qual_var name individual
                 -- Id.nullRange
                 ClBasic.Funct_term term _ _ -> termForm term -- FIX
                 ClBasic.Comment_term term _ _ -> termForm term -- FIX

consSeq :: ClSign.Sign -> [ClBasic.TERM_SEQ] -> CBasic.TERM a
consSeq _ [] = CBasic.Application (CBasic.Qual_op_name nil
  (CBasic.Op_type CBasic.Total [] list Id.nullRange)
  Id.nullRange) [] Id.nullRange
consSeq sig (x : xs) = CBasic.Application (CBasic.Qual_op_name cons
  (CBasic.Op_type CBasic.Total [individual, list] list Id.nullRange)
  Id.nullRange) [termSeqForm sig x, consSeq sig xs] Id.nullRange

termSeqForm :: ClSign.Sign -> ClBasic.TERM_SEQ -> CBasic.TERM a
termSeqForm sig ts = case ts of
        -- ClBasic.Term_seq trm -> termForm trm
        ClBasic.Term_seq trm -> case trm of
             ClBasic.Name_term name -> if not subSig then
                CBasic.Qual_var name individual Id.nullRange else
                    termForm trm
               where subSig = ClSign.isSubSigOf new sig
                     new    = ClSign.Sign
                         {
                           ClSign.items = Set.singleton $ Id.simpleIdToId name
                         , ClSign.discourseItems = Set.singleton $
                               Id.simpleIdToId name
                         }
             ClBasic.Funct_term term _ _ -> termForm term
             ClBasic.Comment_term term _ _ -> termForm term
        ClBasic.Seq_marks seqm -> CBasic.varOrConst seqm

bindingSeq :: ClBasic.NAME_OR_SEQMARK -> CBasic.VAR
bindingSeq bs = case bs of
                  ClBasic.Name name -> name
                  ClBasic.SeqMark seqm -> seqm
