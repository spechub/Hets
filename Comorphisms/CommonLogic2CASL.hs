{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c) Uni Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt

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

import Logic.Logic as Logic
import Logic.Comorphism
import Common.ProofTree
import Common.Result
import Common.AS_Annotation as AS_Anno
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

-- import CommonLogic.CASLSig

data CommonLogic2CASL = CommonLogic2CASL deriving Show

instance Language CommonLogic2CASL where
  language_name CommonLogic2CASL = "CommonLogic2CASL"

instance Comorphism
    CommonLogic2CASL        -- comorphism
    ClLogic.CommonLogic             -- lid domain
    ()                      -- sublogics domain
    ClBasic.BASIC_SPEC              -- Basic spec domain
    ClBasic.SENTENCE                -- sentence domain
    ClBasic.NAME                    -- symbol items domain
    ()                      -- symbol map items domain
    ClSign.Sign                    -- signature domain
    ClMor.Morphism                -- morphism domain
    ClSymbol.Symbol                  -- symbol domain
    ClSymbol.Symbol                  -- rawsymbol domain
    ()                     -- proof tree codomain
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
      mapSublogic CommonLogic2CASL = mapSub
      map_theory CommonLogic2CASL = mapTheory -- TODO
      map_morphism CommonLogic2CASL = mapMor  -- TODO
      map_sentence CommonLogic2CASL = mapSentence

mapSub :: () -> Maybe CSL.CASL_Sublogics
mapSub _ = Nothing

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor _ = Result { diags = [], maybeResult = Nothing }

mapTheory :: (ClSign.Sign,
              [AS_Anno.Named ClBasic.SENTENCE])
              -> Result
                  (CSign.CASLSign,
                   [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) = Result [] $
     Just (mapSig sig, map trNamedForm form)

mapSig :: ClSign.Sign -> CSign.CASLSign
mapSig sign = CSign.uniteCASLSign ((CSign.emptySign ()) {
               CSign.opMap = Set.fold (\x -> Map.insert x
                                ( Set.singleton $ CSign.OpType
                                                   { CSign.opKind = CBasic.Total
                                                   , CSign.opArgs = []
                                                   , CSign.opRes = individual
                                                   }))
                                Map.empty $ ClSign.items sign
               }) caslSig

caslSig :: CSign.CASLSign
caslSig = (CSign.emptySign ())
               { CSign.sortSet = Set.fromList [list, individual]
               , CSign.opMap = Map.fromList [
                          (cons,Set.fromList [CSign.OpType {CSign.opKind = CBasic.Total,
                                                      CSign.opArgs = [individual,list],
                                                      CSign.opRes = list}])
                         ,(fun,Set.fromList [CSign.OpType {CSign.opKind = CBasic.Total,
                                                     CSign.opArgs = [individual,list],
                                                     CSign.opRes = individual}])
                         ,(nil,Set.fromList [CSign.OpType {CSign.opKind = CBasic.Total,
                                                     CSign.opArgs = [],
                                                     CSign.opRes = list}])]
               , CSign.predMap = Map.fromList
                  [(rel, Set.fromList [CSign.PredType {CSign.predArgs = [individual,list]}])]
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

mapSentence :: ClSign.Sign -> ClBasic.SENTENCE -> Result CBasic.CASLFORMULA
mapSentence _ form = Result [] $ Just $ trForm form

trNamedForm :: AS_Anno.Named (ClBasic.SENTENCE)
            -> AS_Anno.Named (CBasic.CASLFORMULA)
trNamedForm form = AS_Anno.mapNamed trForm form

trForm :: ClBasic.SENTENCE -> CBasic.CASLFORMULA
trForm form =
   case form of
     ClBasic.Bool_sent bs rn
        -> case bs of
             ClBasic.Negation s -> CBasic.Negation (trForm s) rn
             ClBasic.Conjunction ss -> CBasic.Conjunction (map trForm ss) rn
             ClBasic.Disjunction ss -> CBasic.Disjunction (map trForm ss) rn
             ClBasic.Implication s1 s2 -> CBasic.Implication (trForm s1) (trForm s2) True rn
             ClBasic.Biconditional s1 s2 -> CBasic.Equivalence (trForm s1) (trForm s2) rn
     ClBasic.Quant_sent qs rn
        -> case qs of
             ClBasic.Universal bs s -> CBasic.Quantification CBasic.Universal
                                           [CBasic.Var_decl (map bindingSeq bs) individual
                                             Id.nullRange] (trForm s) rn --FIX
             ClBasic.Existential bs s -> CBasic.Quantification CBasic.Existential
                                           [CBasic.Var_decl (map bindingSeq bs) individual
                                             Id.nullRange] (trForm s) rn --FIX
     ClBasic.Atom_sent at rn
        -> case at of
             ClBasic.Equation trm1 trm2 ->
                CBasic.Strong_equation (termForm trm1) (termForm trm2) rn
             ClBasic.Atom trm ts -> CBasic.Predication
                                    (CBasic.Pred_name rel) ([termForm trm] ++
                                    (consSeq ts):[]) Id.nullRange
     ClBasic.Comment_sent _ s _ -> trForm s -- FIX
     ClBasic.Irregular_sent s _ -> trForm s -- FIX

termForm :: ClBasic.TERM -> CBasic.TERM a
termForm trm = case trm of
                 ClBasic.Name_term name -> CBasic.varOrConst name
                 ClBasic.Funct_term term _ _ -> termForm term -- FIX
                 ClBasic.Comment_term term _ _ -> termForm term -- FIX

consSeq  :: [ClBasic.TERM_SEQ] -> CBasic.TERM a
consSeq [] = CBasic.Application (CBasic.Op_name nil) [] Id.nullRange
consSeq (x:xs) = CBasic.Application (CBasic.Op_name cons) [termSeqForm x, consSeq xs] Id.nullRange

termSeqForm :: ClBasic.TERM_SEQ -> CBasic.TERM a
termSeqForm ts = case ts of
                   ClBasic.Term_seq trm -> termForm trm
                   ClBasic.Seq_marks seqm -> CBasic.varOrConst seqm

bindingSeq :: ClBasic.NAME_OR_SEQMARK -> CBasic.VAR
bindingSeq bs = case bs of
                  ClBasic.Name name -> name
                  ClBasic.SeqMark seqm -> seqm
