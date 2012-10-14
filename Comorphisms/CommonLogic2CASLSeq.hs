{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CASL
Copyright   :  (c) Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (via Logic.Logic)

Translating comorphism from Common Logic to CASL

-}

module Comorphisms.CommonLogic2CASLSeq
   (
     CommonLogic2CASLSeq (..)
   )
   where

import Logic.Logic as Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.Token
import Common.DocUtils (pretty)
import Common.AS_Annotation as AS_Anno
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Id as Id

import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Function (on)
import Data.List (partition, intersect)

-- Common Logic
import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as ClBasic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSl

import CommonLogic.ModuleElimination

import CommonLogic.PredefinedCASLAxioms as Predefined

-- CASL
import qualified CASL.Logic_CASL as CLogic
import qualified CASL.AS_Basic_CASL as CBasic
import qualified CASL.Sublogic as CSL
import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMor


import Debug.Trace

data CommonLogic2CASLSeq = CommonLogic2CASLSeq deriving Show

instance Language CommonLogic2CASLSeq

instance Comorphism
    CommonLogic2CASLSeq       -- comorphism
    ClLogic.CommonLogic    -- lid domain
    ClSl.CommonLogicSL     -- sublogics codomain
    ClBasic.BASIC_SPEC     -- Basic spec domain
    ClBasic.TEXT_META      -- sentence domain
    ClBasic.SYMB_ITEMS     -- symbol items domain
    ClBasic.SYMB_MAP_ITEMS -- symbol map items domain
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
      sourceLogic CommonLogic2CASLSeq = ClLogic.CommonLogic
      sourceSublogic CommonLogic2CASLSeq = ClSl.folsl{ClSl.compact = False}
            -- the sublogic should be FOL with sequence markers
      targetLogic CommonLogic2CASLSeq = CLogic.CASL
      mapSublogic CommonLogic2CASLSeq = Just . mapSub
      map_theory CommonLogic2CASLSeq = mapTheory
      map_morphism CommonLogic2CASLSeq = mapMor  -- TODO prop
      map_sentence CommonLogic2CASLSeq = mapSentence
      has_model_expansion CommonLogic2CASLSeq = True

mapSub :: ClSl.CommonLogicSL -> CSL.CASL_Sublogics
mapSub _ = CSL.cFol
        { CSL.cons_features = CSL.emptyMapConsFeature }

mapMor :: ClMor.Morphism -> Result CMor.CASLMor
mapMor mor = Result [] $ Just (CMor.embedMorphism ()
    (mapSig $ ClMor.source mor) $ mapSig $ ClMor.target mor)
    { CMor.pred_map = trMor $ ClMor.propMap mor }

-- | Helper for map mor
-- predicates should be mapped according to mor,
-- but their arity should be list
-- check that it works!
trMor :: Map.Map Id.Id Id.Id -> Map.Map (Id.Id, CSign.PredType) Id.Id
trMor mp =
    let
        pt = CSign.PredType {CSign.predArgs = [Predefined.list]}
    in
      Map.foldWithKey
             (\ k a ->
              Map.insert (k, pt) a
             )
      Map.empty
      mp


-- copied from CommonLogic2CASLCompact.hs
-- they should go in a common import
data Q_TYPE = Universal | Existential deriving (Eq, Ord, Show)
data PredOrFunc = Pred | Func deriving (Eq, Ord, Show)
data TextInfo = TextInfo
  { arityPred :: MapSet.MapSet String Int
  , arityFunc :: MapSet.MapSet String Int
  , boundPred :: MapSet.MapSet String Int
  , boundFunc :: MapSet.MapSet String Int
  } deriving Show

emptyTI :: TextInfo
emptyTI = TextInfo
  { arityPred = MapSet.empty
  , arityFunc = MapSet.empty
  , boundPred = MapSet.empty
  , boundFunc = MapSet.empty
  }

unionTI :: TextInfo -> TextInfo -> TextInfo
unionTI s t = TextInfo
  { arityPred = on MapSet.union arityPred s t
  , arityFunc = on MapSet.union arityFunc s t
  , boundPred = on MapSet.union boundPred s t
  , boundFunc = on MapSet.union boundFunc s t
  }

unionsTI :: [TextInfo] -> TextInfo
unionsTI = foldr unionTI emptyTI

removeFromTI :: String -> TextInfo -> TextInfo
removeFromTI n ti = let deln = MapSet.fromMap . Map.delete n . MapSet.toMap in
  ti
  { arityPred = deln $ arityPred ti
  , arityFunc = deln $ arityFunc ti
  }

-- |
mapTheory :: (ClSign.Sign,
              [AS_Anno.Named ClBasic.TEXT_META])
              -> Result
                  (CSign.CASLSign,
                   [AS_Anno.Named CBasic.CASLFORMULA])
mapTheory (sig, form) = return
  (mapSig sig, Predefined.baseCASLAxioms ++ map (trNamedForm sig) form)


mapSig :: ClSign.Sign -> CSign.CASLSign
mapSig sign = CSign.uniteCASLSign ((CSign.emptySign ()) {
               CSign.opMap = MapSet.union (
                             MapSet.union 
                               (Set.fold (\ x -> MapSet.insert x
                                $ CSign.mkTotOpType [list] individual)
                                MapSet.empty $ Set.union (ClSign.discourseNames sign) $ ClSign.nondiscourseNames sign)
                               (Set.fold (\ x -> MapSet.insert x
                                $ CSign.mkTotOpType [] Predefined.list)
                                MapSet.empty $ ClSign.sequenceMarkers sign))
                                (Set.fold (\ x -> MapSet.insert x
                                $ CSign.mkTotOpType [] individual)
                                MapSet.empty $ Set.union (ClSign.discourseNames sign) $ ClSign.nondiscourseNames sign)
                 ,
               CSign.predMap = Set.fold (\x -> MapSet.insert x
                                $ CSign.PredType [list] )
                                MapSet.empty $ Set.union (ClSign.discourseNames sign) $ ClSign.nondiscourseNames sign
               }) Predefined.listSig

trNamedForm :: ClSign.Sign -> AS_Anno.Named ClBasic.TEXT_META
            -> AS_Anno.Named CBasic.CASLFORMULA
trNamedForm sig = AS_Anno.mapNamed $ trFormMeta sig . eliminateModules

mapSentence :: ClSign.Sign -> ClBasic.TEXT_META -> Result CBasic.CASLFORMULA
mapSentence sig form = Result [] $ Just $ trFormMeta sig (eliminateModules form)

-- ignores importations
trFormMeta :: ClSign.Sign -> ClBasic.TEXT_META -> CBasic.CASLFORMULA
trFormMeta sig tm = trForm sig $ ClBasic.getText tm

trForm :: ClSign.Sign -> ClBasic.TEXT -> CBasic.CASLFORMULA
trForm sig form =
   case form of
     ClBasic.Text phrs rn ->
        let ps = filter nonImportAndNonEmpty phrs in
        CBasic.conjunctRange (map (phraseForm sig) ps) rn
     ClBasic.Named_text _ t _ -> trForm sig t
   where nonImportAndNonEmpty :: ClBasic.PHRASE -> Bool
         nonImportAndNonEmpty p = case p of
            ClBasic.Importation _ -> False
            ClBasic.Comment_text _ t _ -> not $ isTextEmpty t
            _ -> True
         isTextEmpty :: ClBasic.TEXT -> Bool
         isTextEmpty txt = case txt of
            ClBasic.Named_text _ t _ -> isTextEmpty t
            ClBasic.Text [] _ -> True
            _ -> False

phraseForm :: ClSign.Sign -> ClBasic.PHRASE -> CBasic.CASLFORMULA
phraseForm sig phr =
   case phr of
     ClBasic.Module _ -> error "CL2CASL.phraseForm.Module"
     -- cannot occur because module elimination applied
     ClBasic.Sentence s -> senForm sig s
     ClBasic.Importation _ -> error "CL2CASL.phraseForm.Importation"
     -- cannot occur, because filtered
     ClBasic.Comment_text _ t _ -> trForm sig t

senForm :: ClSign.Sign -> ClBasic.SENTENCE -> CBasic.CASLFORMULA
senForm sig form = case form of
     ClBasic.Bool_sent bs rn -> case bs of
             ClBasic.Negation s -> CBasic.Negation (senForm sig s) rn
             ClBasic.Junction j ss -> (case j of
               ClBasic.Conjunction -> CBasic.conjunctRange
               ClBasic.Disjunction -> CBasic.disjunctRange)
                   (map (senForm sig) ss) rn
             ClBasic.BinOp j s1 s2 -> CBasic.Relation (senForm sig s1)
               (case j of
               ClBasic.Implication -> CBasic.Implication
               ClBasic.Biconditional -> CBasic.Equivalence)
               (senForm sig s2) rn
     ClBasic.Quant_sent q bs s rn ->
         CBasic.Quantification (case q of
                  ClBasic.Universal -> CBasic.Universal
                  ClBasic.Existential -> CBasic.Existential)
               [CBasic.Var_decl (map bindingSeq bs) individual rn]
               (senForm sig s) rn
     ClBasic.Atom_sent at rn -> case at of
         ClBasic.Equation trm1 trm2 -> CBasic.Equation (termForm sig trm1)
             CBasic.Strong (termForm sig trm2) rn
         ClBasic.Atom trm ts -> trace ("trm:" ++ show trm ++ "\n ts:" ++ show ts ) $ 
             CBasic.Predication
             (termFormPrd trm $ length ts) [consSeq sig ts] rn
     ClBasic.Comment_sent _ s _ -> senForm sig s
     ClBasic.Irregular_sent s _ -> senForm sig s

termForm :: ClSign.Sign -> ClBasic.TERM -> CBasic.TERM a
termForm sig trm = case trm of
                 ClBasic.Name_term name -> let rn = Id.tokPos name in
                    if ClSign.isSubSigOf (ClSign.emptySig {
                            ClSign.discourseNames =
                                Set.singleton (Id.simpleIdToId name)
                          }) sig
                    then trace ("name:" ++ show name)$ CBasic.Application
                          (CBasic.Qual_op_name (Id.simpleIdToId name)
                            (CBasic.Op_type CBasic.Total [] individual rn)
                           rn)
                          [] rn
                    else if ClSign.isSubSigOf (ClSign.emptySig {
                            ClSign.sequenceMarkers =
                                Set.singleton (Id.simpleIdToId name)
                          }) sig
                     then CBasic.Application
                          (CBasic.Qual_op_name (Id.simpleIdToId name)
                            (CBasic.Op_type CBasic.Total [] list rn)
                           rn)
                          [] rn
                     else CBasic.Qual_var name individual rn
                 ClBasic.Funct_term term ts rn ->
                   case term of 
                    ClBasic.Name_term name -> CBasic.Application
                        (CBasic.Qual_op_name (Id.simpleIdToId name)
                          (CBasic.Op_type
                            CBasic.Total [list]
                            individual rn)
                         rn)
                        [consSeq sig ts] rn
                    ClBasic.Comment_term (ClBasic.Name_term name )  _ _ -> 
                         CBasic.Application
                        (CBasic.Qual_op_name (Id.simpleIdToId name)
                          (CBasic.Op_type
                            CBasic.Total [list]
                            individual rn)
                         rn)
                        [consSeq sig ts] rn 
                    _ -> error "only names on function/predicate position"
                 ClBasic.Comment_term term _ _ -> termForm sig term
                 ClBasic.That_term {} -> error "CommonLogic2CASL.termForm"


consSeq :: ClSign.Sign -> [ClBasic.TERM_SEQ] -> CBasic.TERM a
consSeq _ [] = CBasic.Application (CBasic.Qual_op_name nil
  (CBasic.Op_type CBasic.Total [] list Id.nullRange)
  Id.nullRange) [] Id.nullRange
consSeq sig (x : xs) = CBasic.Application (CBasic.Qual_op_name cons
  (CBasic.Op_type CBasic.Total [individual, list] list Id.nullRange)
  Id.nullRange) [termSeqForm sig x, consSeq sig xs] Id.nullRange

termSeqForm :: ClSign.Sign -> ClBasic.TERM_SEQ -> CBasic.TERM a
termSeqForm sig tseq = case tseq of
  ClBasic.Term_seq trm -> trace ("seq: " ++ show trm)$ termForm sig $ uncurryTerm trm
  ClBasic.Seq_marks seqm -> 
    if ClSign.isSubSigOf (ClSign.emptySig {
              ClSign.discourseNames =
                  Set.singleton (Id.simpleIdToId seqm)
            }) sig
      then CBasic.Application
            (CBasic.Qual_op_name (Id.simpleIdToId seqm)
              (CBasic.Op_type CBasic.Total [] list Id.nullRange)
              Id.nullRange)
            [] $ Id.tokPos seqm
      else CBasic.Qual_var seqm list Id.nullRange

{- If curried, uncurries term. Otherwise original term returned
removes comments -}
uncurryTerm :: ClBasic.TERM -> ClBasic.TERM
uncurryTerm trm = case trm of
  ClBasic.Funct_term t tseqs rn ->
      let (nt, args) = uncurryTermWithArgs t tseqs in
      ClBasic.Funct_term nt args rn
  ClBasic.Comment_term t _ _ -> uncurryTerm t
  _ -> trm

uncurryTermWithArgs :: ClBasic.TERM -> [ClBasic.TERM_SEQ] -> (ClBasic.TERM, [ClBasic.TERM_SEQ])
uncurryTermWithArgs trm tseqs = case trm of
  ClBasic.Funct_term t ts _ -> uncurryTermWithArgs t (ts ++ tseqs)
  ClBasic.Comment_term t _ _ -> uncurryTermWithArgs t tseqs
  _ -> (trm, tseqs)


bindingSeq :: ClBasic.NAME_OR_SEQMARK -> CBasic.VAR
bindingSeq bs = case bs of
                  ClBasic.Name name -> name
                  ClBasic.SeqMark seqm -> seqm


termFormApp :: ClBasic.TERM -> Int -> Result CBasic.OP_SYMB
termFormApp trm ar = case trm of
  ClBasic.Name_term n ->
      return $ CBasic.mkQualOp (tok2Id n) (CBasic.Op_type CBasic.Total [list] individual Id.nullRange)
  ClBasic.Comment_term t _ _ -> termFormApp t ar
  _ -> fail "CommonLogic2CASLSeq.termFormApp"

termFormPrd :: ClBasic.TERM -> Int -> CBasic.PRED_SYMB
termFormPrd trm ar = case trm of
  ClBasic.Name_term n ->
      CBasic.Qual_pred_name (tok2Id n) (CBasic.Pred_type [list] Id.nullRange) Id.nullRange
  ClBasic.Comment_term t _ _ -> termFormPrd t ar
  ClBasic.Funct_term {} -> error "CommonLogic2CASLSeq.termFormPrd"
  ClBasic.That_term {} -> error "CommonLogic2CASLSeq.termFormPrd"

tok2Id :: Id.Token -> Id.Id
tok2Id = Id.stringToId . tok2Str

tok2Str :: Id.Token -> String
tok2Str t = let
  s = concatMap (\ c -> if c == 'x' then [c, c] else [c])
    $ Id.tokStr t
  in if elem s casl_reserved_fwords then "x_" ++ s else s


