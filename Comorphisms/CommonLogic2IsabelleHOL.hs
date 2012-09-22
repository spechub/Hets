{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  $Header$
Description :  direct comorphism from CommonLogic to Isabelle-HOL
Copyright   :  (c) Soeren Schulze, Uni Bremen 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  s.schulze@uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

A direct comorphism from CommonLogic to Isabelle-HOL, passing arguments as
native Isabelle lists.
-}

module Comorphisms.CommonLogic2IsabelleHOL where

import qualified Data.Set as Set
import qualified Data.Map as Map

import Logic.Logic
import Logic.Comorphism

import Common.ProofTree
import Common.Result
import Common.AS_Annotation as AS_Anno
import qualified Common.Id as Id
import Common.GlobalAnnotations (emptyGlobalAnnos)

import qualified CommonLogic.Logic_CommonLogic as ClLogic
import qualified CommonLogic.AS_CommonLogic as ClBasic
import qualified CommonLogic.Sign as ClSign
import qualified CommonLogic.Symbol as ClSymbol
import qualified CommonLogic.Morphism as ClMor
import qualified CommonLogic.Sublogic as ClSl
import CommonLogic.ModuleElimination

import Isabelle.IsaSign
import Isabelle.IsaConsts
import Isabelle.Logic_Isabelle
import Isabelle.Translate

data CommonLogic2IsabelleHOL = CommonLogic2IsabelleHOL deriving Show

instance Language CommonLogic2IsabelleHOL where
  language_name CommonLogic2IsabelleHOL = "CommonLogic2Isabelle"

instance Comorphism
         CommonLogic2IsabelleHOL -- comorphism
         ClLogic.CommonLogic     -- lid domain
         ClSl.CommonLogicSL      -- sublogics codomain
         ClBasic.BASIC_SPEC      -- Basic spec domain
         ClBasic.TEXT_META       -- sentence domain
         ClBasic.SYMB_ITEMS      -- symbol items domain
         ClBasic.SYMB_MAP_ITEMS  -- symbol map items domain
         ClSign.Sign             -- signature domain
         ClMor.Morphism          -- morphism domain
         ClSymbol.Symbol         -- symbol domain
         ClSymbol.Symbol         -- rawsymbol domain
         ProofTree               -- proof tree codomain
         Isabelle                -- lid codomain
         ()                      -- sublogics codomain [none]
         ()                      -- Basic spec codomain [none]
         Sentence                -- sentence codomain
         ()                      -- symbol items codomain [none]
         ()                      -- symbol map items codomain [none]
         Sign                    -- signature codomain
         IsabelleMorphism        -- morphism codomain
         ()                      -- symbol codomain [none]
         ()                      -- rawsymbol codomain [none]
         ()                      -- proof tree domain [none]
         where
           sourceLogic CommonLogic2IsabelleHOL = ClLogic.CommonLogic
           sourceSublogic CommonLogic2IsabelleHOL = ClSl.top
           targetLogic CommonLogic2IsabelleHOL = Isabelle
           map_theory CommonLogic2IsabelleHOL = mapTheory
           map_sentence CommonLogic2IsabelleHOL = mapSentence
           has_model_expansion CommonLogic2IsabelleHOL = True
           is_weakly_amalgamable CommonLogic2IsabelleHOL = True
           isInclusionComorphism CommonLogic2IsabelleHOL = True

mapSentence :: ClSign.Sign -> ClBasic.TEXT_META -> Result Sentence
mapSentence sig = return . mkSen . transTextMeta sig

mapTheory :: (ClSign.Sign, [AS_Anno.Named ClBasic.TEXT_META])
             -> Result (Sign, [AS_Anno.Named Sentence])
mapTheory (sig, namedTextMetas) =
  return (mapSig sig, map (transNamed sig) namedTextMetas)

individualS :: String
individualS = "individual"

individualT :: Typ
individualT = mkSType individualS

mapSig :: ClSign.Sign -> Sign
mapSig sig = emptySign {
  tsig = emptyTypeSig {
     arities = Map.singleton individualS [(isaTerm, [])]
     },
  constTab = Map.insert relSymb
             (mkCurryFunType [individualT, mkListType individualT] boolType) $
             Map.insert funSymb
             (mkCurryFunType [individualT, mkListType individualT] individualT) $
             Map.union (Map.fromList $ map
                        (\name -> (mkIsaConstT True emptyGlobalAnnos 0 name
                                   Main_thy Set.empty, individualT))
                        (Set.toList $ ClSign.discourseNames sig))
             (Map.fromList $ map
              (\name -> (mkIsaConstT True emptyGlobalAnnos 0 name
                         Main_thy Set.empty, mkListType individualT))
              (Set.toList $ ClSign.sequenceMarkers sig))
  }

relSymb, funSymb :: VName
relSymb = mkIsaConstT True emptyGlobalAnnos 2
          (Id.stringToId "rel")
          Main_thy Set.empty

funSymb = mkIsaConstT False emptyGlobalAnnos 2
          (Id.stringToId "fun")
          Main_thy Set.empty

quantify :: ClBasic.QUANT -> String -> Term -> Term
quantify q v s = termAppl (conDouble $ qname q) (Abs (mkFree v) s NotCont)
  where qname ClBasic.Universal = allS
        qname ClBasic.Existential = exS

transTextMeta :: ClSign.Sign -> ClBasic.TEXT_META -> Term
transTextMeta sig = transText sig . ClBasic.getText . eliminateModules

transNamed :: ClSign.Sign -> AS_Anno.Named ClBasic.TEXT_META
              -> AS_Anno.Named Sentence
transNamed sig = AS_Anno.mapNamed $ mkSen . transTextMeta sig

transText :: ClSign.Sign -> ClBasic.TEXT -> Term
transText sig txt = case txt of
  ClBasic.Text phrs _ ->
    let phrs' = filter nonImport phrs
    in if null phrs' then true
       else foldl1 binConj (map (transPhrase sig) phrs')
  ClBasic.Named_text _ t _ -> transText sig t
  where nonImport p = case p of
          ClBasic.Importation _ -> False
          _ -> True

transPhrase :: ClSign.Sign -> ClBasic.PHRASE -> Term
transPhrase sig phr = case phr of
  ClBasic.Module _ -> error "transPhase: \"module\" found"
  ClBasic.Sentence s -> transSen sig s
  ClBasic.Importation _ -> error "transPhase: \"import\" found"
  ClBasic.Comment_text _ t _ -> transText sig t

transTerm :: ClSign.Sign -> ClBasic.TERM -> Term
transTerm sig trm = case trm of
  ClBasic.Name_term name -> conDouble $ Id.tokStr name
  ClBasic.Funct_term op args _ -> applyTermSeq funSymb sig op args
  ClBasic.Comment_term t _ _ -> transTerm sig t
  ClBasic.That_term sen _ -> transSen sig sen

transNameOrSeqmark :: ClSign.Sign -> ClBasic.NAME_OR_SEQMARK -> String
transNameOrSeqmark _ ts = Id.tokStr $ case ts of
  ClBasic.Name name -> name
  ClBasic.SeqMark seqm -> seqm

transTermSeq :: ClSign.Sign -> ClBasic.TERM_SEQ -> Term
transTermSeq sig ts = case ts of
  ClBasic.Term_seq trm -> (termAppl . termAppl (conC consV))
                          (transTerm sig trm) (nilPT NotCont)
  ClBasic.Seq_marks seqm -> conDouble $ Id.tokStr seqm

-- applicable for a non-empty argument list where only the last argument
-- (or none) is a seqmark
transArgsSimple :: ClSign.Sign -> [ClBasic.TERM_SEQ] -> Maybe Term
transArgsSimple sig tss =
  foldr
  (\ts trm ->
    do trm' <- trm
       case ts of
         ClBasic.Term_seq clTrm ->
           Just $ (termAppl . termAppl (conC consV)) (transTerm sig clTrm) trm'
         _ -> Nothing)
  (Just $ transTermSeq sig $ last tss)
  (init tss)

transArgs :: ClSign.Sign -> [ClBasic.TERM_SEQ] -> Term
transArgs sig tss = case (tss, transArgsSimple sig tss) of
  ([], _) -> (nilPT NotCont)
  (_, Just trm) -> trm
  (_, Nothing) -> foldr1 (termAppl . termAppl (conC appendV))
                  (map (transTermSeq sig) tss)

applyTermSeq :: VName -> ClSign.Sign -> ClBasic.TERM -> [ClBasic.TERM_SEQ]
                -> Term
applyTermSeq metaSymb sig clTrm clArgs = binVNameAppl metaSymb trm args
  where trm = transTerm sig clTrm
        args = transArgs sig clArgs

transSen :: ClSign.Sign -> ClBasic.SENTENCE -> Term
transSen sig sen = case sen of
  ClBasic.Bool_sent bs _ -> case bs of
    ClBasic.Negation s -> termAppl notOp (transSen sig s)
    ClBasic.Junction j ss ->
      if null ss then true
      else foldr1 (case j of ClBasic.Conjunction -> binConj
                             ClBasic.Disjunction -> binDisj)
           (map (transSen sig) ss)
    ClBasic.BinOp j s1 s2 ->
      (case j of ClBasic.Implication -> binImpl
                 ClBasic.Biconditional -> binEqv)
      (transSen sig s1) (transSen sig s2)
  ClBasic.Quant_sent q bs s _ -> foldr (quantify q) (transSen sig s)
                                 (map (transNameOrSeqmark sig) bs)
  ClBasic.Atom_sent at _ -> case at of
    ClBasic.Equation t1 t2 -> binEq (transTerm sig t1) (transTerm sig t2)
    ClBasic.Atom p args -> applyTermSeq relSymb sig p args
  ClBasic.Comment_sent _ s _ -> transSen sig s
  ClBasic.Irregular_sent s _ -> transSen sig s
