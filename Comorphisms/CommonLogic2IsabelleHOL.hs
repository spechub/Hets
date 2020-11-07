{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}
{- |
Module      :  ./Comorphisms/CommonLogic2IsabelleHOL.hs
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
import qualified Data.HashMap.Strict as Map
import Data.Maybe (fromMaybe)

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

import Isabelle.IsaSign hiding (qname)
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
  return (mapSig sig, ax_that : map (transNamed sig) namedTextMetas)

individualS :: String
individualS = "individual"

individualT :: Typ
individualT = mkSType individualS

ax_that :: AS_Anno.Named Sentence
ax_that = makeNamed "Ax_that" $ forceSimp $ mkSen $
          termAppl (conDouble "ALL") (Abs senTrm s NotCont)
  where s = binEqv senTrm
            (binVNameAppl
             relSymb (termAppl (con thatSymb) senTrm) (nilPT NotCont))
        senTrm = conDouble "sen"
        forceSimp sen = sen { isSimp = True }

type RENAMES = Map.HashMap String VName

mkIndName :: String -> VName
mkIndName name = mkIsaConstT True emptyGlobalAnnos (-1)
                 (Id.stringToId name) Main_thy Set.empty

addRenames :: RENAMES -> [String] -> RENAMES
addRenames = foldr
             (\ k m -> let k' = unclash k m
                           v = mkIndName k' in
                      Map.insert k v $ Map.insert k' v m)
  where unclash k m = if Map.member k m
                      then unclash ("X_" ++ k) m
                      else k

makeRenames :: [String] -> RENAMES
makeRenames = addRenames Map.empty

basicRenames :: ClSign.Sign -> RENAMES
basicRenames sig = addRenames
                   (Map.fromList [("rel", relSymb), ("fun", funSymb),
                                  ("that", thatSymb)])
                   (map (Id.tokStr . Id.idToSimpleId)
                    ( Set.toList (ClSign.sequenceMarkers sig)
                     ++ Set.toList (ClSign.discourseNames sig)))

rename :: RENAMES -> String -> VName
rename rn s = fromMaybe (error $ "Symbol " ++ show s ++ "not found") $
              Map.lookup s rn

mapSig :: ClSign.Sign -> Sign
mapSig sig = emptySign {
  tsig = emptyTypeSig {
     arities = Map.singleton individualS [(isaTerm, [])]
     },
  constTab = Map.insert relSymb
             (mkCurryFunType [individualT, mkListType individualT] boolType) $
             Map.insert funSymb
             (mkCurryFunType [individualT, mkListType individualT] individualT) $
             Map.insert thatSymb
             (mkCurryFunType [boolType] individualT) $
             Map.union (Map.fromList
                        (map ((\ name -> (rename rn name, individualT)) .
                              Id.tokStr . Id.idToSimpleId) $ Set.toList $
                         ClSign.discourseNames sig))
             (Map.fromList
              (map ((\ name -> (rename rn name, mkListType individualT)) .
                    Id.tokStr . Id.idToSimpleId) $ Set.toList $
               ClSign.sequenceMarkers sig))
  }
  where rn = basicRenames sig

relSymb, funSymb, thatSymb :: VName
relSymb = mkIsaConstT True emptyGlobalAnnos 2
          (Id.stringToId "rel")
          Main_thy Set.empty

funSymb = mkIsaConstT False emptyGlobalAnnos 2
          (Id.stringToId "fun")
          Main_thy Set.empty

thatSymb = mkIsaConstT False emptyGlobalAnnos 1
           (Id.stringToId "that")
           Main_thy Set.empty

quantify :: RENAMES -> ClBasic.QUANT -> String -> Term -> Term
quantify rn q v s = termAppl (conDouble $ qname q)
                 (Abs (con $ rename rn v) s NotCont)
  where qname ClBasic.Universal = allS
        qname ClBasic.Existential = exS

transTextMeta :: ClSign.Sign -> ClBasic.TEXT_META -> Term
transTextMeta sig = transText renames . ClBasic.getText . eliminateModules
  where renames = basicRenames sig

transNamed :: ClSign.Sign -> AS_Anno.Named ClBasic.TEXT_META
              -> AS_Anno.Named Sentence
transNamed sig = AS_Anno.mapNamed $ mkSen . transTextMeta sig

transText :: RENAMES -> ClBasic.TEXT -> Term
transText rn txt = case txt of
  ClBasic.Text phrs _ ->
    let phrs' = filter nonImport phrs
    in if null phrs' then true
       else foldl1 binConj (map (transPhrase rn) phrs')
  ClBasic.Named_text _ t _ -> transText rn t
  where nonImport p = case p of
          ClBasic.Importation _ -> False
          _ -> True

transPhrase :: RENAMES -> ClBasic.PHRASE -> Term
transPhrase rn phr = case phr of
  ClBasic.Module _ -> error "transPhase: \"module\" found"
  ClBasic.Sentence s -> transSen rn s
  ClBasic.Importation _ -> error "transPhase: \"import\" found"
  ClBasic.Comment_text _ t _ -> transText rn t

transTerm :: RENAMES -> ClBasic.TERM -> Term
transTerm rn trm = case trm of
  ClBasic.Name_term name -> con $ rename rn (Id.tokStr name)
  ClBasic.Funct_term op args _ -> applyTermSeq funSymb rn op args
  ClBasic.Comment_term t _ _ -> transTerm rn t
  ClBasic.That_term sen _ -> termAppl (con thatSymb) (transSen rn sen)

transNameOrSeqmark :: ClBasic.NAME_OR_SEQMARK -> String
transNameOrSeqmark ts = Id.tokStr $ case ts of
  ClBasic.Name name -> name
  ClBasic.SeqMark seqm -> seqm

transTermSeq :: RENAMES -> ClBasic.TERM_SEQ -> Term
transTermSeq rn ts = case ts of
  ClBasic.Term_seq trm -> (termAppl . termAppl (conC consV))
                          (transTerm rn trm) (nilPT NotCont)
  ClBasic.Seq_marks seqm -> con $ rename rn (Id.tokStr seqm)

{- applicable for a non-empty argument list where only the last argument
(or none) is a seqmark -}
transArgsSimple :: RENAMES -> [ClBasic.TERM_SEQ] -> Maybe Term
transArgsSimple rn tss =
  foldr
  (\ ts trm ->
    do trm' <- trm
       case ts of
         ClBasic.Term_seq clTrm ->
           Just $ (termAppl . termAppl (conC consV)) (transTerm rn clTrm) trm'
         _ -> Nothing)
  (Just $ transTermSeq rn $ last tss)
  (init tss)

transArgs :: RENAMES -> [ClBasic.TERM_SEQ] -> Term
transArgs rn tss = case (tss, transArgsSimple rn tss) of
  ([], _) -> nilPT NotCont
  (_, Just trm) -> trm
  (_, Nothing) -> foldr1 (termAppl . termAppl (con appendV))
                  (map (transTermSeq rn) tss)

applyTermSeq :: VName -> RENAMES -> ClBasic.TERM -> [ClBasic.TERM_SEQ] -> Term
applyTermSeq metaSymb rn clTrm clArgs = binVNameAppl metaSymb trm args
  where trm = transTerm rn clTrm
        args = transArgs rn clArgs

transSen :: RENAMES -> ClBasic.SENTENCE -> Term
transSen rn sen = case sen of
  ClBasic.Bool_sent bs _ -> case bs of
    ClBasic.Negation s -> termAppl notOp (transSen rn s)
    ClBasic.Junction j ss ->
      if null ss then true
      else foldr1 (case j of ClBasic.Conjunction -> binConj
                             ClBasic.Disjunction -> binDisj)
           (map (transSen rn) ss)
    ClBasic.BinOp j s1 s2 ->
      (case j of ClBasic.Implication -> binImpl
                 ClBasic.Biconditional -> binEqv)
      (transSen rn s1) (transSen rn s2)
  ClBasic.Quant_sent q bs s _ -> foldr (quantify rn' q) (transSen rn' s) varNames
    where rn' = addRenames rn varNames
          varNames = map transNameOrSeqmark bs
  ClBasic.Atom_sent at _ -> case at of
    ClBasic.Equation t1 t2 -> binEq (transTerm rn t1) (transTerm rn t2)
    ClBasic.Atom p args -> applyTermSeq relSymb rn p args
  ClBasic.Comment_sent _ s _ -> transSen rn s
  ClBasic.Irregular_sent s _ -> transSen rn s
