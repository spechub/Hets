{- |
Module      :  $Header$
Description :  Comorphism from CommonLogic to CommonLogic
Copyright   :  (c) Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental (not complete: typleclass-instances missing)
Portability :  non-portable (via Logic.Logic)

Translating comorphism from CommonLogic to CommonLogic in order to eliminate 
modules.

-}


module Comorphisms.CommonLogic2CommonLogic (
        --CommonLogic2CommonLogic, 
        eliminateModules --eliminates all modules in a text
    )
    where

import qualified Data.Set as Set
import Data.Set (Set)
import CommonLogic.AS_CommonLogic
import CommonLogic.Tools
import Common.Id



--------------------------------------------------------------------------------
-- ASK TILL ABOUT THAT PART                                                   --
--------------------------------------------------------------------------------
{-
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

data CommonLogic2CommonLogic = CommonLogic2CommonLogic deriving Show

instance Language CommonLogic2CommonLogic where
  language_name CommonLogic2CommonLogic = "CommonLogic2CommonLogic"

instance Comorphism
    CommonLogic2CommonLogic        -- comorphism
    ClLogic.CommonLogic     -- lid domain
    ()                      -- sublogics domain
    ClBasic.BASIC_SPEC              -- Basic spec domain
    ClBasic.SENTENCE                -- sentence domain
    ClBasic.NAME                    -- symbol items domain
    ClBasic.SYMB_MAP_ITEMS          -- symbol map items domain
    ClSign.Sign            -- signature domain
    ClMor.Morphism         -- morphism domain
    ClSymbol.Symbol        -- symbol domain
    ClSymbol.Symbol        -- rawsymbol domain
    ProofTree              -- proof tree codomain
    ProofTree              -- proof tree domain
    where
      sourceLogic CommonLogic2CommonLogic = ClLogic.CommonLogic
      sourceSublogic CommonLogic2CommonLogic = ()
      targetLogic CommonLogic2CommonLogic = ClLogic.CommonLogic
      mapSublogic CommonLogic2CommonLogic = Just . mapSub -- Just . mapSub
      map_theory CommonLogic2CommonLogic = mapTheory -- TODO
      map_morphism CommonLogic2CommonLogic = mapMor  -- TODO prop
      map_sentence CommonLogic2CommonLogic = mapSentence
      has_model_expansion CommonLogic2CommonLogic = True
-}
--------------------------------------------------------------------------------
-- END: ASK TILL ABOUT THAT PART                                              --
--------------------------------------------------------------------------------




-------------------------------------------------------------------------------
-- MODULE ELIMINATION                                                        --
-------------------------------------------------------------------------------

-- | Result is an CL-equivalent text without modules
eliminateModules :: TEXT -> TEXT
eliminateModules txt = Text [Sentence (me_text newName [] txt)] nullRange
    where (newName, _) = freeName ("x", 0) (indvC_text txt)

-- NOTE: ignores importations
me_text :: NAME -> [NAME] -> TEXT -> SENTENCE
me_text newName modules txt  =
    case txt of
        Text phrs _ -> me_phrases newName modules phrs
        Named_text _ t _ -> me_text newName modules t

-- Table 2: R5a - R5b, ignoring importations and comments
me_phrases :: NAME -> [NAME] -> [PHRASE] -> SENTENCE
me_phrases newName modules phrs =
    case length phrs of
         1 -> me_phrase newName modules $ head phrs
         _ -> Bool_sent (
                Conjunction (
                    map (me_phrase newName modules) (filter mod_sen phrs)
                )
            ) nullRange
    where mod_sen p = case p of
            Module _ -> True
            Sentence _ -> True
            _ -> False


-- | converts comment-texts and importations to comment-sentences
me_phrase :: NAME -> [NAME] -> PHRASE -> SENTENCE
me_phrase newName modules p =
    case p of
        Module m -> me_module newName modules m
        Sentence s -> me_sentence newName modules s

me_sentence :: NAME -> [NAME] -> SENTENCE -> SENTENCE
me_sentence newName modules sen =
    if null modules then sen else -- this keeps the sentence simple
    case sen of
        Bool_sent bs _ -> Bool_sent (me_boolsent newName modules bs) nullRange
        Quant_sent qs _ -> Quant_sent (me_quantsent newName modules qs) nullRange
        x -> x                              -- Table 2: R1a - R2b

-- Table 2: R2a - R2e
me_boolsent :: NAME -> [NAME] -> BOOL_SENT -> BOOL_SENT
me_boolsent newName modules bs =
    case bs of
         Conjunction sens -> Conjunction $ map me_sen_mod sens
         Disjunction sens -> Disjunction $ map me_sen_mod sens
         Negation sen -> Negation $ me_sen_mod sen
         Implication s1 s2 -> Implication (me_sen_mod s1) (me_sen_mod s2)
         Biconditional s1 s2 -> Biconditional (me_sen_mod s1) (me_sen_mod s2)
    where me_sen_mod = me_sentence newName modules --TODO: check whether dn stays the same

-- Table 2: R3a - R3b
me_quantsent :: NAME -> [NAME] -> QUANT_SENT -> QUANT_SENT
me_quantsent newName modules qs =
    case qs of 
        Universal noss sen -> Universal noss (
            Bool_sent (Implication 
                (anticedent modules noss)
                (me_sentence newName modules sen)
            ) nullRange)
        Existential noss sen -> Existential noss (
            Bool_sent (Implication 
                (anticedent modules noss)
                (me_sentence newName modules sen)
            ) nullRange)

anticedent :: [NAME] -> [NAME_OR_SEQMARK] -> SENTENCE
anticedent modules noss = 
    case length modules of
         1 -> anticedent1 (head modules) noss
         _ -> Bool_sent (Conjunction (map (flip anticedent1 noss) modules)) nullRange

anticedent1 :: NAME -> [NAME_OR_SEQMARK] -> SENTENCE
anticedent1 m noss = 
    Atom_sent (Atom (Name_term m) (map nos2termseq noss)) nullRange

nos2termseq :: NAME_OR_SEQMARK -> TERM_SEQ
nos2termseq nos = case nos of 
                    Name n -> Term_seq $ Name_term n
                    SeqMark s -> Seq_marks s

-- Table 2 R4
me_module :: NAME -> [NAME] -> MODULE -> SENTENCE
me_module newName modules m =
    case m of
        Mod n t _ -> Bool_sent (Conjunction (
            (me_text newName (n:modules) t)
            : (ex_conj newName (n:modules))
            : (map (ex_conj_indvC newName (n:modules)) $ Set.elems $ indvC_text t)
          )) nullRange
        Mod_ex n excl t _ -> Bool_sent (Conjunction (
            (me_text newName (n:modules) t)
            : (ex_conj newName (n:modules))
            : (map (ex_conj_indvC newName (n:modules)) $ Set.elems $ indvC_text t)
            ++ (map (not_ex_conj_excl newName (n:modules)) excl)
          )) nullRange

-- Table 2 R4: each line in the conjunction
ex_conj :: NAME -> [NAME] -> SENTENCE
ex_conj n modules = Quant_sent (Existential [Name n] (Bool_sent ( Conjunction (
        map (modNameToPredicate n) modules
    )) nullRange)) nullRange

-- Table 2 R4: each line with indvC-elements in the conjunction
ex_conj_indvC :: NAME -> [NAME] -> NAME -> SENTENCE
ex_conj_indvC n modules c =
    Quant_sent (Existential [Name n] (Bool_sent ( Conjunction (
            (Atom_sent (Equation (Name_term n) (Name_term c)) nullRange)
            : map (modNameToPredicate n) modules
        )) nullRange)) nullRange

-- Table 2 R4: each line with excluded elements in the conjunction
not_ex_conj_excl :: NAME -> [NAME] -> NAME -> SENTENCE
not_ex_conj_excl n modules c =
    Bool_sent (Negation (ex_conj_indvC n modules c)) nullRange

-- Table 2 R4: makes a Predicate out of the module name
modNameToPredicate :: NAME -> NAME -> SENTENCE
modNameToPredicate n m =
    Atom_sent (Atom (Name_term m) [Term_seq (Name_term n)]) nullRange
-- what if the module name already occurs as a predicate?
