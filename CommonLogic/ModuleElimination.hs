{- |
Module      :  ./CommonLogic/ModuleElimination.hs
Description :  Module elimination in CommonLogic
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Used by Comorphisms.CommonLogicModuleElimination and Print_KIF.
-}

module CommonLogic.ModuleElimination (eliminateModules) where

import qualified Data.Set as Set
import CommonLogic.Tools
import Common.Id

import CommonLogic.AS_CommonLogic

-- | Result is a CL-equivalent text without modules
eliminateModules :: TEXT_META -> TEXT_META
eliminateModules tm =
  tm { getText = Text [Sentence (me_text newName [] $ getText tm)] nullRange }
  where (newName, _) = freeName ("item", 0) (indvC_text $ getText tm)

-- NOTE: ignores importations
me_text :: NAME -> [NAME] -> TEXT -> SENTENCE
me_text newName modules txt =
    case txt of
        Text phrs _ -> me_phrases newName modules $ filter nonImportation phrs
        Named_text _ t _ -> me_text newName modules t
  where nonImportation p = case p of
          Importation _ -> False
          _ -> True

-- Table 2: R5a - R5b, ignoring importations and comments
me_phrases :: NAME -> [NAME] -> [PHRASE] -> SENTENCE
me_phrases newName modules phrs =
    case length phrs of
         1 -> me_phrase newName modules $ head phrs
         _ -> Bool_sent (
                Junction Conjunction (
                    map (me_phrase newName modules) (filter mod_sen phrs)
                )
            ) nullRange
    where mod_sen p = case p of
            Module _ -> True
            Sentence _ -> True
            _ -> False


-- | converts comment-texts to comment-sentences
me_phrase :: NAME -> [NAME] -> PHRASE -> SENTENCE
me_phrase newName modules p =
    case p of
        Module m -> me_module newName modules m
        Sentence s -> me_sentence newName modules s
        Comment_text c txt r -> Comment_sent c (me_text newName modules txt) r
        Importation _ -> undefined

me_sentence :: NAME -> [NAME] -> SENTENCE -> SENTENCE
me_sentence newName modules sen =
    if null modules then sen else -- this keeps the sentence simple
    case sen of
        Bool_sent bs _ -> Bool_sent (me_boolsent newName modules bs) nullRange
        Quant_sent q vs is _ ->
          Quant_sent q vs (me_quantsent newName modules q vs is) nullRange
        x -> x                              -- Table 2: R1a - R2b

-- Table 2: R2a - R2e
me_boolsent :: NAME -> [NAME] -> BOOL_SENT -> BOOL_SENT
me_boolsent newName modules bs =
    case bs of
         Junction j sens -> Junction j $ map me_sen_mod sens
         Negation sen -> Negation $ me_sen_mod sen
         BinOp op s1 s2 -> BinOp op (me_sen_mod s1) (me_sen_mod s2)
    where me_sen_mod = me_sentence newName modules -- TODO: check whether dn stays the same

-- Table 2: R3a - R3b
me_quantsent :: NAME -> [NAME] -> QUANT -> [NAME_OR_SEQMARK] -> SENTENCE
                -> SENTENCE
me_quantsent newName modules _ noss sen =
  Bool_sent (BinOp Implication
             (anticedent modules noss)
             (me_sentence newName modules sen)) nullRange

anticedent :: [NAME] -> [NAME_OR_SEQMARK] -> SENTENCE
anticedent modules noss =
    case modules of
         [m] -> anticedent1 m noss
         _ -> Bool_sent (Junction Conjunction (map (`anticedent1` noss) modules)) nullRange

anticedent1 :: NAME -> [NAME_OR_SEQMARK] -> SENTENCE
anticedent1 m noss = case noss of
  [nos] -> Atom_sent (Atom (Name_term m) [nos2termseq nos]) nullRange
  _ -> Bool_sent (Junction Conjunction $
                  map (\ nos -> anticedent1 m [nos]) noss) nullRange

nos2termseq :: NAME_OR_SEQMARK -> TERM_SEQ
nos2termseq nos = case nos of
                    Name n -> Term_seq $ Name_term n
                    SeqMark s -> Seq_marks s

-- Table 2 R4
me_module :: NAME -> [NAME] -> MODULE -> SENTENCE
me_module newName modules m =
    case m of
        Mod n t _ -> Bool_sent (Junction Conjunction (
              me_text newName (n : modules) t
            : ex_conj newName (n : modules)
            : map (ex_conj_indvC newName (n : modules)) (Set.elems $ indvC_text t)
          )) nullRange
        Mod_ex n excl t _ -> Bool_sent (Junction Conjunction (
              me_text newName (n : modules) t
            : ex_conj newName (n : modules)
            : map (ex_conj_indvC newName (n : modules)) (Set.elems $ indvC_text t)
            ++ map (not_ex_conj_excl newName (n : modules)) excl
          )) nullRange

-- Table 2 R4: each line in the conjunction
ex_conj :: NAME -> [NAME] -> SENTENCE
ex_conj n modules =
  Quant_sent Existential [Name n] (Bool_sent (Junction Conjunction (
        map (modNameToPredicate n) modules
    )) nullRange) nullRange

-- Table 2 R4: each line with indvC-elements in the conjunction
ex_conj_indvC :: NAME -> [NAME] -> NAME -> SENTENCE
ex_conj_indvC n modules c =
    Quant_sent Existential [Name n] (Bool_sent (Junction Conjunction (
            Atom_sent (Equation (Name_term n) (Name_term c)) nullRange
            : map (modNameToPredicate n) modules
        )) nullRange) nullRange

-- Table 2 R4: each line with excluded elements in the conjunction
not_ex_conj_excl :: NAME -> [NAME] -> NAME -> SENTENCE
not_ex_conj_excl n modules c =
    Bool_sent (Negation (ex_conj_indvC n modules c)) nullRange

-- Table 2 R4: makes a Predicate out of the module name
modNameToPredicate :: NAME -> NAME -> SENTENCE
modNameToPredicate n m =
    Atom_sent (Atom (Name_term m) [Term_seq (Name_term n)]) nullRange
-- what if the module name already occurs as a predicate?
