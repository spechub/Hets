{- |
Just beginning to implement. 
Eugen Kuksa
-}

module CommonLogic.ModuleElim
    where

import CommonLogic.AS_CommonLogic
import Common.Id
import CommonLogic.ClTests

-------------------------------------------------------------------------------
--                                                                           --
-------------------------------------------------------------------------------

rq :: TEXT -> TEXT
rq txt = Text [Sentence (rq_text [] txt)] nullRange

-- | ignores importations
rq_text :: [NAME] -> TEXT -> SENTENCE
rq_text modules txt  =
    case txt of
        Text phrs _ -> rq_phrases modules phrs
        Named_text _ t _ -> rq_text modules t

-- Table 2: R5a - R5b, ignoring importations and comments
rq_phrases :: [NAME] -> [PHRASE] -> SENTENCE
rq_phrases modules phrs = 
    case length phrs of
         1 -> rq_phrase modules $ head phrs
         _ -> Bool_sent (
                Conjunction (map (rq_phrase modules) (filter mod_sen phrs))
            ) nullRange
    where mod_sen p = case p of
            Module _ -> True
            Sentence _ -> True
            _ -> False


-- | converts comment-texts and importations to comment-sentences
rq_phrase :: [NAME] -> PHRASE -> SENTENCE
rq_phrase modules p = 
    case p of
        Module m -> rq_module modules m
        Sentence s -> rq_sentence modules s
        --Importation i -> Comment_sent (Comment (show i)  nullRange) --TODO: remove show
        --Comment_text c t _ -> 
        --    Comment_sent (Comment (show c ++ " " ++ show t)  nullRange) --TODO: remove show

--TODO: determine IndV(E)
rq_module :: [NAME] -> MODULE -> SENTENCE -- TODO: implement like in table 2 R4
rq_module modules m = 
    case m of
         Mod n txt r -> rq_text (n:modules) txt
         Mod_ex n exs txt r -> rq_text (n:modules) txt -- TODO: use exs

rq_sentence :: [NAME] -> SENTENCE -> SENTENCE
rq_sentence modules sen = 
    case sen of
        Bool_sent bs _ -> Bool_sent (rq_boolsent modules bs) nullRange
        Quant_sent qs _ -> Quant_sent (rq_quantsent modules qs) nullRange
        x -> x                              -- Table 2: R1a - R2b

-- Table 2: R2a - R2e
rq_boolsent :: [NAME] -> BOOL_SENT -> BOOL_SENT
rq_boolsent modules bs = 
    case bs of
         Conjunction sens -> Conjunction $ map rq_sen_mod sens
         Disjunction sens -> Disjunction $ map rq_sen_mod sens
         Negation sen -> Negation $ rq_sen_mod sen
         Implication s1 s2 -> Implication (rq_sen_mod s1) (rq_sen_mod s2)
         Biconditional s1 s2 -> Biconditional (rq_sen_mod s1) (rq_sen_mod s2)
    where rq_sen_mod = rq_sentence modules

-- Table 2: R3a - R3b
rq_quantsent :: [NAME] -> QUANT_SENT -> QUANT_SENT
rq_quantsent modules qs = 
    case qs of 
        Universal noss sen -> Universal noss (
            Bool_sent (Implication 
                (anticedent modules noss)
                (rq_sentence modules sen)
            ) nullRange)
        Existential noss sen -> Existential noss (
            Bool_sent (Implication 
                (anticedent modules noss)
                (rq_sentence modules sen)
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


{-



"(cl-module D (P x)) (cl-module E (Q x)) (cl-module Fa (cl-module Fb (forall (z) (R z))))"


Text [
    Module (Mod D (Text [
        Sentence (Atom_sent (Atom (Name_term P) [Term_seq (Name_term x)]) nullRange)
    ] nullRange) nullRange),

    Module (Mod E (Text [
        Sentence (Atom_sent (Atom (Name_term Q) [Term_seq (Name_term x)]) nullRange)
    ] nullRange) nullRange),

    Module (Mod Fa (Text [
        Module (Mod Fb (Text [
            Sentence (Quant_sent (Universal [Name z] (
                Atom_sent (Atom (Name_term R) [Term_seq (Name_term z)]) nullRange
            )) nullRange)
        ] nullRange) nullRange)
    ] nullRange) nullRange)
] nullRange



rq
==>




Text [
Module (Mod D (Text [
    Sentence (Atom_sent (Atom (Name_term P) [Term_seq (Name_term x)]) nullRange)
] nullRange) nullRange),

Module (Mod E (Text [
    Sentence (Atom_sent (Atom (Name_term Q) [Term_seq (Name_term x)]) nullRange)
] nullRange) nullRange),

Module (Mod Fa (Text [
    Module (Mod Fb (Text [
        Sentence (Quant_sent (Universal [Name z] (
            Bool_sent (
                Implication (
                    Bool_sent (Conjunction [
                        Atom_sent (Atom (Name_term Fb) [Term_seq (Name_term z)]) nullRange,
                        Atom_sent (Atom (Name_term Fa) [Term_seq (Name_term z)]) nullRange
                    ]) nullRange
                ) (
                    Atom_sent (Atom (Name_term R) [Term_seq (Name_term z)]) nullRange
                )
            ) nullRange
        )) nullRange)
    ] nullRange) nullRange)
] nullRange) nullRange)
] nullRange










"(cl-module D (P x)) (cl-module E (Q x)) (cl-module Fb (cl-module Fa (forall (z) (if (and (Fa z) (Fb z)) (R z)))))"

Text [
Module (Mod D (Text [
    Sentence (Atom_sent (Atom (Name_term P) [Term_seq (Name_term x)]) nullRange)
] nullRange) nullRange),

Module (Mod E (Text [
    Sentence (Atom_sent (Atom (Name_term Q) [Term_seq (Name_term x)]) nullRange)
] nullRange) nullRange),

Module (Mod Fa (Text [
    Module (Mod Fb (Text [
        Sentence (Quant_sent (Universal [Name z] (
            Bool_sent (
                Implication (
                    Bool_sent (Conjunction [
                        Atom_sent (Atom (Name_term Fb) [Term_seq (Name_term z)]) nullRange,
                        Atom_sent (Atom (Name_term Fa) [Term_seq (Name_term z)]) nullRange
                    ]) nullRange
                ) (
                    Atom_sent (Atom (Name_term R) [Term_seq (Name_term z)]) nullRange
                )
            ) nullRange
        )) nullRange)
    ] nullRange) nullRange)
] nullRange) nullRange)
] nullRange


-}










