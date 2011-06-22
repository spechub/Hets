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

rq_sentence :: SENTENCE -> [NAME] -> SENTENCE
rq_sentence sen modules = 
    case sen of
        Quant_sent qs _ -> rq_quantsent qs modules
        s -> s

rq_quantsent :: QUANT_SENT -> [NAME] -> SENTENCE
rq_quantsent qs modules = 
    case qs of 
        Universal noss sen -> Quant_sent (Universal noss (
            Bool_sent (Implication 
                (anticedent noss modules)
                (rq_sentence sen modules)
            ) nullRange)) nullRange
        Existential noss sen -> Quant_sent (Existential noss (
            Bool_sent (Implication 
                (anticedent noss modules)
                (rq_sentence sen modules)
            ) nullRange)) nullRange

anticedent :: [NAME_OR_SEQMARK] -> [NAME] -> SENTENCE
anticedent noss modules = 
    Bool_sent (Conjunction (map (anticedent1 noss) modules)) nullRange

anticedent1 :: [NAME_OR_SEQMARK] -> NAME -> SENTENCE
anticedent1 noss m = 
    Atom_sent (Atom (Name_term m) (map nos2termseq noss)) nullRange

nos2termseq :: NAME_OR_SEQMARK -> TERM_SEQ
nos2termseq nos = case nos of 
                    Name n -> Term_seq $ Name_term n
                    SeqMark s -> Seq_marks s


{-
"(cl-module D (forall (x) (and (P x) (Q x))))"

==>

"(forall (x) (if (and (D x)) (and (P x) (Q x))))"

Quant_sent (
    Universal [Name x] (Bool_sent (
        Implication 
            (Bool_sent (
                Conjunction [
                    Atom_sent (Atom (Name_term D) [Term_seq (Name_term x)]) nullRange
                ]
            ) nullRange) 
            
            (Bool_sent (
                Conjunction [
                    Atom_sent (Atom (Name_term P) [Term_seq (Name_term x)]) nullRange,
                    Atom_sent (Atom (Name_term Q) [Term_seq (Name_term x)]) nullRange
                ]
            ) nullRange)
    ) nullRange)
) nullRange
-}
{-
Quant_sent (
    Universal [Name x] (Bool_sent (
        Implication (
            Bool_sent (
                Conjunction [
                    Atom_sent (Atom (Name_term D) [Term_seq (Name_term x)]) nullRange
                ]
            ) nullRange) 
            
            (Bool_sent (
                Conjunction [
                    Atom_sent (Atom (Name_term P) [Term_seq (Name_term x)]) nullRange,
                    Atom_sent (Atom (Name_term Q) [Term_seq (Name_term x)]) nullRange
                ]
            ) nullRange)
    ) nullRange)
) nullRange
-}




