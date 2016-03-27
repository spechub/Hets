{- |
Module      :  ./CommonLogic/Tools.hs
Description :  Tools for CommonLogic static analysis
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Tools for CommonLogic static analysis
-}

module CommonLogic.Tools
  ( freeName      -- finds a free discourse name
  , indvC_text    -- retrieves all discourse names from a text
  , indvC_sen     -- retrieves all discourse names from a sentence
  , indvC_term    -- retrieves all discourse names from a term
  , prd_text      -- retrieves all predicates from a text
  , setUnion_list -- maps function @f@ to the list @ts@ and unifies the results
  ) where

import Data.Char (intToDigit)
import Data.Set (Set)
import qualified Data.Set as Set
import CommonLogic.AS_CommonLogic
import Common.Id


{- -----------------------------------------------------------------------------
Misc functions                                                            --
----------------------------------------------------------------------------- -}

{- | Finds a free discourse name (appends "_" at the end until free name found)
given the set of all discourse names -}
freeName :: (String, Int) -> Set NAME -> (NAME, Int)
freeName (s, i) ns =
    if Set.member n ns
       then freeName (s, i + 1) ns
       else (n, i + 1)
    where n = mkSimpleId (s ++ "_" ++ [intToDigit i])

{- -----------------------------------------------------------------------------
Functions to compute the set of individual constants (discourse items),   --
these work by recursing into all subelements                              --
----------------------------------------------------------------------------- -}

-- | maps @f@ to @ts@ and unifies the results
setUnion_list :: (Ord b) => (a -> Set b) -> [a] -> Set b
setUnion_list f = Set.unions . map f

-- | retrieves the individual constants from a text
indvC_text :: TEXT -> Set NAME
indvC_text t =
    case t of
         Text ps _ -> setUnion_list indvC_phrase ps
         Named_text _ txt _ -> indvC_text txt

-- | retrieves the individual constants from a phrase
indvC_phrase :: PHRASE -> Set NAME
indvC_phrase p =
    case p of
         Module m -> indvC_module m
         Sentence s -> indvC_sen s
         Comment_text _ t _ -> indvC_text t
         _ -> Set.empty

-- | retrieves the individual constants from a module
indvC_module :: MODULE -> Set NAME
indvC_module m =
    case m of
         Mod _ t _ -> indvC_text t
         Mod_ex _ _ t _ -> indvC_text t

-- | retrieves the individual constants from a sentence
indvC_sen :: SENTENCE -> Set NAME
indvC_sen s =
    case s of
         Quant_sent q vs is _ -> indvC_quantsent q vs is
         Bool_sent b _ -> indvC_boolsent b
         Atom_sent a _ -> indvC_atomsent a
         Comment_sent _ c _ -> indvC_sen c
         Irregular_sent i _ -> indvC_sen i

-- | retrieves the individual constants from a quantified sentence
indvC_quantsent :: QUANT -> [NAME_OR_SEQMARK] -> SENTENCE -> Set NAME
indvC_quantsent _ = quant
    where quant :: [NAME_OR_SEQMARK] -> SENTENCE -> Set NAME
          quant nss se = Set.difference (indvC_sen se)
            $ setUnion_list nameof nss
          nameof :: NAME_OR_SEQMARK -> Set NAME
          nameof nsm =
              case nsm of
                   Name n -> Set.singleton n
                   SeqMark _ -> Set.empty -- see indvC_termSeq

-- | retrieves the individual constants from a boolean sentence
indvC_boolsent :: BOOL_SENT -> Set NAME
indvC_boolsent b =
    case b of
         Junction _ ss -> setUnion_list indvC_sen ss
         Negation s -> indvC_sen s
         BinOp _ s1 s2 -> setUnion_list indvC_sen [s1, s2]

-- | retrieves the individual constants from an atom
indvC_atomsent :: ATOM -> Set NAME
indvC_atomsent a =
    case a of
         Equation t1 t2 -> indvC_term t1 `Set.union` indvC_term t2
         Atom t ts -> Set.union (nonToplevelNames t)
                    $ setUnion_list indvC_termSeq ts -- arguments

-- | omit predicate names
nonToplevelNames :: TERM -> Set NAME
nonToplevelNames trm = case trm of
        Name_term _ -> Set.empty
        Comment_term t _ _ -> nonToplevelNames t
        _ -> indvC_term trm

-- | retrieves the individual constants from a term
indvC_term :: TERM -> Set NAME
indvC_term trm =
    case trm of
        Name_term n -> Set.singleton n
        Funct_term t ts _ -> Set.union (indvC_term t)
          $ setUnion_list indvC_termSeq ts -- arguments
        Comment_term t _ _ -> indvC_term t
        That_term s _ -> indvC_sen s

-- | retrieves the individual constant from a single argument
indvC_termSeq :: TERM_SEQ -> Set NAME
indvC_termSeq t =
    case t of
        Term_seq txt -> indvC_term txt
        Seq_marks _ -> Set.empty

{- ----------------------------------------------------------------------------
Functions to compute the set of predicates, these work by recursing      --
into all subelements                                                     --
---------------------------------------------------------------------------- -}

-- | Retrieves all predicates from a text
prd_text :: TEXT -> Set.Set NAME
prd_text t =
    case t of
         Text ps _ -> prd_phrases ps
         Named_text _ nt _ -> prd_text nt

prd_phrases :: [PHRASE] -> Set.Set NAME
prd_phrases = setUnion_list prd_phrase

prd_phrase :: PHRASE -> Set.Set NAME
prd_phrase p =
    case p of
         Module m -> prd_module m
         Sentence s -> prd_sentence s
         Importation _ -> Set.empty
         Comment_text _ t _ -> prd_text t

prd_module :: MODULE -> Set.Set NAME
prd_module m =
    case m of
         Mod _ t _ -> prd_text t
         Mod_ex _ _ t _ -> prd_text t

prd_sentence :: SENTENCE -> Set.Set NAME
prd_sentence s =
    case s of
         Quant_sent q vs is _ -> prd_quantSent q vs is
         Bool_sent b _ -> prd_boolSent b
         Atom_sent a _ -> prd_atomSent a
         Comment_sent _ c _ -> prd_sentence c
         Irregular_sent i _ -> prd_sentence i

prd_quantSent :: QUANT -> [NAME_OR_SEQMARK] -> SENTENCE -> Set.Set NAME
prd_quantSent _ _ = prd_sentence
{- we do not know if variables are predicates, we assume no, and only
check the body -}

prd_boolSent :: BOOL_SENT -> Set.Set NAME
prd_boolSent b =
    case b of
         Junction _ ss -> setUnion_list prd_sentence ss
         Negation s -> prd_sentence s
         BinOp _ s1 s2 -> setUnion_list prd_sentence [s1, s2]

prd_atomSent :: ATOM -> Set.Set NAME
prd_atomSent a =
    case a of
         Equation t1 t2 -> setUnion_list prd_term [t1, t2]
         Atom t tseq -> -- the predicate name is in t
           Set.unions [prd_termSeqs tseq, prd_term t, prd_add_term t]

prd_term :: TERM -> Set.Set NAME
prd_term t =
  case t of
    Name_term _ -> Set.empty
    Funct_term ft tseqs _ -> prd_term ft `Set.union` prd_termSeqs tseqs
      -- the function name is not a predicate
    Comment_term ct _ _ -> prd_term ct
    That_term s _ -> prd_sentence s

prd_termSeqs :: [TERM_SEQ] -> Set.Set NAME
prd_termSeqs = setUnion_list prd_termSeq

prd_termSeq :: TERM_SEQ -> Set.Set NAME
prd_termSeq tsec =
    case tsec of
         Term_seq t -> prd_term t
         Seq_marks _ -> Set.empty

prd_add_term :: TERM -> Set.Set NAME
prd_add_term t =
  case t of
    Name_term n -> Set.singleton n
    Comment_term ct _ _ -> prd_add_term ct
    _ -> Set.empty -- from all other terms we do not extract the predicate name
