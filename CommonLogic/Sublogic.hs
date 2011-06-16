{- |
Module      :  $Header$
Description :  Sublogics for CommonLogic
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Sublogics for CommonLogic
-}

module CommonLogic.Sublogic
    (
     sl_basic_spec                  -- determine sublogic for basic spec
    , CLTextType (..)               -- types of CommonLogic texts
    , CommonLogicSL (..)            -- sublogics for CommonLogic
    , sublogics_max                 -- join of sublogics
    , top                           -- FullCommonLogic
    , bottom                        -- Propositional
    , sublogics_all                 -- all sublogics
    , sublogics_name                -- name of sublogics
    , sl_sig                        -- sublogic for a signature
    , sublogic                      -- sublogic for a text
    , sl_sym                        -- sublogic for symbols
    , sl_mor                        -- sublogic for morphisms
    , sl_symmap                     -- sublogic for symbol map items
    , isProp
    , isFOL
    , isCL
    )
    where

import qualified Data.Set as Set
import qualified CommonLogic.AS_CommonLogic as AS
import qualified Common.AS_Annotation as AS_Anno
import qualified CommonLogic.Sign as Sign
import qualified CommonLogic.Symbol as Symbol
import qualified CommonLogic.Morphism as Morphism

-------------------------------------------------------------------------------
-- datatypes                                                                 --
-------------------------------------------------------------------------------

-- | types of sublogics
data CLTextType = Propositional      -- Text without quantifiers
                | FirstOrder         -- Text in First Order Logic
                | FullCommonLogic    -- Text without any constraints
                deriving (Show, Eq, Ord)

-- | sublogics for CommonLogic
data CommonLogicSL = CommonLogicSL
    { format       :: CLTextType     -- Structural restrictions
    } deriving (Show, Eq, Ord)


isProp :: CommonLogicSL -> Bool
isProp sl = format sl == Propositional

isFOL :: CommonLogicSL -> Bool
isFOL sl = format sl == FirstOrder

isCL :: CommonLogicSL -> Bool
isCL sl = format sl == FullCommonLogic

-- | comparison of sublogics
compareLE :: CommonLogicSL -> CommonLogicSL -> Bool
compareLE p1 p2 =
    let f1 = format p1
        f2 = format p2
    in
      case (f1, f2) of
        (_,               FullCommonLogic) -> True
        (FullCommonLogic, FirstOrder)      -> False
        (_,               FirstOrder)      -> True
        (Propositional,   Propositional)   -> True
        (_,               Propositional)   -> False

------------------------------------------------------------------------------
-- Special elements in the Lattice of logics                                --
------------------------------------------------------------------------------

top :: CommonLogicSL
top = CommonLogicSL FullCommonLogic

bottom :: CommonLogicSL
bottom = CommonLogicSL Propositional

folsl :: CommonLogicSL
folsl = CommonLogicSL {format = FirstOrder}


propsl :: CommonLogicSL
propsl = CommonLogicSL {format = Propositional}

-------------------------------------------------------------------------------
-- join and max                                                              --
-------------------------------------------------------------------------------

sublogics_join :: (CLTextType -> CLTextType -> CLTextType)
                  -> CommonLogicSL -> CommonLogicSL -> CommonLogicSL
sublogics_join pfF a b = CommonLogicSL
                         {
                           format    = pfF (format a) (format b)
                         }

joinType :: CLTextType -> CLTextType -> CLTextType
joinType Propositional   Propositional   = Propositional
joinType Propositional   FirstOrder      = FirstOrder
joinType FirstOrder      Propositional   = FirstOrder
joinType FirstOrder      FirstOrder      = FirstOrder
joinType _               _               = FullCommonLogic

sublogics_max :: CommonLogicSL -> CommonLogicSL -> CommonLogicSL
sublogics_max = sublogics_join joinType

-------------------------------------------------------------------------------
-- Helpers                                                                   --
-------------------------------------------------------------------------------

-- compute sublogics from a list of sublogics
--
comp_list :: [CommonLogicSL] -> CommonLogicSL
comp_list l = foldl sublogics_max bottom l

unifyPredicates :: (a -> Set.Set AS.NAME) -> [a] -> Set.Set AS.NAME
unifyPredicates prd_item items =
    foldl (\ns i -> Set.union ns (prd_item i)) Set.empty items

------------------------------------------------------------------------------
-- Functions to compute the set of predicates, these work by recursing      --
-- into all subelements                                                     --
------------------------------------------------------------------------------

prd_text :: AS.TEXT -> Set.Set AS.NAME
prd_text t = 
    case t of
         AS.Text ps _ -> prd_phrases ps
         AS.Named_text _ nt _ -> prd_text nt

prd_phrases :: [AS.PHRASE] -> Set.Set AS.NAME
prd_phrases ps = unifyPredicates prd_phrase ps

prd_phrase :: AS.PHRASE -> Set.Set AS.NAME
prd_phrase p = 
    case p of 
         AS.Module m -> prd_module m
         AS.Sentence s -> prd_sentence s
         AS.Importation i -> prd_importation i
         AS.Comment_text _ t _ -> prd_text t

prd_module :: AS.MODULE -> Set.Set AS.NAME
prd_module m = 
    case m of
         AS.Mod _ t _ -> prd_text t
         AS.Mod_ex _ _ t  _ -> prd_text t 

prd_sentence :: AS.SENTENCE -> Set.Set AS.NAME
prd_sentence s = 
    case s of
         AS.Quant_sent q _ -> prd_quantSent q
         AS.Bool_sent b _ -> prd_boolSent b
         AS.Atom_sent a _ -> prd_atomSent a
         AS.Comment_sent _ c _ -> prd_sentence c
         AS.Irregular_sent i _ -> prd_sentence i

prd_importation :: AS.IMPORTATION -> Set.Set AS.NAME
prd_importation (AS.Imp_name n) = prd_name n

prd_quantSent :: AS.QUANT_SENT -> Set.Set AS.NAME
prd_quantSent q = 
    case q of
         AS.Universal noss s -> 
            Set.union (unifyPredicates prd_nameOrSeqmark noss) $ prd_sentence s
         AS.Existential noss s -> 
            Set.union (unifyPredicates prd_nameOrSeqmark noss) $ prd_sentence s
--TODO SequenceMarker Handling

prd_nameOrSeqmark :: AS.NAME_OR_SEQMARK -> Set.Set AS.NAME
prd_nameOrSeqmark nos = 
    case nos of
         AS.Name n -> prd_name n
         AS.SeqMark s -> prd_seqmark s

prd_boolSent :: AS.BOOL_SENT -> Set.Set AS.NAME
prd_boolSent b = 
    case b of
         AS.Conjunction ss -> unifyPredicates prd_sentence ss
         AS.Disjunction ss -> unifyPredicates prd_sentence ss
         AS.Negation s -> prd_sentence s
         AS.Implication s1 s2 -> unifyPredicates prd_sentence [s1,s2]
         AS.Biconditional s1 s2 -> unifyPredicates prd_sentence [s1,s2]

prd_atomSent :: AS.ATOM -> Set.Set AS.NAME
prd_atomSent a = 
    case a of
         AS.Equation t1 t2 -> unifyPredicates prd_term [t1,t2]
         AS.Atom t tseq -> 
            if null tseq 
               then prd_term t
               else Set.union (prd_termSeqs tseq) $ prd_add_term t

prd_term :: AS.TERM -> Set.Set AS.NAME
prd_term t = 
  case t of
    AS.Name_term n -> prd_name n
    AS.Funct_term ft tseqs _ -> Set.union (prd_add_term ft) (prd_termSeqs tseqs)
    AS.Comment_term ct _ _ -> prd_term ct

prd_name :: AS.NAME -> Set.Set AS.NAME
prd_name _ = Set.empty

prd_seqmark :: AS.SEQ_MARK -> Set.Set AS.NAME
prd_seqmark _ = Set.empty

prd_termSeqs :: [AS.TERM_SEQ] -> Set.Set AS.NAME
prd_termSeqs tsecs = unifyPredicates prd_termSeq tsecs

prd_termSeq :: AS.TERM_SEQ -> Set.Set AS.NAME
prd_termSeq tsec = 
    case tsec of
         AS.Term_seq t -> prd_term t
         AS.Seq_marks s -> prd_seqmark s

prd_add_term :: AS.TERM -> Set.Set AS.NAME
prd_add_term t = 
  case t of
    AS.Name_term n -> prd_add_name n
    AS.Funct_term ft tseqs _ -> Set.union (prd_add_term ft) (prd_termSeqs tseqs)
    AS.Comment_term ct _ _ -> prd_term ct

prd_add_name :: AS.NAME -> Set.Set AS.NAME
prd_add_name n = Set.singleton n

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element, these work    --
-- by recursing into all subelements                                        --
------------------------------------------------------------------------------

-- | determines the sublogic for a complete text
sublogic :: AS.TEXT -> CommonLogicSL
sublogic t = sl_text (prd_text t) bottom t


-- | determines the sublogic for symbol map items
sl_symmap ::  Set.Set AS.NAME -> CommonLogicSL -> AS.SYMB_MAP_ITEMS 
    -> CommonLogicSL
sl_symmap _ cs _ = cs

-- | determines the sublogic for a morphism
sl_mor :: Set.Set AS.NAME -> CommonLogicSL -> Morphism.Morphism -> CommonLogicSL
sl_mor _ cs _ = cs

-- | determines the sublogic for a Signature
sl_sig :: Set.Set AS.NAME -> CommonLogicSL -> Sign.Sign -> CommonLogicSL
sl_sig _ cs _ = cs

-- | determines the sublogic for symbols
sl_sym :: Set.Set AS.NAME -> CommonLogicSL -> Symbol.Symbol -> CommonLogicSL
sl_sym _ cs _ = cs

-- | determines sublogic for texts
sl_text :: Set.Set AS.NAME -> CommonLogicSL -> AS.TEXT -> CommonLogicSL
sl_text prds cs t = 
    case t of
        AS.Text ps _ -> sl_phrases prds cs ps
        AS.Named_text _ nt _ -> sl_text prds cs nt

-- | determines sublogic for phrases
sl_phrases :: Set.Set AS.NAME -> CommonLogicSL -> [AS.PHRASE] -> CommonLogicSL
sl_phrases prds cs ps = foldl sublogics_max cs $ map (sl_phrase prds cs) ps

-- | determines sublogic for a single phrase
sl_phrase :: Set.Set AS.NAME -> CommonLogicSL -> AS.PHRASE -> CommonLogicSL
sl_phrase prds cs p = 
    case p of
        AS.Module m -> sl_module prds cs m
        AS.Sentence s -> sl_sentence prds cs s
        AS.Importation i -> sl_importation prds cs i
        AS.Comment_text _ t _ -> sl_text prds cs t 
            --is the last one correct/necessary?

-- | determines sublogic for a module
sl_module :: Set.Set AS.NAME -> CommonLogicSL -> AS.MODULE -> CommonLogicSL
sl_module prds cs m = 
    case m of
        AS.Mod _ t _ -> sl_text prds cs t
        AS.Mod_ex _ _ t _ -> sl_text prds cs t

sl_sentence :: Set.Set AS.NAME -> CommonLogicSL -> AS.SENTENCE -> CommonLogicSL
sl_sentence prds cs sen = 
    case sen of
        AS.Quant_sent q _ -> sl_quantSent prds cs q
        AS.Bool_sent b _ -> sl_boolSent prds cs b
        AS.Atom_sent a _ -> sl_atomSent prds cs a
        AS.Comment_sent _ s _ -> sl_sentence prds cs s
        AS.Irregular_sent s _ -> sl_sentence prds cs s

-- | determines the sublogic for importations
sl_importation :: Set.Set AS.NAME -> CommonLogicSL -> AS.IMPORTATION
    -> CommonLogicSL
sl_importation prds cs (AS.Imp_name n) = sl_name prds cs n

-- | determines the sublogic for quantified sentences
sl_quantSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.QUANT_SENT 
    -> CommonLogicSL
sl_quantSent prds cs q = 
    case q of
        AS.Universal noss s -> 
            comp_list $ folsl : sl_sentence prds cs s 
                              : map (sl_nameOrSeqmark prds cs) noss
        AS.Existential noss s -> 
            comp_list $ folsl : sl_sentence prds cs s 
                              : map (sl_nameOrSeqmark prds cs) noss

-- | determines the sublogic for boolean sentences
sl_boolSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.BOOL_SENT -> CommonLogicSL
sl_boolSent prds cs b = 
    case b of
      AS.Conjunction ss -> comp_list $ map (sl_sentence prds cs) ss
      AS.Disjunction ss -> comp_list $ map (sl_sentence prds cs) ss
      AS.Negation s -> sl_sentence prds cs s
      AS.Implication s1 s2 -> 
        sublogics_max (sl_sentence prds cs s1) (sl_sentence prds cs s2)
      AS.Biconditional s1 s2 -> 
        sublogics_max (sl_sentence prds cs s1) (sl_sentence prds cs s2)

-- | determines the sublogic for atoms
sl_atomSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.ATOM -> CommonLogicSL
sl_atomSent prds cs a = 
    case a of
        AS.Equation t1 t2 -> 
            comp_list $ folsl : map (sl_term prds cs) [t1,t2]
        AS.Atom t [] -> sl_term prds cs t 
        AS.Atom t tseq -> comp_list 
            $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq

-- | determines the sublogic for NAME_OR_SEQMARK
sl_nameOrSeqmark :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME_OR_SEQMARK 
    -> CommonLogicSL
sl_nameOrSeqmark prds cs nos = 
    case nos of
        AS.Name n -> sl_quantName prds cs n
        AS.SeqMark _ -> cs -- correct?

-- | determines the sublogic for names which are next to a quantifier
sl_quantName :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_quantName prds _ n = if Set.member n prds then top else folsl

-- | determines the sublogic for names
sl_name :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_name _ _ _ = propsl

-- | determines the sublogic for terms
sl_term :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_term prds cs term = 
    case term of
      AS.Name_term n -> sl_name prds cs n
      AS.Funct_term t tseq _ -> 
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t
        --is the last one correct/necessary?

-- | determines the sublogic for term sequences
sl_termSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM_SEQ -> CommonLogicSL
sl_termSeq prds cs tseq = 
    case tseq of
        AS.Term_seq t -> sl_termInSeq prds cs t--------------------
        AS.Seq_marks _ -> cs -- correct?

-- | determines the sublogic for names
sl_nameInTermSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_nameInTermSeq prds _ n = if Set.member n prds then top else propsl

-- | determines the sublogic for terms inside of a term-sequence
sl_termInSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_termInSeq prds cs term = 
    case term of
      AS.Name_term n -> sl_nameInTermSeq prds cs n
      AS.Funct_term t tseq _ -> 
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t
        --is the last one correct/necessary?



-- | determines subloig for basic items
sl_basic_items :: Set.Set AS.NAME -> CommonLogicSL -> AS.BASIC_ITEMS 
    -> CommonLogicSL
sl_basic_items preds ps (AS.Axiom_items xs) = 
    comp_list $ map ((sl_sentence preds ps) . AS_Anno.item) xs

-- | determines sublogic for basic spec
sl_basic_spec :: Set.Set AS.NAME -> CommonLogicSL -> AS.BASIC_SPEC 
    -> CommonLogicSL
sl_basic_spec preds ps (AS.Basic_spec spec) =
    comp_list $ map ((sl_basic_items preds ps) . AS_Anno.item) spec

-- | all sublogics
sublogics_all :: [CommonLogicSL]
sublogics_all =
    [CommonLogicSL
     {
       format    = Propositional
     }
    ,CommonLogicSL
     {
       format    = FirstOrder
     }
    ,CommonLogicSL
     {
       format    = FullCommonLogic
     }
    ]

-------------------------------------------------------------------------------
-- Conversion functions to String                                            --
-------------------------------------------------------------------------------

sublogics_name :: CommonLogicSL -> String
sublogics_name f = case format f of
                     Propositional   -> "Propositional"
                     FirstOrder      -> "First Order"
                     FullCommonLogic -> "Full CommonLogic"

-------------------------------------------------------------------------------
-- Projections to sublogics                                                  --
-------------------------------------------------------------------------------
-- TODO: Projections