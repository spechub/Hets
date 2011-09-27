{- |
Module      :  $Header$
Description :  Sublogics for CommonLogic
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

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
    , fullclsl                      -- FullCommonLogic
    , folsl                         -- FirstOrderLogic
    , propsl                        -- Propositional
    , sublogics_all                 -- all sublogics
    , sublogics_name                -- name of sublogics
    , sl_sig                        -- sublogic for a signature
    , sl_sym                        -- sublogic for symbols
    , sl_mor                        -- sublogic for morphisms
    , sl_symmap                     -- sublogic for symbol map items
    , sl_symitems                   -- sublogic for symbol items
    , sublogic_text                 -- sublogic for a text
    , sublogic_name                 -- sublogic for a text
    , prSymbolM
    , prSig
    , prMor
    , prSymMapM
    , prSymItemsM
    , prName
    , prBasicSpec
    , isProp
    , isFOL
    , isCL
    )
    where

import CommonLogic.Tools
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

-- | all sublogics
sublogics_all :: [CommonLogicSL]
sublogics_all = [fullclsl, folsl, bottom]

------------------------------------------------------------------------------
-- Special elements in the Lattice of logics                                --
------------------------------------------------------------------------------

top :: CommonLogicSL
top = fullclsl

bottom :: CommonLogicSL
bottom = propsl

fullclsl :: CommonLogicSL
fullclsl = CommonLogicSL {format = FullCommonLogic}

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

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element, these work    --
-- by recursing into all subelements                                        --
------------------------------------------------------------------------------

-- | determines the sublogic for a complete text
sublogic_text :: CommonLogicSL -> AS.TEXT -> CommonLogicSL
sublogic_text cs t = sl_text (prd_text t) cs t


-- | determines the sublogic for symbol map items
sl_symmap ::  CommonLogicSL -> AS.SYMB_MAP_ITEMS
    -> CommonLogicSL
sl_symmap cs _ = cs

-- | determines the sublogic for a morphism
sl_mor :: CommonLogicSL -> Morphism.Morphism -> CommonLogicSL
sl_mor cs _ = cs

-- | determines the sublogic for a Signature
sl_sig :: CommonLogicSL -> Sign.Sign -> CommonLogicSL
sl_sig cs _ = cs

-- | determines the sublogic for symbols
sl_sym :: CommonLogicSL -> Symbol.Symbol -> CommonLogicSL
sl_sym cs _ = cs

-- | determines sublogic for texts, given predicates of the super-text
sl_text :: Set.Set AS.NAME -> CommonLogicSL -> AS.TEXT -> CommonLogicSL
sl_text prds cs t = 
    case t of
        AS.Text ps _ -> sl_phrases prds cs ps
        AS.Named_text _ nt _ -> sl_text prds cs nt

-- | determines sublogic for phrases, given predicates of the super-text
sl_phrases :: Set.Set AS.NAME -> CommonLogicSL -> [AS.PHRASE] -> CommonLogicSL
sl_phrases prds cs ps = foldl sublogics_max cs $ map (sl_phrase prds cs) ps

-- | determines sublogic for a single phrase, given predicates of the super-text
sl_phrase :: Set.Set AS.NAME -> CommonLogicSL -> AS.PHRASE -> CommonLogicSL
sl_phrase prds cs p = 
    case p of
        AS.Module m -> sl_module prds cs m
        AS.Sentence s -> sl_sentence prds cs s
        AS.Importation i -> sl_importation prds cs i
        AS.Comment_text _ t _ -> sl_text prds cs t 

-- | determines sublogic for a module, given predicates of the super-text
sl_module :: Set.Set AS.NAME -> CommonLogicSL -> AS.MODULE -> CommonLogicSL
sl_module prds cs m = 
    case m of
        AS.Mod _ t _ -> sl_text prds cs t
        AS.Mod_ex _ _ t _ -> sl_text prds cs t

-- | determines sublogic for a sentence, given predicates of the super-text
sl_sentence :: Set.Set AS.NAME -> CommonLogicSL -> AS.SENTENCE -> CommonLogicSL
sl_sentence prds cs sen = 
    case sen of
        AS.Quant_sent q _ -> sl_quantSent prds cs q
        AS.Bool_sent b _ -> sl_boolSent prds cs b
        AS.Atom_sent a _ -> sl_atomSent prds cs a
        AS.Comment_sent _ s _ -> sl_sentence prds cs s
        AS.Irregular_sent s _ -> sl_sentence prds cs s

-- | determines the sublogic for importations (importations are ignored)
sl_importation :: Set.Set AS.NAME -> CommonLogicSL -> AS.IMPORTATION
    -> CommonLogicSL
sl_importation _ cs _ = cs

-- | determines the sublogic for quantified sentences,
-- given predicates of the super-text
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

-- | determines the sublogic for boolean sentences,
-- given predicates of the super-text
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

-- | determines the sublogic for atoms,
-- given predicates of the super-text
sl_atomSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.ATOM -> CommonLogicSL
sl_atomSent prds cs a = 
    case a of
        AS.Equation t1 t2 -> 
            comp_list $ folsl : map (sl_term prds cs) [t1,t2]
        AS.Atom t [] -> sl_term prds cs t 
        AS.Atom t tseq -> comp_list 
            $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq

-- | determines the sublogic for NAME_OR_SEQMARK,
-- given predicates of the super-text
sl_nameOrSeqmark :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME_OR_SEQMARK 
    -> CommonLogicSL
sl_nameOrSeqmark prds cs nos = 
    case nos of
        AS.Name n -> sl_quantName prds cs n
        AS.SeqMark _ -> fullclsl

-- | determines the sublogic for names which are next to a quantifier,
-- given predicates of the super-text
sl_quantName :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_quantName prds _ n = if Set.member n prds then fullclsl else folsl

-- | determines the sublogic for names,
-- given predicates of the super-text
sl_name :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_name _ = sublogic_name

-- | determines the sublogic for names,
-- ignoring predicates
sublogic_name :: CommonLogicSL -> AS.NAME -> CommonLogicSL
sublogic_name _ _ = propsl

-- | determines the sublogic for terms,
-- given predicates of the super-text
sl_term :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_term prds cs term = 
    case term of
      AS.Name_term n -> sl_name prds cs n
      AS.Funct_term t tseq _ -> 
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t

-- | determines the sublogic for term sequences,
-- given predicates of the super-text
sl_termSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM_SEQ -> CommonLogicSL
sl_termSeq prds cs tseq = 
    case tseq of
        AS.Term_seq t -> sl_termInSeq prds cs t
        AS.Seq_marks _ -> cs -- correct?

-- | determines the sublogic for names,
-- given predicates of the super-text
sl_nameInTermSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_nameInTermSeq prds _ n = if Set.member n prds then fullclsl else propsl

-- | determines the sublogic for terms inside of a term-sequence,
-- given predicates of the super-text
sl_termInSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_termInSeq prds cs term = 
    case term of
      AS.Name_term n -> sl_nameInTermSeq prds cs n
      AS.Funct_term t tseq _ -> 
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t



-- | determines sublogic for basic items
sl_basic_items :: CommonLogicSL -> AS.BASIC_ITEMS -> CommonLogicSL
sl_basic_items cs (AS.Axiom_items (AS_Anno.Annoted (AS.Text_mrs (t,_)) _ _ _)) =
  (uncurry $ flip sl_text cs) $ getPreds  t
  where getPreds :: AS.TEXT -> (Set.Set AS.NAME, AS.TEXT)
        getPreds txt = (prd_text txt, txt)

-- | determines sublogic for basic spec
sl_basic_spec :: CommonLogicSL -> AS.BASIC_SPEC -> CommonLogicSL
sl_basic_spec cs (AS.Basic_spec spec) =
  comp_list $ map ((sl_basic_items cs) . AS_Anno.item) spec

sl_symitems :: CommonLogicSL -> AS.SYMB_ITEMS -> CommonLogicSL
sl_symitems _ (AS.Symb_items noss _) =
  comp_list $ map (sl_nameOrSeqmark Set.empty bottom) noss

-------------------------------------------------------------------------------
-- Conversion functions to String                                            --
-------------------------------------------------------------------------------

sublogics_name :: CommonLogicSL -> String
sublogics_name f = case format f of
                     Propositional   -> "Propositional"
                     FirstOrder      -> "FOL"
                     FullCommonLogic -> "FullCommonLogic"

-------------------------------------------------------------------------------
-- Projections to sublogics                                                  --
-------------------------------------------------------------------------------
-- TODO: Projections

prSymbolM :: CommonLogicSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ sym = Just sym

prSymItemsM :: CommonLogicSL -> AS.SYMB_ITEMS -> Maybe AS.SYMB_ITEMS
prSymItemsM cs si@(AS.Symb_items noss r) = case format cs of
  FullCommonLogic -> Just si
  _ -> Just $ AS.Symb_items (filter isName noss) r
  where isName nos = case nos of
          AS.Name _ -> True
          _ -> False

prSig :: CommonLogicSL -> Sign.Sign -> Sign.Sign
prSig _ sig = sig

prMor :: CommonLogicSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

prSymMapM :: CommonLogicSL
          -> AS.SYMB_MAP_ITEMS
          -> Maybe AS.SYMB_MAP_ITEMS
prSymMapM _ sMap = Just sMap

prName :: CommonLogicSL -> AS.NAME -> Maybe AS.NAME
prName _ n = Just n

-- | filters all TEXTs inside the BASIC_SPEC of which the sublogic is less than
-- or equal to @cs@
prBasicSpec :: CommonLogicSL -> AS.BASIC_SPEC -> AS.BASIC_SPEC
prBasicSpec cs (AS.Basic_spec items) = -- TODO: write some decent function
  AS.Basic_spec $ filter ((isSL_LE cs) . AS_Anno.item) items

isSL_LE :: CommonLogicSL -> AS.BASIC_ITEMS -> Bool
isSL_LE cs (AS.Axiom_items (AS_Anno.Annoted (AS.Text_mrs (t,_)) _ _ _)) =
  compareLE (sublogic_text bottom t) cs
