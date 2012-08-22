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
      sl_basic_spec       -- determine sublogic for basic spec
    , CLTextType (..)     -- types of CommonLogic texts
    , CommonLogicSL (..)  -- sublogics for CommonLogic
    , sublogics_max       -- join of sublogics
    , top                 -- FullCommonLogic
    , bottom              -- Propositional
    , propsl              -- Propositional
    , folsl               -- FirstOrderLogic
    , compactsl           -- Beyond FOL, but without seqMarks
    , funcNoPredsl        -- Beyond Compact, but no function returns a predicate
    , fullclsl            -- FullCommonLogic
    , sublogics_all       -- all sublogics
    , sublogics_name      -- name of sublogics
    , sl_sig              -- sublogic for a signature
    , sl_sym              -- sublogic for symbols
    , sl_mor              -- sublogic for morphisms
    , sl_symmap           -- sublogic for symbol map items
    , sl_symitems         -- sublogic for symbol items
    , sublogic_text       -- sublogic for a text
    , sublogic_name       -- sublogic for a text
    , prSymbolM
    , prSig
    , prMor
    , prSymMapM
    , prSymItemsM
    , prName
    , prBasicSpec
    )
    where

import CommonLogic.Tools
import qualified Data.Set as Set
import qualified CommonLogic.AS_CommonLogic as AS
import qualified Common.AS_Annotation as AS_Anno
import qualified CommonLogic.Sign as Sign
import qualified CommonLogic.Symbol as Symbol
import qualified CommonLogic.Morphism as Morphism

{- -----------------------------------------------------------------------------
datatypes                                                                 --
----------------------------------------------------------------------------- -}

-- | types of sublogics
data CLTextType =
    Propositional      -- ^ Text without quantifiers
  | FirstOrder         -- ^ Text in First Order Logic
  | Compact            -- ^ Text beyond FOL, but without SeqMarks
  | FuncNoPred         -- ^ beyond Compact, but no function returns a predicate
  | FullCommonLogic    -- ^ Text without any constraints
  deriving (Show, Eq, Ord, Enum, Bounded)

-- for comparison of sublogics use the Ord instance

-- | sublogics for CommonLogic
data CommonLogicSL = CommonLogicSL
    { format :: CLTextType     -- Structural restrictions
    } deriving (Show, Eq, Ord, Bounded)

-- | all sublogics
sublogics_all :: [CommonLogicSL]
sublogics_all = map CommonLogicSL [minBound .. maxBound]

{- ----------------------------------------------------------------------------
Special elements in the Lattice of logics                                --
---------------------------------------------------------------------------- -}

-- | Greates sublogc: FullCommonLogic
top :: CommonLogicSL
top = maxBound

-- | Smallest sublogic: Propositional
bottom :: CommonLogicSL
bottom = minBound

fullclsl :: CommonLogicSL
fullclsl = CommonLogicSL {format = FullCommonLogic}

-- | FuncNoPred as Sublogic
funcNoPredsl :: CommonLogicSL
funcNoPredsl = CommonLogicSL {format = FuncNoPred}

-- | Compact as Sublogic
compactsl :: CommonLogicSL
compactsl = CommonLogicSL {format = Compact}

-- | FirstOrder as Sublogic
folsl :: CommonLogicSL
folsl = CommonLogicSL {format = FirstOrder}

-- | Propositional as Sublogic
propsl :: CommonLogicSL
propsl = CommonLogicSL {format = Propositional}

{- -----------------------------------------------------------------------------
join and max                                                              --
----------------------------------------------------------------------------- -}

-- | Yields the greater sublogic
sublogics_max :: CommonLogicSL -> CommonLogicSL -> CommonLogicSL
sublogics_max = max

{- -----------------------------------------------------------------------------
Helpers                                                                   --
----------------------------------------------------------------------------- -}

-- compute sublogics from a list of sublogics
comp_list :: [CommonLogicSL] -> CommonLogicSL
comp_list = foldl sublogics_max bottom

{- ----------------------------------------------------------------------------
Functions to compute minimal sublogic for a given element, these work    --
by recursing into all subelements                                        --
---------------------------------------------------------------------------- -}

-- | determines the sublogic for a complete text
sublogic_text :: CommonLogicSL -> AS.TEXT -> CommonLogicSL
sublogic_text cs t = sl_text (prd_text t) cs t


-- | determines the sublogic for symbol map items
sl_symmap :: CommonLogicSL -> AS.SYMB_MAP_ITEMS
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
        AS.Quant_sent q vs is _ -> sl_quantSent prds cs q vs is
        AS.Bool_sent b _ -> sl_boolSent prds cs b
        AS.Atom_sent a _ -> sl_atomSent prds cs a
        AS.Comment_sent _ s _ -> sl_sentence prds cs s
        AS.Irregular_sent s _ -> sl_sentence prds cs s

-- | determines the sublogic for importations (importations are ignored)
sl_importation :: Set.Set AS.NAME -> CommonLogicSL -> AS.IMPORTATION
    -> CommonLogicSL
sl_importation _ cs _ = cs

{- | determines the sublogic for quantified sentences,
given predicates of the super-text -}
sl_quantSent :: Set.Set AS.NAME -> CommonLogicSL
                -> AS.QUANT -> [AS.NAME_OR_SEQMARK] -> AS.SENTENCE
                -> CommonLogicSL
sl_quantSent prds cs _ noss s =
  comp_list $ folsl : sl_sentence prds cs s
  : map (sl_nameOrSeqmark prds cs) noss

{- | determines the sublogic for boolean sentences,
given predicates of the super-text -}
sl_boolSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.BOOL_SENT -> CommonLogicSL
sl_boolSent prds cs b =
    case b of
      AS.Junction _ ss -> comp_list $ map (sl_sentence prds cs) ss
      AS.Negation s -> sl_sentence prds cs s
      AS.BinOp _ s1 s2 ->
        sublogics_max (sl_sentence prds cs s1) (sl_sentence prds cs s2)

{- | determines the sublogic for atoms,
given predicates of the super-text -}
sl_atomSent :: Set.Set AS.NAME -> CommonLogicSL -> AS.ATOM -> CommonLogicSL
sl_atomSent prds cs a =
    case a of
        AS.Equation t1 t2 ->
            comp_list $ folsl : map (sl_term prds cs) [t1, t2]
        AS.Atom t [] -> sl_term prds cs t
        AS.Atom t tseq ->
            let base = case t of
                  AS.Funct_term {} -> fullclsl
                  _ -> folsl
            in comp_list $ base
                            : sl_term prds cs t : map (sl_termSeq prds cs) tseq

{- | determines the sublogic for NAME_OR_SEQMARK,
given predicates of the super-text -}
sl_nameOrSeqmark :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME_OR_SEQMARK
    -> CommonLogicSL
sl_nameOrSeqmark prds cs nos =
    case nos of
        AS.Name n -> sl_quantName prds cs n
        AS.SeqMark _ -> funcNoPredsl

{- | determines the sublogic for names which are next to a quantifier,
given predicates of the super-text -}
sl_quantName :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_quantName prds _ n = if Set.member n prds then compactsl else folsl

{- | determines the sublogic for names,
given predicates of the super-text -}
sl_name :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_name _ = sublogic_name

{- | determines the sublogic for names,
ignoring predicates -}
sublogic_name :: CommonLogicSL -> AS.NAME -> CommonLogicSL
sublogic_name _ _ = propsl

{- | determines the sublogic for terms,
given predicates of the super-text -}
sl_term :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_term prds cs term =
    case term of
      AS.Name_term n -> sl_name prds cs n
      AS.Funct_term t tseq _ ->
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t
      AS.That_term {} -> fullclsl

{- | determines the sublogic for term sequences,
given predicates of the super-text -}
sl_termSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM_SEQ -> CommonLogicSL
sl_termSeq prds cs tseq =
    case tseq of
        AS.Term_seq t -> sl_termInSeq prds cs t
        AS.Seq_marks _ -> funcNoPredsl

{- | determines the sublogic for names,
given predicates of the super-text -}
sl_nameInTermSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.NAME -> CommonLogicSL
sl_nameInTermSeq prds _ n = if Set.member n prds then compactsl else propsl

{- | determines the sublogic for terms inside of a term-sequence,
given predicates of the super-text -}
sl_termInSeq :: Set.Set AS.NAME -> CommonLogicSL -> AS.TERM -> CommonLogicSL
sl_termInSeq prds cs term =
    case term of
      AS.Name_term n -> sl_nameInTermSeq prds cs n
      AS.Funct_term t tseq _ ->
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      AS.Comment_term t _ _ -> sl_term prds cs t
      AS.That_term {} -> fullclsl

-- | determines sublogic for basic items
sl_basic_items :: CommonLogicSL -> AS.BASIC_ITEMS -> CommonLogicSL
sl_basic_items cs (AS.Axiom_items axs) = comp_list $ map
  (\ AS_Anno.Annoted {AS_Anno.item = tm} ->
    uncurry (`sl_text` cs) $ getPreds $ AS.getText tm
  ) axs
  where getPreds :: AS.TEXT -> (Set.Set AS.NAME, AS.TEXT)
        getPreds txt = (prd_text txt, txt)

-- | determines sublogic for basic spec
sl_basic_spec :: CommonLogicSL -> AS.BASIC_SPEC -> CommonLogicSL
sl_basic_spec cs (AS.Basic_spec spec) =
  comp_list $ map (sl_basic_items cs . AS_Anno.item) spec

-- | determines sublogc for symb items
sl_symitems :: CommonLogicSL -> AS.SYMB_ITEMS -> CommonLogicSL
sl_symitems _ (AS.Symb_items noss _) =
  comp_list $ map (sl_nameOrSeqmark Set.empty bottom) noss

{- -----------------------------------------------------------------------------
Conversion functions to String                                            --
----------------------------------------------------------------------------- -}

-- | String representation of a Sublogic
sublogics_name :: CommonLogicSL -> String
sublogics_name f = case format f of
                     Propositional -> "Propositional"
                     FirstOrder -> "FOL"
                     Compact -> "Compact"
                     FuncNoPred -> "FunctionsNotReturningPredicate"
                     FullCommonLogic -> "FullCommonLogic"

{- -----------------------------------------------------------------------------
Projections to sublogics                                                  --
----------------------------------------------------------------------------- -}

-- | projection of a symbol to a sublogic
prSymbolM :: CommonLogicSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ = Just

prSymItemsM :: CommonLogicSL -> AS.SYMB_ITEMS -> Maybe AS.SYMB_ITEMS
prSymItemsM cs si@(AS.Symb_items noss r) = case format cs of
  FullCommonLogic -> Just si
  _ -> Just $ AS.Symb_items (filter isName noss) r
  where isName nos = case nos of
          AS.Name _ -> True
          _ -> False

-- | projection of a signature to a sublogic
prSig :: CommonLogicSL -> Sign.Sign -> Sign.Sign
prSig _ = id

-- | projection of a morphism to a sublogic
prMor :: CommonLogicSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

-- | projection of symb map items to a sublogic
prSymMapM :: CommonLogicSL
          -> AS.SYMB_MAP_ITEMS
          -> Maybe AS.SYMB_MAP_ITEMS
prSymMapM _ = Just

-- | projection of a name to a sublogic
prName :: CommonLogicSL -> AS.NAME -> Maybe AS.NAME
prName _ = Just

{- | filters all TEXTs inside the BASIC_SPEC of which the sublogic is less than
or equal to @cs@ -}
prBasicSpec :: CommonLogicSL -> AS.BASIC_SPEC -> AS.BASIC_SPEC
prBasicSpec cs (AS.Basic_spec items) = AS.Basic_spec $ map (maybeLE cs) items

maybeLE :: CommonLogicSL ->
            AS_Anno.Annoted AS.BASIC_ITEMS -> AS_Anno.Annoted AS.BASIC_ITEMS
maybeLE cs = fmap
  $ \ (AS.Axiom_items i) -> AS.Axiom_items $ filter (isSL_LE cs) i

isSL_LE :: CommonLogicSL -> AS_Anno.Annoted AS.TEXT_META -> Bool
isSL_LE cs at =
  sublogic_text bottom (AS.getText $ AS_Anno.item at) <= cs
