{-# LANGUAGE DeriveDataTypeable, DeriveGeneric #-}
{- |
Module      :  ./CommonLogic/Sublogic.hs
Description :  Sublogics for CommonLogic
Copyright   :  (c) Eugen Kuksa, Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (via Logic.Logic)

Sublogics for CommonLogic
-}

module CommonLogic.Sublogic
    ( sl_basic_spec       -- determine sublogic for basic spec
    , CLTextType (..)     -- types of CommonLogic texts
    , CommonLogicSL (..)  -- sublogics for CommonLogic
    , sublogics_max       -- join of sublogics
    , top                 -- FullCommonLogic
    , bottom              -- Propositional
    , propsl              -- Propositional
    , folsl               -- FirstOrderLogic
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

import Data.Data
import Data.Function
import qualified Data.HashSet as Set

import CommonLogic.AS_CommonLogic
import Common.AS_Annotation (Annoted (..))
import CommonLogic.Sign
import CommonLogic.Symbol
import CommonLogic.Morphism
import GHC.Generics (Generic)
import Data.Hashable

{- -----------------------------------------------------------------------------
datatypes                                                                 --
----------------------------------------------------------------------------- -}

-- | types of sublogics
data CLTextType =
    Propositional      -- ^ Text without quantifiers
  | FirstOrder         -- ^ Text in First Order Logic
  | Impredicative
  deriving (Show, Eq, Ord, Enum, Bounded, Typeable, Generic)

instance Hashable CLTextType

-- for comparison of sublogics use the Ord instance

-- | sublogics for CommonLogic
data CommonLogicSL = CommonLogicSL
    { format :: CLTextType     -- Structural restrictions
    , compact :: Bool
    } deriving (Show, Eq, Ord, Typeable, Generic)

instance Hashable CommonLogicSL

-- | all sublogics
sublogics_all :: [CommonLogicSL]
sublogics_all =
   [ CommonLogicSL t c
   | t <- [minBound .. maxBound]
   , c <- [True, False]
   ]

{- ----------------------------------------------------------------------------
Special elements in the Lattice of logics                                --
---------------------------------------------------------------------------- -}

-- | Greates sublogc: FullCommonLogic
top :: CommonLogicSL
top = CommonLogicSL maxBound False

-- | Smallest sublogic: Propositional
bottom :: CommonLogicSL
bottom = CommonLogicSL minBound True

fullclsl :: CommonLogicSL
fullclsl = top

-- | Compact as Sublogic
impsl :: CommonLogicSL
impsl = top { compact = True }

-- | FirstOrder as Sublogic
folsl :: CommonLogicSL
folsl = bottom {format = FirstOrder}

-- | Propositional as Sublogic
propsl :: CommonLogicSL
propsl = bottom {format = Propositional}

{- -----------------------------------------------------------------------------
join and max                                                              --
----------------------------------------------------------------------------- -}

-- | Yields the greater sublogic
sublogics_max :: CommonLogicSL -> CommonLogicSL -> CommonLogicSL
sublogics_max s1 s2 = CommonLogicSL (on max format s1 s2) (on min compact s1 s2)

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
sublogic_text :: CommonLogicSL -> TEXT -> CommonLogicSL
sublogic_text cs t = sl_text (prd_text t) cs t


-- | determines the sublogic for symbol map items
sl_symmap :: CommonLogicSL -> SYMB_MAP_ITEMS
    -> CommonLogicSL
sl_symmap cs _ = cs

-- | determines the sublogic for a morphism
sl_mor :: CommonLogicSL -> Morphism -> CommonLogicSL
sl_mor cs _ = cs

-- | determines the sublogic for a Signature
sl_sig :: CommonLogicSL -> Sign -> CommonLogicSL
sl_sig cs _ = cs

-- | determines the sublogic for symbols
sl_sym :: CommonLogicSL -> Symbol -> CommonLogicSL
sl_sym cs _ = cs

-- | determines sublogic for texts, given predicates of the super-text
sl_text :: Set.HashSet NAME -> CommonLogicSL -> TEXT -> CommonLogicSL
sl_text prds cs t =
    case t of
        Text ps _ -> sl_phrases prds cs ps
        Named_text _ nt _ -> sl_text prds cs nt

-- | determines sublogic for phrases, given predicates of the super-text
sl_phrases :: Set.HashSet NAME -> CommonLogicSL -> [PHRASE] -> CommonLogicSL
sl_phrases prds cs ps = foldl sublogics_max cs $ map (sl_phrase prds cs) ps

-- | determines sublogic for a single phrase, given predicates of the super-text
sl_phrase :: Set.HashSet NAME -> CommonLogicSL -> PHRASE -> CommonLogicSL
sl_phrase prds cs p =
    case p of
        Module m -> sl_module prds cs m
        Sentence s -> sl_sentence prds cs s
        Importation i -> sl_importation prds cs i
        Comment_text _ t _ -> sl_text prds cs t

-- | determines sublogic for a module, given predicates of the super-text
sl_module :: Set.HashSet NAME -> CommonLogicSL -> MODULE -> CommonLogicSL
sl_module prds cs m =
    case m of
        Mod _ t _ -> sl_text prds cs t
        Mod_ex _ _ t _ -> sl_text prds cs t

-- | determines sublogic for a sentence, given predicates of the super-text
sl_sentence :: Set.HashSet NAME -> CommonLogicSL -> SENTENCE -> CommonLogicSL
sl_sentence prds cs sen =
    case sen of
        Quant_sent q vs is _ -> sl_quantSent prds cs q vs is
        Bool_sent b _ -> sl_boolSent prds cs b
        Atom_sent a _ -> sl_atomSent prds cs a
        Comment_sent _ s _ -> sl_sentence prds cs s
        Irregular_sent s _ -> sl_sentence prds cs s

-- | determines the sublogic for importations (importations are ignored)
sl_importation :: Set.HashSet NAME -> CommonLogicSL -> IMPORTATION
    -> CommonLogicSL
sl_importation _ cs _ = cs

{- | determines the sublogic for quantified sentences,
given predicates of the super-text -}
sl_quantSent :: Set.HashSet NAME -> CommonLogicSL
                -> QUANT -> [NAME_OR_SEQMARK] -> SENTENCE
                -> CommonLogicSL
sl_quantSent prds cs _ noss s =
  comp_list $ folsl : sl_sentence prds cs s
  : map (sl_nameOrSeqmark prds cs) noss

{- | determines the sublogic for boolean sentences,
given predicates of the super-text -}
sl_boolSent :: Set.HashSet NAME -> CommonLogicSL -> BOOL_SENT -> CommonLogicSL
sl_boolSent prds cs b =
    case b of
      Junction _ ss -> comp_list $ map (sl_sentence prds cs) ss
      Negation s -> sl_sentence prds cs s
      BinOp _ s1 s2 ->
        sublogics_max (sl_sentence prds cs s1) (sl_sentence prds cs s2)

{- | determines the sublogic for atoms,
given predicates of the super-text -}
sl_atomSent :: Set.HashSet NAME -> CommonLogicSL -> ATOM -> CommonLogicSL
sl_atomSent prds cs a =
    case a of
        Equation t1 t2 ->
            comp_list $ folsl : map (sl_term prds cs) [t1, t2]
        Atom t [] -> sl_term prds cs t
        Atom t tseq -> slAppl prds cs t tseq

slAppl :: Set.HashSet NAME -> CommonLogicSL -> TERM -> [TERM_SEQ] -> CommonLogicSL
slAppl prds cs t tseq = comp_list
  $ (if isNameTerm t then folsl else impsl)
  : sl_term prds cs t : map (sl_termSeq prds cs) tseq

-- check for a curried name application
isNameTerm :: TERM -> Bool
isNameTerm term = case term of
  Name_term _ -> True
  Comment_term t _ _ -> isNameTerm t
  Funct_term t _ _ -> isNameTerm t
  That_term {} -> False

{- | determines the sublogic for NAME_OR_SEQMARK,
given predicates of the super-text -}
sl_nameOrSeqmark :: Set.HashSet NAME -> CommonLogicSL -> NAME_OR_SEQMARK
    -> CommonLogicSL
sl_nameOrSeqmark prds cs nos =
    case nos of
        Name n -> sl_quantName prds cs n
        SeqMark _ -> cs { compact = False }

{- | determines the sublogic for names which are next to a quantifier,
given predicates of the super-text -}
sl_quantName :: Set.HashSet NAME -> CommonLogicSL -> NAME -> CommonLogicSL
sl_quantName prds _ n = if Set.member n prds then impsl else folsl

{- | determines the sublogic for names,
given predicates of the super-text -}
sl_name :: Set.HashSet NAME -> CommonLogicSL -> NAME -> CommonLogicSL
sl_name _ = sublogic_name

{- | determines the sublogic for names,
ignoring predicates -}
sublogic_name :: CommonLogicSL -> NAME -> CommonLogicSL
sublogic_name _ _ = propsl

{- | determines the sublogic for terms,
given predicates of the super-text -}
sl_term :: Set.HashSet NAME -> CommonLogicSL -> TERM -> CommonLogicSL
sl_term prds cs term =
    case term of
      Name_term n -> sl_name prds cs n
      Funct_term t tseq _ -> slAppl prds cs t tseq
      Comment_term t _ _ -> sl_term prds cs t
      That_term {} -> impsl

{- | determines the sublogic for term sequences,
given predicates of the super-text -}
sl_termSeq :: Set.HashSet NAME -> CommonLogicSL -> TERM_SEQ -> CommonLogicSL
sl_termSeq prds cs tseq =
    case tseq of
        Term_seq t -> sl_termInSeq prds cs t
        Seq_marks _ -> cs { compact = False }

{- | determines the sublogic for names,
given predicates of the super-text -}
sl_nameInTermSeq :: Set.HashSet NAME -> CommonLogicSL -> NAME -> CommonLogicSL
sl_nameInTermSeq prds _ n = if Set.member n prds then impsl else propsl

{- | determines the sublogic for terms inside of a term-sequence,
given predicates of the super-text -}
sl_termInSeq :: Set.HashSet NAME -> CommonLogicSL -> TERM -> CommonLogicSL
sl_termInSeq prds cs term =
    case term of
      Name_term n -> sl_nameInTermSeq prds cs n
      Funct_term t tseq _ ->
          comp_list $ folsl : sl_term prds cs t : map (sl_termSeq prds cs) tseq
      Comment_term t _ _ -> sl_term prds cs t
      That_term {} -> impsl

-- | determines sublogic for basic items
sl_basic_items :: CommonLogicSL -> BASIC_ITEMS -> CommonLogicSL
sl_basic_items cs (Axiom_items axs) = comp_list $ map
  (\ Annoted {item = tm} ->
    uncurry (`sl_text` cs) $ getPreds $ getText tm
  ) axs
  where getPreds :: TEXT -> (Set.HashSet NAME, TEXT)
        getPreds txt = (prd_text txt, txt)

-- | determines sublogic for basic spec
sl_basic_spec :: CommonLogicSL -> BASIC_SPEC -> CommonLogicSL
sl_basic_spec cs (Basic_spec spec) =
  comp_list $ map (sl_basic_items cs . item) spec

-- | determines sublogc for symb items
sl_symitems :: CommonLogicSL -> SYMB_ITEMS -> CommonLogicSL
sl_symitems _ (Symb_items noss _) =
  comp_list $ map (sl_nameOrSeqmark Set.empty bottom) noss

{- -----------------------------------------------------------------------------
Conversion functions to String                                            --
----------------------------------------------------------------------------- -}

-- | String representation of a Sublogic
sublogics_name :: CommonLogicSL -> String
sublogics_name f = show (format f) ++ if compact f then "" else "Seq"

{- -----------------------------------------------------------------------------
Projections to sublogics                                                  --
----------------------------------------------------------------------------- -}

-- | projection of a symbol to a sublogic
prSymbolM :: CommonLogicSL -> Symbol -> Maybe Symbol
prSymbolM _ = Just

prSymItemsM :: CommonLogicSL -> SYMB_ITEMS -> Maybe SYMB_ITEMS
prSymItemsM cs si@(Symb_items noss r) = case format cs of
  Impredicative -> Just si
  _ -> Just $ Symb_items (filter isName noss) r
  where isName nos = case nos of
          Name _ -> True
          _ -> False

-- | projection of a signature to a sublogic
prSig :: CommonLogicSL -> Sign -> Sign
prSig _ = id

-- | projection of a morphism to a sublogic
prMor :: CommonLogicSL -> Morphism -> Morphism
prMor _ mor = mor

-- | projection of symb map items to a sublogic
prSymMapM :: CommonLogicSL
          -> SYMB_MAP_ITEMS
          -> Maybe SYMB_MAP_ITEMS
prSymMapM _ = Just

-- | projection of a name to a sublogic
prName :: CommonLogicSL -> NAME -> Maybe NAME
prName _ = Just

{- | filters all TEXTs inside the BASIC_SPEC of which the sublogic is less than
or equal to @cs@ -}
prBasicSpec :: CommonLogicSL -> BASIC_SPEC -> BASIC_SPEC
prBasicSpec cs (Basic_spec items) = Basic_spec $ map (maybeLE cs) items

maybeLE :: CommonLogicSL -> Annoted BASIC_ITEMS -> Annoted BASIC_ITEMS
maybeLE cs = fmap $ \ (Axiom_items i) -> Axiom_items $ filter (isSL_LE cs) i

isSL_LE :: CommonLogicSL -> Annoted TEXT_META -> Bool
isSL_LE cs at = sublogic_text bottom (getText $ item at) <= cs
