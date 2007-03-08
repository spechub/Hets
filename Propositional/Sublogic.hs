{-# OPTIONS -fallow-undecidable-instances #-}
{- |
Module      :  $Header$
Description :  Instance of class Logic for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luecke@tzi.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Sublogics for Propositional Logic
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhäuser.
  2005.
-}

module Propositional.Sublogic
    (
     sl_basic_spec                  -- determine sublogic for basic spec
    , PropFormulae (..)             -- types of propositional formulae
    , PropSL (..)                   -- sublogics for propositional logic
    , sublogics_max                 -- join of sublogics
    , top                           -- Propositional
    , bottom                        -- CNF
    , sublogics_all                 -- all sublogics
    , sublogics_name                -- name of sublogics
    , sl_sig                        -- sublogic for a signature
    , sl_form                       -- sublogic for a formula
    , sl_sym                        -- sublogic for symbols
    , sl_symit                      -- sublogic for symbol items
    , sl_mor                        -- sublogic for morphisms
    , sl_symmap                     -- sublogic for symbol map items
    )
    where

import qualified Propositional.Tools as Tools
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Common.AS_Annotation as AS_Anno
import qualified Propositional.Sign as Sign
import qualified Propositional.Symbol as Symbol
import qualified Propositional.Morphism as Morphism

class (Eq l, Show l) => Lattice l where
  cjoin :: l -> l -> l
  ctop :: l
  bot :: l

instance Lattice () where
  cjoin _ _ = ()
  ctop = ()
  bot = ()

instance Lattice Bool where
  cjoin = (||)
  ctop = True
  bot = False

-------------------------------------------------------------------------------
-- datatyper                                                                 --
-------------------------------------------------------------------------------

-- | types of propositional formulae
data PropFormulae = PlainFormula      -- Formula without structural constraints
                  | CNF               -- CNF (implies restriction on ops)
                  deriving (Show, Eq, Ord)

-- | sublogics for propositional logic
data PropSL = PropSL
    {
      format       :: PropFormulae     -- Structural restrictions
    , has_imp      :: Bool             -- Implication ?
    , has_equiv    :: Bool             -- Equivalence ?
    } deriving (Show, Eq)

------------------------------------------------------------------------------
-- Special elements in the Lattice of logics                                --
------------------------------------------------------------------------------

top :: PropSL
top = PropSL PlainFormula True True

bottom :: PropSL
bottom = PropSL CNF False False 

need_PF :: PropSL
need_PF = bottom { format = PlainFormula }

need_imp :: PropSL
need_imp = bottom { has_imp = True }

need_equiv :: PropSL
need_equiv = bottom { has_equiv = True }

-------------------------------------------------------------------------------
-- join and max                                                              --
-------------------------------------------------------------------------------

sublogics_join :: (PropFormulae -> PropFormulae -> PropFormulae)
                  -> (Bool -> Bool -> Bool)
                  -> (Bool -> Bool -> Bool)
                  -> PropSL -> PropSL -> PropSL
sublogics_join pfF imF eqF a b = PropSL
                                 {
                                   format    = pfF (format a) (format b)
                                 , has_imp   = imF (has_imp a) (has_imp b)
                                 , has_equiv = eqF (has_equiv a) (has_equiv b) 
                                 }

joinType :: PropFormulae -> PropFormulae -> PropFormulae
joinType CNF CNF = CNF
joinType _   _   = PlainFormula

sublogics_max :: PropSL -> PropSL -> PropSL
sublogics_max = sublogics_join joinType max max 

-------------------------------------------------------------------------------
-- Helpers                                                                   --
-------------------------------------------------------------------------------

-- compute sublogics from a list of sublogics
--
comp_list :: [PropSL] -> PropSL
comp_list l = foldl sublogics_max bottom l

------------------------------------------------------------------------------
-- Functions to compute minimal sublogic for a given element, these work    --
-- by recursing into all subelements                                        --
------------------------------------------------------------------------------

-- | determines the sublogic for symbol map items
sl_symmap :: PropSL -> AS_BASIC.SYMB_MAP_ITEMS -> PropSL
sl_symmap ps _ = ps

-- | determines the sublogic for a morphism
sl_mor :: PropSL -> Morphism.Morphism -> PropSL
sl_mor ps _ = ps

-- | determines the sublogic for a Signature
sl_sig :: PropSL -> Sign.Sign -> PropSL
sl_sig ps _ = ps

-- | determines the sublogic for Symbol items
sl_symit :: PropSL -> AS_BASIC.SYMB_ITEMS  -> PropSL
sl_symit ps _ = ps

-- | determines the sublogic for symbols
sl_sym :: PropSL -> Symbol.Symbol -> PropSL
sl_sym ps _ = ps

-- | determines sublogic for formula
sl_form :: PropSL -> AS_BASIC.FORMULA -> PropSL
sl_form ps f = sl_fl_form ps $ Tools.flatten f

-- | determines sublogic for flattened formula
sl_fl_form :: PropSL -> [AS_BASIC.FORMULA] -> PropSL
sl_fl_form ps f = foldl (sublogics_max) ps $ map (ana_form ps) f 

-- analysis of single "clauses"
ana_form :: PropSL -> AS_BASIC.FORMULA -> PropSL
ana_form ps f = 
    case f of
      AS_BASIC.Conjunction l _ -> sublogics_max need_PF
                                  (comp_list $ map (ana_form ps) l) 
      AS_BASIC.Implication l m _ -> sublogics_max need_imp $ 
                                    sublogics_max need_PF $
                                    sublogics_max (ana_form ps l)
                                                     (ana_form ps m)
      AS_BASIC.Equivalence l m _ -> sublogics_max need_equiv $ 
                                    sublogics_max need_PF $
                                    sublogics_max (ana_form ps l)
                                                     (ana_form ps m)
      AS_BASIC.Negation l _      -> if (isLiteral l)
                                    then
                                        ps
                                    else
                                        sublogics_max need_PF $ ana_form ps l
      AS_BASIC.Disjunction l _   -> if (foldl (&&) True $ map isLiteral l)
                                     then
                                         ps
                                     else
                                         sublogics_max need_PF
                                         (comp_list $ map (ana_form ps) l)     
      AS_BASIC.True_atom  _      -> ps
      AS_BASIC.False_atom _      -> ps
      AS_BASIC.Predication _     -> ps

-- determines wheter a Formula is a literal
isLiteral :: AS_BASIC.FORMULA -> Bool
isLiteral (AS_BASIC.Predication _)       = True
isLiteral (AS_BASIC.Negation (AS_BASIC.Predication _) _) = True
isLiteral (AS_BASIC.Negation _ _) = False
isLiteral (AS_BASIC.Conjunction _ _) = False
isLiteral (AS_BASIC.Implication _ _ _) = False
isLiteral (AS_BASIC.Equivalence _ _ _) = False
isLiteral (AS_BASIC.Disjunction _ _) = False
isLiteral (AS_BASIC.True_atom  _ ) = True
isLiteral (AS_BASIC.False_atom _) = True

-- | determines subloig for basic items
sl_basic_items :: PropSL -> AS_BASIC.BASIC_ITEMS -> PropSL
sl_basic_items ps bi =
    case bi of 
      AS_BASIC.Pred_decl _    -> ps
      AS_BASIC.Axiom_items xs -> comp_list $ map (sl_form ps) $ 
                                 map AS_Anno.item xs

-- | determines sublogic for basic spec
sl_basic_spec :: PropSL -> AS_BASIC.BASIC_SPEC -> PropSL
sl_basic_spec ps (AS_BASIC.Basic_spec spec) = 
    comp_list $ map (sl_basic_items ps) $ 
              map AS_Anno.item spec

-- | all sublogics
sublogics_all :: [PropSL]
sublogics_all = let bools = [True, False] in
    [PropSL
     {
       format    = CNF
     , has_imp   = False
     , has_equiv = False 
     }
    ] ++ [ PropSL 
           {
             format = PlainFormula
           , has_imp = imps
           , has_equiv = equivs
           }
           | imps <- bools
           , equivs <- bools
         ]

-------------------------------------------------------------------------------
-- Conversion functions to String                                            --
-------------------------------------------------------------------------------

sublogics_name :: PropSL -> [String]
sublogics_name f =
    case formType of
      CNF -> ["CNF"]
      PlainFormula -> ["Prop" ++ 
                      (
                       if (imp) then "I" else ""
                      ) ++
                     (
                      if (equ) then "E" else ""
                     )]
    where formType = format f
          imp      = has_imp f
          equ      = has_equiv f
