{- |
Module      :  $Header$
Description :  Sublogics for propositional logic
Copyright   :  (c) Dominik Luecke, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  experimental
Portability :  non-portable (imports Logic.Logic)

Sublogics for Propositional Logic
-}

{-
  Ref.

  http://en.wikipedia.org/wiki/Propositional_logic

  Till Mossakowski, Joseph Goguen, Razvan Diaconescu, Andrzej Tarlecki.
  What is a Logic?.
  In Jean-Yves Beziau (Ed.), Logica Universalis, pp. 113-@133. Birkhaeuser.
  2005.
-}

module Propositional.Sublogic
    (
     sl_basic_spec                  -- determine sublogic for basic spec
    , PropFormulae (..)             -- types of propositional formulae
    , PropSL (..)                   -- sublogics for propositional logic
    , sublogics_max                 -- join of sublogics
    , top                           -- Propositional
    , bottom                        -- Horn
    , sublogics_all                 -- all sublogics
    , sublogics_name                -- name of sublogics
    , sl_sig                        -- sublogic for a signature
    , sl_form                       -- sublogic for a formula
    , sl_sym                        -- sublogic for symbols
    , sl_symit                      -- sublogic for symbol items
    , sl_mor                        -- sublogic for morphisms
    , sl_symmap                     -- sublogic for symbol map items
    , prSymbolM                     -- projection of symbols
    , prSig                         -- projections of signatures
    , prMor                         -- projections of morphisms
    , prSymMapM                     -- projections of symbol maps
    , prSymM                        -- projections of SYMB_ITEMS
    , prFormulaM                    -- projections of formulae
    , prBasicSpec                   -- projections of basic specs
    , isProp
    , isHC
    )
    where

import qualified Propositional.Tools as Tools
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC
import qualified Common.AS_Annotation as AS_Anno
import qualified Propositional.Sign as Sign
import qualified Propositional.Symbol as Symbol
import qualified Propositional.Morphism as Morphism
import qualified Common.Lib.State as State

-------------------------------------------------------------------------------
-- datatyper                                                                 --
-------------------------------------------------------------------------------

-- | types of propositional formulae
data PropFormulae = PlainFormula      -- Formula without structural constraints
                  | HornClause        -- Horn Clause Formulae
                  deriving (Show, Eq, Ord)

-- | sublogics for propositional logic
data PropSL = PropSL
    {
      format       :: PropFormulae     -- Structural restrictions
    } deriving (Show, Eq, Ord)

isProp :: PropSL -> Bool
isProp sl = format sl == PlainFormula

isHC :: PropSL -> Bool
isHC sl = format sl == HornClause

-- | comparison of sublogics
compareLE :: PropSL -> PropSL -> Bool
compareLE p1 p2 =
    let f1 = format p1
        f2 = format p2
    in
      case (f1, f2) of
        (_,            PlainFormula) -> True
        (HornClause,   HornClause)   -> True
        (_,            HornClause)   -> False

------------------------------------------------------------------------------
-- Special elements in the Lattice of logics                                --
------------------------------------------------------------------------------

top :: PropSL
top = PropSL PlainFormula

bottom :: PropSL
bottom = PropSL HornClause

need_PF :: PropSL
need_PF = bottom { format = PlainFormula }

-------------------------------------------------------------------------------
-- join and max                                                              --
-------------------------------------------------------------------------------

sublogics_join :: (PropFormulae -> PropFormulae -> PropFormulae)
                  -> PropSL -> PropSL -> PropSL
sublogics_join pfF a b = PropSL
                         {
                           format    = pfF (format a) (format b)
                         }

joinType :: PropFormulae -> PropFormulae -> PropFormulae
joinType HornClause HornClause = HornClause
joinType _   _   = PlainFormula

sublogics_max :: PropSL -> PropSL -> PropSL
sublogics_max = sublogics_join joinType

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
sl_fl_form ps f = foldl (sublogics_max) ps
  $ map (\x -> State.evalState (ana_form ps x) 0) f

-- analysis of single "clauses"
ana_form :: PropSL -> AS_BASIC.FORMULA -> State.State Int PropSL
ana_form ps f =
    case f of
      AS_BASIC.Conjunction l _   ->
          do
            st <- State.get
            return $ sublogics_max need_PF $ comp_list $ map
              (\x -> (State.evalState (ana_form ps x) (st + 1))) l
      AS_BASIC.Implication l m _ ->
          do
             st <- State.get
             let analyze = sublogics_max need_PF $ sublogics_max
                   ((\x -> State.evalState (ana_form ps x) (st+1)) l)
                   ((\x -> State.evalState (ana_form ps x) (st+1)) m)
             return $
                    if st < 1
                    then
                        if (format ps == HornClause)
                        then
                            if (checkHornPos l m)
                            then
                                ps
                            else
                                analyze
                        else
                            analyze
                    else
                        analyze
      AS_BASIC.Equivalence l m _ ->
           do
             st <- State.get
             return $ sublogics_max need_PF $ sublogics_max
               ((\x -> State.evalState (ana_form ps x) (st+1)) l)
               ((\x -> State.evalState (ana_form ps x) (st+1)) m)
      AS_BASIC.Negation l _      ->
          if (isLiteral l)
          then
              do
                return ps
          else
              do
                st <- State.get
                return $ (\x -> State.evalState (ana_form ps x) (st+1)) l
      AS_BASIC.Disjunction l _   ->
                    let lprime = concat $ map Tools.flattenDis l in
                    if all isLiteral lprime
                    then
                        do
                          if moreThanNLit lprime 1
                             then
                                 return $ sublogics_max need_PF ps
                             else
                                 return ps
                    else
                        do
                          st <- State.get
                          return $ sublogics_max need_PF $ comp_list $ map
                            (\x -> State.evalState (ana_form ps x) (st+1))
                                      lprime
      AS_BASIC.True_atom  _      -> do return ps
      AS_BASIC.False_atom _      -> do return ps
      AS_BASIC.Predication _     -> do return ps

moreThanNLit :: [AS_BASIC.FORMULA] -> Int -> Bool
moreThanNLit form n = foldl (\y x -> if (x == True) then y + 1 else y) 0
  (map isPosLiteral form) > n

-- determines wheter a Formula is a literal
isLiteral :: AS_BASIC.FORMULA -> Bool
isLiteral (AS_BASIC.Predication _)       = True
isLiteral (AS_BASIC.Negation (AS_BASIC.Predication _) _ ) = True
isLiteral (AS_BASIC.Negation _ _) = False
isLiteral (AS_BASIC.Conjunction _ _) = False
isLiteral (AS_BASIC.Implication _ _ _) = False
isLiteral (AS_BASIC.Equivalence _ _ _) = False
isLiteral (AS_BASIC.Disjunction _ _) = False
isLiteral (AS_BASIC.True_atom  _ ) = True
isLiteral (AS_BASIC.False_atom _) = True

-- determines wheter a Formula is a positive literal
isPosLiteral :: AS_BASIC.FORMULA -> Bool
isPosLiteral (AS_BASIC.Predication _)       = True
isPosLiteral (AS_BASIC.Negation _ _) = False
isPosLiteral (AS_BASIC.Conjunction _ _) = False
isPosLiteral (AS_BASIC.Implication _ _ _) = False
isPosLiteral (AS_BASIC.Equivalence _ _ _) = False
isPosLiteral (AS_BASIC.Disjunction _ _) = False
isPosLiteral (AS_BASIC.True_atom  _ ) = True
isPosLiteral (AS_BASIC.False_atom _) = True

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
sublogics_all =
    [PropSL
     {
       format    = HornClause
     }
    ,PropSL
     {
       format    = PlainFormula
     }
    ]

-------------------------------------------------------------------------------
-- Conversion functions to String                                            --
-------------------------------------------------------------------------------

sublogics_name :: PropSL -> String
sublogics_name f = case format f of
      HornClause -> "HornClause"
      PlainFormula -> "Prop"

-------------------------------------------------------------------------------
-- Projections to sublogics                                                  --
-------------------------------------------------------------------------------

prSymbolM :: PropSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ sym = Just sym

prSig :: PropSL -> Sign.Sign -> Sign.Sign
prSig _ sig = sig

prMor :: PropSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

prSymMapM :: PropSL
          -> AS_BASIC.SYMB_MAP_ITEMS
          -> Maybe AS_BASIC.SYMB_MAP_ITEMS
prSymMapM _ sMap = Just sMap

prSymM :: PropSL -> AS_BASIC.SYMB_ITEMS -> Maybe AS_BASIC.SYMB_ITEMS
prSymM _ sym = Just sym

-- keep an element if its computed sublogic is in the given sublogic
--

prFormulaM :: PropSL -> AS_BASIC.FORMULA -> Maybe AS_BASIC.FORMULA
prFormulaM sl form
           | compareLE (sl_form bottom form) sl = Just form
           | otherwise                          = Nothing

prPredItem :: PropSL -> AS_BASIC.PRED_ITEM -> AS_BASIC.PRED_ITEM
prPredItem _ prI = prI

prBASIC_items :: PropSL -> AS_BASIC.BASIC_ITEMS -> AS_BASIC.BASIC_ITEMS
prBASIC_items pSL bI =
    case bI of
      AS_BASIC.Pred_decl pI -> AS_BASIC.Pred_decl $ prPredItem pSL pI
      AS_BASIC.Axiom_items aIS -> AS_BASIC.Axiom_items $ concat $ map mapH aIS
    where
      mapH :: AS_Anno.Annoted (AS_BASIC.FORMULA)
           -> [(AS_Anno.Annoted (AS_BASIC.FORMULA))]
      mapH annoForm = let formP = prFormulaM pSL $ AS_Anno.item annoForm in
                      case formP of
                        Nothing -> []
                        Just f  -> [ AS_Anno.Annoted
                                   {
                                     AS_Anno.item = f
                                   , AS_Anno.opt_pos = AS_Anno.opt_pos annoForm
                                   , AS_Anno.l_annos = AS_Anno.l_annos annoForm
                                   , AS_Anno.r_annos = AS_Anno.r_annos annoForm
                                   }
                                   ]

prBasicSpec :: PropSL -> AS_BASIC.BASIC_SPEC -> AS_BASIC.BASIC_SPEC
prBasicSpec pSL (AS_BASIC.Basic_spec bS) =
    AS_BASIC.Basic_spec $ map mapH bS
    where
      mapH :: AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)
           -> AS_Anno.Annoted (AS_BASIC.BASIC_ITEMS)
      mapH aBI = AS_Anno.Annoted
                 {
                   AS_Anno.item = prBASIC_items pSL $ AS_Anno.item aBI
                 , AS_Anno.opt_pos = AS_Anno.opt_pos aBI
                 , AS_Anno.l_annos = AS_Anno.l_annos aBI
                 , AS_Anno.r_annos = AS_Anno.r_annos aBI
                 }

checkHornPos :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA -> Bool
checkHornPos fc fl =
    case fc of
      AS_BASIC.Conjunction _ _ -> all isPosLiteral $ Tools.flatten fc
      _                        -> False
    &&
    isPosLiteral fl
