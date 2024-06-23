{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{- |
Module      :  ./Propositional/Sublogic.hs
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
    , isNNF
    , isCNF
    , isDNF
    , isHC
    , analyzeFormula
    )
    where

import Data.Data
import Data.Set
import qualified Data.List as DL

import qualified Propositional.Tools as Tools
import qualified Propositional.AS_BASIC_Propositional as AS_BASIC

import qualified Propositional.Sign as Sign
import qualified Propositional.Symbol as Symbol
import qualified Propositional.Morphism as Morphism

import qualified Common.Lib.State as State
import qualified Common.AS_Annotation as AS_Anno

{- -----------------------------------------------------------------------------
datatypes                                                                 --
----------------------------------------------------------------------------- -}

-- | types of propositional formulae
data PropFormulae = NegationNormalForm      -- Formula in Negation Normal Form
                  | DisjunctiveNormalForm   -- Formula in Disjunctive Normal Form
                  | ConjunctiveNormalForm   -- Formula in Conjunctive Normal Form
                  | HornClause              -- Horn Clause Formulae
                  deriving (Show, Eq, Ord, Typeable, Data)

-- | sublogics for propositional logic
data PropSL = PropSL
    {
      format :: Set PropFormulae     -- Structural restrictions
      {-
       - Each restriction should be an element of the set.
       - Obviously `PlainFormula` can be part of every format because
       - it does not add any requirements. By convention, the set should
       - contain all restrictions that are applicable. E.g., instead of
       - {CNF} it should only be {CNF, NNF}. A Formula without any restrictions
       - is represented as an empty set, i.e., {}.
       -}
    } deriving (Show, Eq, Ord, Typeable, Data)

isProp :: PropSL -> Bool
isProp sl = True

isNNF :: PropSL -> Bool
isNNF sl = NegationNormalForm `elem` format sl

isDNF :: PropSL -> Bool
isDNF sl = DisjunctiveNormalForm `elem` format sl

isCNF :: PropSL -> Bool
isCNF sl = ConjunctiveNormalForm `elem` format sl

isHC :: PropSL -> Bool
isHC sl = HornClause `elem` format sl


-- | comparison of sublogics
compareLE :: PropSL -> PropSL -> Bool
compareLE p1 p2 =
  let f1 = format p1
      f2 = format p2
  in
    f2 `isSubsetOf` f1

{- ----------------------------------------------------------------------------
Special elements in the Lattice of logics                                --
---------------------------------------------------------------------------- -}

top :: PropSL
top = PropSL empty

bottom :: PropSL
bottom = PropSL $ fromList [HornClause, ConjunctiveNormalForm, DisjunctiveNormalForm, NegationNormalForm]

need_PF :: PropSL
need_PF = bottom { format = empty }

{- -----------------------------------------------------------------------------
join and max                                                              --
----------------------------------------------------------------------------- -}

sublogics_join :: PropSL -> PropSL -> PropSL
sublogics_join a b = PropSL
                         {
                           format = intersection (format a) (format b)
                         }

sublogics_max :: PropSL -> PropSL -> PropSL
sublogics_max = sublogics_join

{- -----------------------------------------------------------------------------
Helpers                                                                   --
----------------------------------------------------------------------------- -}

-- compute sublogics from a list of sublogics
--
comp_list :: [PropSL] -> PropSL
comp_list = Prelude.foldl sublogics_max bottom

{- ----------------------------------------------------------------------------
Functions to compute minimal sublogic for a given element, these work    --
by recursing into all subelements                                        --
---------------------------------------------------------------------------- -}

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
sl_symit :: PropSL -> AS_BASIC.SYMB_ITEMS -> PropSL
sl_symit ps _ = ps

-- | determines the sublogic for symbols
sl_sym :: PropSL -> Symbol.Symbol -> PropSL
sl_sym ps _ = ps

-- | determines sublogic for formula
sl_form :: PropSL -> AS_BASIC.FORMULA -> PropSL
sl_form ps f = sl_fl_form ps $ Tools.flatten f

-- | determines sublogic for flattened formula
sl_fl_form :: PropSL -> [AS_BASIC.FORMULA] -> PropSL
sl_fl_form ps f = Prelude.foldl sublogics_max ps
  $ Prelude.map (\ x -> State.evalState (ana_form ps x) 0) f

-- analysis of single "clauses"
ana_form :: PropSL -> AS_BASIC.FORMULA -> State.State Int PropSL
ana_form ps f =
    case f of
      AS_BASIC.Conjunction l _ ->
          do
            st <- State.get
            return $ sublogics_max need_PF $ comp_list $ Prelude.map
              (\ x -> State.evalState (ana_form ps x) (st + 1)) l
      AS_BASIC.Implication l m _ ->
          do
             st <- State.get
             let analyze = sublogics_max need_PF $ sublogics_max
                   ((\ x -> State.evalState (ana_form ps x) (st + 1)) l)
                   ((\ x -> State.evalState (ana_form ps x) (st + 1)) m)
             return $
                    if st < 1 && HornClause `elem` format ps && checkHornPos l m
                    then ps else analyze
      AS_BASIC.Equivalence l m _ ->
           do
             st <- State.get
             return $ sublogics_max need_PF $ sublogics_max
               ((\ x -> State.evalState (ana_form ps x) (st + 1)) l)
               ((\ x -> State.evalState (ana_form ps x) (st + 1)) m)
      AS_BASIC.Negation l _ ->
          if isLiteral l
          then return ps
          else
              do
                st <- State.get
                return $ (\ x -> State.evalState (ana_form ps x) (st + 1)) l
      AS_BASIC.Disjunction l _ ->
                    let lprime = concatMap Tools.flattenDis l in
                    if all isLiteral lprime
                    then return $
                          if moreThanNLit lprime 1
                          then sublogics_max need_PF ps else ps
                    else
                        do
                          st <- State.get
                          return $ sublogics_max need_PF $ comp_list $ Prelude.map
                            (\ x -> State.evalState (ana_form ps x) (st + 1))
                                      lprime
      AS_BASIC.True_atom _ -> return ps
      AS_BASIC.False_atom _ -> return ps
      AS_BASIC.Predication _ -> return ps

moreThanNLit :: [AS_BASIC.FORMULA] -> Int -> Bool
moreThanNLit form n = Prelude.foldl (\ y x -> if x then y + 1 else y) 0
  (Prelude.map isPosLiteral form) > n

-- determines wheter a Formula is a literal
isLiteral :: AS_BASIC.FORMULA -> Bool
isLiteral (AS_BASIC.Predication _) = True
isLiteral (AS_BASIC.Negation (AS_BASIC.Predication _) _ ) = True
isLiteral (AS_BASIC.Negation _ _) = False
isLiteral (AS_BASIC.Conjunction _ _) = False
isLiteral (AS_BASIC.Implication {}) = False
isLiteral (AS_BASIC.Equivalence {}) = False
isLiteral (AS_BASIC.Disjunction _ _) = False
isLiteral (AS_BASIC.True_atom _ ) = True
isLiteral (AS_BASIC.False_atom _) = True

-- determines wheter a Formula is a positive literal
isPosLiteral :: AS_BASIC.FORMULA -> Bool
isPosLiteral (AS_BASIC.Predication _) = True
isPosLiteral (AS_BASIC.Negation _ _) = False
isPosLiteral (AS_BASIC.Conjunction _ _) = False
isPosLiteral (AS_BASIC.Implication {}) = False
isPosLiteral (AS_BASIC.Equivalence {}) = False
isPosLiteral (AS_BASIC.Disjunction _ _) = False
isPosLiteral (AS_BASIC.True_atom _ ) = True
isPosLiteral (AS_BASIC.False_atom _) = True

-- | determines subloig for basic items
sl_basic_items :: PropSL -> AS_BASIC.BASIC_ITEMS -> PropSL
sl_basic_items ps bi =
    case bi of
      AS_BASIC.Pred_decl _ -> ps
      AS_BASIC.Axiom_items xs -> comp_list $ Prelude.map (sl_form ps . AS_Anno.item) xs

-- | determines sublogic for basic spec
sl_basic_spec :: PropSL -> AS_BASIC.BASIC_SPEC -> PropSL
sl_basic_spec ps (AS_BASIC.Basic_spec spec) =
    comp_list $ Prelude.map (sl_basic_items ps . AS_Anno.item) spec

-- | all sublogics
sublogics_all :: [PropSL]
sublogics_all =
  Prelude.map (\x -> PropSL{ format = x }) $
    Prelude.filter isIllegalConfig $
    toList $ powerSet $ fromList [NegationNormalForm, DisjunctiveNormalForm, ConjunctiveNormalForm, HornClause]
      where
        isIllegalConfig :: Set PropFormulae -> Bool
        isIllegalConfig restr | HornClause `elem` restr && ConjunctiveNormalForm `notElem` restr = False
                              | ConjunctiveNormalForm `elem` restr && NegationNormalForm `notElem` restr = False
                              | DisjunctiveNormalForm `elem` restr && NegationNormalForm `notElem` restr = False
                              | otherwise = True

{- -----------------------------------------------------------------------------
Conversion functions to String                                            --
----------------------------------------------------------------------------- -}

sublogics_name :: PropSL -> String
sublogics_name f = if Prelude.null listOfSLs then "PlainFormula" else DL.intercalate "_" listOfSLs
  where
    listOfSLs = Prelude.map (\case
                                HornClause -> "HornClause"
                                ConjunctiveNormalForm -> "CNF"
                                DisjunctiveNormalForm -> "DNF"
                                NegationNormalForm -> "NNF") $ toList $ format f

{- -----------------------------------------------------------------------------
Projections to sublogics                                                  --
----------------------------------------------------------------------------- -}

prSymbolM :: PropSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ = Just

prSig :: PropSL -> Sign.Sign -> Sign.Sign
prSig _ sig = sig

prMor :: PropSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

prSymMapM :: PropSL
          -> AS_BASIC.SYMB_MAP_ITEMS
          -> Maybe AS_BASIC.SYMB_MAP_ITEMS
prSymMapM _ = Just

prSymM :: PropSL -> AS_BASIC.SYMB_ITEMS -> Maybe AS_BASIC.SYMB_ITEMS
prSymM _ = Just

-- keep an element if its computed sublogic is in the given sublogic
--

prFormulaM :: PropSL -> AS_BASIC.FORMULA -> Maybe AS_BASIC.FORMULA
prFormulaM sl form
           | compareLE (sl_form bottom form) sl = Just form
           | otherwise = Nothing

prPredItem :: PropSL -> AS_BASIC.PRED_ITEM -> AS_BASIC.PRED_ITEM
prPredItem _ prI = prI

prBASIC_items :: PropSL -> AS_BASIC.BASIC_ITEMS -> AS_BASIC.BASIC_ITEMS
prBASIC_items pSL bI =
    case bI of
      AS_BASIC.Pred_decl pI -> AS_BASIC.Pred_decl $ prPredItem pSL pI
      AS_BASIC.Axiom_items aIS -> AS_BASIC.Axiom_items $ concatMap mapH aIS
    where
      mapH :: AS_Anno.Annoted AS_BASIC.FORMULA
           -> [AS_Anno.Annoted AS_BASIC.FORMULA]
      mapH annoForm = let formP = prFormulaM pSL $ AS_Anno.item annoForm in
                      case formP of
                        Nothing -> []
                        Just f -> [ AS_Anno.Annoted
                                   {
                                     AS_Anno.item = f
                                   , AS_Anno.opt_pos = AS_Anno.opt_pos annoForm
                                   , AS_Anno.l_annos = AS_Anno.l_annos annoForm
                                   , AS_Anno.r_annos = AS_Anno.r_annos annoForm
                                   }
                                   ]

prBasicSpec :: PropSL -> AS_BASIC.BASIC_SPEC -> AS_BASIC.BASIC_SPEC
prBasicSpec pSL (AS_BASIC.Basic_spec bS) =
    AS_BASIC.Basic_spec $ Prelude.map mapH bS
    where
      mapH :: AS_Anno.Annoted AS_BASIC.BASIC_ITEMS
           -> AS_Anno.Annoted AS_BASIC.BASIC_ITEMS
      mapH aBI = AS_Anno.Annoted
                 {
                   AS_Anno.item = prBASIC_items pSL $ AS_Anno.item aBI
                 , AS_Anno.opt_pos = AS_Anno.opt_pos aBI
                 , AS_Anno.l_annos = AS_Anno.l_annos aBI
                 , AS_Anno.r_annos = AS_Anno.r_annos aBI
                 }


-- check if a formula is in a certain sublogic

analyzeFormula :: AS_BASIC.FORMULA -> PropSL
analyzeFormula formula = PropSL {
  format = fromList
    $ Prelude.map (\case
          checkNNF -> NegationNormalForm
          checkDNF -> DisjunctiveNormalForm
          checkCNF -> ConjunctiveNormalForm
          checkHorn -> HornClause)
      $ Prelude.filter (`apply` formula) [checkNNF, checkCNF, checkDNF, checkHorn]
}
  where
    apply f x = f x

checkNNF :: AS_BASIC.FORMULA -> Bool
checkNNF formula =
  case formula of
      AS_BASIC.Conjunction conjs _ -> all (\case
                                        AS_BASIC.Disjunction form _ -> all checkNNF form
                                        AS_BASIC.Conjunction form _ -> all checkNNF form
                                        conj -> isLiteral conj) conjs
      AS_BASIC.Disjunction disjs _ -> all (\case
                                        AS_BASIC.Disjunction form _ -> all checkNNF form
                                        AS_BASIC.Conjunction form _ -> all checkNNF form
                                        disj -> isLiteral disj) disjs
      form -> isLiteral form

checkDNF :: AS_BASIC.FORMULA -> Bool
checkDNF formula =
  case formula of
      AS_BASIC.Disjunction disjs _ -> all (\case
                                        AS_BASIC.Conjunction form _ -> all isLiteral form
                                        disj -> isLiteral disj) disjs
      form -> isLiteral form

checkCNF :: AS_BASIC.FORMULA -> Bool
checkCNF formula =
  case formula of
      AS_BASIC.Conjunction conjs _ -> all (\case
                                        AS_BASIC.Disjunction form _ -> all isLiteral form
                                        conj -> isLiteral conj) conjs
      form -> isLiteral form

checkHorn :: AS_BASIC.FORMULA -> Bool
checkHorn formula =
  case formula of
    AS_BASIC.Conjunction conjs _ -> all (\case
                                      AS_BASIC.Disjunction disjs _ -> length (Prelude.filter isPosLiteral disjs) <= 1
                                      AS_BASIC.Implication lhs rhs _ -> checkCNF lhs && isLiteral rhs
                                      conj -> isLiteral conj) conjs
    form -> isLiteral form

checkHornPos :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA -> Bool
checkHornPos fc fl =
    case fc of
      AS_BASIC.Conjunction _ _ -> all isPosLiteral $ Tools.flatten fc
      _ -> False
    &&
    isPosLiteral fl
