{- |
Module      :  $Header$
Description :  Sublogics for propositional logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  <jonathan.von_schroeder@dfki.de>
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

module QBF.Sublogic
    (
     slBasicSpec                  -- determine sublogic for basic spec
    , PropFormulae (..)             -- types of propositional formulae
    , PropSL (..)                   -- sublogics for propositional logic
    , sublogicsMax                 -- join of sublogics
    , top                           -- Propositional
    , bottom                        -- Horn
    , sublogicsAll                 -- all sublogics
    , sublogicsName                -- name of sublogics
    , slSig                        -- sublogic for a signature
    , slForm                       -- sublogic for a formula
    , slSym                        -- sublogic for symbols
    , slSymit                      -- sublogic for symbol items
    , slMor                        -- sublogic for morphisms
    , slSymmap                     -- sublogic for symbol map items
    , prSymbolM                     -- projection of symbols
    , prSig                         -- projections of signatures
    , prMor                         -- projections of morphisms
    , prSymMapM                     -- projections of symbol maps
    , prSymM                        -- projections of SYMBITEMS
    , prFormulaM                    -- projections of formulae
    , prBasicSpec                   -- projections of basic specs
    , isProp
    , isHC
    )
    where

import qualified QBF.Tools as Tools
import qualified QBF.AS_BASIC_QBF as AS_BASIC
import qualified Common.AS_Annotation as AS_Anno
import qualified Propositional.Sign as Sign
import qualified QBF.Symbol as Symbol
import qualified QBF.Morphism as Morphism
import qualified Common.Lib.State as State

-- | types of propositional formulae
data PropFormulae = PlainFormula      -- Formula without structural constraints
                  | HornClause        -- Horn Clause Formulae
                  deriving (Show, Eq, Ord)

-- | sublogics for propositional logic
data PropSL = PropSL
    {
      format :: PropFormulae     -- Structural restrictions
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
        (_, PlainFormula) -> True
        (HornClause, HornClause) -> True
        (_, HornClause) -> False

-- Special elements in the Lattice of logics

top :: PropSL
top = PropSL PlainFormula

bottom :: PropSL
bottom = PropSL HornClause

needPF :: PropSL
needPF = bottom { format = PlainFormula }

-- join and max

sublogicsJoin :: (PropFormulae -> PropFormulae -> PropFormulae)
                  -> PropSL -> PropSL -> PropSL
sublogicsJoin pfF a b = PropSL
                         {
                           format = pfF (format a) (format b)
                         }

joinType :: PropFormulae -> PropFormulae -> PropFormulae
joinType HornClause HornClause = HornClause
joinType _ _ = PlainFormula

sublogicsMax :: PropSL -> PropSL -> PropSL
sublogicsMax = sublogicsJoin joinType

-- Helpers

-- compute sublogics from a list of sublogics

compList :: [PropSL] -> PropSL
compList = foldl sublogicsMax bottom

-- Functions to compute minimal sublogic for a given element, these work
-- by recursing into all subelements

-- | determines the sublogic for symbol map items
slSymmap :: PropSL -> AS_BASIC.SYMBMAPITEMS -> PropSL
slSymmap ps _ = ps

-- | determines the sublogic for a morphism
slMor :: PropSL -> Morphism.Morphism -> PropSL
slMor ps _ = ps

-- | determines the sublogic for a Signature
slSig :: PropSL -> Sign.Sign -> PropSL
slSig ps _ = ps

-- | determines the sublogic for Symbol items
slSymit :: PropSL -> AS_BASIC.SYMBITEMS -> PropSL
slSymit ps _ = ps

-- | determines the sublogic for symbols
slSym :: PropSL -> Symbol.Symbol -> PropSL
slSym ps _ = ps

-- | determines sublogic for formula
slForm :: PropSL -> AS_BASIC.FORMULA -> PropSL
slForm ps f = slFlForm ps $ Tools.flatten f

-- | determines sublogic for flattened formula
slFlForm :: PropSL -> [AS_BASIC.FORMULA] -> PropSL
slFlForm ps f = foldl sublogicsMax ps
  $ map (\ x -> State.evalState (anaForm ps x) 0) f

-- analysis of single "clauses"
anaForm :: PropSL -> AS_BASIC.FORMULA -> State.State Int PropSL
anaForm ps f =
    case f of
      AS_BASIC.Conjunction l _ ->
          do
            st <- State.get
            return $ sublogicsMax needPF $ compList $ map
              (\ x -> (State.evalState (anaForm ps x) (st + 1))) l
      AS_BASIC.Implication l m _ ->
          do
             st <- State.get
             let analyze = sublogicsMax needPF $ sublogicsMax
                   ((\ x -> State.evalState (anaForm ps x) (st + 1)) l)
                   ((\ x -> State.evalState (anaForm ps x) (st + 1)) m)
             return $
                    if st < 1 && format ps == HornClause && checkHornPos l m
                    then
                        ps
                    else
                        analyze
      AS_BASIC.Equivalence l m _ ->
           do
             st <- State.get
             return $ sublogicsMax needPF $ sublogicsMax
               ((\ x -> State.evalState (anaForm ps x) (st + 1)) l)
               ((\ x -> State.evalState (anaForm ps x) (st + 1)) m)
      AS_BASIC.Negation l _ ->
          if isLiteral l
          then
                return ps
          else
              do
                st <- State.get
                return $ (\ x -> State.evalState (anaForm ps x) (st + 1)) l
      AS_BASIC.Disjunction l _ ->
                    let lprime = concatMap Tools.flattenDis l in
                    if all isLiteral lprime
                    then
                        if moreThanNLit lprime 1
                          then
                              return $ sublogicsMax needPF ps
                          else
                              return ps
                    else
                        do
                          st <- State.get
                          return $ sublogicsMax needPF $ compList $ map
                            (\ x -> State.evalState (anaForm ps x) (st + 1))
                                      lprime
      AS_BASIC.TrueAtom _ -> return ps
      AS_BASIC.FalseAtom _ -> return ps
      AS_BASIC.Predication _ -> return ps
      AS_BASIC.ForAll _ _ _ -> return needPF
      AS_BASIC.Exists _ _ _ -> return needPF

moreThanNLit :: [AS_BASIC.FORMULA] -> Int -> Bool
moreThanNLit form n = foldl (\ y x -> if x then y + 1 else y) 0
  (map isPosLiteral form) > n

-- determines wheter a Formula is a literal
isLiteral :: AS_BASIC.FORMULA -> Bool
isLiteral (AS_BASIC.Predication _) = True
isLiteral (AS_BASIC.Negation (AS_BASIC.Predication _) _ ) = True
isLiteral (AS_BASIC.Negation _ _) = False
isLiteral (AS_BASIC.Conjunction _ _) = False
isLiteral (AS_BASIC.Implication _ _ _) = False
isLiteral (AS_BASIC.Equivalence _ _ _) = False
isLiteral (AS_BASIC.Disjunction _ _) = False
isLiteral (AS_BASIC.ForAll _ _ _) = False
isLiteral (AS_BASIC.Exists _ _ _) = False
isLiteral (AS_BASIC.TrueAtom _) = True
isLiteral (AS_BASIC.FalseAtom _) = True

-- determines wheter a Formula is a positive literal
isPosLiteral :: AS_BASIC.FORMULA -> Bool
isPosLiteral (AS_BASIC.Predication _) = True
isPosLiteral (AS_BASIC.Negation _ _) = False
isPosLiteral (AS_BASIC.Conjunction _ _) = False
isPosLiteral (AS_BASIC.Implication _ _ _) = False
isPosLiteral (AS_BASIC.Equivalence _ _ _) = False
isPosLiteral (AS_BASIC.Disjunction _ _) = False
isPosLiteral (AS_BASIC.ForAll _ _ _) = False
isPosLiteral (AS_BASIC.Exists _ _ _) = False
isPosLiteral (AS_BASIC.TrueAtom _ ) = True
isPosLiteral (AS_BASIC.FalseAtom _) = True

-- | determines subloig for basic items
slBasicItems :: PropSL -> AS_BASIC.BASICITEMS -> PropSL
slBasicItems ps bi =
    case bi of
      AS_BASIC.PredDecl _ -> ps
      AS_BASIC.AxiomItems xs -> compList $ map (slForm ps . AS_Anno.item) xs

-- | determines sublogic for basic spec
slBasicSpec :: PropSL -> AS_BASIC.BASICSPEC -> PropSL
slBasicSpec ps (AS_BASIC.BasicSpec spec) =
    compList $ map (slBasicItems ps . AS_Anno.item) spec

-- | all sublogics
sublogicsAll :: [PropSL]
sublogicsAll =
    [PropSL
     {
       format = HornClause
     }
    , PropSL
     {
       format = PlainFormula
     }
    ]

-- Conversion functions to String

sublogicsName :: PropSL -> String
sublogicsName f = case format f of
      HornClause -> "HornClause"
      PlainFormula -> "Prop"

-- Projections to sublogics

prSymbolM :: PropSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ = Just

prSig :: PropSL -> Sign.Sign -> Sign.Sign
prSig _ sig = sig

prMor :: PropSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

prSymMapM :: PropSL
          -> AS_BASIC.SYMBMAPITEMS
          -> Maybe AS_BASIC.SYMBMAPITEMS
prSymMapM _ = Just

prSymM :: PropSL -> AS_BASIC.SYMBITEMS -> Maybe AS_BASIC.SYMBITEMS
prSymM _ = Just

-- keep an element if its computed sublogic is in the given sublogic
--

prFormulaM :: PropSL -> AS_BASIC.FORMULA -> Maybe AS_BASIC.FORMULA
prFormulaM sl form
           | compareLE (slForm bottom form) sl = Just form
           | otherwise = Nothing

prPredItem :: PropSL -> AS_BASIC.PREDITEM -> AS_BASIC.PREDITEM
prPredItem _ prI = prI

prBASICItems :: PropSL -> AS_BASIC.BASICITEMS -> AS_BASIC.BASICITEMS
prBASICItems pSL bI =
    case bI of
      AS_BASIC.PredDecl pI -> AS_BASIC.PredDecl $ prPredItem pSL pI
      AS_BASIC.AxiomItems aIS -> AS_BASIC.AxiomItems $ concatMap mapH aIS
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

prBasicSpec :: PropSL -> AS_BASIC.BASICSPEC -> AS_BASIC.BASICSPEC
prBasicSpec pSL (AS_BASIC.BasicSpec bS) =
    AS_BASIC.BasicSpec $ map mapH bS
    where
      mapH :: AS_Anno.Annoted AS_BASIC.BASICITEMS
           -> AS_Anno.Annoted AS_BASIC.BASICITEMS
      mapH aBI = AS_Anno.Annoted
                 {
                   AS_Anno.item = prBASICItems pSL $ AS_Anno.item aBI
                 , AS_Anno.opt_pos = AS_Anno.opt_pos aBI
                 , AS_Anno.l_annos = AS_Anno.l_annos aBI
                 , AS_Anno.r_annos = AS_Anno.r_annos aBI
                 }

checkHornPos :: AS_BASIC.FORMULA -> AS_BASIC.FORMULA -> Bool
checkHornPos fc fl =
    case fc of
      AS_BASIC.Conjunction _ _ -> all isPosLiteral $ Tools.flatten fc
      _ -> False
    &&
    isPosLiteral fl
