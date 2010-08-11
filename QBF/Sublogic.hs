{- |
Module      :  $Header$
Description :  Sublogics for propositional logic
Copyright   :  (c) Jonathan von Schroeder, DFKI GmbH 2010
License     :  GPLv2 or higher

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
    , QBFFormulae (..)             -- types of propositional formulae
    , QBFSL (..)                   -- sublogics for propositional logic
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
data QBFFormulae = PlainFormula      -- Formula without structural constraints
                  | HornClause        -- Horn Clause Formulae
                  deriving (Show, Eq, Ord)

-- | sublogics for propositional logic
data QBFSL = QBFSL
    {
      format :: QBFFormulae     -- Structural restrictions
    } deriving (Show, Eq, Ord)

isProp :: QBFSL -> Bool
isProp sl = format sl == PlainFormula

isHC :: QBFSL -> Bool
isHC sl = format sl == HornClause

-- | comparison of sublogics
compareLE :: QBFSL -> QBFSL -> Bool
compareLE p1 p2 =
    let f1 = format p1
        f2 = format p2
    in
      case (f1, f2) of
        (_, PlainFormula) -> True
        (HornClause, HornClause) -> True
        (_, HornClause) -> False

-- Special elements in the Lattice of logics

top :: QBFSL
top = QBFSL PlainFormula

bottom :: QBFSL
bottom = QBFSL HornClause

needPF :: QBFSL
needPF = bottom { format = PlainFormula }

-- join and max

sublogicsJoin :: (QBFFormulae -> QBFFormulae -> QBFFormulae)
                  -> QBFSL -> QBFSL -> QBFSL
sublogicsJoin pfF a b = QBFSL
                         {
                           format = pfF (format a) (format b)
                         }

joinType :: QBFFormulae -> QBFFormulae -> QBFFormulae
joinType HornClause HornClause = HornClause
joinType _ _ = PlainFormula

sublogicsMax :: QBFSL -> QBFSL -> QBFSL
sublogicsMax = sublogicsJoin joinType

-- Helpers

-- compute sublogics from a list of sublogics

compList :: [QBFSL] -> QBFSL
compList = foldl sublogicsMax bottom

-- Functions to compute minimal sublogic for a given element, these work
-- by recursing into all subelements

-- | determines the sublogic for symbol map items
slSymmap :: QBFSL -> AS_BASIC.SYMBMAPITEMS -> QBFSL
slSymmap ps _ = ps

-- | determines the sublogic for a morphism
slMor :: QBFSL -> Morphism.Morphism -> QBFSL
slMor ps _ = ps

-- | determines the sublogic for a Signature
slSig :: QBFSL -> Sign.Sign -> QBFSL
slSig ps _ = ps

-- | determines the sublogic for Symbol items
slSymit :: QBFSL -> AS_BASIC.SYMBITEMS -> QBFSL
slSymit ps _ = ps

-- | determines the sublogic for symbols
slSym :: QBFSL -> Symbol.Symbol -> QBFSL
slSym ps _ = ps

-- | determines sublogic for formula
slForm :: QBFSL -> AS_BASIC.FORMULA -> QBFSL
slForm ps = slFlForm ps . Tools.flatten

-- | determines sublogic for flattened formula
slFlForm :: QBFSL -> [AS_BASIC.FORMULA] -> QBFSL
slFlForm ps = foldl sublogicsMax ps
  . map (\ x -> State.evalState (anaForm ps x) 0)

-- analysis of single "clauses"
anaForm :: QBFSL -> AS_BASIC.FORMULA -> State.State Int QBFSL
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
moreThanNLit = (>) . foldl (\ y x -> if x then y + 1 else y) 0
  . map isPosLiteral

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
slBasicItems :: QBFSL -> AS_BASIC.BASICITEMS -> QBFSL
slBasicItems ps bi =
    case bi of
      AS_BASIC.PredDecl _ -> ps
      AS_BASIC.AxiomItems xs -> compList $ map (slForm ps . AS_Anno.item) xs

-- | determines sublogic for basic spec
slBasicSpec :: QBFSL -> AS_BASIC.BASICSPEC -> QBFSL
slBasicSpec ps (AS_BASIC.BasicSpec spec) =
    compList $ map (slBasicItems ps . AS_Anno.item) spec

-- | all sublogics
sublogicsAll :: [QBFSL]
sublogicsAll =
    [QBFSL
     {
       format = HornClause
     }
    , QBFSL
     {
       format = PlainFormula
     }
    ]

-- Conversion functions to String

sublogicsName :: QBFSL -> String
sublogicsName f = case format f of
      HornClause -> "HornClause"
      PlainFormula -> "Prop"

-- Projections to sublogics

prSymbolM :: QBFSL -> Symbol.Symbol -> Maybe Symbol.Symbol
prSymbolM _ = Just

prSig :: QBFSL -> Sign.Sign -> Sign.Sign
prSig _ sig = sig

prMor :: QBFSL -> Morphism.Morphism -> Morphism.Morphism
prMor _ mor = mor

prSymMapM :: QBFSL
          -> AS_BASIC.SYMBMAPITEMS
          -> Maybe AS_BASIC.SYMBMAPITEMS
prSymMapM _ = Just

prSymM :: QBFSL -> AS_BASIC.SYMBITEMS -> Maybe AS_BASIC.SYMBITEMS
prSymM _ = Just

-- keep an element if its computed sublogic is in the given sublogic

prFormulaM :: QBFSL -> AS_BASIC.FORMULA -> Maybe AS_BASIC.FORMULA
prFormulaM sl form
           | compareLE (slForm bottom form) sl = Just form
           | otherwise = Nothing

prPredItem :: QBFSL -> AS_BASIC.PREDITEM -> AS_BASIC.PREDITEM
prPredItem _ prI = prI

prBASICItems :: QBFSL -> AS_BASIC.BASICITEMS -> AS_BASIC.BASICITEMS
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

prBasicSpec :: QBFSL -> AS_BASIC.BASICSPEC -> AS_BASIC.BASICSPEC
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
