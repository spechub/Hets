{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder, Bremen 2015
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian Maeder
Stability   :  provisional
Portability :  portable

-}

module SoftFOL.StatAna (basicAnalysis) where

import Common.AS_Annotation (Named, makeNamed, SenAttr (..))
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import qualified Common.Lib.MapSet as MapSet
import Common.Result

import qualified Data.Map as Map
import qualified Data.Set as Set

import SoftFOL.Sign
import SoftFOL.Morphism

basicAnalysis :: ([TPTP], Sign, GlobalAnnos)
  -> Result ([TPTP], ExtSign Sign SFSymbol, [Named Sentence])
basicAnalysis (sp, sg, _) =
  let ns = toNamedSen sp
      sig2 = foldr (addSyms True Set.empty . sentence) sg ns
      sig3 = if sig2 == emptySign then sig2 else sig2
           { sortMap = Map.insert universeSort Nothing $ sortMap sig2 }
  in return (sp, ExtSign sig3 $ Set.difference (symOf sig3) $ symOf sg, ns)

toNamedSen :: [TPTP] -> [Named Sentence]
toNamedSen = concatMap $ \ f -> case f of
           FormAnno _ (Name n) r t _ -> [
             let sen = makeNamed n t
             in case r of
                 Axiom -> sen
                 Hypothesis -> sen
                 Definition -> sen { isAxiom = False, isDef = True}
                 Assumption -> sen
                 Lemma -> sen
                 Theorem -> sen
                 _ -> sen { isAxiom = False } ]
           _ -> []

formulaSymbols :: [SPSymbol]
formulaSymbols =
  [ SPOr
  , SPAnd
  , SPNot
  , SPImplies
  , SPImplied
  , SPEquiv ]

universeSort :: SPIdentifier
universeSort = mkSimpleId "U"

addSyms :: Bool -> Set.Set SPTerm -> SPTerm -> Sign -> Sign
addSyms isFormula boundVars t sig = case t of
  SPQuantTerm _ vs f ->
    addSyms True (Set.union boundVars $ Set.fromList vs) f sig
  SPComplexTerm ssym args ->
    let sig2 = foldr (addSyms (elem ssym formulaSymbols) boundVars)
               sig args
    in case ssym of
       SPCustomSymbol sid | not (null args)
         || Set.notMember t boundVars ->
           let pf = replicate (length args) universeSort
           in if isFormula then sig2
                { predMap = MapSet.setInsert sid pf $ predMap sig2 }
           else sig2
                { funcMap = MapSet.setInsert sid (pf, universeSort)
                  $ funcMap sig2 }
       _ -> sig2
