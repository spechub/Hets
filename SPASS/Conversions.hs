{- |
Module      :  $Header$
Copyright   :  (c) Rene Wagner, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  rwagner@tzi.de
Stability   :  provisional
Portability :  unknown

Functions to convert to internal SP* data structures.

-}

module SPASS.Conversions where

import Maybe

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import Common.AS_Annotation
import SPASS.Sign

{- |
  Converts a Sign to an initial (no axioms or goals) SPLogicalPart.
-}
signToSPLogicalPart :: Sign -> SPLogicalPart
signToSPLogicalPart s = SPLogicalPart {symbolList = sList,
                                       declarationList = decList,
                                       formulaLists = []}
  where
    sList = if Rel.null (sortRel s) && Map.null (funcMap s) && 
               Map.null (predMap s) && Map.null (sortMap s)
              then Nothing
              else Just emptySymbolList { functions = map (\(f, t) -> SPSignSym {sym = f, arity = length (fst t)}) (Map.toList (funcMap s)),
                                          predicates = map (\(p, t) -> SPSignSym {sym = p, arity = length t}) (Map.toList (predMap s)),
                                          sorts = map SPSimpleSignSym (Set.toList ((Rel.nodes (sortRel s)) `Set.union` (Map.keysSet (sortMap s))))}

    decList = subsortDecl ++ termDecl ++ predDecl ++ genDecl

    subsortDecl = map (\(a, b) -> SPSubsortDecl {sortSymA = a, sortSymB = b}) (Rel.toList (Rel.transReduce (sortRel s)))

    termDecl = map (\(fsym, (args, ret)) -> SPTermDecl {termDeclTermList = map (\(t, x) -> SPComplexTerm {symbol = SPCustomSymbol t, arguments = [SPSimpleTerm (SPCustomSymbol ('x' : (show x)))]}) (zip args [1..]), termDeclTerm = SPComplexTerm {symbol = SPCustomSymbol ret, arguments = [SPComplexTerm {symbol = SPCustomSymbol fsym, arguments = map (SPSimpleTerm . SPCustomSymbol . ('x':) . show . snd) (zip args [1..])}]}}) (Map.toList (funcMap s))

    predDecl = map (\(p, t) -> SPPredDecl {predSym = p, sortSyms = t}) (Map.toList (predMap s))

    genDecl = map (\(ssym, Just gen) -> SPGenDecl {sortSym = ssym, freelyGenerated = freely gen, funcList = byFunctions gen}) (filter (isJust . snd) (Map.toList (sortMap s)))

{- |
  Inserts a Named Sentence (axiom or goal) into an SPLogicalPart.
-}
insertSentence :: SPLogicalPart -> Named Sentence -> SPLogicalPart
insertSentence lp nSen = lp {formulaLists = fLists'}
  where
    insertFormula oType x [] =
      [SPFormulaList {originType= oType, formulae= [x]}]
    insertFormula oType x (l:ls) = 
      if originType l == oType
        then l{formulae= x:(formulae l)}:ls
        else l:(insertFormula oType x ls)
    fLists' = if isAxiom nSen
                then insertFormula SPOriginAxioms nSen fLists
                else insertFormula SPOriginConjectures nSen fLists
    fLists = formulaLists lp
