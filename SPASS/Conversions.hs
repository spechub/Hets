{- |
Module      :  $Header$
Description :  Functions to convert to internal SP* data structures.
Copyright   :  (c) Rene Wagner, Klaus Lüttich, Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  unknown

Functions to convert to internal SP* data structures.

-}

module SPASS.Conversions where

import Control.Exception
import System.Time
import Data.Maybe

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel

import Common.AS_Annotation
import SPASS.Sign

{- |
  Converts a Sign to an initial (no axioms or goals) SPLogicalPart.
-}
signToSPLogicalPart :: Sign -> SPLogicalPart
signToSPLogicalPart s = 
    assert (checkArities s) 
               (SPLogicalPart {symbolList = sList,
                               declarationList = decList,
                               formulaLists = []})
  where
    sList = if Rel.null (sortRel s) && Map.null (funcMap s) && 
               Map.null (predMap s) && Map.null (sortMap s)
              then Nothing
              else Just emptySymbolList 
                       { functions = 
                             map (\(f, ts) -> 
                                      SPSignSym {sym = f, 
                                                 arity = length (fst (head 
                                                            (Set.toList ts)))}) 
                                     (Map.toList (funcMap s)),
                         predicates = 
                             map (\(p, ts) -> 
                                      SPSignSym {sym = p, 
                                                 arity = length (head
                                                          (Set.toList ts))}) 
                                     (Map.toList (predMap s)),
                         sorts = map SPSimpleSignSym $ Map.keys $ sortMap s }

    decList = subsortDecl ++ termDecl ++ predDecl ++ genDecl

    subsortDecl = map (\(a, b) -> SPSubsortDecl {sortSymA = a, sortSymB = b}) (Rel.toList (Rel.transReduce (sortRel s)))

    termDecl = concatMap termDecls (Map.toList (funcMap s))

    termDecls (fsym, tset) = map (toFDecl fsym) (Set.toList tset)
    toFDecl fsym (args, ret) = 
        if null args
        then SPSimpleTermDecl 
                 (SPComplexTerm {symbol = SPCustomSymbol ret,
                                 arguments = [SPSimpleTerm 
                                              (SPCustomSymbol fsym)]})
        else SPTermDecl {termDeclTermList = 
                             map (\(t, i) -> 
                                      SPComplexTerm {symbol = SPCustomSymbol t,
                                                     arguments = 
                                                         [SPSimpleTerm (SPCustomSymbol ('X' : (show i)))]}) (zip args [(1::Int)..]),
                       termDeclTerm = SPComplexTerm {symbol = SPCustomSymbol ret, 
                                                     arguments = [SPComplexTerm {symbol = SPCustomSymbol fsym,
                                                                                 arguments = map (SPSimpleTerm . SPCustomSymbol . ('X':) . show . snd) (zip args [(1::Int)..])}]}}

    predDecl = concatMap predDecls (Map.toList (predMap s))

    predDecls (p, tset) = concatMap (toPDecl p) (Set.toList tset)
    toPDecl p t 
        | null t    = []
        | otherwise = [SPPredDecl {predSym = p, sortSyms = t}]

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

{- | generate a SPASS problem with time stamp while maybe adding a goal.-}
genSPASSProblem :: String -> SPLogicalPart 
                -> Maybe (Named SPTerm) -> IO SPProblem
genSPASSProblem thName lp m_nGoal =
    do d <- getClockTime
       return $ problem $ show d
    where
    problem sd = SPProblem 
        {identifier = "hets_exported",
         description = SPDescription 
                       {name = thName++
                               (maybe "" 
                                      (\ nGoal -> '_':senName nGoal)
                                      m_nGoal),
                        author = "hets",
                        SPASS.Sign.version = Nothing,
                        logic = Nothing,
                        status = SPStateUnknown,
                        desc = "",
                        date = Just sd},
         logicalPart = maybe lp (insertSentence lp) m_nGoal,
         settings = []}
