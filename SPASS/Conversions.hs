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
import Data.List

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import Common.AS_Annotation
import SPASS.Sign

{- |
  Converts a Sign to an initial (no axioms or goals) SPLogicalPart.
-}
signToSPLogicalPart :: Sign -> SPLogicalPart
signToSPLogicalPart s =
    assert (checkArities s)
               (emptySPLogicalPart {symbolList = sList,
                                    declarationList = decList,
                                    formulaLists = if null decList 
                                                   then [] 
                                                   else [predArgRestrictions]
                                   }
               )
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

    decList = if (singleSorted s &&
                  (null . Map.elems . sortMap) s ) then []
                else subsortDecl ++ termDecl ++ predDecl ++ genDecl

    subsortDecl = map (\(a, b) -> SPSubsortDecl {sortSymA = a, sortSymB = b})
                      (Rel.toList (Rel.transReduce (sortRel s)))

    termDecl = concatMap termDecls (Map.toList (funcMap s))

    termDecls (fsym, tset) = map (toFDecl fsym) (Set.toList tset)
    toFDecl fsym (args, ret) =
        if null args
        then SPSimpleTermDecl
                 (SPComplexTerm {symbol = SPCustomSymbol ret,
                                 arguments = [SPSimpleTerm
                                              (SPCustomSymbol fsym)]})
        else SPTermDecl {
               termDeclTermList =
                 map (\(t, i) -> SPComplexTerm {symbol = SPCustomSymbol t,
                                                arguments = [SPSimpleTerm
                                      (SPCustomSymbol ('X' : (show i)))]})
                     (zip args [(1::Int)..]),
               termDeclTerm = SPComplexTerm {symbol = SPCustomSymbol ret,
                                             arguments =
                   [SPComplexTerm {symbol = SPCustomSymbol fsym,
                                   arguments = map
                           (SPSimpleTerm . SPCustomSymbol 
                            . ('X':) . show . snd)
                           (zip args [(1::Int)..])}]}}

    predArgRestrictions = 
          SPFormulaList { originType = SPOriginAxioms
                        , formulae = Map.foldWithKey toArgRestriction []  
                                     $ predMap s
                        }
    toArgRestriction psym tset acc 
        | Set.null tset = error "SPASS.Conversions.toArgRestriction: empty set"
        | Set.size tset == 1 = acc ++
            maybe [] 
                  ((:[]) . makeNamed ("arg_restriction_"++psym))
                  ((listToMaybe $ toPDecl psym $ head $ Set.toList tset) 
                    >>= predDecl2Term)
        | otherwise = acc ++
            (let argLists = Set.toList tset
             in [makeNamed ("arg_restriction_o_"++psym) $
                 makeTerm psym $
                 foldl (zipWith (flip (:))) 
                      (replicate (length $ head argLists) []) argLists])

    makeTerm psym tss = 
        let varList = take (length tss) $
                      genVarList psym (nub $ concat tss)
            varListTerms = spTerms varList
        in if null varList 
           then error "SPASS.Conversions.makeTerm: no propositional constants"
           else (SPQuantTerm{ 
                   quantSym=SPForall,
                   variableList=varListTerms,
                   qFormula=SPComplexTerm{
                               symbol=SPImplies,
                               arguments=[SPComplexTerm{
                                            symbol=SPCustomSymbol psym,
                                            arguments=varListTerms},
                                          foldl1 mkConj $ 
                                          zipWith (\ v -> 
                                                       foldl1 mkDisj . 
                                                       map (typedVarTerm v))
                                          varList tss]
                                                       }
                                            })
                                         
    predDecl = concatMap predDecls (Map.toList (predMap s))

    predDecls (p, tset) = -- assert (Set.size tset == 1) 
                          concatMap (toPDecl p) (Set.toList tset)
    toPDecl p t
        | null t    = []
        | otherwise = [SPPredDecl {predSym = p, sortSyms = t}]

    genDecl = map (\(ssym, Just gen) -> 
                       SPGenDecl {sortSym = ssym,
                                  freelyGenerated = freely gen,
                                  funcList = byFunctions gen})
                  (filter (isJust . snd) (Map.toList (sortMap s)))

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

{- |
  Generate a SPASS problem with time stamp while maybe adding a goal.
-}
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

{-| 
  generates a variable for each for each symbol in the input list 
  without symbol overlap
-}
genVarList :: SPIdentifier -> [SPIdentifier] -> [SPIdentifier]
genVarList chSym symList =
    let reservSym = chSym:symList
        varSource = filter (\x -> not $ elem x reservSym) $ 
                           map (showChar 'Y' . show) [(0::Int)..]
    in take (length symList) varSource

predDecl2Term :: SPDeclaration -> Maybe SPTerm
predDecl2Term pd = case pd of
                     SPPredDecl {} -> mkPredTerm
                     _ -> Nothing
    where mkPredTerm = let varList = genVarList (predSym pd)
                                                (sortSyms pd)
                           varListTerms = spTerms varList
                       in if null varList 
                          then Nothing
                          else Just ( 
                               SPQuantTerm{ 
                                 quantSym=SPForall,
                                 variableList=varListTerms,
                                 qFormula=SPComplexTerm{
                                   symbol=SPImplies,
                                   arguments=[SPComplexTerm{
                                                symbol=SPCustomSymbol
                                                           (predSym pd),
                                                arguments=varListTerms},
                                              foldl1 mkConj $ 
                                                zipWith typedVarTerm
                                                        varList $ sortSyms pd]
                                                       }
                                            })

