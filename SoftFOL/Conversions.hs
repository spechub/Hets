{- |
Module      :  $Header$
Description :  Functions to convert to internal SP* data structures.
Copyright   :  (c) Rene Wagner, Klaus Luettich, Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  unknown

Functions to convert to internal SP* data structures.
-}

module SoftFOL.Conversions where

import Control.Exception
import System.Time
import Data.Maybe
import Data.List

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.Rel as Rel

import Common.AS_Annotation
import Common.Id
import Common.Utils (number)

import SoftFOL.Sign

{- |
  Converts a Sign to an initial (no axioms or goals) SPLogicalPart.
-}
signToSPLogicalPart :: Sign -> SPLogicalPart
signToSPLogicalPart s =
    assert (checkArities s)
               (emptySPLogicalPart {symbolList = sList,
                                    declarationList = Just decList,
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

    decList = if singleSorted s && null (Map.elems $ sortMap s) then []
                else subsortDecl ++ termDecl ++ predDecl ++ genDecl

    subsortDecl = map (\(a, b) -> SPSubsortDecl {sortSymA = a, sortSymB = b})
                      (Rel.toList (Rel.transReduce (sortRel s)))

    termDecl = concatMap termDecls (Map.toList (funcMap s))

    termDecls (fsym, tset) = map (toFDecl fsym) (Set.toList tset)
    toFDecl fsym (args, ret) =
        if null args
        then SPSimpleTermDecl $ compTerm (spSym ret) [simpTerm $ spSym fsym]
        else let
            xTerm :: Int -> SPTerm
            xTerm i = simpTerm $ mkSPCustomSymbol $ 'X' : show i
            in SPTermDecl
               { termDeclTermList =
                 map (\ (t, i) -> compTerm (spSym t) [xTerm i]) $ number args
               , termDeclTerm = compTerm (spSym ret) [compTerm (spSym fsym)
                   $ map (xTerm . snd) $ number args] }
    predArgRestrictions =
          SPFormulaList { originType = SPOriginAxioms
                        , formulae = Map.foldWithKey toArgRestriction []
                                     $ predMap s
                        }
    toArgRestriction psym tset acc
        | Set.null tset = error
           "SoftFOL.Conversions.toArgRestriction: empty set"
        | Set.size tset == 1 = acc ++
            maybe []
                  ((: []) . makeNamed ("arg_restriction_" ++ tokStr psym))
                  (listToMaybe (toPDecl psym $ head $ Set.toList tset)
                    >>= predDecl2Term)
        | otherwise = acc ++
             let argLists = Set.toList tset
             in [makeNamed ("arg_restriction_o_" ++ tokStr psym) $
                 makeTerm psym $
                 foldl (zipWith (flip (:)))
                      (map (const []) $ head argLists) argLists]

    makeTerm psym tss =
        let varList = zipWith const (genVarList psym $ nub $ concat tss) tss
            varListTerms = spTerms varList
        in if null varList
           then error
             "SoftFOL.Conversions.makeTerm: no propositional constants"
           else SPQuantTerm {
                   quantSym=SPForall,
                   variableList=varListTerms,
                   qFormula= compTerm SPImplies
                     [ compTerm (spSym psym) varListTerms
                     , foldl1 mkConj $ zipWith
                       (\ v ->  foldl1 mkDisj . map (typedVarTerm v))
                       varList tss ]}

    predDecl = concatMap predDecls $ Map.toList $ predMap s

    predDecls (p, tset) = -- assert (Set.size tset == 1)
                          concatMap (toPDecl p) (Set.toList tset)
    toPDecl p t
        | null t    = []
        | otherwise = [SPPredDecl {predSym = p, sortSyms = t}]

    genDecl = map (\ (ssym, Just gen) ->
                       SPGenDecl {sortSym = ssym,
                                  freelyGenerated = freely gen,
                                  funcList = byFunctions gen})
              $ filter (isJust . snd) $ Map.toList $ sortMap s

{- |
  Inserts a Named Sentence (axiom or goal) into an SPLogicalPart.
-}
insertSentence :: SPLogicalPart -> Named Sentence -> SPLogicalPart
insertSentence lp nSen = lp {formulaLists = fLists'}
  where
    insertFormula oType x [] =
      [SPFormulaList {originType= oType, formulae= [x]}]
    insertFormula oType x (l : ls) =
      if originType l == oType
        then l{formulae = case formulae l of
               [f] | oType == SPOriginConjectures ->
                  [reName (const "ga_conjunction_of_theorem")
                   $ mapNamed (const $ mkConj (sentence f) $ sentence x) f]
               fs -> x : fs} : ls
        else l : insertFormula oType x ls
    fLists' = if isAxiom nSen
                then insertFormula SPOriginAxioms nSen fLists
                else insertFormula SPOriginConjectures nSen fLists
    fLists = formulaLists lp

{- |
  Generate a SoftFOL problem with time stamp while maybe adding a goal.
-}
genSoftFOLProblem :: String -> SPLogicalPart
                -> Maybe (Named SPTerm) -> IO SPProblem
genSoftFOLProblem thName lp m_nGoal =
    do d <- getClockTime
       return $ problem $ show d
    where
    problem sd = SPProblem
        {identifier = "hets_exported",
         description = SPDescription
                       {name = thName ++ maybe "" (('_' :) . senAttr) m_nGoal,
                        author = "hets",
                        SoftFOL.Sign.version = Nothing,
                        logic = Nothing,
                        status = SPStateUnknown,
                        desc = "",
                        date = Just sd},
         logicalPart = maybe lp (insertSentence lp) m_nGoal,
         settings = []}

{- |
  generates a variable for each for each symbol in the input list
  without symbol overlap
-}
genVarList :: SPIdentifier -> [SPIdentifier] -> [SPIdentifier]
genVarList chSym symList =
    let reservSym = chSym:symList
        varSource = filter (flip notElem reservSym)
          $ map (mkSimpleId . showChar 'Y' . show) [(0::Int) ..]
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
                          else Just
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
                                            }

{- |
'checkArities'
checks if the signature has only overloaded symbols with the same arity
-}
checkArities :: Sign -> Bool
checkArities s =
    checkPredArities (predMap s) && checkFuncArities (funcMap s)

checkPredArities :: PredMap -> Bool
checkPredArities = Map.fold checkSet True
    where checkSet s bv = bv && not (Set.null s) &&
                  all (\ x -> length x == length hd) tl
                      where hd : tl = Set.toList s

checkFuncArities :: FuncMap -> Bool
checkFuncArities = checkPredArities . mapToPredMap
    where mapToPredMap = Map.map (Set.map fst)
