{- | Module     : $Header$
 -  Description : Implementation of logic instance of CK+CM
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher, see LICENSE.txt
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of CK+CM.
 -}

module GMP.Logics.CKCM where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of feature for the feature of CK+CM
--------------------------------------------------------------------------------

data CKCM a = CKCM [Formula a] deriving (Eq,Show)

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature CKCM b c d where
    nefMatch flags seq = let g0 = gZeros seq
                             compGraphs = map constructCompGraphs g0
                         in if (flags!!1) 
                            then
                              [ trace ("Matching <g0>: " ++ pretty_list gZ ++ " Using <graph>: " ++ show cG) $
                                let sss = (ckcmPremise gZ cG) in trace ("Premise: " ++ show (map (map pretty_seq) (sss)) )
                                sss | (gZ,cGs) <- compGraphs, cG <- cGs ]
                            else
                              [ (ckcmPremise gZ cG) | (gZ,cGs) <- compGraphs, cG <- cGs ]
    nefPretty d = genfPretty d "[CK+CM]"
    nefFeatureFromSignature sig = CKCM
    nefFeatureFromFormula phi = CKCM
    nefStripFeature (CKCM phis) = phis
    nefSeparator sig = "=>"

gZeros :: [Formula (CKCM (b c))] -> [[Formula (CKCM (b c))]]
gZeros seq = let poslits = [ (Mod (CKCM phis)) | (Mod (CKCM phis)) <- seq]
                 neglits = [ Neg (Mod (CKCM phis)) | Neg (Mod (CKCM phis)) <- seq]
             in [ neglits ++ [poslit] | poslit <- poslits ]

constructCompGraphs :: [Formula (a (b c))] -> ([Formula (a (b c))],[([[Int]],[([Int],[Int])])])
constructCompGraphs gZ = (gZ,(allCompGraphs ((length gZ) - 2 )))

allCompGraphs :: Int -> [([[Int]],[([Int],[Int])])]
allCompGraphs i = removeDuplicates (iteratedLayerAdding [([[0..i]],[])])

removeDuplicates :: [([[Int]],[([Int],[Int])])] -> [([[Int]],[([Int],[Int])])]
removeDuplicates [] = []
removeDuplicates (g:gs) = if (appearsIn g gs) then (removeDuplicates gs)
                                              else g:(removeDuplicates gs)

appearsIn :: ([[Int]],[([Int],[Int])]) -> [([[Int]],[([Int],[Int])])] -> Bool
appearsIn graph [] = False
appearsIn graph (g:gs) = if (graph == g) then True
                                         else (appearsIn graph gs)

iteratedLayerAdding :: [([[Int]],[([Int],[Int])])] -> [([[Int]],[([Int],[Int])])]
iteratedLayerAdding graphs = -- trace ("graphs: " ++ show graphs) $
                             let extendedGraphs = nub (sort (concatMap addLayer graphs))
                             in if (nub (sort graphs)) == extendedGraphs
                                        then graphs
                                        else iteratedLayerAdding (concatMap addLayer graphs)

addLayer :: ([[Int]],[([Int],[Int])]) -> [([[Int]],[([Int],[Int])])]
addLayer graph@(worlds,rel) = let exps = initialStates graph 
                              in case exps of
                                  [] -> --trace ("initial states: " ++ show (exps)) $
                                        [graph]
                                  _  -> --trace ("initial states: " ++ show (exps)) $
                                        graph: [ --trace ("expansion: " ++ show (nub stateSetExpansion)) $
                                          (expandAll graph (nub stateSetExpansion)) |
                                          stateSetExpansion <- stateSetExpansions exps ]

stateSetExpansions :: [[Int]] -> [[([Int],[[Int]])]]
stateSetExpansions [] = [[]]
stateSetExpansions (w:ws) = [ concatMap (decomp:) (stateSetExpansions ws) | decomp <- decompositions w ]

expandAll :: ([[Int]],[([Int],[Int])]) -> [([Int],[[Int]])] -> ([[Int]],[([Int],[Int])])
expandAll graph@(worlds,rel) [] = graph
expandAll graph@(worlds,rel) ((state,expansion):expansions) = expandAll ((nub (sort (worlds++expansion))),
                                                                         (nub (sort (rel++(newPairs state expansion))))) expansions

newPairs :: [Int] -> [[Int]] -> [([Int],[Int])]
newPairs state expansion = [ (newState,state) | newState <- expansion]

decompositions :: [Int] -> [([Int],[[Int]])]
decompositions world = map (\decomp -> (world,decomp)) (nub (concat [ (sort (decomposition (first:(world\\[first])))) | first <- world ]))

decomposition :: [Int] -> [[[Int]]]
decomposition []        = []
decomposition [x]       = []
decomposition is@(x:xs) = --trace ("decomposing " ++ show is) $ 
                          [ --trace ("decomposition: " ++ show (nub decomp\\[is])) $ 
                            (nub (decomp\\[is])) | decomp <- (decompose is), not ((nub (decomp\\[is])) == []), not ((nub decomp)==[(sort is)])] 

isInfixOf               :: (Eq a) => [a] -> [a] -> Bool
isInfixOf needle haystack = any (isPrefixOf needle) (tails haystack)

decompose :: [Int] -> [[[Int]]]
decompose []        = [[[]]]
decompose [x]       = [[[x]]]
decompose is@(x:xs) = [[is]] ++ [ --trace ("x: " ++ show x ++ " xs:" ++ show xs ++ " cont: " ++ show contained ++
                               --" excl: " ++ show exclusives ++ "subD: " ++ show subDecomposition) $ 
                       ((sort (x:contained)) : subDecomposition)\\[[]] | contained <- (powerList xs), exclusives <- (powerList contained),
                                                                         subDecomposition <- (decompose (xs\\(exclusives))),
                                                                         not ((xs\\contained)==[]),
                                                                         not (any (\w -> (isInfixOf w (x:contained))) subDecomposition)]

initialStates :: ([[Int]],[([Int],[Int])]) -> [[Int]]
initialStates graph@(worlds,rel) = filter (\w -> not ((length w) == 1))
                                          (filter (\s -> not (any (\p -> ((p,s)`elem` rel)) worlds)) worlds)

initialStates2 :: ([[Int]],[([Int],[Int])]) -> [[Int]]
initialStates2 graph@(worlds,rel) = [s | s <- worlds, (all (\p -> (not((p,s)`elem` rel))) worlds)]

ckcmPremise :: (SigFeature b c d, Eq (b (c d)), Eq (c d)) => 
                 [Formula (CKCM (b (c d)))] ->
                 ([[Int]],[([Int],[Int])]) -> [[Sequent]]
ckcmPremise gZ cG@(worlds,rel) = let allNegConsequents = [ (Neg psi) | (Neg (Mod (CKCM [phi,psi]))) <- gZ]
                                     allNegAntecedents = [ (Neg phi) | (Neg (Mod (CKCM [phi,psi]))) <- gZ]
                                     consequent      (Mod (CKCM [phi,psi]))  = psi
                                     consequent (Neg (Mod (CKCM [phi,psi]))) = psi
                                     antecedent      (Mod (CKCM [phi,psi]))  = phi
                                     antecedent (Neg (Mod (CKCM [phi,psi]))) = phi
                                     negArgs state = [ Neg (antecedent (gZ!!ind)) | ind <- state ] ++
                                                     [ Neg (consequent (gZ!!ind)) | ind <- state ]
                                 in [ [Sequent (equiv (keep initialstate gZ))]
                                                        | initialstate <- initialStates2 cG ] ++
                                    [ [Sequent ((antecedent (gZ!!j)) : (negArgs v))] 
                                                        | v <- worlds, w <- worlds, ((v,w)`elem`rel), j <- w] ++
                                    [ [Sequent ((consequent (gZ!!((length gZ) - 1))) : (take ((length gZ)-1) allNegConsequents))] ] ++
                                    [ [Sequent ((antecedent (gZ!!((length gZ) - 1))) : (take ((length gZ)-1) allNegConsequents)
                                                                                    ++ (take ((length gZ)-1) allNegAntecedents) )] ] ++
                                    [ [Sequent ((Neg (antecedent (gZ!!((length gZ) -1)))) : [antecedent (gZ!!i)])]
                                                        | i <- [0..((length gZ)-2)] ]

keep :: (SigFeature b c d, Eq (b (c d)), Eq (c d)) =>
               [Int] ->
               [Formula (CKCM (b (c d)))] -> [Formula (CKCM (b (c d)))]
keep [] seq = []
keep (x:xs) seq = if x<(length seq) then (seq!!x):(keep xs seq)
                                    else (keep xs seq)

equiv :: (SigFeature b c d, Eq (b (c d)), Eq (c d)) =>
               [Formula (CKCM (b (c d)))] -> [Formula (b (c d))]
equiv [] = --trace ("no more element, nothing needs to be shown... ") $
           [T]
equiv [x] = --trace ("only one element, nothing needs to be shown... " ++ pretty x) $
            [T]
equiv (x:y:xs) = --trace ("equiv added...") $
                 let antecedent xi = case xi of (Neg (Mod (CKCM (phi:psi:_)))) -> phi
                                                (Mod (CKCM (phi:psi:_)))       -> phi
                                                _                              -> F
                 in (And (Neg (And (Neg (antecedent x)) (antecedent y)))
                         (Neg (And (Neg (antecedent y)) (antecedent x)))) : (equiv (y:xs))

--------------------------------------------------------------------------------
-- instance of sigFeature for CK+CM
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature CKCM b c d where
  neGoOn sig flag = genericPGoOn sig flag

