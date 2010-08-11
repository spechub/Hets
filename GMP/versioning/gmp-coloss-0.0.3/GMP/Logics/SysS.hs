{- | Module     : $Header$
 -  Description : Implementation of logic instance of 'System S'
 -  Copyright   : (c) Daniel Hausmann & Georgel Calin & Lutz Schroeder, DFKI Lab Bremen,
 -                Rob Myers & Dirk Pattinson, Department of Computing, ICL 
 -  License     : GPLv2 or higher
 -  Maintainer  : hausmann@dfki.de
 -  Stability   : provisional
 -  Portability : portable
 -
 - Provides the implementation of the matching functions of 'System S'.
 -}

module GMP.Logics.SysS where
import List
import Ratio
import Maybe

import Debug.Trace
import Text.ParserCombinators.Parsec

import GMP.Logics.Generic
import GMP.Parser

--------------------------------------------------------------------------------
-- instance of System S and needed functions
--------------------------------------------------------------------------------

data SysS a = SysS [Formula a] deriving (Eq,Show)

instance (SigFeature b c d, Eq (b (c d)), Eq (c d)) => NonEmptyFeature SysS b c d where
-- compute all Gamma 0, construct all cStructures over each Gamma 0
    nefMatch flags seq = let g0s = (sysCGammaZeros seq)
                             cStructuress = map cStructures g0s
-- for any structure <m> and any equivalence class <inds> on it, compute <deltaM inds>
                         in if (flags!!1)
                              then
                                trace ("  <All G0s for current sequent:>                " ++ show (map pretty_list g0s) ++ "\n") $
                                [ trace "\n  <Starting a new G0...>\n" $ sysCprems strucs | strucs <- cStructuress ]
                              else [ sysCprems strucs | strucs <- cStructuress ]

    nefPretty d = genfPretty d "[SysS]"
    nefFeatureFromSignature sig = SysS
    nefFeatureFromFormula phi = SysS
    nefStripFeature (SysS phis) = phis
    nefSeparator sig = "=>"

--------------------------------------------------------------------------------
-- additional functions for the matching function of this logic
--------------------------------------------------------------------------------

pretty_c :: (Feature SysS (a (b c))) => ([Int],[(Int,Int)],[Formula (SysS (a (b c)))]) -> String
pretty_c (worlds,rel,seq) = show worlds ++ show rel ++ pretty_list seq


sysCprems :: (SigFeature a b c, Eq (a (b c)), Eq (b c)) => [([Int],[(Int,Int)],[Formula (SysS (a (b c)))])] -> [[Sequent]]
sysCprems strucs = [ (trace ("  Structure M (for g0=" ++ pretty_list sequ ++ "): <worlds> " ++ show worlds ++ " <rel> " ++ show rel)) $
                     (orOverInds m (nu m)) | m@(worlds,rel,sequ) <- strucs ]

orOverInds :: (SigFeature a b c, Eq (a (b c)), Eq (b c)) => ([Int],[(Int,Int)],[Formula (SysS (a (b c)))]) -> [[Int]] -> [Sequent]
orOverInds struc [] = []
orOverInds struc (inds:indss) = (trace ("  <deltaM(ec) (ec="++show inds++"):> " ++ pretty_seq (deltaM struc inds))) $
                                (deltaM struc inds):(orOverInds struc indss)


-------------------------------------------------------------------------------
-- compute deltaM(inds)
-- two cases, either the head of the input equivalence class is equivalent
-- wrt. the 'less remote than' relation to 0, or not. refer to paper for
-- more details...
-------------------------------------------------------------------------------
deltaM :: (SigFeature a b c, Eq (a (b c))) => ([Int],[(Int,Int)],[Formula (SysS (a (b c)))]) -> [Int] -> Sequent
deltaM struc@(worlds,rel,seq) ec = case ( ((head ec),0) `elem` rel) && ( (0,(head ec)) `elem` rel) of
                                        -- equivalence class contains 0
                                        True  -> Sequent (concat [ [(Neg ante),(Neg conseq)] | (Neg (Mod (SysS (ante:conseq:_)))) <- (seqswAt seq ec)] ++
                                                 concat [ [(Neg ante),conseq]       |      (Mod (SysS (ante:conseq:_)))  <- [(seq!!0)]      ] ++
                                                 [ ante | (Neg (Mod (SysS (ante:conseq:_)))) <- seqsAt seq ([0..((length seq)-1)]\\worlds)])
                                        -- equivalence class does not contain 0
                                        False -> Sequent (concat [ [(Neg ante),(Neg conseq)] | (Neg (Mod (SysS (ante:conseq:_)))) <- (seqsAt seq ec)] ++
                                                 [ ante | (Neg (Mod (SysS (ante:conseq:_)))) <- seqsAt seq ([0..((length seq)-1)]\\worlds)] ++
                                                 [ ante | (Neg (Mod (SysS (ante:conseq:_)))) <- seqsAt seq (biggerInds struc (head ec))] ++
                                                 [ ante | (Mod (SysS (ante:conseq:_))) <- seqsAt seq (biggerInds struc (head ec))])

-------------------------------------------------------------------------------
-- return those indices of a cStructure which are 'strictly bigger' wrt. to the
-- 'less remote than' relation than the input integer
-------------------------------------------------------------------------------
biggerInds :: ([Int],[(Int,Int)],[Formula (SysS a)]) -> Int -> [Int]
biggerInds struc@(worlds,rel,seq) i = [ j | j <- [0..(length seq)], ((i,j)`elem`rel)&& (not((j,i)`elem`rel)) ]

-------------------------------------------------------------------------------
-- keep only the indexed parts of sequents (w/wo 0)
-------------------------------------------------------------------------------
seqswAt :: [Formula (SysS a)] -> [Int] -> [Formula (SysS a)]
seqswAt [] inds = []
seqswAt seq [] = []
seqswAt seq (ind:inds) = if ind==0 then (seqsAt seq inds)
                                   else seq!!ind : (seqsAt seq inds)

seqsAt :: [Formula (SysS a)] -> [Int] -> [Formula (SysS a)]
seqsAt [] inds = []
seqsAt seq [] = []
seqsAt seq (ind:inds) = seq!!ind : (seqsAt seq inds)

-------------------------------------------------------------------------------
-- given a sequent, return the big disjunction of this sequent
-------------------------------------------------------------------------------
orIfy :: [Formula (SysS a)] -> Formula (SysS a)
orIfy [] = F
orIfy (phi:[]) = phi
orIfy (phi:phis) = (Or phi (orIfy phis))

-------------------------------------------------------------------------------
-- compute all possible sequents of the form "\Gamma 0" that may be built
-- from the input sequent seq
-------------------------------------------------------------------------------
sysCGammaZeros :: [Formula (SysS a)] -> [[Formula (SysS a)]]
sysCGammaZeros seq = let negNegMods = [ (Neg(Mod (SysS phis))) | (Neg(Mod (SysS phis))) <- seq]
                         posMods    = [ (Mod (SysS phis)) | (Mod (SysS phis)) <- seq]
-- use this for complete application of the rule (i.e. all combinations of
-- negative literals)
--                       allNegs    = powerList negNegMods
-- use this for maximal application of the rule (i.e. only consider all
-- negative literals at once)
                         allNegs    = [negNegMods]
                     in [(pos:negs)| negs <- allNegs, pos <- posMods ]

-------------------------------------------------------------------------------
-- let nu return all equivalence classes for the input cStructure
-------------------------------------------------------------------------------
nu :: ([Int],[(Int,Int)],[Formula (SysS a)]) -> [[Int]]
nu struc@(worlds,rel,seq) = equivClasses worlds rel

-------------------------------------------------------------------------------
-- given a set of worlds and a transitive and reflexive relation over this set
-- of worlds, compute the equivalence classes according to this relation
-------------------------------------------------------------------------------
equivClasses :: (Eq a) => [a] -> [(a,a)] -> [[a]]
equivClasses [] rel = []
equivClasses (world:worlds) rel = let ec = (equivClass world worlds rel)
                                  in ec:(equivClasses (worlds\\ec) rel)

equivClass :: (Eq a) => a -> [a] -> [(a,a)] -> [a]
equivClass world worlds rel = world:[ w | w <- worlds, (((w,world)`elem`rel) && ((world,w)`elem`rel))]

-------------------------------------------------------------------------------
-- for any set of worlds, compute all possible cStructures over it, i.e.
-- endow this set of worlds with any possible 'less remote than' relation
-------------------------------------------------------------------------------
cStructures :: [Formula (SysS a)] -> [([Int],[(Int,Int)],[Formula (SysS a)])]
cStructures seq = [ (worlds,rel,seq) | (worlds,rel) <- (cStructs2 (powerList [0..((length seq)-1)]))]

cStructs2 :: [[Int]] -> [([Int],[(Int,Int)])]
cStructs2 worldss = concat [ cStructs worlds | worlds <- worldss ]

cStructs :: [Int] -> [([Int],[(Int,Int)])]
cStructs worlds = [ (worlds,rel) | rel <- (allRels worlds)]

-------------------------------------------------------------------------------
-- get all 'less remote than' relations, i.e. all linear pre-orders with
-- greatest element 0
-------------------------------------------------------------------------------

allRels :: [Int] -> [[(Int,Int)]]
allRels worlds = (nub $ map List.sort (buildRels worlds (allPairs worlds) (diagonal worlds))) \\ [[]]

-- is a binary relation over worlds transitive, linear and has greatest element 0?
okRel :: [Int] -> [(Int,Int)] -> Bool
okRel worlds rel = (transBreakers worlds rel == []) && (linearBreakers worlds rel == []) && (great0Breakers worlds rel == []) 

-- given a relation, add pairs to it in a consistent manner (i.e. closing of under transitivity, linearity and 0 being
-- greatest element). continue with the remaining pairs.
buildRels :: [Int] -> [(Int,Int)] -> [(Int,Int)] -> [[(Int,Int)]]
buildRels worlds [] rel = -- trace ("finishing: " ++ show rel) $
                          if okRel worlds rel then [rel] else []
buildRels worlds pairs [] = []
buildRels worlds (pair:pairs) rel = -- trace ("building: " ++ show (pair:pairs) ++ show rel) $ 
                                    if pair `elem` rel then buildRels worlds pairs rel
                                    else let closedRel = closeRel worlds pair rel
                                         in closedRel ++ (concatMap (buildRels worlds pairs) closedRel) ++ (buildRels worlds pairs rel)
                                    
-- add pairs to a relation until it is transitive, linear and has greatest element 0. if that's not
-- possible, return []
closeRel :: [Int] -> (Int,Int) -> [(Int,Int)] -> [[(Int,Int)]]
closeRel worlds pair@(x,y) rel = -- trace ("closing: " ++ show worlds ++ show pair ++ show rel) $
                                 if pair `elem` rel then
                                   if (okRel worlds rel) then [rel] else []
                                 else
                                   case transBreakers worlds (pair:rel) of
                                   w:ws -> closeRel worlds w (pair:rel)
                                   []   -> case linearBreakers worlds (pair:rel) of
                                              (v,w):ws -> (closeRel worlds v (pair:rel)) ++
                                                          (closeRel worlds w (pair:rel))
                                              []       -> case great0Breakers worlds (pair:rel) of
                                                             w:ws -> closeRel worlds w (pair:rel)
                                                             []   -> [(pair:rel)]

-- return the diagonal relation over worlds
diagonal :: [Int] -> [(Int,Int)]
diagonal [] = []
diagonal (w:ws) = (w,w) : diagonal ws

-- return the set of pairs that break transitivity
transBreakers :: [Int] -> [(Int,Int)] -> [(Int,Int)]
transBreakers worlds rel = [ (x,z) | z <- worlds, y <- worlds, x <- worlds,
                                    (((x,y)`elem`rel)&&((y,z)`elem`rel)&&(not((x,z)`elem`rel)))]

-- return the set of pairs of pairs the break linearity
linearBreakers :: [Int] -> [(Int,Int)] -> [((Int,Int),(Int,Int))]
linearBreakers worlds rel = [ ((x,z),(z,x)) | z <- worlds, x <- worlds,
                                              ( (not((x,z) `elem` rel)) && (not((z,x) `elem` rel)) )]

-- return the set of pairs that violate that 0 is greatest element
great0Breakers :: [Int] -> [(Int,Int)] -> [(Int,Int)]
great0Breakers worlds rel = [ (z,0) | z <- worlds, (not((z,0) `elem` rel))]

-- return all combinations of worlds
allPairs :: [Int] -> [(Int,Int)]
allPairs worlds = [(x,y) | x <- worlds, y <- worlds]

--------------------------------------------------------------------------------
-- instance of sigFeature for 'System S'
--------------------------------------------------------------------------------

instance (SigFeature b c d, Eq (c d), Eq (b (c d))) => NonEmptySigFeature SysS b c d where
  neGoOn sig flag = genericPGoOn sig flag

