{- |
Module      :  $Header$
Description :  Intended to replace Common.Matching
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Matching2 where

import Data.List as L
--import Data.Set as S
import Data.Map as M

data Profile t fid sid p =
    Profile 
    { theory :: t,       -- ^ 't' is the theory where the profile belongs to
      formulaId :: fid,  -- ^ 'fid' is the id of the original formula relative to the theory 't'
      skeleton :: sid, -- ^ 'sid' the skeleton (or an representative id); i.e. the abstracted formula resulting from normalization
      parameter :: [p]   -- ^ '[p]' are the corresponding formula parameter
    } deriving (Eq, Ord, Show)

type ProfileMorphism s p = (FormulaIdMap s,ParameterMap p)
type FormulaIdMap fid = M.Map fid fid -- from source to target
type ParameterMap p = M.Map p p -- from source to target


allInterpretations :: (Ord s, Ord p) => [Profile t f s p] -> M.Map t [Profile t f s p] -> M.Map t [ProfileMorphism s p]
allInterpretations source = M.map (theoryInterpretations source)

theoryInterpretations :: (Ord s, Ord p) => [Profile t f s p] -> [Profile t f s p] -> [ProfileMorphism s p]
theoryInterpretations source target =
    L.foldr1 mergePMLists (L.map (formulaInterpretations (theorems target)) (axioms source))

theorems :: [Profile t f s p] -> [Profile t f s p]
theorems = undefined

axioms :: [Profile t f s p] -> [Profile t f s p]
axioms = undefined

formulaInterpretations :: (Ord s, Ord p) => [Profile t f s p] -> Profile t f s p -> [ProfileMorphism s p]
formulaInterpretations ps p = maybeMap (match p) ps

joinProfileMorphisms :: (Ord s,Ord p) => ProfileMorphism s p -> ProfileMorphism s p -> ProfileMorphism s p
joinProfileMorphisms (f1,p1) (f2,p2) = (M.union f1 f2, M.union p1 p2)

mergePMLists :: (Ord s,Ord p) => [ProfileMorphism s p] -> [ProfileMorphism s p] -> [ProfileMorphism s p]
mergePMLists s1 s2 = [joinProfileMorphisms pm1 pm2 | pm1 <- s1, pm2 <- s2, compatible pm1 pm2]

match :: Profile t f s p -> Profile t f s p -> Maybe (ProfileMorphism s p)
match = undefined

compatible :: ProfileMorphism s p -> ProfileMorphism s p -> Bool
compatible (_,p1) (_,p2) = undefined

maybeMap :: (a -> Maybe b) -> [a] -> [b]  -- in Utils
maybeMap _ [] = []
maybeMap f (x:xs) = 
    case f x of (Just y) -> y:(maybeMap f xs)
                Nothing -> (maybeMap f xs)

profileListToMap :: (Ord t) => [Profile t f s p] -> M.Map t [Profile t f s p]
profileListToMap ps = undefined
-- M.fromList (zip (L.map theory ps) ps)


{- in a nut shell:
theoryInterp S T = fold merge (map matchSet (theoremsOf T) (axiomsOf S))
  where matchSet F f = fold union (map (match f) F)
        merge X Y = {s union t | s <- X, t <- Y, compatible s t}
-}