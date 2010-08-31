{- |
Module      :  $Header$
Description :  Signature colimits for first-order logic with dependent
               types (DFOL)
Copyright   :  (c) Kristina Sojakova, DFKI Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  k.sojakova@jacobs-university.de
Stability   :  experimental
Portability :  portable

Algorithm description:

Input : graph where nodes are signatures and edges are morphisms
Output : a signature "sig" and for each input signature "sig1" a morphism
         m : sig1 -> sig

1 : Compute the transitive and symmetric closure of the relation R induced
    by the morphisms in the graph

2 : Initialize the output signature "sig" and collection of morphisms "M" to
    empty
    Initialize the set of analyzed symbols to empty

3 : For each input signature sig1 :
    3.1 : Initialize the output map "m" to empty
    3.2 : For each symbol "s" in sig1 (keeping the order in which they are
              defined) :
          3.1.1 Check if s R s' for any already analyzed symbol "s'"
          3.1.2 If yes:
                3.1.2.1 Recover from M the value "c" that s' maps to
                3.1.2.2 Update m by adding the pair (s,c)
          3.1.3 If no:
                3.1.3.1 Get the type "t" of s in sig1
                3.1.3.2 Translate t along m; call this new type "t1"
                3.1.3.3 Update sig by adding the declaration s : t1
                        (in case the name s is already contained in sig,
                        we generate a fresh name "s1" and add the declaration
                        s1 : t and pair (s,s1) to sig and m respectively.
    3.3 : Add m to M
-}

module DFOL.Colimit (
    sigColimit
  ) where

import DFOL.AS_DFOL
import DFOL.Sign
import DFOL.Morphism
import Common.Result
import Common.Id
import Common.Lib.Graph
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.IntMap as IntMap

-- main functions
sigColimit :: Gr Sign (Int, Morphism) -> Result (Sign, Map.Map Int Morphism)
sigColimit gr =
  let sigs = Graph.labNodes gr
      rel = computeRel gr
      (sig,maps) = addSig emptySig IntMap.empty Set.empty rel sigs
      maps1 = IntMap.mapWithKey (\ i m -> let Just sig1 = Graph.lab gr i
                                              in Morphism sig1 sig m
                                )
                                maps
      maps2 = Map.fromList $ IntMap.toList maps1
      in Result [] $ Just (sig,maps2)

-- preparation for computing the colimit
addSig :: Sign -> IntMap.IntMap (Map.Map NAME NAME) -> Set.Set (Int, NAME) ->
          Rel.Rel (Int, NAME) -> [(Int, Sign)] ->
          (Sign, IntMap.IntMap (Map.Map NAME NAME))
addSig sig maps _ _ [] = (sig,maps)
addSig sig maps doneSyms rel ((i, Sign ds):sigs) =
  processSig sig maps Map.empty i (expandDecls ds) doneSyms rel sigs

-- main function for computing the colimit
processSig :: Sign ->                        -- the signature determined so far
       IntMap.IntMap (Map.Map NAME NAME) ->  -- the morphisms determined so far
       Map.Map NAME NAME ->                  -- the current map
       Int ->                                -- the number or the current sig
       [DECL] ->                             -- the declarations to be processed
       Set.Set (Int, NAME) ->                -- the symbols done so far
       Rel.Rel (Int, NAME) ->                -- the equality relation
       [(Int, Sign)] ->                      -- the signatures to be processed
       (Sign, IntMap.IntMap (Map.Map NAME NAME))     -- the determined colimit

processSig sig maps m i [] doneSyms rel sigs =
  let maps1 = IntMap.insert i m maps
      in addSig sig maps1 doneSyms rel sigs

processSig sig maps m i (([n],t):ds) doneSyms rel sigs =
  let n1 = (i,n)
      eqSyms = Set.filter (\ k -> Rel.member n1 k rel) doneSyms
      in if (Set.null eqSyms)
            then let mt = toTermMap m
                     syms = getSymbols sig
                     t1 = translate mt syms t
                     n2 = toName n syms
                     sig1 = addSymbolDecl ([n2],t1) sig
                     m1 = Map.insert n n2 m
                     doneSyms1 = Set.insert n1 doneSyms
                     in processSig sig1 maps m1 i ds doneSyms1 rel sigs
            else let k = Set.findMin eqSyms
                     c = findValue k $ IntMap.insert i m maps
                     m1 = Map.insert n c m
                     doneSyms1 = Set.insert n1 doneSyms
                     in processSig sig maps m1 i ds doneSyms1 rel sigs

processSig _ _ _ _ _ _ _ _ = (emptySig, IntMap.empty)

-- helper functions
findValue :: (Int, NAME) -> IntMap.IntMap (Map.Map NAME NAME) -> NAME
findValue (i,k) maps = let Just m = IntMap.lookup i maps
                           in Map.findWithDefault k k m

toName :: NAME -> Set.Set NAME -> NAME
toName n names =
  if (Set.notMember n names)
     then n
     else let s = tokStr n
              n1 = Token ("gn_" ++ s) nullRange
              in getNewName n1 names

computeRel :: Gr Sign (Int, Morphism) -> Rel.Rel (Int, NAME)
computeRel gr =
  let morphs = Graph.labEdges gr
      rel = foldl (\ r1 (i,j,(_,m)) ->
                     let syms = Set.toList $ getSymbols $ source m
                         in foldl (\ r2 s -> let t = mapSymbol m s
                                                 in Rel.insert (i,s) (j,t)
                                                     $ Rel.insert (j,t) (i,s) r2
                                  )
                                  r1
                                  syms
                  )
                  Rel.empty
                  morphs
     in Rel.transClosure rel
