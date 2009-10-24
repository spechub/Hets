{- |
Module      :  $Header$
Description :  Signature colimits for first-order logic with dependent
               types (DFOL)
Copyright   :  (c) Kristina Sojakova, Jacobs University 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  k.sojakova@ijacobs-university.de
Stability   :  experimental
Portability :  portable
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
