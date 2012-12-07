{- |
Module      :  $Header$
Description :  intermediate calculus table
Copyright   :  (c) Uni Bremen 2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL.CompositionTable.ModelTable where

import CASL.CompositionTable.CompositionTable
import Common.Utils

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap
import qualified Data.Map as Map
import Data.List

data Table2 = Table2 String Int (IntMap.IntMap Baserel) BSet CmpTbl ConTables

type BSet = IntSet.IntSet

type CmpTbl = IntMap.IntMap (IntMap.IntMap IntSet.IntSet)

type ConTable = IntMap.IntMap IntSet.IntSet

type ConTables = (ConTable, ConTable, ConTable, ConTable)

lkup :: (Show a, Ord a) => a -> Map.Map a Int -> Int
lkup i = Map.findWithDefault
  (error $ "CASL.CompositionTable.ModelTable.lkup" ++ show i) i

toTable2 :: Table -> Table2
toTable2 (Table (Table_Attrs name id_ baserels)
  (Compositiontable comptbl) convtbl _ _) =
  let ns = number baserels
      m = Map.fromList ns
  in Table2 name (lkup id_ m)
    (IntMap.fromList $ map (\ (a, b) -> (b, a)) ns)
    (IntSet.fromAscList [1 .. Map.size m])
    (toCmpTbl m comptbl)
    $ toConTables m convtbl

toCmpTbl :: Map.Map Baserel Int -> [Cmptabentry] -> CmpTbl
toCmpTbl m =
  foldl' (\ t (Cmptabentry (Cmptabentry_Attrs rel1 rel2) bs)
              -> IntMap.insertWith IntMap.union (lkup rel1 m)
                 (IntMap.insertWith IntSet.union (lkup rel2 m)
                 (IntSet.fromList $ map (`lkup` m) bs) IntMap.empty) t)
  IntMap.empty

toConTab :: Map.Map Baserel Int -> (a -> Baserel) -> (a -> [Baserel]) -> [a]
  -> ConTable
toConTab m s1 s2 = foldl' (\ t a ->
    IntMap.insertWith IntSet.union (lkup (s1 a) m)
           (IntSet.fromList $ map (`lkup` m) $ s2 a) t) IntMap.empty

toConTab2 :: Map.Map Baserel Int -> [Contabentry_Ternary] -> ConTable
toConTab2 m =
  toConTab m contabentry_TernaryArgBaseRel contabentry_TernaryConverseBaseRels

toConTables :: Map.Map Baserel Int -> Conversetable -> ConTables
toConTables m c = case c of
  Conversetable l ->
    (toConTab m contabentryArgBaseRel contabentryConverseBaseRel l
    , IntMap.empty, IntMap.empty, IntMap.empty)
  Conversetable_Ternary l1 l2 l3 ->
    (IntMap.empty, toConTab2 m l1, toConTab2 m l2, toConTab2 m l3)
