{- |
Module      :  ./CASL/CompositionTable/Pretty2.hs
Description :  pretty output for composition tables
Copyright   :  (c) Christian Maeder DFKI 2012
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module CASL.CompositionTable.Pretty2 where

import CASL.CompositionTable.CompositionTable
import CASL.CompositionTable.ModelTable
import CASL.CompositionTable.Keywords

import qualified Data.IntSet as IntSet
import qualified Data.IntMap as IntMap

import Common.Doc

ctxt :: String -> Doc
ctxt = text . (':' :)

table2Doc :: Table2 -> Doc
table2Doc (Table2 name br m brs cs ct) =
   parens $ text defCalculusS <+> doubleQuotes (text name)
   $+$ ctxt identityRelationS <+> baserel m br
   $+$ (if IntSet.null brs then empty else
        ctxt baseRelationsS <+> parens
             (hsep $ map (baserel m) $ IntSet.toList brs))
   $+$ conversetable m ct
   $+$ (if IntMap.null cs then empty else
        colon <> (text compositionOperationS $+$
                  parens (vcat $ concatMap (cmptab m) $ IntMap.toList cs)))

baserel :: IntMap.IntMap Baserel -> Int -> Doc
baserel m i = case IntMap.lookup i m of
  Just (Baserel br) -> text br
  Nothing -> error $ "CASL.CompositionTable.Pretty2.baserel " ++ show i

cmptab :: IntMap.IntMap Baserel -> (Int, IntMap.IntMap IntSet.IntSet) -> [Doc]
cmptab m (a1, m2) = map
  (\ (a2, s) -> parens $ baserel m a1 <+> baserel m a2
                <+> parens (hsep $ map (baserel m) $ IntSet.toList s))
  $ IntMap.toList m2

conversetable :: IntMap.IntMap Baserel -> ConTables -> Doc
conversetable m (l, l1, l2, l3) =
    vcat [ contab m converseOperationS l
         , contab m inverseOperationS l1
         , contab m shortcutOperationS l2
         , contab m homingOperationS l3 ]

contab :: IntMap.IntMap Baserel -> String -> ConTable -> Doc
contab m t l = if IntMap.null l then empty else
   colon <> (text t $+$ parens (vcat $ map (contabentry m) $ IntMap.toList l))

contabentry :: IntMap.IntMap Baserel -> (Int, IntSet.IntSet) -> Doc
contabentry m (a, bs) = parens $ baserel m a <+> case IntSet.toList bs of
  [b] -> baserel m b
  l -> parens $ hsep $ map (baserel m) l
