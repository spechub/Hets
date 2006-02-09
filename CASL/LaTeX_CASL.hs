{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable

latex printing of sign and morphism data types
-}

module CASL.LaTeX_CASL where

import Common.Keywords
import CASL.LaTeX_AS_Basic()
import CASL.Sign
import CASL.Morphism
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Lib.Pretty(($$), empty, vcat, (<>))
import Common.LaTeX_utils
import Common.PrintLaTeX

instance PrintLaTeX OpType where
  printLatex0 ga ot = printLatex0 ga $ toOP_TYPE ot

instance PrintLaTeX PredType where
  printLatex0 ga pt = printLatex0 ga $ toPRED_TYPE pt

instance (PrintLaTeX f, PrintLaTeX e) => PrintLaTeX (Sign f e) where
    printLatex0 ga s =
        hc_sty_plain_keyword sortS <\+>
                             commaT_latex ga (Set.toList $ sortSet s)
        $$
        (if Rel.null (sortRel s) then empty
            else hc_sty_plain_keyword sortS <\+>
             (vcat $ map printRel $ Map.toList $ Rel.toMap
                       $ Rel.transpose $ sortRel s))
        $$
        vcat (map (\ (i, t) ->
                   hc_sty_plain_keyword opS <\+>
                   printLatex0 ga i <\+> colon_latex <>
                   printLatex0 ga t)
              $ concatMap (\ (o, ts) ->
                          map ( \ ty -> (o, ty) ) $ Set.toList ts)
               $ Map.toList $ opMap s)
        $$
        vcat (map (\ (i, t) ->
                   hc_sty_plain_keyword predS <\+>
                   printLatex0 ga i <\+> colon_latex <\+>
                   printLatex0 ga (toPRED_TYPE t))
             $ concatMap (\ (o, ts) ->
                          map ( \ ty -> (o, ty) ) $ Set.toList ts)
             $ Map.toList $ predMap s)
     where printRel (supersort, subsorts) =
             commaT_latex ga (Set.toList subsorts) <\+> hc_sty_axiom lessS
                              <\+> printLatex0 ga supersort

instance PrintLaTeX Symbol where
  printLatex0 ga sy =
    printLatex0 ga (symName sy) <>
    case symbType sy of
       SortAsItemType -> empty
       t -> colon_latex <> printLatex0 ga t

instance PrintLaTeX SymbType where
  printLatex0 ga (OpAsItemType ot) = printLatex0 ga ot
  printLatex0 ga (PredAsItemType pt) = printLatex0 ga pt
  printLatex0 _ SortAsItemType = empty

instance PrintLaTeX Kind where
  printLatex0 _ SortKind = hc_sty_plain_keyword sortS
  printLatex0 _ FunKind = hc_sty_plain_keyword opS
  printLatex0 _ PredKind = hc_sty_plain_keyword predS

instance PrintLaTeX RawSymbol where
  printLatex0 ga rsym = case rsym of
    ASymbol sy -> printLatex0 ga sy
    AnID i -> printLatex0 ga i
    AKindedId k i -> printLatex0 ga k <\+> printLatex0 ga i

instance (PrintLaTeX f, PrintLaTeX e, PrintLaTeX m) =>
    PrintLaTeX (Morphism f e m) where
  printLatex0 ga mor =
   let printPair (s1,s2) = printLatex0 ga s1 <\+> hc_sty_axiom "\\mapsto"
                               <\+> printLatex0 ga s2
   in sp_braces_latex2 (vcat (map printPair $ Map.toList
                             $ Map.filterWithKey (/=)
                             $ morphismToSymbMap mor))
   $$ printLatex0 ga (extended_map mor)
   <\+> colon_latex $$
   sp_braces_latex2 (printLatex0 ga $ msource mor) <\+>
   hc_sty_axiom "\\rightarrow" <\+>
   sp_braces_latex2 (printLatex0 ga $ mtarget mor)
