{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable
    
   latex printing of sign and morphism data types

-}

module CASL.LaTeX_CASL where

import Common.Keywords
import CASL.AS_Basic_CASL
import CASL.LaTeX_AS_Basic
import CASL.Sign
import CASL.Morphism
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Lib.Pretty
import Common.PPUtils
import Common.LaTeX_utils
import Common.PrintLaTeX

instance PrintLaTeX OpType where
  printLatex0 ga ot = printLatex0 ga $ toOP_TYPE ot

instance PrintLaTeX PredType where
  printLatex0 ga pt = printLatex0 ga $ toPRED_TYPE pt

instance Analyzable lid b s f e => PrintLaTeX (Sign lid b s f e) where
    printLatex0 ga s = 
	ptext sortS <+> commaT_latex ga (Set.toList $ sortSet s) 
	$$ 
        (if Rel.isEmpty (sortRel s) then empty
            else ptext sortS <+> 
             (vcat $ map printRel $ Map.toList $ Rel.toMap $ sortRel s))
	$$ 
	vcat (map (\ (i, t) -> 
		   ptext opS <+>
		   printLatex0 ga i <+> colon <>
		   printLatex0 ga t) 
	      $ concatMap (\ (o, ts) ->
			  map ( \ ty -> (o, ty) ) $ Set.toList ts)
	       $ Map.toList $ opMap s)
	$$ 
	vcat (map (\ (i, t) -> 
		   ptext predS <+>
		   printLatex0 ga i <+> colon <+>
		   printLatex0 ga (toPRED_TYPE t)) 
	     $ concatMap (\ (o, ts) ->
			  map ( \ ty -> (o, ty) ) $ Set.toList ts)
	     $ Map.toList $ predMap s)
     where printRel (subs, supersorts) =
             printLatex0 ga subs <+> ptext lessS <+> printSet ga supersorts

instance PrintLaTeX Symbol where
  printLatex0 ga sy = 
    printLatex0 ga (symName sy) <> 
    (if isEmpty t then empty
      else ptext colonS <> t)
    where
    t = printLatex0 ga (symbType sy)

instance PrintLaTeX SymbType where
  printLatex0 ga (OpAsItemType ot) = printLatex0 ga ot
  printLatex0 ga (PredAsItemType pt) = printLatex0 ga pt
  printLatex0 _ SortAsItemType = empty 

instance PrintLaTeX Kind where
  printLatex0 _ SortKind = ptext sortS
  printLatex0 _ FunKind = ptext opS
  printLatex0 _ PredKind = ptext predS

instance PrintLaTeX RawSymbol where
  printLatex0 ga rsym = case rsym of
    ASymbol sy -> printLatex0 ga sy
    AnID i -> printLatex0 ga i
    AKindedId k i -> printLatex0 ga k <+> printLatex0 ga i

instance Analyzable lid b s f e => PrintLaTeX (Morphism lid b s f e) where
  printLatex0 ga mor = 
   (if null sorts then empty
       else ptext sortS <+> (fsep $ punctuate comma sorts))
   $$ 
   (if null ops then empty
       else ptext opS <+> (fsep $ punctuate comma ops))
   $$
   (if null preds then empty
       else ptext predS <+> (fsep $ punctuate comma preds))
   <+>
   ptext " : " $$ 
   ptext "{" <+>  printLatex0 ga (msource mor) <+> ptext "}" <+> 
   ptext "->" <+> 
   ptext "{" <+>  printLatex0 ga (mtarget mor) <+> ptext "}"
   where sorts = map print_sort_map (Map.toList $ sort_map mor)
         print_sort_map (s1,s2) = 
           printLatex0 ga s1 <+> ptext "|->" <+> printLatex0 ga s2
         ops = map print_op_map (Map.toList $ fun_map mor)
         print_op_map ((id1,ot),(id2, _)) = 
           printLatex0 ga (Qual_op_name id1 (toOP_TYPE ot) [])
           <+> ptext "|->" <+> 
           printLatex0 ga id2
         preds = map print_pred_map (Map.toList $ pred_map mor)
         print_pred_map ((id1,pt),id2) = 
           printLatex0 ga (Qual_pred_name id1 (toPRED_TYPE pt) [])
           <+> ptext "|->" <+> 
           printLatex0 ga id2
