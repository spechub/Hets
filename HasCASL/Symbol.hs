{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable

   
   HasCASL analysed symbols of a signature
-}

module HasCASL.Symbol where

import HasCASL.Le
import HasCASL.PrintLe
import HasCASL.As
import HasCASL.Unify
import HasCASL.RawSym
import Common.Id
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

checkSymbols :: SymbolSet -> SymbolSet -> Result a -> Result a 
checkSymbols s1 s2 r = 
    let s = foldr ( \ e2 d -> 
                 Set.filter (not . matchSymb e2 . ASymbol) d)
                  s1 $ Set.toList s2 in
    if Set.isEmpty s then r else
       pfatal_error 
       (text "unknown symbols: " 
          <+> printText s) $ posOfId $ symName $ Set.findMin s

dependentSyms :: Symbol -> Env -> SymbolSet
dependentSyms sym sig = 
    Set.fold ( \ op se -> 
	       if Set.member sym $ subSymsOf op then
	       Set.insert op se else se) Set.empty $ symOf sig

hideRelSymbol :: Symbol -> Env -> Env
hideRelSymbol sym sig = 
    hideSymbol sym $ Set.fold hideSymbol sig $ dependentSyms sym sig


hideSymbol :: Symbol -> Env -> Env
hideSymbol sym sig = 
    let i = symName sym
	tm = typeMap sig
	as = assumps sig in
    case symType sym of 
    ClassAsItemType _ -> sig
    TypeAsItemType _ -> sig { typeMap = 
			      Map.delete i tm }
    OpAsItemType ot -> 
	let OpInfos os = Map.findWithDefault (OpInfos []) i as
	    rs = filter (not . isUnifiable tm 1 ot . opType) os
        in sig { assumps = if null rs then Map.delete i as
		          else Map.insert i (OpInfos rs) as }

plainHide :: SymbolSet -> Env -> Env
plainHide syms sigma = 
    let (opSyms, otherSyms) = Set.partition (\ sy -> case symType sy of
					      OpAsItemType _ -> True
					      _ -> False) syms
    in Set.fold hideSymbol (Set.fold hideSymbol sigma otherSyms) opSyms 

-- | type ids within a type
subSyms :: Env -> Type -> SymbolSet
subSyms e t = case t of
	   TypeName i k n ->
	       if n == 0 then if i == unitTypeId then Set.empty 
                  else Set.single $ idToTypeSymbol e i k
	       else Set.empty
	   TypeAppl t1 t2 -> Set.union (subSyms e t1) (subSyms e t2)
	   ExpandedType _ t1 -> subSyms e t1
	   KindedType tk _ _ -> subSyms e tk
	   LazyType tl _ -> subSyms e tl
	   ProductType l _ -> Set.unions $ map (subSyms e) l
           FunType t1 _ t2 _ -> Set.union (subSyms e t1) (subSyms e t2)
	   _ -> error ("subSyms: " ++ show t)

subSymsOf :: Symbol -> SymbolSet
subSymsOf sy = case symType sy of
     OpAsItemType (TypeScheme _ ty _) -> subSyms (symEnv sy) ty
     _ -> Set.empty

closeSymbSet :: SymbolSet -> SymbolSet
closeSymbSet s = Set.unions (s : map subSymsOf (Set.toList s)) 

symOf :: Env -> SymbolSet
symOf sigma = 
    let classes = Map.foldWithKey ( \ i ks s -> 
			Set.insert (idToClassSymbol sigma i $ 
				    Intersection (classKinds ks) []) s)
		  Set.empty $ classMap sigma
	types = Map.foldWithKey ( \ i ti s -> 
			Set.insert (idToTypeSymbol sigma i $
				    typeKind ti) s) 
		classes $ typeMap sigma
        ops = Map.foldWithKey ( \ i ts s0 ->
		      foldr ( \ t s1 -> 
			  Set.insert (idToOpSymbol sigma i $
				      opType t) s1) s0 $ opInfos ts)
	      types $ assumps sigma
	in ops

