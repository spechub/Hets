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
import HasCASL.HToken
import HasCASL.As
import HasCASL.Unify
import HasCASL.Merge
import Common.Id
import Common.Keywords
import Common.Result
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lib.State
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set

-- new type to defined a different Eq and Ord instance
data TySc = TySc TypeScheme deriving Show

instance Eq TySc where
    TySc sc1 == TySc sc2 = 
	let Result _ ms = mergeScheme Map.empty 0 sc1 sc2 
	    in maybe False (const True) ms

instance Ord TySc where
-- this does not match with Eq TypeScheme!
    TySc sc1 <= TySc sc2 = 
	TySc sc1 == TySc sc2 || 
	         let (t1, c) = runState (freshInst sc1) 1
		     t2 = evalState (freshInst sc2) c
		     v1 = varsOf t1
		     v2 = varsOf t2
                 in case compare (Set.size v1) $ Set.size v2 of 
			LT -> True
			EQ -> t1 <= subst (Map.fromAscList $
			    zipWith (\ v (TypeArg i k _ _) ->
				     (v, TypeName i k 1)) 
					   (Set.toList v1) $ Set.toList v2) t2
			GT -> False 		   

data SymbolType = OpAsItemType TySc
		| TypeAsItemType Kind
		| ClassAsItemType Kind
		  deriving (Show, Eq, Ord)

instance PrettyPrint SymbolType where
    printText0 ga t = case t of 
      OpAsItemType (TySc sc) -> printText0 ga sc
      TypeAsItemType k -> printText0 ga k
      ClassAsItemType k -> printText0 ga k

data Symbol = Symbol {symName :: Id, symType :: SymbolType} 
	      deriving (Show, Eq, Ord)

instance PrettyPrint Symbol where
  printText0 ga s = text (case symType s of 
			  OpAsItemType _ -> opS
			  TypeAsItemType _ -> typeS
			  ClassAsItemType _ -> classS) <+> 
                    printText0 ga (symName s) <+> text colonS <+> 
		    printText0 ga (symType s)

type SymbolMap = Map.Map Symbol Symbol 
type SymbolSet = Set.Set Symbol 

idToTypeSymbol :: Id -> Kind -> Symbol
idToTypeSymbol idt k = Symbol idt $ TypeAsItemType k

idToClassSymbol :: Id -> Kind -> Symbol
idToClassSymbol idt k = Symbol idt $ ClassAsItemType k

idToOpSymbol :: Id -> TySc -> Symbol
idToOpSymbol idt typ = Symbol idt $ OpAsItemType typ

checkSymbols :: SymbolSet -> SymbolSet -> Result a -> Result a 
checkSymbols s1 s2 r = 
    let s = s1 Set.\\ s2 in
    if Set.isEmpty s then r else
       pfatal_error 
       (ptext "unknown symbols: " 
          <+> printText s) $ posOfId $ symName $ Set.findMin s

hideSymbol :: Symbol -> Env -> Env
hideSymbol sym sig = 
    let i = symName sym
	tm = typeMap sig
	as = assumps sig in
    case symType sym of 
    ClassAsItemType _ -> sig
    TypeAsItemType _ -> sig { typeMap = 
			      Map.delete i tm }
    OpAsItemType (TySc ot) -> 
	let OpInfos os = Map.findWithDefault (OpInfos []) i as
	    rs = filter (not . isUnifiable tm 0 ot . opType) os
        in sig { assumps = if null rs then Map.delete i as
		          else Map.insert i (OpInfos rs) as }

plainHide :: SymbolSet -> Env -> Env
plainHide syms sigma = 
    let (opSyms, otherSyms) = Set.partition (\ sy -> case symType sy of
					      OpAsItemType _ -> True
					      _ -> False) syms
    in Set.fold hideSymbol (Set.fold hideSymbol sigma otherSyms) opSyms 

-- | type ids within a type
subSyms :: Type -> SymbolSet
subSyms t = case t of
	   TypeName i k n ->
	       if n == 0 then Set.single $ idToTypeSymbol i k
	       else Set.empty
	   TypeAppl t1 t2 -> Set.union (subSyms t1) (subSyms t2)
	   TypeToken _ -> Set.empty
	   BracketType _ l _ -> Set.unions $ map subSyms l
	   KindedType tk _ _ -> subSyms tk
	   MixfixType l -> Set.unions $ map subSyms l
	   LazyType tl _ -> subSyms tl
	   ProductType l _ -> Set.unions $ map subSyms l
           FunType t1 _ t2 _ -> Set.union (subSyms t1) (subSyms t2)

subSymsOf :: Symbol -> SymbolSet
subSymsOf sy = case symType sy of
     OpAsItemType (TySc (TypeScheme _ (_ :=> ty) _)) -> subSyms ty
     _ -> Set.empty

closeSymbSet :: SymbolSet -> SymbolSet
closeSymbSet s = Set.unions (s : map subSymsOf (Set.toList s)) 

symOf :: Env -> SymbolSet
symOf sigma = 
    let classes = Map.foldWithKey ( \ i ks s -> 
			Set.insert (Symbol i $ ClassAsItemType $
				    Intersection (classKinds ks) []) s) 
		  Set.empty $ classMap sigma
	types = Map.foldWithKey ( \ i ti s -> 
			Set.insert (Symbol i $ TypeAsItemType $
				    typeKind ti) s) 
		classes $ typeMap sigma
        ops = Map.foldWithKey ( \ i ts s0 ->
		      foldr ( \ t s1 -> 
			  Set.insert (Symbol i $ OpAsItemType $ TySc $
				      opType t) s1) s0 $ opInfos ts)
	      types $ assumps sigma
	in ops

