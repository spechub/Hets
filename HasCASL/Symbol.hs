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

data SymbolType = OpAsItemType TypeScheme
		| TypeAsItemType Kind
		| ClassAsItemType Kind
		  deriving (Show, Eq, Ord)

data SyTy = OpAsITy TySc
	  | TypeAsITy Kind
	  | ClassAsITy Kind
	    deriving (Show, Eq, Ord)

-- just for the Eq and Ord instances for Symbol
toSyTy :: SymbolType -> SyTy
toSyTy st = case st of
    OpAsItemType sc -> OpAsITy $ TySc sc
    TypeAsItemType k -> TypeAsITy k
    ClassAsItemType k -> ClassAsITy k

instance PrettyPrint SymbolType where
    printText0 ga t = case t of 
      OpAsItemType sc -> printText0 ga sc
      TypeAsItemType k -> printText0 ga k
      ClassAsItemType k -> printText0 ga k

data Symbol = Symbol {symName :: Id, symType :: SymbolType, symEnv :: Env} 
	      deriving Show

instance Eq Symbol where
    s1 == s2 = (symName s1, toSyTy $ symType s1) == 
	       (symName s2, toSyTy $ symType s2)

instance Ord Symbol where
    s1 <= s2 = (symName s1, toSyTy $ symType s1) <= 
	       (symName s2, toSyTy $ symType s2)

instance PrettyPrint Symbol where
  printText0 ga s = text (case symType s of 
			  OpAsItemType _ -> opS
			  TypeAsItemType _ -> typeS
			  ClassAsItemType _ -> classS) <+> 
                    printText0 ga (symName s) <+> text colonS <+> 
		    printText0 ga (symType s)

type SymbolMap = Map.Map Symbol Symbol 
type SymbolSet = Set.Set Symbol 

idToTypeSymbol :: Env -> Id -> Kind -> Symbol
idToTypeSymbol e idt k = Symbol idt (TypeAsItemType k) e

idToClassSymbol :: Env -> Id -> Kind -> Symbol
idToClassSymbol e idt k = Symbol idt (ClassAsItemType k) e

idToOpSymbol :: Env -> Id -> TypeScheme -> Symbol
idToOpSymbol e idt typ = Symbol idt (OpAsItemType typ) e

checkSymbols :: SymbolSet -> SymbolSet -> Result a -> Result a 
checkSymbols s1 s2 r = 
    let s = s1 Set.\\ s2 in
    if Set.isEmpty s then r else
       pfatal_error 
       (ptext "unknown symbols: " 
          <+> printText s) $ posOfId $ symName $ Set.findMin s

dependentSyms :: Symbol -> Env -> SymbolSet
dependentSyms sym sig = 
    Set.fold ( \ op se -> 
	       if Set.member sym $ subSymsOf op then
	       Set.insert op se else se) Set.empty $ symOf sig

hideRelSymbol :: Symbol -> Env -> Env
hideRelSymbol sym sig = 
    let depSyms = dependentSyms sym sig 
	relSyms = relatedSyms sig sym
	in
    if Set.isEmpty depSyms then hideSymbol sym sig
       else if Set.isEmpty relSyms then 
	    hideSymbol sym $ Set.fold hideSymbol sig depSyms
	    else sig


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
subSyms :: Env -> Type -> SymbolSet
subSyms e t = case t of
	   TypeName i k n ->
	       if n == 0 then Set.single $ idToTypeSymbol e i k
	       else Set.empty
	   TypeAppl t1 t2 -> Set.union (subSyms e t1) (subSyms e t2)
	   KindedType tk _ _ -> subSyms e tk
	   LazyType tl _ -> subSyms e tl
	   ProductType l _ -> Set.unions $ map (subSyms e) l
           FunType t1 _ t2 _ -> Set.union (subSyms e t1) (subSyms e t2)
	   _ -> error ("subSyms: " ++ show t)

subSymsOf :: Symbol -> SymbolSet
subSymsOf sy = case symType sy of
     OpAsItemType (TypeScheme _ (_ :=> ty) _) -> subSyms (symEnv sy) ty
     _ -> Set.empty

relatedSyms :: Env -> Symbol -> SymbolSet
relatedSyms e sy = 
    case symType sy of
    TypeAsItemType _ -> Set.delete sy $ 
			Set.image ( \ i -> sy { symName = i }) $
			   allRelIds (typeMap e) $ symName sy
    _ -> Set.empty

closeSymbSet :: SymbolSet -> SymbolSet
closeSymbSet s = Set.unions (s : map subSymsOf (Set.toList s)) 

symOf :: Env -> SymbolSet
symOf sigma = 
    let classes = Map.foldWithKey ( \ i ks s -> 
			Set.insert (Symbol i (ClassAsItemType $
				    Intersection (classKinds ks) []) sigma) s)
		  Set.empty $ classMap sigma
	types = Map.foldWithKey ( \ i ti s -> 
			Set.insert (Symbol i (TypeAsItemType $
				    typeKind ti) sigma) s) 
		classes $ typeMap sigma
        ops = Map.foldWithKey ( \ i ts s0 ->
		      foldr ( \ t s1 -> 
			  Set.insert (Symbol i (OpAsItemType $
				      opType t) sigma) s1) s0 $ opInfos ts)
	      types $ assumps sigma
	in ops

