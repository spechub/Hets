{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ClassAna
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result
import Common.Lib.State

data ApplMode = OnlyArg | TopLevel 

mkTypeConstrAppls :: ApplMode -> Type -> State Env Type
mkTypeConstrAppls _ t@(TypeName _ _ _) = 
       return t 

mkTypeConstrAppls m (TypeAppl t1 t2) = 
    do t3 <- mkTypeConstrAppls m t1
       t4 <- mkTypeConstrAppls OnlyArg t2
       return $ TypeAppl t3 t4 

mkTypeConstrAppls _ (TypeToken t) = 
    do let i = simpleIdToId t
       tk <- gets typeMap
       let m = getKind tk i
	   c = if isTypeVar tk i then 1 else 0
       case m of 
	      Just k -> return $ TypeName i k c 
	      _ -> return $ TypeToken t

mkTypeConstrAppls m t@(BracketType b ts ps) =
    do args <- mapM (mkTypeConstrAppls m) ts
       let toks@[o,c] = mkBracketToken b ps 
	   i = if null ts then Id toks [] [] 
	       else Id [o, Token place $ posOfType $ head ts, c] [] []
       tk <- gets typeMap
       let mk = getKind tk i
	   n = case mk of Just k -> TypeName i k 0
			  _ -> t
	   ds = [mkDiag Error "illegal type" t]
       if null ts then return n
	  else if null $ tail ts 
	       then return $ case b of 
			   Parens -> head args 
			   _ -> TypeAppl n (head args)
	       else do case m of
			      TopLevel -> do addDiags ds
			      OnlyArg -> case b of 
					 Parens -> return ()
					 _ -> do addDiags ds
		       return $ BracketType b args ps

mkTypeConstrAppls _ (MixfixType []) = error "mkTypeConstrAppl (MixfixType [])"
mkTypeConstrAppls _ (MixfixType (f:a)) =
   do newF <- mkTypeConstrAppls TopLevel f 
      newA <- mapM (mkTypeConstrAppls OnlyArg) a
      return $ foldl1 TypeAppl $ newF : newA
 
mkTypeConstrAppls m (KindedType t k p) =
    do newT <- mkTypeConstrAppls m t
       return $ KindedType newT k p

mkTypeConstrAppls _ (LazyType t p) =
    do newT <- mkTypeConstrAppls TopLevel t
       return $ LazyType newT p

mkTypeConstrAppls _ (ProductType ts ps) =
    do newTs <- mapM (mkTypeConstrAppls TopLevel) ts
       return $ ProductType newTs ps

mkTypeConstrAppls _ (FunType t1 a t2 ps) =
    do newT1 <- mkTypeConstrAppls TopLevel t1
       newT2 <- mkTypeConstrAppls TopLevel t2
       return $ FunType newT1 a newT2 ps

expandApplKind :: Class -> State Env Kind
expandApplKind c = 
    case c of
    Intersection s _ -> if Set.isEmpty s then return star else
        do k <- anaClassId  $ Set.findMin s
	   case k of 
		  ExtClass c2 _ _ -> expandApplKind c2
		  _ -> return k
    _ -> return star

inferKind :: Type -> State Env Kind
inferKind (TypeName i k _) = do j <- getIdKind i
				checkKinds i k j
				return j
inferKind (TypeAppl t1 t2) = 
    do mk1 <- inferKind t1 
       case mk1 of 
		KindAppl k1 k2 _ -> do checkTypeKind t2 k1
				       return k2
		ExtClass c _ _ -> 
			   do k <- expandApplKind c 
			      case k of
			            KindAppl k1 k2 _ -> do checkTypeKind t2 k1
							   return k2
				    _ -> do addDiags
					       [mkDiag Error 
						"incompatible kind of type" 
						t1] 
					    return star
inferKind (FunType t1 _ t2 _) = 
    do checkTypeKind t1 star 
       checkTypeKind t2 star
       return star 
inferKind (ProductType ts _) = 
    do mapM_ ( \ t -> checkTypeKind t star) ts 
       return star 
inferKind (LazyType t _) = 
    do checkTypeKind t star
       return star 
inferKind (TypeToken t) = getIdKind $ simpleIdToId t
inferKind (KindedType t k _) =
    do checkTypeKind t k
       return k
inferKind t =
    do addDiags [mkDiag Error "unresolved type" t] 
       return star

checkTypeKind :: Type -> Kind -> State Env ()
checkTypeKind t j = do k <- inferKind t 
		       checkKinds t j k

getIdKind :: Id -> State Env Kind
getIdKind i = 
    do tk <- gets typeMap
       let m = getKind tk i
       case m of
	    Nothing -> do addDiags [mkDiag Error "undeclared type" i]
                          return star
	    Just k -> return k

getKind :: TypeMap -> Id -> Maybe Kind
getKind tk i = 
       case Map.lookup i tk of
       Nothing -> Nothing
       Just (TypeInfo k _ _ _) -> Just k

isTypeVar :: TypeMap -> Id -> Bool
isTypeVar tk i = 
       case Map.lookup i tk of
       Just (TypeInfo _ _ _ TypeVarDefn) -> True
       _ -> False

anaType :: (Kind, Type) -> State Env (Kind, Type)
anaType (k, t) = 
    do newT <- mkTypeConstrAppls TopLevel t
       newK <- inferKind newT 
       checkKinds newT newK k
       return (newK, newT)

anaStarType :: Type -> State Env Type
anaStarType t = fmap snd $ anaType (star, t)

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token ((\ (o,c) -> [o,c]) $ getBrackets k) 
		[head ps, last ps] 


