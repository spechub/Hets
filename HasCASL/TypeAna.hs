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
import HasCASL.Le
import HasCASL.Unify
import Data.List
import Data.Maybe
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.Lib.State

data ApplMode = OnlyArg | TopLevel 

mkTypeConstrAppls :: ApplMode -> Type -> State Env (Maybe Type)
mkTypeConstrAppls _ t@(TypeName _ _ _) = 
       return $ Just t 

mkTypeConstrAppls m (TypeAppl t1 t2) = 
    do mt3 <- mkTypeConstrAppls m t1
       mt4 <- mkTypeConstrAppls OnlyArg t2
       case (mt3, mt4) of
           (Just t3, Just t4) -> return $ Just $ TypeAppl t3 t4 
	   _ -> return Nothing

mkTypeConstrAppls _ (TypeToken t) = 
    do let i = simpleIdToId t
       tk <- gets typeMap
       let m = getKind tk i
	   c = if isTypeVar tk i then 1 else 0
       case m of 
	      Just k -> return $ Just $ TypeName i k c 
	      _ -> do addDiags [mkDiag Error "unknown type" t]
		      return Nothing

mkTypeConstrAppls m t@(BracketType b ts ps) =
    do mArgs <- mapM (mkTypeConstrAppls m) ts
       if all isJust mArgs then 
	  do let err = do addDiags [mkDiag Error "illegal type" t]
			  return Nothing 
	     case catMaybes mArgs of 
	          [x] -> case b of
		         Parens -> return $ Just x 		
			 _ -> do let [o,c] = mkBracketToken b ps 
				     i = Id [o, Token place $ posOfType 
					    $ head ts, c] [] []
				 tk <- gets typeMap
				 case getKind tk i of
				     Nothing -> err
				     Just k -> return $ Just $ TypeAppl 
					       (TypeName i k 0) x 
		  _ -> err
          else return Nothing

mkTypeConstrAppls _ (MixfixType []) = error "mkTypeConstrAppl (MixfixType [])"
mkTypeConstrAppls _ (MixfixType (f:a)) =
   do mF <- mkTypeConstrAppls TopLevel f 
      case mF of
          Nothing -> return Nothing
	  Just newF -> 
	      do mA <- mapM (mkTypeConstrAppls OnlyArg) a
		 if all isJust mA then
		    return $ Just $ foldl1 TypeAppl $ newF : catMaybes mA
		    else return Nothing

mkTypeConstrAppls m (KindedType t k p) =
    do mT <- mkTypeConstrAppls m t
       return $ fmap ( \ newT -> KindedType newT k p ) mT

mkTypeConstrAppls _ (LazyType t p) =
    do mT <- mkTypeConstrAppls TopLevel t
       return $ fmap ( \ newT -> LazyType newT p ) mT

mkTypeConstrAppls _ (ProductType ts ps) =
    do mTs <- mapM (mkTypeConstrAppls TopLevel) ts
       if all isJust mTs then
	  return $ Just $ ProductType (catMaybes mTs) ps
	  else return Nothing

mkTypeConstrAppls _ (FunType t1 a t2 ps) =
    do mT1 <- mkTypeConstrAppls TopLevel t1
       mT2 <- mkTypeConstrAppls TopLevel t2
       case (mT1, mT2) of 
           (Just newT1, Just newT2) -> 
	       return $ Just $ FunType newT1 a newT2 ps
	   _ -> return Nothing

expandApplKind :: Class -> State Env Kind
expandApplKind c = 
    case c of
    Intersection s _ -> if Set.isEmpty s then return star else
        do mk <- anaClassId  $ Set.findMin s
           case mk of 
	       Just k -> case k of 
		   ExtClass c2 _ _ -> expandApplKind c2
		   _ -> return k
	       Nothing -> error "expandApplKind"
    _ -> return star

inferKind :: Type -> State Env Kind
inferKind (TypeName i _ _) = do j <- getIdKind i
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

anaType :: (Kind, Type) -> State Env (Kind, Maybe Type)
anaType (k, t) = 
    do mT <- mkTypeConstrAppls TopLevel t
       tm <- gets typeMap
       case mT of 
            Nothing -> return (star, mT)
	    Just nt -> do let (newT,_) = expandAlias tm nt
			  newK <- inferKind newT 
			  checkKinds newT newK k
			  return (newK, Just newT)

anaStarType :: Type -> State Env (Maybe Type)
anaStarType t = fmap snd $ anaType (star, t)

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token ((\ (o,c) -> [o,c]) $ getBrackets k) 
		[head ps, last ps] 


