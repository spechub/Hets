
{- HetCATS/HasCASL/TypeAna.hs
   $Id$
   Authors: Christian Maeder
   Year:    2003
   
   analyse given classes and types
-}

module HasCASL.TypeAna where

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.ClassAna
import Common.Id
import HasCASL.Le
import Data.List
import Data.Maybe
import HasCASL.Reader
import HasCASL.PrintAs()
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Result
import Common.PrettyPrint

data ApplMode = OnlyArg | TopLevel 

mkTypeConstrAppls :: ApplMode -> Type -> ReadR TypeMap Type
mkTypeConstrAppls _ t@(TypeName _ _ _) = 
       return t 

mkTypeConstrAppls m (TypeAppl t1 t2) = 
    do t3 <- mkTypeConstrAppls m t1
       t4 <- mkTypeConstrAppls OnlyArg t2
       return $ TypeAppl t3 t4 

mkTypeConstrAppls _ (TypeToken t) = 
    do let i = simpleIdToId t
       tk <- ask
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
       tk <- ask
       let mk = getKind tk i
	   n = case mk of Just k -> TypeName i k 0
			  _ -> t
	   ds = [Diag Error ("illegal type: " ++ showPretty t "")
		$ posOfType t]
       if null ts then return n
	  else if null $ tail ts 
	       then return $ case b of 
			   Parens -> head args 
			   _ -> TypeAppl n (head args)
	       else do lift $ Result (case m of
			      TopLevel -> ds
			      OnlyArg -> case b of 
						Parens -> []
						_ -> ds) 
					     $ Just $ BracketType b args ps

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

expandApplKind :: Class -> ReadR ClassMap Kind
expandApplKind c = 
    case c of
    Intersection s _ -> if Set.isEmpty s then return star else
        do k <- anaClassId  $ Set.findMin s
	   case k of 
		  ExtClass c2 _ _ -> expandApplKind c2
		  _ -> return k
    _ -> return star

inferKind :: Type -> ReadR (ClassMap, TypeMap) Kind
inferKind (TypeName i k _) = do j <- withReadR snd $ getIdKind i
				withReadR fst $ checkKinds (posOfId i) k j
				return j

inferKind (TypeAppl t1 t2) = 
    do mk1 <- inferKind t1 
       case mk1 of 
		KindAppl k1 k2 _ -> do checkKind t2 k1
				       return k2
		ExtClass c _ _ -> 
			   do k <- withReadR fst $ expandApplKind c 
			      case k of
			            KindAppl k1 k2 _ -> do checkKind t2 k1
							   return k2
				    _ -> do lift $ Result 
					       [mkDiag Error 
						"incompatible kind of type" 
						t1] Nothing

inferKind (FunType t1 _ t2 _) = 
    do checkKind t1 star 
       checkKind t2 star
       return star 
inferKind (ProductType ts _) = 
    do ms <- mapM ( \ t -> checkKind t star) ts 
       return star 
inferKind (LazyType t _) = 
    do checkKind t star
       return star 
inferKind (TypeToken t) = withReadR snd $ getIdKind $ simpleIdToId t
inferKind (KindedType t k _) =
    do checkKind t k
       return k
inferKind t =
    lift $ Result [mkDiag Error "unresolved type" t] Nothing

checkKind :: Type -> Kind -> ReadR (ClassMap, TypeMap) ()
checkKind t j = do
	k <- inferKind t 
	withReadR fst $ checkKinds (posOfType t) j k

getIdKind :: Id -> ReadR TypeMap Kind
getIdKind i = 
    do tk <- ask
       let m = getKind tk i
       case m of
	    Nothing -> lift $ Result [mkDiag Error "undeclared type" i]
                          Nothing
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

anaType :: Type -> ReadR (ClassMap, TypeMap) (Kind, Type)
anaType t = 
    do newT <- withReadR snd $ mkTypeConstrAppls TopLevel t
       k <- inferKind newT
       return (k, newT)

mkBracketToken :: BracketKind -> [Pos] -> [Token]
mkBracketToken k ps = 
    if null ps then mkBracketToken k [nullPos]
       else zipWith Token ((\ (o,c) -> [o,c]) $ getBrackets k) 
		[head ps, last ps] 


