{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)
    
analyse alternatives of data types

-}

module HasCASL.DataAna where

import HasCASL.As
import HasCASL.AsUtils
import Common.Id
import Common.Result
import HasCASL.Le
import Data.Maybe
import HasCASL.TypeAna
import HasCASL.Reader

anaAlts :: Type -> [Alternative] -> ReadR (ClassMap, TypeMap) [AltDefn]
anaAlts dt alts = do l <- foldReadR (anaAlt dt) alts
		     lift $ Result (checkUniqueness $ map 
				    ( \ (Construct i _ _ _) -> i) l) 
				    $ Just l

anaAlt :: Type -> Alternative -> ReadR (ClassMap, TypeMap) AltDefn 
anaAlt _ (Subtype ts ps) = 
    do kts <- mapM anaType $ map ( \ t -> (star, t)) ts
       mapM ( \ (ki, ti) -> checkKindsR ti star ki) kts
       lift $ Result [Diag Warning "data subtype ignored" $ firstPos ts ps]
	    $ Nothing 
anaAlt dt (Constructor i cs p _) = 
    do newCs <- mapM (anaComp i dt) $ zip cs $ map (:[]) [1..]
       let sels = concatMap snd newCs
	   con = Construct i (map fst newCs) p sels
	   -- check for disjoint selectors 
       lift $ Result (checkUniqueness $ map ( \ (Select s _ _) -> s ) sels)
	    $ Just con


getConstrType :: Type -> Partiality -> [Type] -> Type
getConstrType dt p = addPartiality p .
		       foldr ( \ c r -> FunType c FunArr r [] ) dt 


addPartiality :: Partiality -> Type -> Type
addPartiality Total t = t		 
addPartiality Partial t = makePartial t		 

makePartial :: Type -> Type
makePartial t =
    case t of 
	   FunType t1 a t2 ps ->
	       case t2 of 
		       FunType _ _ _ _ -> FunType t1 a (makePartial t2) ps
		       _ -> FunType t1 PFunArr t2 ps
	   _ -> LazyType t []  

anaComp :: Id -> Type -> (Components, [Int]) 
	-> ReadR (ClassMap, TypeMap) (Type, [Selector]) 
anaComp _ _ (Selector s p t _ _, _) =
    do (k, ct) <- anaType (star, t) 
       checkKindsR t star k
       return (ct, [Select s ct p])
anaComp con rt (NoSelector t, i) =
    do (k, ct) <- anaType (star, t) 
       checkKindsR t star k
       return (ct, [Select (simpleIdToId $ mkSimpleId 
			    ("%(" ++ showPretty rt "." ++ 
			     showId con ".sel_" ++ show i ++ ")%"))
		    ct Partial])

anaComp con rt (NestedComponents cs ps, i) =
    do newCs <- mapM (anaComp con rt) $ zip cs $ map (:i) [1..]
       return (ProductType (map fst newCs) ps,
	       concatMap snd newCs)

getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p rt = addPartiality p $ FunType dt FunArr rt []
