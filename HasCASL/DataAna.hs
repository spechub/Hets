{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable (MonadState)
    
analyse alternatives of data types

-}

module HasCASL.DataAna where

import HasCASL.As
import Common.Id
import Common.Lib.State
import Common.Result
import HasCASL.Le
import HasCASL.ClassAna
import HasCASL.TypeAna
import Data.Maybe


anaAlts :: Type -> [Alternative] -> State Env [AltDefn]
anaAlts dt alts = do ll <- mapM (anaAlt dt) alts
		     let l = concat ll
		     addDiags (checkUniqueness $ map 
				    ( \ (Construct i _ _ _) -> i) l) 
		     return l


anaAlt :: Type -> Alternative -> State Env [AltDefn] 
anaAlt _ (Subtype ts ps) = 
    do mapM_ anaStarType ts
       addDiags [Diag Warning "data subtype ignored" $ firstPos ts ps]
       return []

anaAlt dt (Constructor i cs p _) = 
    do newCs <- mapM (anaComp i dt) $ zip cs $ map (:[]) [1..]
       let mts = map fst newCs
       if all isJust mts then 
	  do let sels = concatMap snd newCs
		 con = Construct i (catMaybes mts) p sels
		 -- check for disjoint selectors 
	     addDiags (checkUniqueness $ map ( \ (Select s _ _) -> s ) sels)
	     return [con]
	  else return []

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
	-> State Env (Maybe Type, [Selector]) 
anaComp _ _ (Selector s p t _ _, _) =
    do mt <- anaStarType t
       case mt of 
           Just ct -> return (mt, [Select s ct p])
	   _ -> return (Nothing, [])
anaComp con rt (NoSelector t, i) =
    do mt <- anaStarType t
       case mt of 
           Just ct -> return (mt, [Select (simpleIdToId $ mkSimpleId 
			   ("%(" ++ showPretty rt "." ++ 
			    showId con ".sel_" ++ show i ++ ")%"))
				   ct Partial])
	   _ -> return  (Nothing, [])

anaComp con rt (NestedComponents cs ps, i) =
    do newCs <- mapM (anaComp con rt) $ zip cs $ map (:i) [1..]
       let mts = map fst newCs
       if all isJust mts then 
	  return (Just $ ProductType (catMaybes mts) ps,
		  concatMap snd newCs)
	  else return  (Nothing, [])

getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p rt = addPartiality p $ FunType dt FunArr rt []
