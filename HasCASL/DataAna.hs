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

import Data.Maybe

import Common.Id
import Common.Result
import qualified Common.Lib.Set as Set

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.AsUtils
import HasCASL.Unify

anaAlts :: [(Id, Type)] -> Type -> [Alternative] -> TypeMap -> Result [AltDefn]
anaAlts tys dt alts tm = 
    do l <- mapM (anaAlt tys dt tm) alts
       Result (checkUniqueness $ catMaybes $ 
	       map ( \ (Construct i _ _ _) -> i) l) $ Just ()
       return l

anaAlt :: [(Id, Type)] -> Type -> TypeMap -> Alternative -> Result AltDefn 
anaAlt _ _ tm (Subtype ts _) = 
    do l <- mapM ( \ t -> anaType (Just star, t) tm) ts
       return $ Construct Nothing (map snd l) Partial []
anaAlt tys dt tm (Constructor i cs p _) = 
    do newCs <- mapM (anaComps tys dt tm) cs
       let sels = map snd newCs
       Result (checkUniqueness $ catMaybes $ 
		map ( \ (Select s _ _) -> s ) $ concat sels) $ Just ()
       return $ Construct (Just i) (map fst newCs) p sels

anaComps :: [(Id, Type)] -> Type -> TypeMap -> [Component]
	 -> Result (Type, [Selector]) 
anaComps tys rt tm cs =
    do newCs <- mapM (anaComp tys rt tm) cs
       return (mkProductType (map fst newCs) [], map snd newCs)

anaComp :: [(Id, Type)] -> Type -> TypeMap -> Component 
	-> Result (Type, Selector)
anaComp tys rt tm (Selector s p t _ _) =
    do ct <- anaCompType tys rt t tm
       return (ct, Select (Just s) ct p)
anaComp tys rt tm (NoSelector t) =
    do ct <- anaCompType tys rt t tm
       return  (ct, Select Nothing ct Partial)

getSelType :: Type -> Partiality -> Type -> Type
getSelType dt p rt = (case p of 
    Partial -> addPartiality [dt]
    Total -> id) $ FunType dt FunArr rt []

anaCompType :: [(Id, Type)] -> Type -> Type -> TypeMap -> Result Type
anaCompType tys dt t tm = do
    (_, ct) <- anaType (Just star, t) tm
    ct2 <- unboundTypevars (varsOf dt) ct
    mapM (checkMonomorphRecursion ct2 tm) tys
    return ct2
 
checkMonomorphRecursion :: Type	-> TypeMap -> (Id, Type) -> Result ()
checkMonomorphRecursion t tm (i, rt) = 
    if occursIn tm i $ unalias tm t then 
       if equalSubs tm t rt then return ()
       else Result [Diag Error  ("illegal polymorphic recursion" 
				 ++ expected rt t) $ getMyPos t] Nothing
    else return ()

unboundTypevars :: Set.Set TypeArg -> Type -> Result Type
unboundTypevars args ct = 
    let restVars = varsOf ct Set.\\ args in
    if Set.isEmpty restVars then return ct
       else Result [mkDiag Error ("unbound type variable(s)\n\t"
				  ++ showSepList ("," ++) showPretty 
				  (Set.toList restVars) " in") ct] Nothing
