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
import Data.List as List

import Common.Id
import Common.Result
import Common.AS_Annotation

import HasCASL.As
import HasCASL.Le
import HasCASL.TypeAna
import HasCASL.AsUtils
import HasCASL.Builtin
import HasCASL.Unify


mkSelId :: String -> Int -> Int -> Id
mkSelId str n m = mkId [mkSimpleId (str ++ "_" ++ show n ++ "_" ++ show m)]

mkSelVar :: Int -> Int -> Type -> VarDecl
mkSelVar n m ty = VarDecl (mkSelId "x" n m) ty  Other []

genTuple :: Int -> Int -> [Selector] -> [VarDecl]
genTuple _ _ [] = [] 
genTuple n m (Select _ ty _ : sels) = 
    mkSelVar n m ty : genTuple n (m + 1) sels

genSelVars :: Int -> [[Selector]]  -> [[VarDecl]]
genSelVars _ [] = []
genSelVars n (ts:sels)  = 
    genTuple n 1 ts : genSelVars (n + 1) sels

makeSelTupleEqs :: Type -> [TypeArg] -> Term -> Int -> Int -> [Selector]
		-> [Named Term]
makeSelTupleEqs dt args ct n m (Select mi ty p : sels) = 
    (case mi of
    Nothing -> []
    Just i -> let sc = TypeScheme args ([] :=> getSelType dt p ty) [] 
		  vt = QualVar $ mkSelVar n m ty
		  eq = mkEqTerm eqId [] (mkApplTerm (mkOpTerm i sc) [ct]) vt
              in [NamedSen ("ga_select_" ++ show i) eq])
    ++ makeSelTupleEqs dt args ct n (m + 1) sels
makeSelTupleEqs _ _ _ _ _ [] = []

makeSelEqs :: Type -> [TypeArg] -> Term -> Int -> [[Selector]] 
           -> [Named Term]
makeSelEqs dt args ct n (sel:sels) = 
    makeSelTupleEqs dt args ct n 1 sel 
    ++ makeSelEqs dt args ct (n + 1) sels 
makeSelEqs _ _ _ _ _ = []

makeAltSelEqs :: Type -> [TypeArg] -> AltDefn -> [Named Term]
makeAltSelEqs dt args (Construct mc ts p sels) = 
    case mc of
    Nothing -> []
    Just c -> let sc = TypeScheme args ([] :=> getConstrType dt p ts) [] 
		  vars = genSelVars 1 sels 
		  as = map ( \ vs -> mkTupleTerm (map QualVar vs) []) vars
		  ct = mkApplTerm (mkOpTerm c sc) as
              in map (mapNamed (mkForall (map GenTypeVarDecl args
				  ++ map GenVarDecl (concat vars))))
	         $ makeSelEqs dt args ct 1 sels

makeDataSelEqs :: DataEntry -> [Named Sentence]
makeDataSelEqs (DataEntry _ i _ args alts) =
    map (mapNamed Formula) $  
    concatMap (makeAltSelEqs (typeIdToType i args star) args) alts

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
    if occursIn tm i t then 
       if equalSubs tm t rt then return ()
       else Result [Diag Error  ("illegal polymorphic recursion" 
				 ++ expected rt t) $ getMyPos t] Nothing
    else return ()

unboundTypevars :: [TypeArg] -> Type -> Result Type
unboundTypevars args ct = 
    let restVars = varsOf ct List.\\ args in
    if null restVars then return ct
       else Result [mkDiag Error ("unbound type variable(s)\n\t"
				  ++ showSepList ("," ++) showPretty 
				  restVars " in") ct] Nothing
