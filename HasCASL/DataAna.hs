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

makeSelTupleEqs :: DataPat -> Term -> Int -> Int -> [Selector] -> [Named Term]
makeSelTupleEqs dt ct n m (Select mi ty p : sels) = 
    let Result _ msc = getSelType dt p ty in
    (case (mi, msc) of
    (Just i, Just sc) -> let
		  vt = QualVar $ mkSelVar n m ty
		  eq = mkEqTerm eqId [] (mkApplTerm (mkOpTerm i sc) [ct]) vt
              in [NamedSen ("ga_select_" ++ show i) eq]
    _ -> [])
    ++ makeSelTupleEqs dt ct n (m + 1) sels
makeSelTupleEqs _ _ _ _ [] = []

makeSelEqs :: DataPat -> Term -> Int -> [[Selector]] -> [Named Term]
makeSelEqs dt ct n (sel:sels) = 
    makeSelTupleEqs dt ct n 1 sel 
    ++ makeSelEqs dt ct (n + 1) sels 
makeSelEqs _ _ _ _ = []

makeAltSelEqs :: DataPat -> AltDefn -> [Named Term]
makeAltSelEqs dt@(_, args, _) (Construct mc ts p sels) = 
    case mc of
    Nothing -> []
    Just c -> let sc = TypeScheme args ([] :=> getConstrType dt p ts) [] 
		  Result _ msc = generalize sc
		  newSc = maybe sc id msc
		  vars = genSelVars 1 sels 
		  as = map ( \ vs -> mkTupleTerm (map QualVar vs) []) vars
		  ct = mkApplTerm (mkOpTerm c newSc) as
              in map (mapNamed (mkForall (map GenTypeVarDecl args
				  ++ map GenVarDecl (concat vars))))
	         $ makeSelEqs dt ct 1 sels

makeDataSelEqs :: DataEntry -> Kind -> [Named Sentence]
makeDataSelEqs (DataEntry _ i _ args alts) k =
    map (mapNamed Formula) $  
    concatMap (makeAltSelEqs(i, args, k)) alts

anaAlts :: [DataPat] -> DataPat -> [Alternative] -> TypeMap -> Result [AltDefn]
anaAlts tys dt alts tm = 
    do l <- mapM (anaAlt tys dt tm) alts
       Result (checkUniqueness $ catMaybes $ 
	       map ( \ (Construct i _ _ _) -> i) l) $ Just ()
       return l

anaAlt :: [DataPat] -> DataPat -> TypeMap -> Alternative -> Result AltDefn 
anaAlt _ (_, args, _) tm (Subtype ts _) = 
    do l <- mapM ( \ t -> anaType (Just star, t) tm) ts
       return $ Construct Nothing (map (mkGenVars args . snd) l) Partial []
anaAlt tys dt tm (Constructor i cs p _) = 
    do newCs <- mapM (anaComps tys dt tm) cs
       let sels = map snd newCs
       Result (checkUniqueness $ catMaybes $ 
		map ( \ (Select s _ _) -> s ) $ concat sels) $ Just ()
       return $ Construct (Just i) (map fst newCs) p sels

anaComps :: [DataPat] -> DataPat -> TypeMap -> [Component]
	 -> Result (Type, [Selector]) 
anaComps tys rt tm cs =
    do newCs <- mapM (anaComp tys rt tm) cs
       return (mkProductType (map fst newCs) [], map snd newCs)

anaComp :: [DataPat] -> DataPat -> TypeMap -> Component 
	-> Result (Type, Selector)
anaComp tys rt tm (Selector s p t _ _) =
    do ct <- anaCompType tys rt t tm
       return (ct, Select (Just s) ct p)
anaComp tys rt tm (NoSelector t) =
    do ct <- anaCompType tys rt t tm
       return  (ct, Select Nothing ct Partial)

getSelType :: DataPat -> Partiality -> Type -> Result TypeScheme
getSelType dp@(_, args, _) p rt = let dt = typeIdToType dp in 
    generalize $ TypeScheme args ([] :=> (case p of 
    Partial -> addPartiality [dt]
    Total -> id) (FunType dt FunArr rt [])) []

anaCompType :: [DataPat] -> DataPat -> Type -> TypeMap -> Result Type
anaCompType tys (_, as, _) t tm = do
    (_, ct1) <- anaType (Just star, t) tm
    let ct = mkGenVars as ct1
        ds = unboundTypevars as ct 
    if null ds then return () else Result ds Nothing
    mapM (checkMonomorphRecursion ct tm) tys
    return ct
 
checkMonomorphRecursion :: Type	-> TypeMap -> DataPat -> Result ()
checkMonomorphRecursion t tm p@(i, _, _) = 
    let rt = typeIdToType p in
    if occursIn tm i t then 
       if equalSubs tm t rt then return ()
       else Result [Diag Error  ("illegal polymorphic recursion" 
				 ++ expected rt t) $ getMyPos t] Nothing
    else return ()
