
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

type inference 

-}

module HasCASL.TypeCheck where

import HasCASL.Unify 
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.MixAna
import qualified Common.Lib.Map as Map
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.Lib.State
import Data.Maybe


aVar :: Id
aVar = simpleIdToId $ mkSimpleId "a"
aType :: Type
aType = TypeName aVar star 1

bindA :: Type -> TypeScheme
bindA ty = TypeScheme [TypeArg aVar star Other []] ([] :=> ty) []

eqType, logType, defType, notType, ifType :: TypeScheme
eqType = bindA $ 
	  FunType (ProductType [aType, aType] [])
	  PFunArr logicalType []
logType = simpleTypeScheme $ 
	  FunType (ProductType [logicalType, logicalType] [])
	  PFunArr logicalType []
defType = bindA $ FunType aType PFunArr logicalType []
notType = simpleTypeScheme $ FunType logicalType PFunArr logicalType []

ifType = bindA $ 
	  FunType (ProductType [logicalType, aType, aType] [])
	  PFunArr aType []

bList :: [(Id, TypeScheme)]
bList = (defId, defType) : (notId, notType) : (ifThenElse, ifType) :
        map ( \ e -> (e, eqType)) [eqId, exEq] ++
	map ( \ o -> (o, logType)) [andId, orId, eqvId, implId]
	    

addUnit :: TypeMap -> TypeMap
addUnit = let TypeName i k _ = logicalType in 
		 Map.insertWith ( \ _ old -> old) i
			 (TypeInfo k [] [] NoTypeDefn)

addOps :: Assumps -> Assumps
addOps as = foldr ( \ (i, sc) m -> 
		 Map.insertWith ( \ _ old -> old) i
		 (OpInfos [OpInfo sc [] NoOpDefn]) m) as bList

resolveTerm :: GlobalAnnos -> Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm ga mt trm = do
    mtrm <- resolve ga trm
    case mtrm of 
	      Nothing -> return Nothing
	      Just t -> typeCheck mt t 


mUnifySc :: Maybe Type -> OpInfo
	 -> State Env (Maybe (Subst, Type, OpInfo))
mUnifySc mt oi = do
     tm <- gets typeMap
     ty <- toEnvState $ freshInst $ opType oi
     let Result ds ms = mUnify tm mt ty
     addDiags ds		 
     case ms of Nothing -> return Nothing
		Just s -> return $ Just (s, subst s ty, oi)

checkList :: [Type] -> [Term] -> State Env [(Subst, [Type], [Term])]
checkList [] [] = return [(eps, [], [])]
checkList (ty : rty) (trm : rt) = do 
      fts <- infer (Just ty) trm
      combs <- mapM ( \ (sf, tyf, tf) -> do
		      rts <- checkList (map (subst sf) rty) rt
		      mapM ( \ (sr, tys, tts) -> 
			     return (compSubst sf sr,
				     subst sr tyf : tys,
				     tf : tts)) rts) fts
      return $ concat combs
checkList _ _ = error "checkList"

typeCheck :: Maybe Type -> Term -> State Env (Maybe Term)
typeCheck mt trm = 
    do alts <- infer mt trm
       if null alts then 
	  do addDiags [mkDiag Error "no typing for" trm]
	     return Nothing
	  else if null $ tail alts then
	       let (_,_,t) = head alts in
		   return $ Just t
	  else do addDiags [Diag Error 
			 ("ambiguous typings \n\t" ++
			  showSepList (showString "\n\t") 
			  showPretty (take 5 $ map ( \ (_,_,t) -> t) alts) "")
			    $ posOfTerm trm]
	          return Nothing

freshTypeVar :: State Env Type		  
freshTypeVar = do var <- toEnvState freshVar 
		  return $ TypeName var star 1

freshVars :: [a] -> State Env [Type]
freshVars l = mapM (const freshTypeVar) l

infer :: Maybe Type -> Term -> State Env [(Subst, Type, Term)]
infer mt trm = do
    tm <- gets typeMap
    as <- gets assumps
    case trm of 
        QualVar v t ps -> do 
	    let Result ds ms = mUnify tm mt t
	    addDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> let ty = (subst s t) in 
			      return [(s, ty, QualVar v ty ps)] 
	QualOp io sc ps -> do
	    ty <- toEnvState $ freshInst sc
	    let Result ds ms = mUnify tm mt ty
	    addDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> return [(s, subst s ty, QualOp io sc ps)]
	ResolvedMixTerm i ts ps ->
	    if null ts then do 
	       let ois = opInfos $ Map.findWithDefault (OpInfos []) i as
	       mls <- mapM (mUnifySc mt) ois
	       let ls = catMaybes mls
	       if null ls then do addDiags [mkDiag Error "no match for" i]
				  return []
	          else return $ map ( \ (s, ty, oi) -> 
			      case opDefn oi of
			      VarDefn -> (s, ty, QualVar i ty ps)
			      _ -> (s, ty, QualOp (InstOpId i [] [])
						  (opType oi) ps)) ls
	    else infer mt $ ApplTerm (ResolvedMixTerm i [] ps)
		 (if isSingle ts then head ts else TupleTerm ts ps) ps
	ApplTerm t1 t2 ps -> do 
	    aty <- freshTypeVar
	    rty <- case mt of 
		  Nothing -> freshTypeVar
		  Just ty -> return ty
	    ops <- infer (Just $ FunType aty PFunArr rty []) t1
	    combs <- mapM ( \ (sf, _, tf) -> do 
		   args <- infer (Just $ subst sf aty) t2 
		   return $ map ( \ (sa, _, ta) -> 
			  (compSubst sf sa, 
			   subst sa (subst sf rty), 
			   ApplTerm tf ta ps)) args) ops
	    let res = concat combs 
	    if null res then 
	       do addDiags [mkDiag Error "no type match for" trm]
		  return res
	       else  return res
	TupleTerm ts ps -> do
	     vs <- freshVars ts
	     let pt = ProductType vs []
	         Result ds ms = mUnify tm mt pt
	     addDiags ds
	     case ms of 
		     Nothing -> return []
		     Just s  -> do 
                         ls <- checkList (subst s vs) ts 
			 return $ map ( \ (su, tys, trms) ->
                                   (compSubst s su, ProductType tys ps, 
				    TupleTerm trms ps)) ls
	TypedTerm t qual ty ps -> do 
	    case qual of 
		OfType -> do
		    let Result ds ms = mUnify tm mt ty
		    addDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer (Just $ subst s ty) t 
			    return $ map ( \ (s2, typ, tr) -> 
				(compSubst s s2, typ, 
				 TypedTerm tr qual ty ps)) rs
		InType -> do 
		    let Result ds ms = mUnify tm mt logicalType
		    addDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer Nothing t 
			    return $ map ( \ (s2, _, tr) -> 
				(compSubst s s2, logicalType, 
				 TypedTerm tr qual ty ps)) rs
		AsType -> do
		    let Result ds ms = mUnify tm mt ty
		    addDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer Nothing t 
			    return $ map ( \ (s2, _, tr) -> 
				(compSubst s s2, subst s2 ty, 
				 TypedTerm tr qual ty ps)) rs
	QuantifiedTerm quant decls t ps -> do
	    mapM_ addGenVarDecl decls
	    let Result ds ms = mUnify tm mt logicalType
	    addDiags ds
	    case ms of 
		Nothing -> return []
		Just _ -> do 
		    rs <- infer (Just logicalType) t 
		    putAssumps as
		    return $ map ( \ (s, typ, tr) -> 
			(s, typ, QuantifiedTerm quant decls tr ps)) rs
	_ -> do ty <- freshTypeVar
		return [(eps, ty, trm)]
                
{-
Quantifier [GenVarDecl] Term [Pos]
          -- pos quantifier, ";"s, dot
	  -- only "forall" may have a TypeVarDecl
	  | LambdaTerm [Pattern] Partiality Term [Pos]
          -- pos "\", dot (plus "!") 
	  | CaseTerm Term [ProgEq] [Pos]
	  -- pos "case", "of", "|"s 
	  | LetTerm [ProgEq] Term [Pos]
-}



