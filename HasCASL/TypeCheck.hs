
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
import HasCASL.Le
import HasCASL.MixAna
import qualified Common.Lib.Map as Map
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.Lib.State
import Common.PrettyPrint
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
addUnit tm = foldr ( \ (i, k, d) m -> 
		 Map.insertWith ( \ _ old -> old) i
			 (TypeInfo k [] [] d) m) tm
	      [(simpleIdToId $ mkSimpleId "Unit",
	        star, AliasTypeDefn $ simpleTypeScheme logicalType), 
	       (simpleIdToId $ mkSimpleId "Pred", 
		KindAppl star star [],
		AliasTypeDefn defType)]

addOps :: Assumps -> Assumps
addOps as = foldr ( \ (i, sc) m -> 
		 Map.insertWith ( \ _ old -> old) i
		 (OpInfos [OpInfo sc [] NoOpDefn]) m) as bList

resolveTerm :: GlobalAnnos -> Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm ga mt trm = do
    mtrm <- resolve ga trm
    case mtrm of 
	      Nothing -> return Nothing
	      Just t -> typeCheck infer mt t 

checkPattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
checkPattern ga pat = do
    mPat <- resolvePattern ga pat
    case mPat of 
	      Nothing -> return Nothing
	      Just p -> do 
		  (np, _) <- extractBindings p 
		  typeCheck inferPat Nothing np

mUnifySc :: Maybe Type -> OpInfo
	 -> State Env (Maybe (Subst, Type, OpInfo))
mUnifySc mt oi = do
     tm <- gets typeMap
     ty <- toEnvState $ freshInst $ opType oi
     let Result ds ms = mUnify tm mt ty
     addDiags ds		 
     case ms of Nothing -> return Nothing
		Just s -> return $ Just (s, subst s ty, oi)

checkList :: (Maybe Type -> a -> State Env [(Subst, Type, a)])
	  -> [Type] -> [a] -> State Env [(Subst, [Type], [a])]
checkList _ [] [] = return [(eps, [], [])]
checkList inf (ty : rty) (trm : rt) = do 
      fts <- inf (Just ty) trm
      combs <- mapM ( \ (sf, tyf, tf) -> do
		      rts <- checkList inf (map (subst sf) rty) rt
		      return $ map ( \ (sr, tys, tts) -> 
			     (compSubst sf sr,
				     subst sr tyf : tys,
				     tf : tts)) rts) fts
      return $ concat combs
checkList _ _ _ = error "checkList"

typeCheck :: (PosItem a, PrettyPrint a) => 
	     (Maybe Type -> a -> State Env [(Subst, Type, a)])
	  -> Maybe Type -> a -> State Env (Maybe a)
typeCheck inf mt trm = 
    do alts <- inf mt trm
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
			    $ getMyPos trm]
	          return Nothing

freshTypeVar :: State Env Type		  
freshTypeVar = do var <- toEnvState freshVar 
		  return $ TypeName var star 1

freshVars :: [a] -> State Env [Type]
freshVars l = mapM (const freshTypeVar) l

inferAppl :: (PosItem a, PrettyPrint a) => 
	     (Maybe Type -> a -> State Env [(Subst, Type, a)])
	  -> (a -> a -> a)   
          -> Maybe Type -> a  -> a -> State Env [(Subst, Type, a)]
inferAppl inf appl mt t1 t2 = do
	    aty <- freshTypeVar
	    rty <- case mt of 
		  Nothing -> freshTypeVar
		  Just ty -> return ty
	    ops <- inf (Just $ FunType aty PFunArr rty []) t1
	    combs <- mapM ( \ (sf, _, tf) -> do 
		   args <- inf (Just $ subst sf aty) t2 
		   return $ map ( \ (sa, _, ta) -> 
			  (compSubst sf sa, 
			   subst sa (subst sf rty), 
			   appl tf ta)) args) ops
	    let res = concat combs 
	    if null res then 
	       do addDiags [mkDiag Error "no type match for" (appl t1 t2)]
		  return res
	       else  return res

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
	ApplTerm t1 t2 ps -> inferAppl infer ( \ x y -> ApplTerm x y ps) 
			     mt t1 t2
	TupleTerm ts ps -> do
	     vs <- freshVars ts
	     let pt = ProductType vs []
	         Result ds ms = mUnify tm mt pt
	     addDiags ds
	     case ms of 
		     Nothing -> return []
		     Just s  -> do 
                         ls <- checkList infer (subst s vs) ts 
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
        LambdaTerm pats part resTrm ps -> do 
	    vs <- freshVars pats
	    rty <- freshTypeVar
	    let fty l = if null l then rty else 
			FunType (head l) PFunArr (fty $ tail l) []
		myty = fty vs
                Result ds ms = mUnify tm mt myty
	    addDiags ds 
	    case ms of 
	        Nothing -> return []
		Just s -> do 
                    ls <- checkList inferPat (subst s vs) pats
		    rs <- mapM ( \ ( s2, _, nps) -> do
		       bs <- mapM extractBindings nps
		       mapM_ addVarDecl (concatMap snd bs)
		       let newS = compSubst s s2 
		       es <- infer (Just $ subst newS rty) resTrm
                       putAssumps as
		       return $ map ( \ (s3, _, rtm) -> 
				      (compSubst newS s3,
				       subst s3 (subst newS myty), 
				       LambdaTerm nps part rtm ps)) es) ls
		    return $ concat rs 
	CaseTerm ofTrm eqs ps -> do 
	    ts <- infer Nothing ofTrm
	    rty <- case mt of 
		   Nothing -> freshTypeVar
		   Just ty -> return ty
	    if null ts then addDiags [mkDiag Error 
				      "unresolved of-term in case" ofTrm]
	        else return () 
	    rs <- mapM ( \ (s1, oty, otrm) -> do 
		 es <- inferCaseEqs oty (subst s1 rty) eqs
		 return $ map ( \ (s2, _, ty, nes) ->
				(compSubst s1 s2, ty, 
				 CaseTerm otrm nes ps)) es) ts
	    return $ concat rs
        LetTerm eqs inTrm ps -> do 
	    vs <- freshVars eqs
	    es <- checkList inferLetEq vs eqs
	    rs <- mapM ( \ (s1, _, nes) -> do 
	       ts <- infer mt inTrm 
	       return $ map ( \ (s2, ty, nt) -> 
 			      (compSubst s1 s2, ty, 
			       LetTerm nes nt ps)) ts) es
	    putAssumps as
	    return $ concat rs
    	_ -> do ty <- freshTypeVar
		addDiags [mkDiag Error "unexpected term" trm]
		return [(eps, ty, trm)]


inferLetEq :: Maybe Type -> ProgEq -> State Env [(Subst, Type, ProgEq)]
inferLetEq _ (ProgEq pat trm ps) = do
    ts <- infer Nothing trm
    nps <- mapM ( \ (s2, tyt, nt) -> do
           pps <- inferPat (Just tyt) pat		     
           mapM ( \ (s3, _, pp) -> do
               (_, nbs) <- extractBindings pp 
               mapM_ addVarDecl nbs
	       return (compSubst s2 s3, tyt, ProgEq pp nt ps)) pps) ts
    return $ concat nps

                
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

-- | type check patterns
inferPat :: Maybe Type -> Pattern -> State Env [(Subst, Type, Pattern)]
inferPat mt pat = do 
    tm <- gets typeMap
    as <- gets assumps
    case pat of
	PatternVar (VarDecl v t sk ps) -> do  
	    let Result ds ms = mUnify tm mt t
	    addDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> do let ty = (subst s t) 
			     return [(s, ty, PatternVar (VarDecl v ty sk ps))]
	PatternConstr io sc qs -> do
	    ty <- toEnvState $ freshInst sc
	    let Result ds ms = mUnify tm mt ty
	    addDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> return [(s, subst s ty, PatternConstr io sc qs)]
	ResolvedMixPattern i ts ps ->
	    if null ts then do 
	       let ois = opInfos $ Map.findWithDefault (OpInfos []) i as
	       mls <- mapM (mUnifySc mt) ois
	       let ls = catMaybes mls
	       if null ls then do addDiags [mkDiag Error "no match for" i]
				  return []
	          else return $ map ( \ (s, ty, oi) -> 
			      case opDefn oi of
			      VarDefn -> (s, ty, 
					  PatternVar $ VarDecl i ty Other ps)
			      _ -> (s, ty, PatternConstr (InstOpId i [] [])
						  (opType oi) ps)) ls
	    else inferPat mt $ ApplPattern (ResolvedMixPattern i [] ps)
		 (if isSingle ts then head ts else TuplePattern ts ps) ps
	ApplPattern p1 p2 ps -> inferAppl inferPat 
				( \ x y -> ApplPattern x y ps) mt p1 p2
	TuplePattern ts ps -> do
	     vs <- freshVars ts
	     let pt = ProductType vs []
	         Result ds ms = mUnify tm mt pt
	     addDiags ds
	     case ms of 
		     Nothing -> return []
		     Just s  -> do 
                         ls <- checkList inferPat (subst s vs) ts 
			 return $ map ( \ (su, tys, trms) ->
                                   (compSubst s su, ProductType tys ps, 
				    TuplePattern trms ps)) ls
	TypedPattern p ty ps -> do 
		    let Result ds ms = mUnify tm mt ty
		    addDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- inferPat (Just $ subst s ty) p
			    return $ map ( \ (s2, typ, tr) -> 
				(compSubst s s2, typ, 
				 TypedPattern tr ty ps)) rs
	_ -> do ty <- freshTypeVar
		addDiags [mkDiag Error "unexpected pattern" pat]
		return [(eps, ty, pat)] 

inferCaseEq :: Type -> Type -> ProgEq 
	    -> State Env [(Subst, Type, Type, ProgEq)]
inferCaseEq pty tty (ProgEq pat trm ps) = do
   as <- gets assumps
   let newAs = filterAssumps ( \ o -> case opDefn o of
					      ConstructData _ -> True
					      VarDefn -> True
					      _ -> False) as
   putAssumps newAs
   pats <- inferPat (Just pty) pat 
   putAssumps as
   if null pats then addDiags [mkDiag Error "unresolved case pattern" pat]
      else return ()
   es <- mapM ( \ (s, ty, p) -> do 
		(_, bs) <- extractBindings p
		mapM_ addVarDecl bs
		ts <- infer (Just $  subst s tty) trm
		putAssumps as
		return $ map ( \ (st, tyt, t) -> 
		       (compSubst s st, subst st ty, tyt, 
			ProgEq p t ps)) ts) pats
   return $ concat es

inferCaseEqs :: Type -> Type -> [ProgEq] 
	    -> State Env [(Subst, Type, Type, [ProgEq])]
inferCaseEqs pty tTy [] = return [(eps, pty, tTy, [])]
inferCaseEqs pty tty (eq:eqs) = do 
  fts <- inferCaseEq pty tty eq
  rs <- mapM (\ (_, pty1, tty1, ne) -> do 
	      rts <- inferCaseEqs pty1 tty1 eqs
	      return $ map ( \ (s2, pty2, tty2, nes) ->
			     (s2, pty2, tty2, ne:nes)) rts) fts
  return $ concat rs

