
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

type inference 

-}

module HasCASL.TypeCheck where

import HasCASL.Unify 
import HasCASL.AsUtils
import HasCASL.Merge
import HasCASL.VarDecl
import HasCASL.As
import HasCASL.Le
import HasCASL.MixAna
import HasCASL.MapTerm
import HasCASL.Constrain

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Id
import Common.Result
import Common.GlobalAnnotations
import Common.Lib.State
import Data.Maybe

substTerm :: Subst -> Term -> Term
substTerm s = mapTerm (id, subst s)

resolveTerm :: GlobalAnnos -> Maybe Type -> Term -> State Env (Maybe Term)
resolveTerm ga mt trm = do
    mtrm <- resolve ga trm
    case mtrm of 
	      Nothing -> return Nothing
	      Just t -> typeCheck mt t 

checkPattern :: GlobalAnnos -> Pattern -> State Env (Maybe Pattern)
checkPattern ga pat = do
    mPat <- resolvePattern ga pat
    case mPat of 
	      Nothing -> return Nothing
	      Just p -> do 
		  np <- anaPattern p 
		  typeCheck Nothing np

freshInstList :: TypeScheme -> State Int (Type, Constraints, [Type])
freshInstList (TypeScheme tArgs (_ :=> t) _) = 
    do m <- mkSubst tArgs 
       return ( subst (Map.fromList m) t
	      , Set.fromList $ map ( \ (TypeArg _ k _ _, ty) 
				     -> Kinding ty k) m
	      ,	map snd m)

instantiate :: OpInfo -> State Env (Type, [Type], Constraints, OpInfo)
instantiate oi = do
     (ty, cs, inst) <- toEnvState $ freshInstList $ opType oi
     return (ty, inst, cs, oi)

lookupError :: Type -> [OpInfo] -> String
lookupError ty ois = 
    "  with type: " ++  showPrettyWithPos ty "\n"
    ++ "  known types:\n    " ++
       showSepList ("\n    "++) (showPrettyWithPos . opType) ois "" 

checkList :: [Maybe Type] -> [Term] 
	  -> State Env [(Subst, Constraints, [Type], [Term])]
checkList [] [] = return [(eps, noC, [], [])]
checkList (ty : rty) (trm : rt) = do 
      fts <- infer ty trm
      combs <- mapM ( \ (sf, cs, tyf, tf) -> do
		      rts <- checkList (map (fmap (subst sf)) rty) rt
		      return $ map ( \ (sr, cr, tys, tts) ->
			     (compSubst sf sr, 
			      substC sr cs `joinC` cr,
			      subst sr tyf : tys,
				     tf : tts)) rts) fts
      return $ concat combs
checkList _ _ = error "checkList"

typeCheck :: Maybe Type -> Term -> State Env (Maybe Term)
typeCheck mt trm = 
    do alts <- infer mt trm
       let p = getMyPos trm
       if null alts then 
	  do addDiags [mkDiag Error "no typing for" trm]
	     return Nothing
	  else if null $ tail alts then do
	       tm <- gets typeMap
	       let (s, cs, _, t) = head alts
		   (ds, rcs) = simplify tm noC cs 
		   es = map ( \ d -> d {diagKind = Hint, diagPos = p}) ds
	       addDiags(es ++ map (	\ c -> 
		      mkDiag Error "unresolved constraint" c)
	              (Set.toList rcs))
	       return $ Just $ substTerm s t
	  else do addDiags [Diag Error 
			 ("ambiguous typings \n  " ++
			  showSepList ("\n  "++) 
			  showPrettyWithPos 
			  (take 5 $ map ( \ (s,_,_,t) -> 
					  substTerm s t) alts) "")
			    p]
	          return Nothing

freshTypeVar :: Pos -> State Env Type		  
freshTypeVar p = 
    do var <- toEnvState $ freshVar p
       return $ TypeName var star 1

freshVars :: [Term] -> State Env [Type]
freshVars l = mapM (freshTypeVar . posOfTerm) l

inferAppl :: [Pos] -> Maybe Type -> Term  -> Term 
	  -> State Env [(Subst, Constraints, Type, Term)]
inferAppl ps mt t1 t2 = do
	    aty <- freshTypeVar $ posOfTerm t2
	    rty <- case mt of 
		  Nothing -> freshTypeVar $ posOfTerm t1
		  Just ty -> return ty
	    ops <- infer (Just $ FunType aty PFunArr rty []) t1
	    combs <- mapM ( \ (sf, cs, _, tf) -> do 
		   args <- infer (Just $ subst sf aty) t2 
		   return $ map ( \ (sa, cr, _, ta) -> 
				  let s = compSubst sf sa in
			  (s, substC sa cs `joinC` cr, 
			   subst s rty, 
			   ApplTerm tf ta ps)) args) ops
	    let res = concat combs 
		origAppl = ApplTerm t1 t2 ps
	    if null res then 
	       addDiags [case mt of 
		       Nothing -> mkDiag Error
				  "wrongly typed application" origAppl
		       Just ty -> mkDiag Hint 
			    ("wrong result type "
			    ++ showPrettyWithPos ty "\n  for application")
		            origAppl]
	       else return ()
	    return res

infer :: Maybe Type -> Term -> State Env [(Subst, Constraints, Type, Term)]
infer mt trm = do
    tm <- gets typeMap
    let mUnify = mgu tm mt . Just
	uniDiags = addDiags . map (improveDiag trm)
    as <- gets assumps
    case trm of 
        QualVar (VarDecl v t ok ps)  -> do 
	    let Result ds ms = mUnify t
	    uniDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> let ty = subst s t in 
		    return [(s, noC, ty, QualVar $ VarDecl v ty ok ps)] 
	QualOp b (InstOpId i ts qs) sc ps -> do
	    (ty, cs, inst) <- toEnvState $ freshInstList sc
	    let Result ds ms = mgu tm (mt, if null ts then inst else ts) 
			       (Just ty, inst)
	    uniDiags ds 
	    case ms of 
		Nothing -> return []
		Just s -> return [(s, substC s cs, subst s ty, QualOp b 
				   (InstOpId i (map (subst s) inst) qs)
				   sc ps)]
	ResolvedMixTerm i ts ps ->
	    if null ts then do 
	       let ois = opInfos $ Map.findWithDefault (OpInfos []) i as
	       insts <- mapM instantiate ois 
	       ls <- case mt of 
		     Nothing -> return $ map ( \ (ty, is, cs, oi) 
					      -> (eps, ty, is, cs, oi)) insts
		     Just inTy -> do 
                         let rs = concatMap ( \ (ty, is, cs, oi) ->
				  let Result _ ms = mgu tm inTy ty in
				  case ms of Nothing -> []
					     Just s -> [(s, ty
							, map (subst s) is
							, substC s cs
							, oi)]) insts
			 if null rs then 
			    addDiags [Diag Hint
			       ("no type match for: " ++ showId i "\n"
				++ lookupError inTy ois)
			       (posOfId i) ]
		            else return ()
			 return rs
	       return $ map ( \ (s, ty, is, cs, oi) -> 
			      case opDefn oi of
			      VarDefn -> (s, cs, ty, QualVar $ 
					  VarDecl i ty Other ps)
			      x -> let br = case x of
				            NoOpDefn b -> b
				            Definition b _ -> b
				            _ -> Op in 
				      (s, cs, ty, 
				       QualOp br (InstOpId i is [])
						  (opType oi) ps)) ls
	    else infer mt $ ApplTerm (ResolvedMixTerm i [] ps)
		 (mkTupleTerm ts ps) ps
	ApplTerm t1 t2 ps -> inferAppl ps
			     mt t1 t2
	TupleTerm ts ps -> 
	    case mt of 
            Nothing -> do 		    
                ls <- checkList (map (const Nothing) ts) ts 
		return $ map ( \ (su, cs, tys, trms) ->
                                   (su, cs, mkProductType tys ps, 
				    mkTupleTerm trms ps)) ls
	    Just ty -> do 
	        vs <- freshVars ts
	        let pt = mkProductType vs []
	            Result ds ms = mgu tm ty pt
		uniDiags ds
	        case ms of 
		     Nothing -> return []
		     Just s  -> do 
                         ls <- checkList (map (Just . subst s) vs) ts 
			 return $ map ( \ (su, cs, tys, trms) ->
					(compSubst s su, substC s cs, 
					 mkProductType tys ps, 
					 mkTupleTerm trms ps)) ls
	TypedTerm t qual ty ps -> do 
	    case qual of 
		OfType -> do
		    let Result ds ms = mUnify ty
		    uniDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer (Just $ subst s ty) t 
			    return $ map ( \ (s2, cs, typ, tr) -> 
				(compSubst s s2, substC s cs, typ, 
				 TypedTerm tr qual ty ps)) rs
		InType -> do 
		    let Result ds ms = mUnify logicalType
		    uniDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer Nothing t -- Nothing 
			    return $ map ( \ (s2, cs, _, tr) -> 
				(compSubst s s2, substC s cs, logicalType, 
				 TypedTerm tr qual ty ps)) rs
		AsType -> do
		    let Result ds ms = mUnify ty
		    uniDiags ds
		    case ms of 
		        Nothing -> return []
			Just s -> do 
			    rs <- infer Nothing t -- Nothing
			    return $ map ( \ (s2, cs, _, tr) -> 
				(compSubst s s2, substC s cs, ty, 
				 TypedTerm tr qual ty ps)) rs
	QuantifiedTerm quant decls t ps -> do
	    mapM_ addGenVarDecl decls
	    let Result ds ms = mUnify logicalType
	    uniDiags ds
	    case ms of 
		Nothing -> return []
		Just _ -> do 
		    rs <- infer (Just logicalType) t 
		    putAssumps as
		    return $ map ( \ (s, cs, typ, tr) -> 
			(s, cs, typ, QuantifiedTerm quant decls tr ps)) rs
        LambdaTerm pats part resTrm ps -> do 
	    vs <- freshVars pats
	    rty <- freshTypeVar $ posOfTerm resTrm
	    let fty l = if null l then rty else 
			FunType (head l) PFunArr (fty $ tail l) []
		myty = fty vs
                Result ds ms = mUnify myty
	    uniDiags ds 
	    case ms of 
	        Nothing -> return []
		Just s -> do 
                    ls <- checkList (map (Just . subst s) vs) pats
		    rs <- mapM ( \ ( s2, cs, _, nps) -> do
		       mapM_ addVarDecl $ concatMap extractVars nps
		       let newS = compSubst s s2 
		       es <- infer (Just $ subst newS rty) resTrm
                       putAssumps as
		       return $ map ( \ (s3, cr, _, rtm) -> 
				      (compSubst newS s3, 
				       substC s3 cs `joinC` cr,
				       subst s3 (subst newS myty), 
				       LambdaTerm nps part rtm ps)) es) ls
		    return $ concat rs 
	CaseTerm ofTrm eqs ps -> do 
	    ts <- infer Nothing ofTrm
	    rty <- case mt of 
		   Nothing -> freshTypeVar $ posOfTerm trm
		   Just ty -> return ty
	    if null ts then addDiags [mkDiag Error 
				      "unresolved of-term in case" ofTrm]
	        else return () 
	    rs <- mapM ( \ (s1, cs, oty, otrm) -> do 
		 es <- inferCaseEqs oty (subst s1 rty) eqs
		 return $ map ( \ (s2, cr, _, ty, nes) ->
				(compSubst s1 s2, 
				 substC s2 cs `joinC` cr, ty, 
				 CaseTerm otrm nes ps)) es) ts
	    return $ concat rs
        LetTerm b eqs inTrm ps -> do 
	    es <- inferLetEqs eqs
	    rs <- mapM ( \ (s1, cs, _, nes) -> do 
	       mapM_ addVarDecl $ concatMap (\ (ProgEq p _ _) -> 
					     extractVars p) nes
	       ts <- infer mt inTrm 
	       return $ map ( \ (s2, cr, ty, nt) -> 
 			      (compSubst s1 s2, 
			       substC s2 cs `joinC` cr,
			       ty, 
			       LetTerm b nes nt ps)) ts) es
	    putAssumps as
	    return $ concat rs
	AsPattern (VarDecl v _ ok qs) pat ps -> do 
	   pats <- infer mt pat
	   return $ map ( \ (s1, cs, t1, p1) -> (s1, cs, t1, 
			  AsPattern (VarDecl v t1 ok qs) p1 ps)) pats
    	_ -> do ty <- freshTypeVar $ posOfTerm trm
		addDiags [mkDiag Error "unexpected term" trm]
		return [(eps, noC, ty, trm)]

inferLetEqs :: [ProgEq] -> State Env [(Subst, Constraints, [Type], [ProgEq])]
inferLetEqs es = do
    let pats = map (\ (ProgEq p _ _) -> p) es 
	trms = map (\ (ProgEq _ t _) -> t) es
	qs = map (\ (ProgEq _ _ q) -> q) es
    do as <- gets assumps 
       newPats <- checkList (map (const Nothing) pats) pats
       combs <- mapM ( \ (sf, _, tys, pps) -> do
	     mapM_ addVarDecl $ concatMap extractVars pps 
	     newTrms <- checkList (map Just tys) trms 
	     return $ map ( \ (sr, _, tys2, tts ) ->  
			  (compSubst sf sr, noC, tys2, 
			   zipWith3 ( \ p t q -> ProgEq (substTerm sr p) t q)
			       pps tts qs)) newTrms) newPats
       putAssumps as					   
       return $ concat combs 

inferCaseEq :: Type -> Type -> ProgEq 
	    -> State Env [(Subst, Constraints, Type, Type, ProgEq)]
inferCaseEq pty tty (ProgEq pat trm ps) = do
   as <- gets assumps
   let newAs = filterAssumps ( \ o -> case opDefn o of
					      ConstructData _ -> True
					      VarDefn -> True
					      _ -> False) as
   putAssumps newAs
   pats <- infer (Just pty) pat 
   putAssumps as
   if null pats then addDiags [mkDiag Error "unresolved case pattern" pat]
      else return ()
   es <- mapM ( \ (s, cs, ty, p) -> do 
		mapM_ addVarDecl $ extractVars p
		ts <- infer (Just $  subst s tty) trm
		putAssumps as
		return $ map ( \ (st, cr, tyt, t) -> 
		       (compSubst s st, 
			substC st cs `joinC` cr,
                        subst st ty, tyt, 
			ProgEq p t ps)) ts) pats
   return $ concat es

inferCaseEqs :: Type -> Type -> [ProgEq] 
	    -> State Env [(Subst, Constraints, Type, Type, [ProgEq])]
inferCaseEqs pty tTy [] = return [(eps, noC, pty, tTy, [])]
inferCaseEqs pty tty (eq:eqs) = do 
  fts <- inferCaseEq pty tty eq
  rs <- mapM (\ (_, cs, pty1, tty1, ne) -> do 
	      rts <- inferCaseEqs pty1 tty1 eqs
	      return $ map ( \ (s2, cr, pty2, tty2, nes) ->
			     (s2, 
			      substC s2 cs `joinC` cr,
			      pty2, tty2, ne:nes)) rts) fts
  return $ concat rs

