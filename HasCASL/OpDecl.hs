{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

   analyse operation declarations
-}

module HasCASL.OpDecl where

import Data.Maybe

import Common.Id
import Common.AS_Annotation
import Common.Lib.State
import Common.Result
import Common.GlobalAnnotations

import HasCASL.As
import HasCASL.VarDecl
import HasCASL.Le
import HasCASL.Builtin
import HasCASL.AsUtils
import HasCASL.TypeAna
import HasCASL.TypeCheck
import HasCASL.ProgEq

anaAttr :: GlobalAnnos -> TypeScheme -> OpAttr -> State Env (Maybe OpAttr)
anaAttr ga (TypeScheme tvs ty _) (UnitOpAttr trm ps) = 
    do let mTy = case unalias ty of 
		      FunType arg _ t3 _ -> 
			  case unalias arg of 
			  ProductType [t1, t2] _ -> Just (t1,t2,t3)
			  _ -> Nothing
		      _ -> Nothing
       tm <- gets typeMap
       mapM_ (addTypeVarDecl False) tvs
       case mTy of 
	     Nothing -> do addDiags [mkDiag Error 
				     "unexpected type of operation" ty]
			   mt <- resolveTerm ga Nothing trm
			   putTypeMap tm
			   case mt of 
				   Nothing -> return Nothing
				   Just t  -> return $ Just $ UnitOpAttr t ps
	     Just (t1, t2, t3) -> 
		 do if t1 == t2 && t2 == t3 then
		       return ()
		       else addDiags [mkDiag Error 
				 "unexpected type components of operation" ty]
                    mt <- resolveTerm ga (Just t3) trm
		    putTypeMap tm
		    case mt of Nothing -> return Nothing
	                       Just t -> return $ Just $ UnitOpAttr t ps
anaAttr _ _ b = return $ Just b

filterVars :: Assumps -> Assumps
filterVars = filterAssumps (not . isVarDefn)

patternsToType :: [[VarDecl]] -> Type -> Type
patternsToType [] t = t
patternsToType (p: ps) t = FunType (tuplePatternToType p) PFunArr 
			  (patternsToType ps t) []

tuplePatternToType :: [VarDecl] -> Type
tuplePatternToType vds = mkProductType (map ( \ (VarDecl _ t _ _) -> t) vds) []

getUninstOpId :: TypeScheme -> OpId -> (OpId, TypeScheme)
getUninstOpId (TypeScheme tvs q ps) (OpId i args qs) =
      (OpId i [] qs, TypeScheme (args ++ tvs) q ps)  

anaOpId :: GlobalAnnos -> OpBrand -> TypeScheme -> [OpAttr] -> OpId 
	-> State Env (Maybe OpId) 
anaOpId ga br partSc attrs o =
    do let (OpId i _ _, sc) = getUninstOpId partSc o
       mSc <- anaTypeScheme sc 
       case mSc of 
           Nothing -> return Nothing
	   Just newSc -> do
               mAttrs <- mapM (anaAttr ga newSc) attrs
               mo <- addOpId i newSc (catMaybes mAttrs) $ NoOpDefn br 
               return $ fmap (const o) mo

anaOpItem :: GlobalAnnos -> OpBrand -> OpItem -> State Env OpItem
anaOpItem ga br (OpDecl is sc attr ps) = do
	us <- mapM (anaOpId ga br sc attr) is
	return $ OpDecl (catMaybes us) sc attr ps

anaOpItem ga br (OpDefn o oldPats sc partial trm ps) = 
    do let (op@(OpId i _ _), extSc@(TypeScheme tArgs scTy qs)) = 
	       getUninstOpId sc o
       checkUniqueVars $ concat oldPats
       tm <- gets typeMap
       mArgs <- mapM anaTypeVarDecl tArgs
       mPats <- mapM (mapM anaVarDecl) oldPats
       let newPats = map catMaybes mPats
           monoPats = map (map makeMonomorph) newPats
           pats = map (\ l -> mkTupleTerm (map QualVar l) []) monoPats
       as <- gets assumps
       mapM (mapM addVarDecl) monoPats
       let newArgs = catMaybes mArgs  
       checkUniqueTypevars newArgs
       mty <- anaStarType scTy
       case mty of 
	   Just ty -> do 
               mt <- resolveTerm ga (Just ty) trm
	       putAssumps as
	       putTypeMap tm
	       mSc <- fromResult $ const $ generalize $ 
			                TypeScheme tArgs 
					(patternsToType newPats ty) qs
	       case (mt, mSc) of 
		   (Just lastTrm, Just newSc) -> do 
		       let lamTrm = case (pats, partial) of 
				    ([], Total) -> lastTrm
				    _ -> LambdaTerm pats partial lastTrm ps
			   ot = QualOp br (InstOpId i [] []) newSc []
			   lhs = mkApplTerm ot pats
			   ef = mkEqTerm eqId ps lhs lastTrm
			   f = mkForall (map GenTypeVarDecl tArgs
					  ++ (map GenVarDecl $ 
					      concatMap extractVars pats)) ef
		       addOpId i newSc [] $ Definition br lamTrm
		       appendSentences [NamedSen 
						   ("def_" ++ showId i "")
						   $ Formula f] 
		       return $ OpDefn op [] newSc Total lamTrm ps
		   _ -> return $ OpDefn op newPats extSc partial trm ps
	   Nothing -> do 
	       mt <- resolveTerm ga Nothing trm
	       putAssumps as
	       putTypeMap tm
	       return $ OpDefn op oldPats extSc partial 
			      (case mt of Nothing -> trm
			                  Just x -> x) ps
							  
-- ----------------------------------------------------------------------------
-- ProgEq
-- ----------------------------------------------------------------------------

anaProgEq :: GlobalAnnos -> ProgEq -> State Env ProgEq
anaProgEq ga pe@(ProgEq pat trm qs) =
    do as <- gets assumps
       mp <- checkPattern ga pat
       case mp of 
	   Nothing -> return pe
	   Just newPat -> do 
	       let exbs = extractVars newPat
	       checkUniqueVars exbs
	       mapM_ addVarDecl exbs
	       mt <- resolveTerm ga Nothing trm
	       putAssumps as
	       case mt of 
		   Just newTerm  -> let newPrg = ProgEq newPat newTerm qs in
		     case getAppl newPat of
		       Just (i, sc, _) -> do 
			   addOpId i sc [] $ NoOpDefn Op
			   appendSentences [NamedSen ("pe_" ++ showId i "")
					    $ ProgEqSen i sc newPrg]
			   e <- get
			   if isLHS e newPat then return () 
			      else addDiags [mkDiag Warning
					 "illegal lhs pattern"
					 newPat]
			   return newPrg
		       _ -> do addDiags [mkDiag Error 
					 "illegal toplevel pattern"
					 newPat]
			       return newPrg
		   _ -> return $ ProgEq newPat trm qs 


getApplConstr :: Pattern -> (Pattern, [Pattern])
getApplConstr pat = 
    case pat of 
    ApplTerm p1 p2 _ -> 
	let (tp, args) = getApplConstr p1 in (tp, p2:args)
    TypedTerm tp _ _ _ -> getApplConstr tp
    _ -> (pat, [])
			   



