
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

Mixfix analysis of terms and patterns, adapted from the CASL analysis

-}

module HasCASL.MixAna where 

import Common.GlobalAnnotations
import Common.Result
import Common.Id
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Lib.State
import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import HasCASL.ClassAna
import HasCASL.TypeAna
import HasCASL.TypeDecl
import HasCASL.MixParserState
import Data.Maybe

-- import Debug.Trace

-- Earley Algorithm

lookUp :: (Ord a) => Map.Map a [b] -> a -> [b]
lookUp ce k = Map.findWithDefault [] k ce

type PMap a = Map.Map Index [PState a]

data ParseMap a = ParseMap { lastIndex :: Index
			   , parseMap :: PMap a
			   }

termToToken :: Term -> Token
termToToken trm = 
    case trm of 
	  TermToken x -> x 
	  TypedTerm _ _ _ _ -> inTok
          _ -> opTok

-- match (and shift) a token (or partially finished term)
scan :: Knowns -> (Maybe Type, a) -> (a -> Token) 
     -> State (Env, ParseMap a) ()
scan knowns (ty, trm) f =
  do (e, pm) <- get 
     let m = parseMap pm
	 i = lastIndex pm
	 incI = incrIndex i
	 (ps, c2) = runState (mapM (scanState (typeMap e) knowns (ty, trm) 
				   $ f trm) $ lookUp m i) $ counter e
     put (e { counter = c2 }, pm { lastIndex = incI, 
				   parseMap = Map.insert incI (concat ps) m })
	      
-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> TypeMap -> PMap a -> (PState a -> a) 
	   -> PState a -> [PState a]
-- pre: finished rule 
collectArg ga tm m f
	   s@(PState { ruleId = argIde, stateNo = arg, ruleType = argType }) =
    map (\ p -> p { restRule = tail $ restRule p })  
    $ mapMaybe (filterByType tm (argType, f s))
    $ filter (filterByPrec ga argIde)
    $ lookUp m arg

compl :: GlobalAnnos -> TypeMap -> PMap a -> (PState a -> a) 
      -> [PState a] -> [PState a]
compl ga tm m f l = 
  concat $ map (collectArg ga tm m f) 
  $ filter (null . restRule) l

complRec :: GlobalAnnos -> TypeMap -> PMap a -> (PState a -> a) 
      -> [PState a] -> [PState a]
complRec ga tm m f l = let l1 = compl ga tm m f l in 
    if null l1 then l else complRec ga tm m f l1 ++ l

complete :: GlobalAnnos -> (PState a -> a) -> State (Env, ParseMap a) ()
complete ga f =
    do (e, pm) <- get
       let m = parseMap pm
	   i = lastIndex pm 
       put (e, pm { parseMap = Map.insert i 
		    (complRec ga (typeMap e) m f $ lookUp m i) m })

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: (Index -> State Int [PState a]) -> State (Env, ParseMap a) ()
predict f = 
    do (e, pm) <- get 
       let m = parseMap pm
	   i = lastIndex pm 
	   c = counter e
       if not (isStartIndex i) && any (\ (PState { restRule = ts }) ->
				    not (null ts) && head ts == termTok) 
	                       (lookUp m i)
		 then let (nextStates, c2) = runState (f i) c
		      in put (e { counter = c2 }, 
			      pm { parseMap = Map.insertWith (++) i 
				   nextStates m })
		 else return ()

addDiag :: Diagnosis -> State (Env, ParseMap a) ()
addDiag d = do (e, pm) <- get
	       put (e { envDiags = d : envDiags e}, pm)

completeScanPredict :: (PrettyPrint a, PosItem a) 
		    => GlobalAnnos -> Knowns
		    -> (Maybe Type, a) -> (PState a -> a) -> (a -> Token)
                    -> (Index -> State Int [PState a])
		    -> State (Env, ParseMap a) ()
completeScanPredict ga knowns (ty, a) fromState toToken initStates =
    do predict initStates
       scan knowns (ty, a) toToken
       complete ga fromState
       pm <- gets snd
       let m = parseMap pm
	   i = lastIndex pm
       if (null $ lookUp m i) && (not $ null $ lookUp m $ decrIndex i)
           then addDiag $ mkDiag Error "unexpected mixfix token" a
	   else return ()

nextState :: GlobalAnnos -> (Maybe Type, Term) -> State (Env, ParseMap Term) ()
nextState ga (ty, trm) = 
    do e <- gets fst
       completeScanPredict ga Set.empty (ty, trm) 
           stateToAppl termToToken $ initialState ga $ assumps e

-- | find information for qualified operation
findOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> Type -> Maybe OpInfo
findOpId as tm c i ty = listToMaybe $ fst $
			partitionOpId as tm c i $ TypeScheme [] ([] :=> ty) []

iterStates :: GlobalAnnos -> Type -> [Term] 
	   -> State (Env, ParseMap Term) ()
iterStates ga ty terms = 
    do (e, pm) <- get
       let self = iterStates ga ty 
           as = assumps e
	   tm = typeMap e
	   c = counter e
       if null terms then return () else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms)
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms)
	    t@(QualVar v typ _) -> 
	        let mi = findOpId as tm c v typ in
		    case mi of 
		        Just _ -> do nextState ga (Just typ, t)
			     	     self (tail terms)
	                Nothing -> addDiag $ mkDiag Error "value not found" v
	    t@(QualOp (InstOpId v _ _) (TypeScheme _ (_ :=> typ) _) _) ->
	        let mi = findOpId as tm c v typ in 
	            case mi of 
			Just _ -> do nextState ga (Just typ, t)
			     	     self (tail terms)
			Nothing -> addDiag $ mkDiag Error "value not found" v
	    TypedTerm hd tqual typ ps -> 
		do let (mtt, e2) = runState
			   (case tqual of 
			        OfType -> resolve ga (typ, hd)
			        _ -> resolveAny ga hd) e
	           put (e2, pm)			       
		   case mtt of  
			Just (_, ttt) -> 
	                   do nextState ga (Just (case tqual of 
				    InType -> logicalType
				    _ -> typ), TypedTerm ttt tqual typ ps)
	                      self (tail terms) 
			Nothing -> return ()
	    QuantifiedTerm quant decls hd ps ->
		do let (mtt, e2) = runState (resolve ga (logicalType, hd)) e
	           put (e2, pm)			       
		   case mtt of 
	               Just (_, tt) -> 
	                   do nextState ga (Just logicalType, 
					    QuantifiedTerm quant decls tt ps)
	                      self (tail terms) 
	               Nothing -> return ()
	    LambdaTerm decls part hd ps -> 
		do let (mtt, e2) = runState (resolveAny ga hd) e 
	           put (e2, pm)			       
		   case mtt of 
	               Just (typ, tt) -> 
                           do nextState ga (Just typ, 
					    LambdaTerm decls part tt ps)
	                      self (tail terms) 
	               Nothing -> return () 
	    CaseTerm hd (ProgEq pat e1 pps : _) ps -> 
 		do let (mtt, e2) = runState (resolveAny ga hd) e
                       (frst, e3) = runState 
		            (resolveAny ga e1) e2
 	           put (e3, pm)			       
		   case (mtt, frst)  of 
	               (Just (_, tt), Just (typ, te)) ->
	                   do nextState ga (Just typ, 
					    CaseTerm tt [ProgEq pat te pps] ps)
	                      self (tail terms) 
	               _ -> return ()
	    LetTerm eqs hd ps ->
		do let (mtt, e2) = runState 
		            (resolveAny ga hd) e
	           put (e2, pm)			       
		   case mtt of 
		       Just (typq, tt) -> 
	                   do nextState ga (Just typq, LetTerm eqs tt ps)
                              self (tail terms)
		       Nothing -> return ()
	    t@(TermToken _) -> do nextState ga (Nothing, t)
	                          self (tail terms) 
	    t -> error ("iterStates: " ++ show t)

getAppls :: ParseMap a -> [PState a]
getAppls pm = 
	filter (\ (PState { restRule = ts, stateNo = k }) 
		-> null ts && isStartIndex k) $ 
	     lookUp (parseMap pm) $ lastIndex pm

getLastType :: ParseMap a -> Type
getLastType pm = 
    let tys =  map ruleType $ 
	      filter (\ (PState { restRule = ts, stateNo = k }) 
		      -> null ts && isStartIndex k) $ 
	      lookUp (parseMap pm) $ lastIndex pm
    in if null tys then error "getLastType" else head tys

resolveToParseMap :: GlobalAnnos -> Type -> Term -> State Env (ParseMap Term)
resolveToParseMap ga ty trm =
    do as <- gets assumps
       initStates <- toEnvState (initialState ga as startIndex) 
       let pm = ParseMap { lastIndex = startIndex
			, parseMap = Map.single startIndex initStates }
       e <- get 
       let (_, (e2, pm2)) = runState (iterStates ga ty [trm]) (e, pm)
       put e2
       return pm2

checkResultType :: TypeMap -> Type -> ParseMap a -> ParseMap a
checkResultType tm t pm =
    let m = parseMap pm
	i = lastIndex pm in
	    pm { parseMap = Map.insert i 
		 (mapMaybe (filterByResultType tm t) 
		 $ lookUp m i) m }

resolveAny :: GlobalAnnos -> Term -> State Env (Maybe (Type, Term))
resolveAny ga trm =
    do tvar <- toEnvState freshVar
       resolve ga (TypeName tvar star 1, trm)

resolveFromParseMap :: (PosItem a, PrettyPrint a) => (PState a -> a) 
		    -> (Type, a) -> ParseMap a -> State Env (Maybe (Type, a))
resolveFromParseMap f (ty, a) pm0 =
    do tm <- gets typeMap
       let i = lastIndex pm0
           pm = checkResultType tm ty pm0
	   ts = map f $ getAppls pm
       if null ts then do if (null $ lookUp (parseMap pm0) i) 
				 || i == startIndex
			     then return () 
			     else addDiags [mkDiag FatalError 
					    "no resolution for" a] 
			  return Nothing
           else if null $ tail ts then return (Just (getLastType pm, head ts))
	       else do addDiags [mkDiag Error 
				 ("ambiguous applications:\n\t" ++ 
				  (concatMap ( \ t -> showPretty t "\n\t" )
				  $ take 5 ts) ++ "for" ) a]
		       return Nothing

resolve :: GlobalAnnos -> (Type, Term) -> State Env (Maybe (Type, Term))
resolve ga (ty, trm) =
    do pm <- resolveToParseMap ga ty trm
       resolveFromParseMap (toAppl ga) (ty, trm) pm 

resolveTerm :: GlobalAnnos -> Type -> Term -> State Env (Maybe Term)
resolveTerm ga ty oldTrm = 
    do trm <- anaTypesInTerm oldTrm
       mr <- resolve ga (ty, trm)	    
       return $ fmap snd mr 

-- ---------------------------------
-- patterns
-- ---------------------------------

extractBindings :: Pattern -> [VarDecl]
extractBindings pat = 
    case pat of
    PatternVar l -> [l]
    PatternConstr _ _ ps _ -> concatMap extractBindings ps
    TuplePattern ps _ -> concatMap extractBindings ps
    TypedPattern p _ _ -> extractBindings p
    AsPattern p q _ -> extractBindings p ++ extractBindings q
    _ -> error ("extractBindings: " ++ show pat)

patToToken :: Pattern -> Token
patToToken pat =
    case pat of 
    PatternToken x -> x 
    TypedPattern _ _ _ -> inTok
    _ -> error ("patToToken: " ++ show pat)

patFromState :: PState Pattern -> Pattern
patFromState p =
    let r@(Id ts _ _)= ruleId p
        sc@(TypeScheme _ (_ :=> _ty) _) = ruleScheme p
        ar = reverse $ ruleArgs p
	qs = reverse $ posList p
    in if  r == inId 
	   || r == opId 
	   || r == parenId
       then head ar
       else if r == applId then
	    case head ar of 
	    PatternConstr instOp isc args ps ->
		PatternConstr instOp isc (args ++ tail ar) (ps ++ qs)  
	    t -> error ("patFromState: " ++ show t)
       else if r == tupleId || r == unitId then
	    TuplePattern ar qs
       else if isUnknownId r then 
	        if null $ tail ts then error "patFromState"
	        else PatternVar (VarDecl (Id [head $ tail ts] [] []) 
				 (ruleType p) Other qs)
	    else PatternConstr (InstOpId (setIdePos r ar qs) [] []) sc ar qs

initialPatState :: Assumps -> Index -> State Int [PState a]
initialPatState as i = 
    do let ids = concatMap (\ (ide, l) -> map ( \ e -> (ide, e)) $ opInfos l) 
		 $ Map.toList as
       l1 <- mapM (mkMixfixState i) ids
       l2 <- mapM (mkPlainApplState i) $ filter (isMixfix . fst) ids
       a  <- mkApplTokState i applId
       p  <- mkParenTokState i parenId
       t  <- mkTupleTokState i tupleId
       l3 <- mapM (mkTokState i)
              [unitId,
	       unknownId,
	       inId,
	       opId]
       return (a:p:t:l1 ++ l2 ++ l3)

nextPatState :: GlobalAnnos -> Knowns -> (Maybe Type, Pattern) 
	     -> State (Env, ParseMap Pattern) ()
nextPatState ga knowns (ty, trm) = 
    do as <- gets (assumps . fst)
       completeScanPredict ga knowns (ty, trm) patFromState patToToken
			       $ initialPatState as

iterPatStates :: GlobalAnnos -> Knowns -> Type -> [Pattern] 
	      -> State (Env, ParseMap Pattern) ()
iterPatStates ga knowns ty pats = 
    do (e, pm) <- get 
       let self = iterPatStates ga knowns ty
       if null pats then return ()
	  else case head pats of
            MixfixPattern ts -> self (ts ++ tail pats)
            BracketPattern b ts ps -> self 
	       (expandPos PatternToken (getBrackets b) ts ps ++ tail pats)
	    TypedPattern hd typ ps -> 
		do let (mtt, e2) = runState (resolvePat ga (typ, hd)) e
		   put (e2, pm)
		   case mtt of  
			Just (_, ttt) -> 
			    do nextPatState ga knowns (Just typ, 
						       TypedPattern ttt typ ps)
			       self (tail pats) 
			Nothing -> return ()
	    t@(PatternToken _) -> do nextPatState ga knowns (Nothing, t)
				     self (tail pats)
	    t -> error ("iterPatStates: " ++ show t)

getKnowns :: Id -> Knowns
getKnowns (Id ts cs _) = Set.union (Set.fromList (map tokStr ts)) $ 
			 Set.unions (map getKnowns cs) 

resolvePatToParseMap :: GlobalAnnos -> Type -> Pattern 
		     -> State Env (ParseMap Pattern)
resolvePatToParseMap ga ty trm = 
    do as <- gets assumps 
       initStates <- toEnvState $ initialPatState as startIndex
       let ids = Map.keys as 
	   knowns = Set.union (Set.fromList 
			       (tokStr inTok : map (:[]) "{}[](),"))
		    $ Set.unions $ map getKnowns ids
       e <- get
       let (_, (e2, pm2)) = runState (iterPatStates ga knowns ty [trm]) 
			    (e, ParseMap 
			     { lastIndex = startIndex
			     , parseMap = Map.single startIndex initStates })
       put e2
       return pm2

resolveAnyPat :: GlobalAnnos -> Pattern -> State Env (Maybe (Type, Pattern))
resolveAnyPat ga trm =
    do tvar <- toEnvState freshVar
       resolvePat ga (TypeName tvar star 1, trm)

resolvePat :: GlobalAnnos -> (Type, Pattern) 
	   -> State Env (Maybe (Type, Pattern))
resolvePat ga (ty, trm) =
    do pm <- resolvePatToParseMap ga ty trm
       mr <- resolveFromParseMap patFromState (ty, trm) pm
       case mr of
	   Nothing -> return Nothing
	   Just (newTy, pat) -> 
	       do e <- get
                  let (r, (c, _, ds)) = 
			  runState (specializePatVars
				    (typeMap e) (newTy, pat)) 
				       (counter e, Map.empty, [])
		  put e { counter = c }
		  addDiags ds
		  return $ Just r

resolvePattern :: GlobalAnnos -> Pattern -> State Env (Maybe (Type, Pattern))
resolvePattern ga oldPat = 
    do pat <- anaTypesInPattern oldPat
       resolveAnyPat ga pat

-- ---------------------------------------------------------------------------
-- resolve types in terms and patterns
-- ---------------------------------------------------------------------------

anaTypesInTerm :: Term -> State Env Term
anaTypesInTerm trm = 
    case trm of
	   QualVar v t ps -> 
	       do ty <- anaStarType t
		  return $ QualVar v ty ps
	   QualOp io (TypeScheme vs (qs :=> t) ps1) ps ->
	       do ty <- anaStarType t
		  return $ QualOp io (TypeScheme vs (qs :=> ty) ps1) ps
	   ApplTerm t1 t2 ps -> 
	       do t3 <- anaTypesInTerm t1
		  t4 <- anaTypesInTerm t2
		  return $ ApplTerm t3 t4 ps
	   TupleTerm ts ps -> 
	       do tys <- mapM anaTypesInTerm ts
		  return $ TupleTerm tys ps
	   TypedTerm t1 q t ps ->
	       do t2 <- anaTypesInTerm t1
		  ty <- anaStarType t
		  return $ TypedTerm t2 q ty ps 
	   QuantifiedTerm q vs t ps -> 
	       do e <- anaTypesInTerm t 
		  return $ QuantifiedTerm q vs e ps
	   LambdaTerm pats part t ps -> 
	       do nPats <- mapM anaTypesInPattern pats
	          e <- anaTypesInTerm t 
		  return $ LambdaTerm nPats part e ps
	   CaseTerm t es ps ->
	       do e <- anaTypesInTerm t
		  nEs <- mapM anaTypesInProgEq es
		  return $ CaseTerm e nEs ps
	   LetTerm es t ps ->
	       do nEs <- mapM anaTypesInProgEq es
		  e <- anaTypesInTerm t
		  return $ LetTerm nEs e ps
	   MixfixTerm ts -> 
	       fmap MixfixTerm $ mapM anaTypesInTerm ts
	   BracketTerm b ts ps -> 
	       do nTs <- mapM anaTypesInTerm ts
		  return $ BracketTerm b nTs ps
	   _ -> return trm


anaTypesInPattern :: Pattern -> State Env Pattern 
anaTypesInPattern pat = 
    case pat of 
	     PatternVar (VarDecl v t k ps) ->
		 do ty <- anaStarType t
		    return $ PatternVar (VarDecl v ty k ps)
	     PatternConstr io (TypeScheme vs (qs :=> t) ps1) pats ps ->
		 do ty <- anaStarType t
		    nPats <- mapM anaTypesInPattern pats
		    return $ PatternConstr io (TypeScheme vs (qs :=> ty) ps1)
			   nPats ps
             PatternToken _ -> return pat
	     BracketPattern b pats ps ->
		 do nPats <- mapM anaTypesInPattern pats
		    return $ BracketPattern b nPats ps 
	     TuplePattern pats ps -> 
		 do nPats <- mapM anaTypesInPattern pats
		    return $ TuplePattern nPats ps 
	     MixfixPattern pats -> 
		 fmap MixfixPattern $ mapM anaTypesInPattern pats
	     TypedPattern p t ps -> 
		 do nPat <- anaTypesInPattern p
		    ty <- anaStarType t
		    return $ TypedPattern nPat ty ps 
	     AsPattern p1 p2 ps ->
		 do p3 <- anaTypesInPattern p1 
		    p4 <- anaTypesInPattern p2
		    return $ AsPattern p3 p4 ps

anaTypesInProgEq :: ProgEq -> State Env ProgEq
anaTypesInProgEq (ProgEq p t ps) = 
    do pat <- anaTypesInPattern p 
       trm <- anaTypesInTerm t
       return $ (ProgEq pat trm ps)

-- ---------------------------------------------------------------------------
-- specialize 
-- ---------------------------------------------------------------------------

getArgsRes :: Type -> [a] -> Result ([Type], Type)
getArgsRes t [] = return ([], t)
getArgsRes (FunType t1 _ t2 _) (_:r) = 
    do (as, res) <- getArgsRes t2 r 
       return (t1:as, res)
getArgsRes t _ = Result [mkDiag FatalError "too many arguments for type" t]
		 Nothing

specializePatVars :: TypeMap -> (Type, Pattern) 
		  -> State (Int, Subst, [Diagnosis]) (Type, Pattern)
specializePatVars tm (ty, pat) = do
  (c, oldSubst, ds) <- get
  case pat of 
    PatternVar (VarDecl v vty k ps) -> 
	do let r = unify tm (subst oldSubst ty) $ subst oldSubst vty
	   case maybeResult r of 
	       Nothing -> do put (c, oldSubst, diags r ++ ds)
			     return (ty, pat)
	       Just newSubst -> 
		   do put (c, newSubst, ds)
		      return (subst newSubst ty, 
			      PatternVar $ VarDecl v 
			      (subst newSubst vty) k ps)
    PatternConstr i sc args ps ->
        do let (ity, c2) = runState (freshInst sc) c
	       argsRes = getArgsRes ity args
           case maybeResult argsRes of 
	       Nothing -> do put (c2, oldSubst, diags argsRes ++ ds)
			     return (ty, pat)
	       Just (ats, res) -> 
		   do let r = unify tm (subst oldSubst ty) 
			      $ subst oldSubst res 
		      case maybeResult r of 
		          Nothing -> do put (c2, oldSubst, diags r ++ ds)
					return (ty, pat)
			  Just newSubst -> 
			      do put (c2, newSubst, ds) 	      
				 largs <- mapM (specializePatVars tm) 
					  $ zip ats args
				 (_, lastSubst, _) <- get
				 return (subst lastSubst res, 
				         PatternConstr i sc (map snd largs) ps)
    TuplePattern args ps ->
	case ty of 
		ProductType ats qs -> 
		    if length ats == length args then 
		    do largs <- mapM (specializePatVars tm) $ zip ats args
		       (_, lastSubst,_) <- get
		       return (subst lastSubst $ ProductType (map fst largs) qs
			      , TuplePattern (map snd largs) ps)
		    else do put (c, oldSubst, mkDiag Error
				 "wrong number of arguments for tuple" ty : ds)
	                    return (ty, pat) 
		_ -> do put (c, oldSubst, mkDiag Error
			     "wrong type for tuple" pat : ds)
			return (ty, pat)
    TypedPattern tpat vty ps ->
	do let r = unify tm (subst oldSubst ty) 
		       $ subst oldSubst vty 
           case maybeResult r of
	       Nothing -> do put (c, oldSubst, diags r ++ ds)
			     return (ty, pat)
               Just newSubst -> 
		   do put (c, newSubst, ds)
	              (newTy, newPat) <- specializePatVars tm 
					 (subst newSubst vty, tpat) 
		      return (newTy, case newPat of 
			      PatternVar _ -> newPat 
			      TypedPattern _ _ _ -> newPat
			      _ -> TypedPattern newPat newTy ps)
    _ -> do put (c, oldSubst, mkDiag Error
		 "unexpected pattern" pat : ds)
	    return (ty, pat)
