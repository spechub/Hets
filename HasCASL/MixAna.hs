
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

data ParseMap a = ParseMap { varCount :: Int
			   , lastIndex :: Index
			   , failDiags :: [Diagnosis]
			   , parseMap :: PMap a
			   }

termToToken :: Term -> Token
termToToken trm = 
    case trm of 
	  TermToken x -> x 
	  TypedTerm _ _ _ _ -> inTok
          _ -> opTok

-- match (and shift) a token (or partially finished term)
scan :: TypeMap -> Knowns -> (Maybe Type, a) -> (a -> Token) 
     -> ParseMap a -> ParseMap a
scan tm knowns (ty, trm) f pm =
  let m = parseMap pm
      i = lastIndex pm
      incI = incrIndex i
      (ps, c2) = runState (mapM (scanState tm knowns (ty, trm) $ f trm) 
			     $ lookUp m i) $ varCount pm
  in
    pm { lastIndex = incI
       , varCount = c2
       , parseMap = Map.insert incI (concat ps) m }
	      
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

complete :: GlobalAnnos -> TypeMap -> (PState a -> a) 
	 -> ParseMap a -> ParseMap a
complete ga tm f pm =
    let m = parseMap pm
	i = lastIndex pm in
    pm { parseMap = Map.insert i (complRec ga tm m f $ lookUp m i) m }

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: (Index -> State Int [PState a]) -> ParseMap a -> ParseMap a
predict f pm = 
    let m = parseMap pm
	i = lastIndex pm 
	c = varCount pm in
    if not (isStartIndex i) && any (\ (PState { restRule = ts }) ->
				    not (null ts) && head ts == termTok) 
	                       (lookUp m i)
		 then let (nextStates, c2) = runState (f i) c
		      in pm { varCount = c2
			    , parseMap = Map.insertWith (++) i nextStates m }
		 else pm

completeScanPredict :: (PrettyPrint a, PosItem a) 
		    => GlobalAnnos -> TypeMap -> Knowns
		    -> (Maybe Type, a) -> (PState a -> a) -> (a -> Token)
                    -> (Index -> State Int [PState a])
		    -> ParseMap a -> ParseMap a
completeScanPredict ga tm knowns (ty, a) fromState toToken initStates pm =
    let pm3 = complete ga tm fromState
	      $ scan tm knowns (ty, a) toToken
	      $ predict initStates pm
    in if (null $ lookUp (parseMap pm3) $ lastIndex pm3) 
	   && null (failDiags pm3)
       then  pm3 { failDiags = [mkDiag Error 
				("unexpected mixfix token") a] }
       else pm3

nextState :: GlobalAnnos -> Assumps -> TypeMap -> (Maybe Type, Term) 
	  -> ParseMap Term -> ParseMap Term
nextState ga as tm (ty, trm) = 
    completeScanPredict ga tm Set.empty (ty, trm) stateToAppl termToToken $
			initialState ga as 

-- | find information for qualified operation
findOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> Type -> Maybe OpInfo
findOpId as tm c i ty = listToMaybe $ fst $
			partitionOpId as tm c i $ TypeScheme [] ([] :=> ty) []

iterStates :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Type -> [Term] 
	   -> ParseMap Term -> ParseMap Term
iterStates ga as tm cm ty terms pm = 
    let self = iterStates ga as tm cm ty
    in if null terms then pm
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) pm
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) pm
	    t@(QualVar v typ _) -> 
			let mi = findOpId as tm (varCount pm) v typ in 
			    case mi of 
			    Just _ -> self (tail terms) $ nextState ga as tm 
				      (Just typ, t) pm
			    Nothing -> pm { failDiags = 
					    [mkDiag Error 
					     "value not found" v] }
	    t@(QualOp (InstOpId v _ _) (TypeScheme _ (_ :=> typ) _) _) ->
			let mi = findOpId as tm (varCount pm) v typ in 
			    case mi of 
			    Just _ -> self (tail terms) $ nextState ga as tm 
				      (Just typ, t) pm
			    Nothing -> pm { failDiags = 
					    [mkDiag Error 
					     "value not found" v] }
	    TypedTerm hd tqual typ ps -> 
		    let (Result ds mtt, c2) = runState
			   (case tqual of 
			        OfType -> resolve ga as tm cm (typ, hd)
			        _ -> resolveAny ga as tm cm hd) 
				       $ varCount pm
			pm2 = pm { varCount = c2, failDiags = ds }
			in case mtt of  
			Just (_, ttt) -> self (tail terms) 
				   $ nextState ga as tm 
				   (Just (case tqual of 
				    InType -> logicalType
				    _ -> typ), 
				    TypedTerm ttt tqual typ ps) pm2
			Nothing -> pm2
	    QuantifiedTerm quant decls hd ps ->
		let (Result ds mtt, c2) = runState 
		        (resolve ga as tm cm (logicalType, hd)) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (_, tt) -> self (tail terms) $ nextState ga as tm 
		         (Just logicalType, 
			  QuantifiedTerm quant decls tt ps) pm2
		    Nothing -> pm2
	    LambdaTerm decls part hd ps -> 
		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (typ, tt) -> self (tail terms) $ nextState ga as tm 
		         (Just typ, LambdaTerm decls part tt ps) pm2
		    Nothing -> pm2
	    CaseTerm hd (ProgEq pat e1 pps : _) ps -> 
 		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
                    (Result es frst, c3) = runState 
		            (resolveAny ga as tm cm e1) c2
 		    pm2 = pm { varCount = c3, failDiags = ds++es }
		    in case (mtt, frst)  of 
		    (Just (_, tt), Just (typ, te)) -> self (tail terms) 
		                            $ nextState ga as tm 
		         (Just typ, CaseTerm tt [ProgEq pat te pps] ps) pm2
		    _ -> pm2
	    LetTerm eqs hd ps ->
		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (typq, tt) -> self (tail terms) $ nextState ga as tm 
		         (Just typq, LetTerm eqs tt ps) pm2
		    Nothing -> pm2
	    t@(TermToken _) ->  self (tail terms) 
		 $ nextState ga as tm (Nothing, t) pm
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

resolveToParseMap :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Int 
		  -> Type -> Term -> ParseMap Term
resolveToParseMap ga as tm cm c ty trm = 
    let (initStates, c2) = runState (initialState ga as startIndex) c in
    iterStates ga as tm cm ty [trm] 
	       ParseMap { lastIndex = startIndex
			, failDiags = []  
			, varCount = c2
			, parseMap = Map.single startIndex initStates }

checkResultType :: TypeMap -> Type -> ParseMap a -> ParseMap a
checkResultType tm t pm =
    let m = parseMap pm
	i = lastIndex pm in
	    pm { parseMap = Map.insert i 
		 (mapMaybe (filterByResultType tm t) 
		 $ lookUp m i) m }

resolveAny :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap 
	-> Term -> State Int (Result (Type, Term))
resolveAny ga as tm cm trm =
    do tvar <- freshVar
       resolve ga as tm cm (TypeName tvar star 1, trm)

resolveFromParseMap :: (PosItem a, PrettyPrint a) => (PState a -> a) 
		    -> TypeMap -> (Type, a) -> ParseMap a -> Result (Type, a)
resolveFromParseMap f tm (ty, a) pm0 =
    let pm = checkResultType tm ty $ pm0
	ds = failDiags pm
	ts = map f $ getAppls pm in 
	if null ts then Result 
	       (if null ds then 
		[mkDiag FatalError "no resolution for" a] 
		else ds) Nothing
        else if null $ tail ts then Result ds (Just (getLastType pm, head ts))
	     else Result (mkDiag 
			  Error ("ambiguous applications:\n\t" ++ 
				 (concatMap ( \ t -> showPretty t "\n\t")
				 $ take 5 ts) ++ "for" ) a : ds) Nothing

resolve :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap 
	-> (Type, Term) -> State Int (Result (Type, Term))
resolve ga as tm cm (ty, trm) =
    do c <- get
       let pm = resolveToParseMap ga as tm cm c ty trm
       put (varCount pm) 
       return $ resolveFromParseMap (toAppl ga) tm (ty, trm) pm 

resolveTerm :: GlobalAnnos -> Type -> Term -> State Env (Maybe Term)
resolveTerm ga ty oldTrm = 
    do trm <- anaTypesInTerm oldTrm
       s <- get
       let (Result ds mr, c2) = runState (resolve ga
	    (assumps s) (typeMap s) (classMap s) (ty, trm))
			(counter s)
       put s { counter = c2 }
       addDiags ds
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

nextPatState :: GlobalAnnos -> Assumps -> TypeMap -> Knowns 
	     -> (Maybe Type, Pattern) -> ParseMap Pattern -> ParseMap Pattern
nextPatState ga as tm knowns (ty, trm) = 
    completeScanPredict ga tm knowns (ty, trm) patFromState patToToken
			$ initialPatState as

iterPatStates :: GlobalAnnos -> Assumps -> TypeMap -> Knowns -> ClassMap 
	      -> Type -> [Pattern] -> ParseMap Pattern -> ParseMap Pattern
iterPatStates ga as tm knowns cm ty pats pm = 
    let self = iterPatStates ga as tm knowns cm ty
    in if null pats then pm
       else case head pats of
            MixfixPattern ts -> self (ts ++ tail pats) pm
            BracketPattern b ts ps -> self 
	       (expandPos PatternToken (getBrackets b) ts ps ++ tail pats) pm
	    TypedPattern hd typ ps -> 
		    let (Result ds mtt, c2) = runState
 			   (resolvePat ga as tm cm (typ, hd)) $ varCount pm
			pm2 = pm { varCount = c2, failDiags = ds }
			in case mtt of  
			Just (_, ttt) -> self (tail pats) 
				   $ nextPatState ga as tm knowns
				   (Just typ, TypedPattern ttt typ ps) pm2
			Nothing -> pm2
	    t@(PatternToken _) -> self (tail pats)
				  $ nextPatState ga as tm knowns
				 (Nothing, t) pm
	    t -> error ("iterPatStates: " ++ show t)

getKnowns :: Id -> Knowns
getKnowns (Id ts cs _) = Set.union (Set.fromList (map tokStr ts)) $ 
			 Set.unions (map getKnowns cs) 

resolvePatToParseMap :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Int 
		     -> Type -> Pattern -> ParseMap Pattern
resolvePatToParseMap ga as tm cm c ty trm = 
    let (initStates, c2) = runState (initialPatState as startIndex) c 
	ids = Map.keys as 
	knowns = Set.union (Set.fromList (tokStr inTok : map (:[]) "{}[](),"))
		 $ Set.unions $ map getKnowns ids
    in
    iterPatStates ga as tm knowns cm ty [trm] 
	       ParseMap { lastIndex = startIndex
			, failDiags = []  
			, varCount = c2
			, parseMap = Map.single startIndex initStates }

resolveAnyPat :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap 
	-> Pattern -> State Int (Result (Type, Pattern))
resolveAnyPat ga as tm cm trm =
    do tvar <- freshVar
       resolvePat ga as tm cm (TypeName tvar star 1, trm)

resolvePat :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap 
	-> (Type, Pattern) -> State Int (Result (Type, Pattern))
resolvePat ga as tm cm (ty, trm) =
    do c <- get
       let pm = resolvePatToParseMap ga as tm cm c ty trm
	   c2 = varCount pm
           r = resolveFromParseMap patFromState tm (ty, trm) pm
       case maybeResult r of
	   Nothing -> do put c2
			 return r
	   Just (newTy, pat) -> 
	       do let (r2, (c3, _, ds)) = runState (specializePatVars tm 
						    (newTy, pat)) 
					  (c2, Map.empty, [])
		  put c3
		  return $ Result ds $ Just r2 
       

resolvePattern :: GlobalAnnos -> Pattern -> State Env (Maybe (Type, Pattern))
resolvePattern ga oldPat = 
    do pat <- anaTypesInPattern oldPat
       s <- get
       let (Result ds mr, c) = runState (resolveAnyPat ga
		      (assumps s) (typeMap s) (classMap s) pat) $ counter s
       put s { counter = c}
       addDiags ds
       return mr

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
