
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 

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
import Common.Lib.State
import HasCASL.As
import HasCASL.AsUtils
import HasCASL.Le
import HasCASL.Unify
import HasCASL.TypeAna
import HasCASL.Reader
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
	  QualVar _ _ _ -> opTok
	  QualOp _ _ _ -> opTok
	  TypedTerm _ _ _ _ -> inTok
	  _ -> opTok

-- match (and shift) a token (or partially finished term)
scan :: TypeMap -> (Type, a) -> (a -> Token) -> ParseMap a -> ParseMap a
scan tm (ty, trm) f pm =
  let m = parseMap pm
      i = lastIndex pm
      incI = incrIndex i
      (ps, c2) = runState (mapM (scanState tm (ty, trm) $ f trm) 
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
		    => GlobalAnnos -> TypeMap 
		    -> (Type, a) -> (PState a -> a) -> (a -> Token)
                    -> (Index -> State Int [PState a])
		    -> ParseMap a -> ParseMap a
completeScanPredict ga tm (ty, a) fromState toToken initStates pm =
    let pm3 = complete ga tm fromState
	      $ scan tm (ty, a) toToken
	      $ predict initStates pm
    in if (null $ lookUp (parseMap pm3) $ lastIndex pm3) 
	   && null (failDiags pm3)
       then  pm3 { failDiags = [mkDiag Error "unexpected mixfix token" a] }
       else pm3

nextState :: GlobalAnnos -> Assumps -> TypeMap -> (Type, Term) 
	  -> ParseMap Term -> ParseMap Term
nextState ga is tm (ty, trm) = 
    completeScanPredict ga tm (ty, trm) stateToAppl termToToken $
			initialState ga is 

-- | find information for qualified operation
findOpId :: Assumps -> TypeMap -> Int -> UninstOpId -> Type
	 -> Maybe OpInfo
findOpId as tm c i ty = 
    let l = Map.findWithDefault [] i as 
	s = filter (isUnifiable tm c (TypeScheme [] ([] :=> ty) []) . opType) l
	in if null s then Nothing else Just $ head s

iterStates :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Type -> [Term] 
	   -> ParseMap Term -> ParseMap Term
iterStates ga as tm cm ty terms pm = 
    let self = iterStates ga as tm cm ty
    in if null terms then pm
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) pm
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) pm
	    t@(QualVar v tyq _) -> 
		let (Result es mt) = (readR $ anaType (star, tyq)) (cm, tm) in
		    case mt of 
		    Just (_, typq) ->
			let mi = findOpId as tm (varCount pm) v typq in 
			    case mi of 
			    Just _ -> self (tail terms) $ nextState ga as tm 
				      (typq, t) pm
			    Nothing -> pm { failDiags = 
					    [mkDiag Error 
					     "value not found" v] }
		    Nothing -> pm { failDiags = es }
	    t@(QualOp (InstOpId v _ _) (TypeScheme _ (_ :=> tyq) _) _) ->
		let (Result es mt) = (readR $ anaType (star, tyq)) (cm, tm) in
		    case mt of 
		    Just (_, typq) ->
			let mi = findOpId as tm (varCount pm) v typq in 
			    case mi of 
			    Just _ -> self (tail terms) $ nextState ga as tm 
				      (typq, t) pm
			    Nothing -> pm { failDiags = 
					    [mkDiag Error 
					     "value not found" v] }
		    Nothing -> pm { failDiags = es }
	    TypedTerm hd tqual tyq ps -> 
		let (Result es mt) = (readR $ anaType (star, tyq)) (cm, tm) in
	        case mt of 
		Just (_, typq) -> 
		    let (Result ds mtt, c2) = runState
			   (case tqual of 
			        OfType -> resolve ga as tm cm (typq, hd)
			        _ -> resolveAny ga as tm cm hd) 
				       $ varCount pm
			pm2 = pm { varCount = c2, failDiags = es++ds }
			in case mtt of  
			Just (_, ttt) -> self (tail terms) 
				   $ nextState ga as tm 
				   (case tqual of 
				    InType -> logicalType
				    _ -> typq, TypedTerm ttt tqual typq ps) pm2
			Nothing -> pm2
		Nothing -> pm { failDiags = es }
	    QuantifiedTerm quant decls hd ps ->
		let (Result ds mtt, c2) = runState 
		        (resolve ga as tm cm (logicalType, hd)) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (_, tt) -> self (tail terms) $ nextState ga as tm 
		         (logicalType, QuantifiedTerm quant decls tt ps) pm2
		    Nothing -> pm2
	    LambdaTerm decls part hd ps -> 
		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (typq, tt) -> self (tail terms) $ nextState ga as tm 
		         (typq, LambdaTerm decls part tt ps) pm2
		    Nothing -> pm2
	    CaseTerm hd (ProgEq pat e1 pps : _) ps -> 
 		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
                    (Result es frst, c3) = runState 
		            (resolveAny ga as tm cm e1) c2
 		    pm2 = pm { varCount = c3, failDiags = ds++es }
		    in case (mtt, frst)  of 
		    (Just (_, tt), Just (typq, te)) -> self (tail terms) 
		                            $ nextState ga as tm 
		         (typq, CaseTerm tt [ProgEq pat te pps] ps) pm2
		    _ -> pm2
	    LetTerm eqs hd ps ->
		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (typq, tt) -> self (tail terms) $ nextState ga as tm 
		         (typq, LetTerm eqs tt ps) pm2
		    Nothing -> pm2
	    t  ->  self (tail terms) $ nextState ga as tm (MixfixType [], t) pm

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
       return $ resolveFromParseMap (toAppl ga) tm (ty, trm) $ 
	      resolveToParseMap ga as tm cm c ty trm

resolveTerm :: Type -> Term -> State Env (Result Term)
resolveTerm ty trm = 
    do s <- get
       r <- toEnvState $ resolve (globalAnnos s) 
	    (assumps s) (typeMap s) (classMap s) (ty, trm)
       return $ fmap snd r 

-- ---------------------------------
-- patterns
-- ---------------------------------

extractBindings :: Pattern -> [VarDecl]
extractBindings pat = 
    case pat of
    PatternVars l _ -> l
    PatternConstr _ _ ps _ -> concatMap extractBindings ps
    TuplePattern ps _ -> concatMap extractBindings ps
    TypedPattern p _ _ -> extractBindings p
    AsPattern p q _ -> extractBindings p ++ extractBindings q
    _ -> error "extractBindings"

patToToken :: Pattern -> Token
patToToken pat =
    case pat of 
    PatternToken x -> x 
    TypedPattern _ _ _ -> inTok
    _ -> opTok

patFromState :: PState Pattern -> Pattern
patFromState p =
    let r = ruleId p
        sc@(TypeScheme _ (_ :=> _ty) _) = ruleScheme p
        ar = reverse $ ruleArgs p
	qs = reverse $ posList p
    in if  r == inId 
	   || r == opId 
       then head ar
       else PatternConstr (InstOpId r [] []) sc ar qs

nextPatState :: GlobalAnnos -> Assumps -> TypeMap -> (Type, Pattern) 
	      -> ParseMap Pattern -> ParseMap Pattern
nextPatState ga is tm (ty, trm) = 
    completeScanPredict ga tm (ty, trm) patFromState patToToken
			$ initialState ga is

iterPatStates :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Type 
	   -> [Pattern] -> ParseMap Pattern -> ParseMap Pattern
iterPatStates ga as tm cm ty pats pm = 
    let self = iterPatStates ga as tm cm ty
    in if null pats then pm
       else case head pats of
            MixfixPattern ts -> self (ts ++ tail pats) pm
            BracketPattern b ts ps -> self 
	       (expandPos PatternToken (getBrackets b) ts ps ++ tail pats) pm
	    TypedPattern hd tyq ps -> 
		let (Result es mt) = (readR $ anaType (star, tyq)) (cm, tm) in
	        case mt of 
		Just (_, typq) -> 
		    let (Result ds mtt, c2) = runState
 			   (resolvePat ga as tm cm (typq, hd)) $ varCount pm
			pm2 = pm { varCount = c2, failDiags = es++ds }
			in case mtt of  
			Just (_, ttt) -> self (tail pats) 
				   $ nextPatState ga as tm 
				   (typq, TypedPattern ttt typq ps) pm2
			Nothing -> pm2
		Nothing -> pm { failDiags = es }
	    t -> self (tail pats) $ nextPatState ga as tm 
		   (MixfixType [], t) pm

resolvePatToParseMap :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Int 
		     -> Type -> Pattern -> ParseMap Pattern
resolvePatToParseMap ga as tm cm c ty trm = 
    let (initStates, c2) = runState (initialState ga as startIndex) c in
    iterPatStates ga as tm cm ty [trm] 
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
       return $ resolveFromParseMap patFromState tm (ty, trm) $ 
	      resolvePatToParseMap ga as tm cm c ty trm

resolvePattern :: Type -> Pattern -> State Env (Result Pattern)
resolvePattern ty trm = 
    do s <- get
       r <- toEnvState $ resolvePat (globalAnnos s) 
	    (assumps s) (typeMap s) (classMap s) (ty, trm)
       return $ fmap snd r 
