
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

Mixfix analysis of terms, adapted from the CASL analysis

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

-- match (and shift) a token (or partially finished term)
scan :: TypeMap -> (Type, Term) -> ParseMap Term -> ParseMap Term
scan tm (ty, trm) pm =
  let m = parseMap pm
      i = lastIndex pm
      t = case trm of 
	  TermToken x -> x 
	  QualVar _ _ _ -> opTok
	  QualOp _ _ _ -> opTok
	  TypedTerm _ _ _ _ -> inTok
	  _ -> opTok
      incI = incrIndex i
      (ps, c2) = runState (mapM (scanState tm (ty, trm) t) 
			     $ lookUp m i) $ varCount pm
  in
    pm { lastIndex = incI
       , varCount = c2
       , parseMap = Map.insert incI (concat ps) m }
	      
-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> TypeMap -> PMap Term -> PState Term 
	   -> [PState Term]
-- pre: finished rule 
collectArg ga tm m
	   s@(PState { ruleId = argIde, stateNo = arg, ruleType = argType }) =
    map (\ p -> p { restRule = tail $ restRule p })  
    $ mapMaybe (filterByType tm (argType, stateToAppl s))
    $ filter (filterByPrec ga argIde)
    $ lookUp m arg

compl :: GlobalAnnos -> TypeMap -> PMap Term -> [PState Term] -> [PState Term]
compl ga tm m l = 
  concat $ map (collectArg ga tm m) 
  $ filter (null . restRule) l

complRec :: GlobalAnnos -> TypeMap -> PMap Term -> [PState Term] 
	 -> [PState Term]
complRec ga tm m l = let l1 = compl ga tm m l in 
    if null l1 then l else complRec ga tm m l1 ++ l

complete :: GlobalAnnos -> TypeMap -> ParseMap Term -> ParseMap Term
complete ga tm pm =
    let m = parseMap pm
	i = lastIndex pm in
    pm { parseMap = Map.insert i (complRec ga tm m $ lookUp m i) m }

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: GlobalAnnos -> Assumps -> ParseMap a -> ParseMap a
predict ga is pm = 
    let m = parseMap pm
	i = lastIndex pm 
	c = varCount pm in
    if not (isStartIndex i) && any (\ (PState { restRule = ts }) ->
				    not (null ts) && head ts == termTok) 
	                       (lookUp m i)
		 then let (nextStates, c2) = runState (initialState ga is i) c
		      in pm { varCount = c2
			    , parseMap = Map.insertWith (++) i nextStates m }
		 else pm

nextState :: GlobalAnnos -> Assumps -> TypeMap -> (Type, Term) 
	  -> ParseMap Term -> ParseMap Term
nextState ga is tm (ty, trm) pm =
    let pm3 = complete ga tm
	      $ scan tm (ty, trm)
	      $ predict ga is pm
    in if (null $ lookUp (parseMap pm3) $ lastIndex pm3) 
	   && null (failDiags pm3)
       then  pm3 { failDiags = [mkDiag Error "unexpected mixfix token" trm] }
       else pm3

iterStates :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap -> Type -> [Term] 
	   -> ParseMap Term -> ParseMap Term
iterStates ga as tm cm ty terms pm = 
    let self = iterStates ga as tm cm ty
    in if null terms then pm
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) pm
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) pm
	    t@(QualVar v qty _) -> let l = Map.findWithDefault [] v as in
	        if null l then pm { failDiags = 
				    [mkDiag Error "variable not found" v] }
		else self (tail terms) $ nextState ga as tm (qty, t) pm
	    t@(QualOp (InstOpId v _ _) (TypeScheme _ (_ :=> qty) _) _) ->
		let l = Map.findWithDefault [] v as in
	        if null l then pm { failDiags = 
				    [mkDiag Error "operation not found" v] }
		else self (tail terms) $ nextState ga as tm (qty, t) pm
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
	    t@(CaseTerm hd eqs ps) -> 
                    pm { failDiags = [mkDiag Error "not handle" t] }
	    LetTerm eqs hd ps ->
		let (Result ds mtt, c2) = runState 
		            (resolveAny ga as tm cm hd) $ varCount pm
		    pm2 = pm { varCount = c2, failDiags = ds }
		    in case mtt of 
		    Just (typq, tt) -> self (tail terms) $ nextState ga as tm 
		         (typq, LetTerm eqs tt ps) pm2
		    Nothing -> pm2
	    t  ->  self (tail terms) $ nextState ga as tm (MixfixType [], t) pm

getAppls :: GlobalAnnos -> ParseMap Term -> [Term]
getAppls ga pm = 
    map (toAppl ga) $ 
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

resolve :: GlobalAnnos -> Assumps -> TypeMap -> ClassMap 
	-> (Type, Term) -> State Int (Result (Type, Term))
resolve ga as tm cm (ty, trm) =
    do c <- get
       let pm = checkResultType tm ty $ resolveToParseMap ga as tm cm c ty trm
	   ds = failDiags pm
	   ts = getAppls ga pm 
       return $ 
         if null ts then if null ds then 
                        fatal_error ("no resolution for term: "
					     ++ showPretty trm "")
					    (posOfTerm trm)
		       else Result ds Nothing
         else if null $ tail ts then Result ds (Just (getLastType pm, head ts))
	    else Result (Diag Error ("ambiguous mixfix term: " ++ 
				     showPretty trm "\n\t" ++ 
			 (concatMap ( \ t -> showPretty t "\n\t" )
			 $ take 5 ts)) (posOfTerm trm) : ds) Nothing

resolveTerm :: Type -> Term -> State Env (Result Term)
resolveTerm ty trm = 
    do s <- get
       r <- toEnvState $ resolve (globalAnnos s) 
	    (assumps s) (typeMap s) (classMap s) (ty, trm)
       return $ fmap snd r 
