
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2003 

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

Mixfix analysis of terms, adapted from the CASL analysis

-}

module HasCASL.MixAna (resolveTerm) where 

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
import HasCASL.MixParserState
import Data.Maybe

-- import Debug.Trace

-- Earley Algorithm

lookUp :: (Ord a) => Map.Map a [b] -> a -> [b]
lookUp ce k = Map.findWithDefault [] k ce

data ParseMap = ParseMap { varCount :: Int
			 , typeAliases :: TypeMap
			 , lastIndex :: Index
			 , failDiags :: [Diagnosis]
			 , parseMap :: Map.Map Index [PState]
			 }

-- match (and shift) a token (or partially finished term)
scan :: (Type, Term) -> ParseMap -> ParseMap
scan (ty, trm) pm =
  let m = parseMap pm
      tm = typeAliases pm
      i = lastIndex pm
      t = case trm of 
	  TermToken x -> x 
	  QualVar _ _ _ -> varTok
	  _ -> opTok
      incI = incrIndex i
      (tvar, c2) = runState freshVar $ varCount pm
  in
    pm { lastIndex = incI
       , varCount = c2
       , parseMap = Map.insert incI ( 
       foldr (\ p l ->
	      let ts = restRule p
	          a = ruleArgs p in
	      if null ts || head ts /= t then l 
	      else if t == commaTok then 
	      let newTy = case ruleType p of 
	                  FunType (ProductType tys ps) 
	                      PFunArr (ProductType _ _) _ -> 
	                      let newTuple = ProductType 
	                           (tys++[TypeName tvar star 1]) ps in
	                      FunType newTuple PFunArr newTuple []
	                  same -> same 
              in  
	      -- list elements separator 
	             p { restRule = termTok : commaTok : tail ts
		       , ruleType = newTy }
	             : p { restRule = termTok : tail ts } : l
              else if t == varTok || t == opTok || t == predTok then
	             let mp = do q <- filterByType tm (ty,trm) p
	                         return q { restRule = tail ts }
	             in maybeToList mp ++ l
	      else if t == colonTok || t == asTok || t == inTok then
	             p { restRule = [], ruleArgs = [head a] } : l
	      else p { restRule = tail ts, posList = tokPos t : posList p } : l
	     ) [] (lookUp m i)) m }
	      
-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> PState -> [PState]
-- pre: finished rule 
collectArg g (ParseMap { typeAliases = tm, parseMap = m })
	   s@(PState { ruleId = argIde, stateNo = arg, ruleType = argType }) =
    map (\ p -> p { restRule = tail $ restRule p })  
    $ mapMaybe (filterByType tm (argType, stateToAppl s))
    $ filter (filterByPrec g argIde)
    $ lookUp m arg

compl :: GlobalAnnos -> ParseMap -> [PState] -> [PState]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (null . restRule) l

complRec :: GlobalAnnos -> ParseMap -> [PState] -> [PState]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> ParseMap -> ParseMap
complete g pm =
    let m = parseMap pm
	i = lastIndex pm in
    pm { parseMap = Map.insert i (complRec g pm $ lookUp m i) m }

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: GlobalAnnos -> Assumps -> ParseMap -> ParseMap
predict g is pm = 
    let m = parseMap pm
	i = lastIndex pm 
	c = varCount pm in
    if not (isStartIndex i) && any (\ (PState { restRule = ts }) ->
				    not (null ts) && head ts == termTok) 
	                       (lookUp m i)
		 then let (nextStates, c2) = runState (initialState g is i) c
		      in pm { varCount = c2
			    , parseMap = Map.insertWith (++) i nextStates m }
		 else pm

nextState :: GlobalAnnos -> Assumps -> (Type, Term) 
	  -> ParseMap -> ParseMap
nextState g is (ty, trm) pm =
    let pm3 = complete g
	      $ scan (ty, trm)
	      $ predict g is pm
    in if (null $ lookUp (parseMap pm3) $ lastIndex pm3) 
	   && null (failDiags pm3)
       then  pm3 { failDiags = [mkDiag Error "unexpected mixfix token" trm] }
       else pm3

iterStates :: GlobalAnnos -> Assumps -> Type -> [Term] 
	   -> ParseMap -> ParseMap
iterStates g ops ty terms pm = 
    let self = iterStates g ops ty
    in if null terms then pm
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) pm
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) pm
	    t@(QualVar v qty _) -> let l = Map.findWithDefault [] v ops in
	        if null l then pm { failDiags = 
				    [mkDiag Error "variable not found" v] }
		else self (tail terms) $ nextState g ops (qty, t) pm
	    t  ->  self (tail terms) $ nextState g ops (MixfixType [], t) pm

getAppls :: GlobalAnnos -> ParseMap -> [Term]
getAppls g pm = 
    map (toAppl g) $ 
	filter (\ (PState { restRule = ts, stateNo = k }) 
		-> null ts && isStartIndex k) $ 
	     lookUp (parseMap pm) $ lastIndex pm

getLastType :: ParseMap -> Type
getLastType pm = 
    let tys =  map ruleType $ 
	      filter (\ (PState { restRule = ts, stateNo = k }) 
		      -> null ts && isStartIndex k) $ 
	      lookUp (parseMap pm) $ lastIndex pm
    in if null tys then error "getLastType" else head tys

resolveToParseMap :: GlobalAnnos -> Assumps -> TypeMap -> Int 
		  -> Type -> Term -> ParseMap
resolveToParseMap g ops tm c ty trm = 
    let (initStates, c2) = runState (initialState g ops startIndex) c in
    iterStates g ops ty [trm] 
	       ParseMap { lastIndex = startIndex
			, typeAliases = tm
			, failDiags = []  
			, varCount = c2
			, parseMap = Map.single startIndex initStates }

checkResultType :: Type -> ParseMap -> ParseMap
checkResultType t pm =
    let m = parseMap pm
	i = lastIndex pm in
	    pm { parseMap = Map.insert i 
		 (mapMaybe (filterByResultType (typeAliases pm) t) 
		 $ lookUp m i) m }

resolve :: GlobalAnnos -> Assumps -> TypeMap 
	-> (Type, Term) -> State Int (Result (Type, Term))
resolve g ops tm (ty, trm) =
    do c <- get
       let pm = checkResultType ty $ resolveToParseMap g ops tm c ty trm
	   ds = failDiags pm
	   ts = getAppls g pm 
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
       let tm = typeMap s
	   as = assumps s
	   c = counter s
	   ga = globalAnnos s
           (r, c2) = runState (resolve ga as tm (ty, trm)) c
       put s { counter = c2 }
       return $ fmap snd r 
