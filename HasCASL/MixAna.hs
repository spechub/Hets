
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder 2003

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  non-portable 

Mixfix analysis of terms, adapted from the CASL analysis

-}

module HasCASL.MixAna where 

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.Le
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import Common.Lexer
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Common.Lib.State
import Data.Maybe
import HasCASL.Unify

-- Earley Algorithm


-- avoid confusion with the variable counter Int
newtype Index = Index Int deriving (Eq, Ord, Show)

-- deriving Num is also possible  
-- but the following functions are sufficient
startIndex :: Index
startIndex = Index 0

-- (also hiding (==) seems not possible) 
isStartIndex :: Index -> Bool
isStartIndex = (== startIndex)

incrIndex :: Index -> Index
incrIndex (Index i) = Index (i + 1)

data PState = PState { ruleId :: Id        -- the rule to match
		     , ruleScheme :: TypeScheme -- to make id unique
                     , ruleType :: Type    -- type of Id
                     , posList :: [Pos]    -- positions of Id tokens
		     , ruleArgs :: [Term]  -- currently collected arguments 
		                           -- both in reverse order
		     , restRule :: [Token] -- part of the rule after the "dot"
		     , stateNo :: Index -- index into the ParseMap/input string
		     }

instance Eq PState where
    PState r1 s1 _ _ _ t1 p1 == PState r2 s2 _ _ _ t2 p2 =
	(r1, s1, t1, p1) == (r2, s2, t2, p2)

instance Show PState where
    showsPrec _ p = 
	let d = restRule p
	    v = getTokenList place (ruleId p)
	    first = take (length v - length d) v
	    Index i = stateNo p 
	    in showChar '{' 
			  . showSepList (showString "") showTok first
			  . showChar '.' 
			  . showSepList (showString "") showTok d
			  . shows i . showChar '}'



termStr :: String
termStr = "(T)"
commaTok, parenTok, termTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId termStr
parenTok = mkSimpleId "(..)" 

colonTok, asTok, varTok, opTok, predTok, inTok, caseTok, litTok :: Token
colonTok = mkSimpleId ":"
asTok = mkSimpleId "as"
inTok = mkSimpleId "in"
caseTok = mkSimpleId "case"
varTok = mkSimpleId "(v)"
opTok = mkSimpleId "(o)"
predTok = mkSimpleId "(p)"
litTok = mkSimpleId "\""

mkRuleId :: [Token] -> Id
mkRuleId toks = Id toks [] []
applId, parenId, colonId, asId, inId, varId, opId, litId :: Id
applId       = mkRuleId [termTok, termTok]
parenId      = mkRuleId [parenTok]
colonId      = mkRuleId [termTok, colonTok]
asId         = mkRuleId [termTok, asTok]
inId  	     = mkRuleId [termTok, inTok]
varId	     = mkRuleId [varTok]
opId	     = mkRuleId [opTok]
litId	     = mkRuleId [litTok]

mkPState :: Index -> Id -> TypeScheme -> Type -> [Token] -> PState
mkPState ind ide sc ty toks = 
    PState { ruleId = ide
	   , ruleScheme = sc
	   , ruleType = ty
	   , posList = []
	   , ruleArgs = []
	   , restRule = toks
	   , stateNo = ind }

mkState :: Index -> (Id, OpInfo) -> State Int PState 
mkState i (ide, info) = 
    do let sc = opType info
       t <- freshInst sc
       let stripped = case t of 
			     FunType t1 _ _ _ -> 
				 case t1 of 
					 ProductType _ _ -> ide
					 _ -> stripFinalPlaces ide
			     _ -> stripFinalPlaces ide
       return $ mkPState i stripped sc t $ getTokenList termStr stripped

mkApplState :: Index -> (Id, OpInfo) -> State Int PState 
mkApplState i (ide, info) =     
    do let sc = opType info
       t <- freshInst sc
       return $ mkPState i ide sc t $ getTokenList place ide

listToken :: Token 
listToken = mkSimpleId "[]"
listId :: Id -> Id
-- unique id (usually "[]" yields two tokens)
listId i = Id [listToken] [i] []

isListId :: Id -> Bool
isListId (Id ts cs _) = not (null ts) && head ts == listToken && length cs == 1

listStates :: GlobalAnnos -> Index -> State Int [PState]
-- no empty list (can be written down directly)
listStates g i = 
    do ty <- freshType star
       let lists = list_lit $ literal_annos g
	   listState co toks = mkPState i (listId co) (simpleTypeScheme $ 
					   BracketType Squares [] []) 
			       ty toks
	   in return $ concatMap ( \ (bs, n, c) ->
	     let (b1, b2, cs) = getListBrackets bs 
		 e = Id (b1 ++ b2) cs [] in
	     (if e == n then [] -- add b1 ++ b2 if its not yet included by n
	      else [listState c $ getTokenList place e]) ++
                   [listState c (b1 ++ [termTok] ++ b2) 
		   , listState c (b1 ++ [termTok, commaTok] ++ b2)]
		   ) $ Set.toList lists

-- these are the possible matches for the nonterminal (T)
-- the same states are used for the predictions  

initialState :: GlobalAnnos -> [(Id, OpInfo)] -> Index -> State Int [PState]
initialState g ids i = 
    do ls <- listStates g i
       l1 <- mapM (mkState i) ids
       l2 <- mapM (mkApplState i) $ filter (isMixfix . fst) ids   
       let ty = MixfixType []
	   sc = simpleTypeScheme ty
	   mkTokState r = mkPState i r sc ty $ getTokenList place r
       return (mkTokState parenId : 
	       mkTokState colonId :
	       mkTokState asId :
	       mkTokState inId :
	       mkTokState varId :
	       mkTokState opId :
	       mkTokState litId :
	       mkTokState applId :
	       ls ++ l1 ++ l2)

lookUp :: (Ord a) => Map.Map a [b] -> a -> [b]
lookUp ce k = Map.findWithDefault [] k ce

data ParseMap = ParseMap { varCount :: Int
			 , typeAliases :: TypeMap
			 , lastIndex :: Index
			 , failDiags :: [Diagnosis]
			 , parseMap :: Map.Map Index [PState]
			 }

addArgument :: TypeMap -> Term -> PState -> [PState]
addArgument tm arg opState =
    let prevArgs = ruleArgs opState 
	newRule = tail $ restRule opState
	in
    case expandType tm $ ruleType opState of
		FunType _ _ t2 _ -> [
		    opState { ruleType = t2
			    , restRule = newRule
			    , ruleArgs = arg : prevArgs } ]
		_ -> [opState { restRule = newRule
				  , ruleArgs = arg: prevArgs } ]

-- match (and shift) a token (or partially finished term)
scan :: Term -> ParseMap -> ParseMap
scan trm pm =
  let m = parseMap pm
      tm = typeAliases pm
      i = lastIndex pm
      t = case trm of 
	  TermToken x -> if isLitToken x then litTok else
			 x 
	  _ -> litTok
      incI = incrIndex i
  in
    pm { lastIndex = incI
       , parseMap = Map.insert incI ( 
       foldr (\ p l ->
	      let ts = restRule p
	          a = ruleArgs p in
	      if null ts || head ts /= t then l 
	      else if t == commaTok then 
	      -- list elements separator
	             p { restRule = termTok : commaTok : tail ts }
	             : p { restRule = termTok : tail ts } : l
              else if t == parenTok || t == litTok then
	           addArgument tm trm p ++ l 
              else if t == varTok || t == opTok || t == predTok then
                     p { restRule = tail ts, ruleArgs = [trm] } : l 
	      else if t == colonTok || t == asTok then
	             p { restRule = [], ruleArgs = [mkTerm $ head a] } : l
	      else p { restRule = tail ts, posList = tokPos t : posList p } : l
	     ) [] (lookUp m i)) m }
     where mkTerm t1 = case trm of 
			  _ -> t1
	      
-- construct resulting term from PState 

stateToAppl :: PState -> Term
stateToAppl p = 
    let r = ruleId p
        ar = reverse $ ruleArgs p
	qs = reverse $ posList p
    in if r == colonId 
	   || r == asId 
	   || r == inId 
	   || r == litId 
	   || r == parenId 
	   || r == varId 
	   || r == opId 
       then head ar
       else if r == applId then
	    ApplTerm (head ar) (head (tail ar)) qs 
       else foldr (\ (a, q) t -> ApplTerm t a [q]) 
		(QualOp (InstOpId (ruleId p) [] []) (ruleScheme p) qs) 
		$ zip ar (posList p ++ repeat (if null qs then nullPos
					       else last qs))
	       
toAppl :: GlobalAnnos -> PState -> Term
toAppl g s = let i = ruleId s in
    if isListId i then    
           let Id _ [f] _ = i
	       ListCons b c = getLiteralType g f
	       (b1, _, _) = getListBrackets b
	       cl = length $ getTokenList place b
               nb1 = length b1
               ra = reverse $ ruleArgs s
               na = length ra
	       br = reverse $ posList s
               nb = length br
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null ra then asAppl c [] 
		  (if null br then nullPos else head br)
	      else if nb + 2 == cl + na then
		   let br1 = drop (nb1 - 1) br 
	           in  mkList ra br1  
		   else error "toAppl"
    else stateToAppl s

asAppl :: Id -> [Term] -> Pos -> Term
asAppl f args p = let pos = if null args then [] else [p]
		  in ApplTerm (QualOp (InstOpId f [] [])
			       (simpleTypeScheme $ MixfixType []) 
			       []) (TupleTerm args []) pos

-- precedence graph stuff

checkArg :: GlobalAnnos -> AssocEither -> Id -> Id -> Bool
checkArg g dir op arg = 
    if arg == op 
       then isAssoc dir (assoc_annos g) op || not (isInfix op)
       else 
       case precRel (prec_annos g) op arg of
       Lower -> True
       Higher -> False
       BothDirections -> False
       NoDirection -> not $ isInfix arg

checkAnyArg :: GlobalAnnos -> Id -> Id -> Bool
checkAnyArg g op arg = 
    case precRel (prec_annos g) op arg of
    BothDirections -> isInfix op && op == arg
    _ -> True				       

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
filterByPrec :: GlobalAnnos -> PState -> PState -> Bool
filterByPrec g PState { ruleId = argIde } 
		 PState { ruleId = opIde, ruleArgs = args, restRule = ts } =
    if null ts then False else
       if head ts == termTok then 
	  if isListId opIde || isListId argIde then True
	  else let n = length args in
		    if isLeftArg opIde n then 
		       if isPostfix opIde && (isPrefix argIde
					      || isInfix argIde) then False
		       else checkArg g ALeft opIde argIde 
		    else if isRightArg opIde n then 
                            if isPrefix opIde && isInfix argIde then False
	                    else checkArg g ARight opIde argIde
                         else checkAnyArg g opIde argIde
       else False

expandType :: TypeMap -> Type -> Type
expandType tm oldT = 
    case oldT of 
	   TypeName _ _ _ -> fst $ expandAlias tm oldT
	   KindedType t _ _ -> t
	   LazyType t _ -> t
	   _ -> oldT

addArgState :: PState -> PState -> PState
addArgState arg op = op { ruleArgs = stateToAppl arg : ruleArgs op }

mkTupleTerm :: TypeMap -> [Type] -> PState -> PState 
	    -> [Term] -> [Term] -> Type -> Maybe PState
mkTupleTerm tm types arg op prevTerms prevArgs argType =
    let n = length prevTerms 
	fini = n + 1 == length types in
    if n >= length types then Nothing 
    else do s <- maybeResult $ unify tm (types !! n) $ ruleType arg
	    let singleArg = stateToAppl arg
                argTerms = (if fini then reverse else id)
			   (singleArg : prevTerms)
		argTerm = if fini then if n == 0 then singleArg 
			               else TupleTerm argTerms (posList arg) 
			  else MixfixTerm argTerms
                newType = subst s (if fini then argType else
				  FunType (ProductType types []) 
				  PFunArr argType [])
	    return op { ruleArgs = argTerm : prevArgs
		      , ruleType = newType }
 
filterByType :: ParseMap -> PState -> PState -> Maybe PState
filterByType cm argState opState =
    let tm = typeAliases cm 
	prevArgs = ruleArgs opState in
    if ruleId opState == applId && null prevArgs then 
       Just (addArgState argState opState) { ruleType = ruleType argState }
    else 
    case expandType tm $ ruleType opState of
		(FunType t1 _ t2 _) -> 
		    case expandType tm t1 of 
		    ProductType ts _ -> 
			let (prevTerms, restArgs) = 
				if null prevArgs then ([], []) 
				else case head prevArgs of
				MixfixTerm trms -> (trms, tail prevArgs)
				_ -> ([], prevArgs) in
			mkTupleTerm tm ts argState opState 
				    prevTerms restArgs t2
		    expType -> mkTupleTerm tm [expType] argState opState 
			       [] prevArgs t2
		TypeName _ _ v -> if v == 0 then Nothing
				  else Just $ addArgState argState opState
		_ -> Nothing

-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> PState -> [PState]
-- pre: finished rule 
collectArg g m s = 
    map (\ p -> p { restRule = tail $ restRule p })  
    $ mapMaybe (filterByType m s)
    $ filter (filterByPrec g s)
    $ lookUp (parseMap m) $ stateNo s

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

predict :: GlobalAnnos -> [(Id, OpInfo)] -> ParseMap -> ParseMap
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

nextState :: GlobalAnnos -> [(Id, OpInfo)] -> Term -> ParseMap -> ParseMap
nextState g is trm pm =
    let pm3 = complete g
	      $ scan trm
	      $ predict g is pm
    in if (null $ lookUp (parseMap pm3) $ lastIndex pm3) 
	   && null (failDiags pm3)
       then  pm3 { failDiags = [mkDiag Error "unexpected mixfix token" trm] }
       else pm3

iterStates :: GlobalAnnos -> [(Id, OpInfo)] -> [Term] -> ParseMap -> ParseMap
iterStates g ops terms pm = 
    let self = iterStates g ops
        resolveInternal = resolve g ops (typeAliases pm) Nothing
    in if null terms then pm
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) pm
            BracketTerm Parens ts ps -> 
		let (rtsNew, c2) = runState (mapM resolveInternal ts) 
					 $ varCount pm 
		    Result mds v = 
			do ttsNew <- sequence rtsNew
			   let tsNew = map snd ttsNew
			   return (if length tsNew == 1 then head tsNew 
				   else TupleTerm tsNew ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		in self (tail terms) $ nextState g ops tNew 
		   pm { varCount = c2, failDiags = mds ++ failDiags pm }
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) pm
	    t ->  self (tail terms) (nextState g ops t pm)

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

resolveToParseMap :: GlobalAnnos -> [(Id, OpInfo)] -> TypeMap -> Int 
		  -> Term -> ParseMap
resolveToParseMap g ops tm c trm = 
    let (initStates, c2) = runState (initialState g ops startIndex) c in
    iterStates g ops [trm] 
	       ParseMap { lastIndex = startIndex
			, typeAliases = tm
			, failDiags = []  
			, varCount = c2
			, parseMap = Map.single startIndex initStates }

checkResultType :: Maybe Type -> ParseMap -> ParseMap
checkResultType mt pm =
    case mt of 
    Nothing -> pm
    Just t ->  let m = parseMap pm
		   i = lastIndex pm in
		       pm { parseMap = Map.insert i 
			(mapMaybe (filterByResultType (typeAliases pm) t) 
			$ lookUp m i) m }

filterByResultType :: TypeMap -> Type -> PState -> Maybe PState
filterByResultType tm t p = 
    do let rt = ruleType p 
       s <- maybeResult $ unify tm t rt
       return p { ruleType = subst s rt } 

resolve :: GlobalAnnos -> [(Id, OpInfo)] -> TypeMap 
	-> Maybe Type -> Term -> State Int (Result (Type, Term))
resolve g ops tm ty trm =
    do c <- get
       let pm = checkResultType ty $ resolveToParseMap g ops tm c trm
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

resolveTermWithType :: Maybe Type -> Term -> State Env (Result Term)
resolveTermWithType ty trm = 
    do s <- get
       let tm = typeMap s
	   as = assumps s
	   c = counter s
	   ga = globalAnnos s
           ops = concatMap (\ (i, l) -> map ( \ e -> (i, e)) l) 
		 $ Map.toList as  
           (r, c2) = runState (resolve ga ops tm ty trm) c
       put s { counter = c2 }
       return $ fmap snd r 

resolveTerm :: Term -> State Env (Result Term)
resolveTerm = resolveTermWithType Nothing



 		  
