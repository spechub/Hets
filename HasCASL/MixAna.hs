
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
import HasCASL.PrintAs
import HasCASL.Le
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import Common.Lexer
import Common.PrettyPrint
import qualified Common.Lib.Map as Map
import Control.Monad
import Control.Monad.State
import qualified Char as C
import Data.Maybe(mapMaybe)
import HasCASL.Unify

-- Earley Algorithm

data PState = PState { ruleId :: Id        -- the rule to match
		     , ruleScheme :: TypeScheme -- to make id unique
                     , ruleType :: Type    -- type of Id
                     , posList :: [Pos]    -- positions of Id tokens
		     , ruleArgs :: [Term]  -- currently collected arguments 
		                           -- both in reverse order
		     , restRule :: [Token] -- part of the rule after the "dot"
		     , stateNo :: Int -- index into the ParseMap/input string
		     }

instance Eq PState where
    PState r1 s1 _ _ _ t1 p1 == PState r2 s2 _ _ _ t2 p2 =
	(r1, s1, t1, p1) == (r2, s2, t2, p2)

instance Show PState where
    showsPrec _ (PState r _ _ _ _ d p) = showChar '{' 
				 . showSepList (showString "") showTok first
				 . showChar '.' 
				 . showSepList (showString "") showTok d
				 . shows p . showChar '}'
	where first = take (length v - length d) v
	      v = getTokenList place r


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

mkState :: Int -> (Id, OpInfo) -> State Int PState 
mkState i (ide, info) = 
    do let sc = opType info
	   side = stripFinalPlaces ide
       t <- freshInst sc
       return $ PState side sc t [] [] (getTokenList termStr side) i

mkApplState :: Int -> (Id, OpInfo) -> State Int PState 
mkApplState i (ide, info) =     
    do let sc = opType info
       t <- freshInst sc
       return $ PState ide sc t [] [] (getTokenList place ide) i

listId :: Id
-- unique id (usually "[]" yields two tokens)
listId = Id [mkSimpleId "[]"] [] []


listStates :: GlobalAnnos -> Int -> State Int [PState]
-- no empty list (can be written down directly)
listStates g i = 
    do ty <- freshType star
       let listState toks = PState listId (simpleTypeScheme $ 
					   BracketType Squares [] []) 
			    ty [] [] toks i
	   (b1, b2) = listBrackets g
       return $ if null b1 || null b2 then []
	      else [ listState (b1 ++ [termTok] ++ b2) 
		     , listState (b1 ++ [termTok, commaTok] ++ b2)]

tupleStates :: Int -> State Int [PState]
tupleStates i = 
    do ty <- freshType star
       let tupleState toks = PState (Id [parenTok] [] [])
			     (simpleTypeScheme $ 
			      BracketType Parens [] []) 
			     ty [] [] toks i
	   (b1, b2) = ([mkSimpleId "("], [mkSimpleId ")"])
       return [ tupleState (b1 ++ b2) 
	      , tupleState (b1 ++ [termTok] ++ b2) 
	      , tupleState (b1 ++ [termTok, commaTok] ++ b2)]

-- these are the possible matches for the nonterminal (T)
-- the same states are used for the predictions  

initialState :: GlobalAnnos -> [(Id, OpInfo)] -> Int -> State Int [PState]
initialState g ids i = 
    do ls <- listStates g i
       ts <- tupleStates i
       l1 <- mapM (mkState i) ids
       l2 <- mapM (mkApplState i) $ filter (isMixfix . fst) ids   
       let ty = MixfixType []
	   sc = simpleTypeScheme ty
	   mkTokState r = PState r sc ty
			     [] [] (getTokenList place r) i
       return (mkTokState parenId : 
	       mkTokState colonId :
	       mkTokState asId :
	       mkTokState inId :
	       mkTokState varId :
	       mkTokState opId :
	       mkTokState litId :
	       mkTokState applId :
	       ls ++ ts ++ l1 ++ l2)


lookUp :: (Ord a, MonadPlus m) => Map.Map a (m b) -> a -> (m b)
lookUp ce k = Map.findWithDefault mzero k ce

-- match (and shift) a token (or partially finished term)

scan :: Term -> Int -> ParseMap -> ParseMap
scan trm i cm =
  let t = case trm of 
	  TermToken x -> if isLitToken x then litTok else
			 x 
	  _ -> litTok
      m = parseMap cm
  in
    cm { parseMap = Map.insert (i+1) ( 
       foldr (\ (PState o sc ty b a ts k) l ->
	      if null ts || head ts /= t then l 
	      else let p = tokPos t : b in 
                   if t == commaTok then 
	      -- list elements separator
	             (PState o sc ty p a 
		      (termTok : commaTok : tail ts) k)
                     : (PState o sc ty p a (termTok : tail ts) k) : l
              else if t == parenTok || t == litTok then
                     (PState o sc ty b (trm : a) (tail ts) k) : l
              else if t == varTok || t == opTok || t == predTok then
                     (PState o sc ty b [trm] (tail ts) k) : l
	      else if t == colonTok || t == asTok then
	             (PState o sc ty b [mkTerm $ head a] [] k) : l
	           else (PState o sc ty p a (tail ts) k) : l) [] 
	      (lookUp m i)) m }
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
toAppl g s =
    if ruleId s == listId then    
       case list_lit $ literal_annos g of
       Nothing -> error "toAppl" 
       Just (b, c, f) -> 
	   let (b1, b2) = getListBrackets b
               nb1 = length b1
               nb2 = length b2
               ra = reverse $ ruleArgs s
               na = length ra
	       br = reverse $ posList s
               nb = length br
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null ra then asAppl c [] 
		  (if null br then nullPos else head br)
	      else if nb + 1 == nb1 + nb2 + na then
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
       ExplGroup BothDirections -> False
       ExplGroup NoDirection -> not $ isInfix arg

checkAnyArg :: GlobalAnnos -> Id -> Id -> Bool
checkAnyArg g op arg = 
    case precRel (prec_annos g) op arg of
    ExplGroup BothDirections -> isInfix op && op == arg
    _ -> True				       

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
filterByPrec :: GlobalAnnos -> PState -> PState -> Bool
filterByPrec _ _ (PState _ _ _ _ _ [] _) = False 
filterByPrec g (PState argIde _ _ _ _ _ _) 
		 (PState opIde _ _ _ args (hd:_) _) = 
       if hd == termTok then 
	  if opIde == listId || argIde == listId then True
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
 
filterByType :: ParseMap -> PState -> PState -> Maybe PState
filterByType cm argState opState =
    let tm = typeAliases cm in
    if ruleId opState == applId && null (ruleArgs opState) then 
       Just (addArgState argState opState) { ruleType = ruleType argState }
    else 
    case expandType tm $ ruleType opState of
		FunType t1 _ t2 _ -> 
		    case expandType tm t1 of 
		    argType -> 
			do s <- maybeResult $ unify tm argType
				$ ruleType argState
			   return (addArgState argState opState) 
				      {ruleType = subst s t2}
		TypeName _ _ v -> if v == 0 then Nothing
				  else Just $ addArgState argState opState
		_ -> Nothing

-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> PState -> [PState]
-- pre: finished rule 
collectArg g m s@(PState _ _ _ _ _ _ k) = 
    map (\ p -> p { restRule = tail $ restRule p })  
    $ mapMaybe (filterByType m s)
    $ filter (filterByPrec g s)
    $ lookUp (parseMap m) k

compl :: GlobalAnnos -> ParseMap -> [PState] -> [PState]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (PState _ _ _ _ _ ts _) -> null ts) l

complRec :: GlobalAnnos -> ParseMap -> [PState] -> [PState]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> ParseMap -> ParseMap
complete g i cm =
    let m = parseMap cm in
    cm { parseMap = Map.insert i (complRec g cm $ lookUp m i) m }

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

data ParseMap = ParseMap { varCount :: Int
			 , typeAliases :: TypeMap  
			 , parseMap :: Map.Map Int [PState]
			 }

predict :: GlobalAnnos -> [(Id, OpInfo)] -> Int -> ParseMap -> ParseMap
predict g is i cm = 
    let m = parseMap cm in 
    if i /= 0 && any (\ (PState _ _ _ _ _ ts _) -> not (null ts) 
			 && head ts == termTok) 
		 (lookUp m i)
		 then let (ps, c2) = runState (initialState g is i) 
				     (varCount cm)
		      in cm { varCount = c2
			    , parseMap = Map.insertWith (++) i ps m }
		 else cm

data Chart = Chart { chartCount :: Int
		   , chartDiags :: [Diagnosis]
		   , chartMap :: ParseMap }

incrChartCount :: Chart -> Chart
incrChartCount c = c { chartCount = chartCount c + 1 }

addChartDiags :: [Diagnosis] -> Chart -> Chart
addChartDiags ds c = c { chartDiags = ds ++ chartDiags c } 

nextState :: GlobalAnnos -> [(Id, OpInfo)] -> Term -> Chart -> Chart
nextState g is trm c@(Chart { chartCount = i }) =
    let cm1 = predict g is i $ chartMap c
        cm2 = complete g (i+1) $
		 scan trm i cm1
	c2 = incrChartCount c 
    in if null (lookUp (parseMap cm2) (i+1)) && null (chartDiags c)
       then addChartDiags [mkDiag Error "unexpected mixfix token" trm] c2
       else c2 { chartMap = cm2 }

iterateStates :: GlobalAnnos -> [(Id, OpInfo)] -> [Term] -> Chart -> Chart
iterateStates g ops terms c = 
    let self = iterateStates g ops
        _resolveTerm = resolve g ops
    in if null terms then c
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) c
            BracketTerm b ts ps -> self 
	       (expandPos TermToken (getBrackets b) ts ps ++ tail terms) c
	    t ->  self (tail terms) (nextState g ops t c)

getAppls :: GlobalAnnos -> Int -> ParseMap -> [Term]
getAppls g i m = 
    map (toAppl g) $ 
	filter (\ (PState _ _ _ _ _ ts k) -> null ts && k == 0) $ 
	     lookUp (parseMap m) i

resolve :: GlobalAnnos -> [(Id, OpInfo)] -> ParseMap -> Term -> Result Term
resolve g ops p trm =
    let (ps, c2) = runState (initialState g ops 0) (varCount p)
        Chart { chartCount = i, chartDiags = ds, chartMap = m } = 
	    iterateStates g ops [trm] 
		     Chart { chartCount = 0
			   , chartDiags = []
			   , chartMap = p { varCount = c2
					  , parseMap = Map.single 0 $ ps } } 
        ts = getAppls g i m 
    in if null ts then if null ds then 
                        plain_error trm ("no resolution for term: "
					     ++ showPretty trm "")
					    (nullPos)
		       else Result ds (Just trm)
       else if null $ tail ts then Result ds (Just (head ts))
	    else Result (Diag Error ("ambiguous mixfix term\n\t" ++ 
			 (concatMap ( \ t -> showPretty t "\n\t" )
			 $ take 5 ts)) (nullPos) : ds) (Just trm)

resolveTerm ::  Term -> State Env (Result Term)
resolveTerm t = 
    do tm <- getTypeMap
       as <- getAssumps
       c <- getCounter
       ga <- getGlobalAnnos
       let ops = concatMap (\ (i, l) -> map ( \ e -> (i, e)) l) 
		 $ Map.toList as  
       return $ resolve ga ops (ParseMap c tm Map.empty) t  		  
