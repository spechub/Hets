
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
import HasCASL.AsUtils()
import HasCASL.Le
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import Common.Result
import Common.Id
import Common.Lexer
import qualified Common.Lib.Map as Map
import Control.Monad
import Control.Monad.State
import qualified Char as C
import Data.List(intersperse)
import HasCASL.Unify

-- Earley Algorithm

data PState = PState { ruleId :: Id        -- the rule to match
                     , ruleType :: Type    -- type of Id
                     , posList :: [Pos]    -- positions of Id tokens
		     , ruleArgs :: [Term]  -- currently collected arguments 
		                           -- both in reverse order
		     , restRule :: [Token] -- part of the rule after the "dot"
		     , stateNo :: Int -- index into the ParseMap/input string
		     }

instance Eq PState where
    PState r1 _ _ _ t1 p1 == PState r2 _ _ _ t2 p2 =
	(r1, t1, p1) == (r2, t2, p2)

instance Ord PState where
    PState r1 _ _ _ t1 p1 <= PState r2 _ _ _ t2 p2 =
	(r1, t1, p1) <= (r2, t2, p2)

instance Show PState where
    showsPrec _ (PState r _ _ _ d p) = showChar '{' 
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

stripFinalPlaces :: Id -> Id
stripFinalPlaces (Id ts cs ps) =
    Id (fst $ splitMixToken ts) cs ps 

mkState :: Int -> (Id, OpInfo) -> State Int PState 
mkState i (ide, info) = 
    do t <- freshInst $ opType info 
       return $ PState ide t [] [] 
			      (getTokenList termStr $ stripFinalPlaces ide) i

mkApplState :: Int -> (Id, OpInfo) -> State Int PState 
mkApplState i (ide, info) =     
    do t <- freshInst $ opType info 
       return $ PState ide t [] [] (getTokenList place ide) i

listId :: Id
-- unique id (usually "[]" yields two tokens)
listId = Id [mkSimpleId "[]"] [] []


listStates :: GlobalAnnos -> Int -> State Int [PState]
-- no empty list (can be written down directly)
listStates g i = 
    do ty <- freshType star
       let listState toks = PState listId ty [] [] toks i
	   (b1, b2) = listBrackets g
       return $ if null b1 || null b2 then []
	      else [ listState (b1 ++ [termTok] ++ b2) 
		     , listState (b1 ++ [termTok, commaTok] ++ b2)]

-- these are the possible matches for the nonterminal (T)
-- the same states are used for the predictions  

initialState :: GlobalAnnos -> [(Id, OpInfo)] -> Int -> State Int [PState]
initialState g ids i = 
    do ls <- listStates g i
       l1 <- mapM (mkState i) ids
       l2 <- mapM (mkApplState i) ids   
       let mkTokState toks = PState (Id toks [] []) (MixfixType []) 
			     [] [] toks i
       return (mkTokState [parenTok] : 
	       mkTokState [termTok, colonTok] :
	       mkTokState [termTok, asTok] :
	       mkTokState [termTok, inTok] :
	       mkTokState [varTok] :
	       mkTokState [opTok] :
	       mkTokState [litTok] :
	       mkTokState [termTok, termTok] :
	       ls ++ l1 ++ l2)


lookUp :: (Ord a, MonadPlus m) => Map.Map a (m b) -> a -> (m b)
lookUp ce k = Map.findWithDefault mzero k ce

-- match (and shift) a token (or partially finished term)

scan :: Term -> Int -> ParseMap -> ParseMap
scan trm i cm =
  let t = case trm of 
	  TermToken x -> if isLitToken x then litTok else
			 x 
      m = parseMap cm
  in
    cm { parseMap = Map.insert (i+1) ( 
       foldr (\ (PState o ty b a ts k) l ->
	      if null ts || head ts /= t then l 
	      else let p = tokPos t : b in 
                   if t == commaTok && o == listId then 
	      -- list elements separator
	             (PState o ty p a 
		      (termTok : commaTok : tail ts) k)
                     : (PState o ty p a (termTok : tail ts) k) : l
              else if t == parenTok then
                     (PState o ty b (trm : a) (tail ts) k) : l
              else if t == varTok || t == opTok || t == predTok then
                     (PState o ty b [trm] (tail ts) k) : l
	      else if t == colonTok || t == asTok then
	             (PState o ty b [mkTerm $ head a] [] k) : l
	           else (PState o ty p a (tail ts) k) : l) [] 
	      (lookUp m i)) m }
     where mkTerm t1 = case trm of 
			  _ -> t1
	      
-- construct resulting term from PState 

stateToAppl :: PState -> Term
stateToAppl (PState ide _ rs a _ _) = 
    let vs = getTokenList place ide 
        ar = reverse a
        _qs = reverse rs
    in if  vs == [termTok, colonTok] 
	   || vs == [termTok, asTok] 
	   || vs == [varTok] 
           || vs == [opTok]
           || vs == [predTok]
           || vs == [parenTok]
       then head ar
       else head ar

toAppl :: GlobalAnnos -> PState -> Term
toAppl g s@(PState i _ bs a _ _) =
    if i == listId then    
       case list_lit $ literal_annos g of
       Nothing -> error "toAppl" 
       Just (_, c, f) -> 
	   let (b1, b2) = listBrackets g
               nb1 = length b1
               nb2 = length b2
               ra = reverse a
               na = length ra
               nb = length bs
	       mkList [] ps = asAppl c [] (head ps)
	       mkList (hd:tl) ps = asAppl f [hd, mkList tl (tail ps)] (head ps)
	   in if null a then asAppl c [] (if null bs then nullPos else last bs)
	      else if nb + 1 == nb1 + nb2 + na then
		   let br = reverse bs 
		       br1 = drop (nb1 - 1) br 
	           in  mkList (reverse a) br1  
		   else error "toAppl"
    else stateToAppl s

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
filterByPrec _ _ (PState _ _ _ _ [] _) = False 
filterByPrec g (PState argIde _ _ _ _ _) (PState opIde _ _ args (hd:_) _) = 
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

filterByType :: ParseMap -> PState -> PState -> Bool
filterByType cm argState opState = 
    case ruleType (opState) of
		t@(TypeName _ _ _) -> 
		    let (newT, b) = expandAlias (typeAliases cm) t in
			if b then filterByType cm argState 
                                  opState {ruleType = newT}
			else False 
		FunType t1 a t2 _ -> True
		_ -> False

-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> PState -> [PState]
-- pre: finished rule 
collectArg g m s@(PState _ _ _ _ _ k) = 
    foldr (\ (PState o ty b a ts k1) l ->
	 PState o ty b (toAppl g s : a) 
	 (tail ts) k1 : l) []
    $ filter (filterByType m s)
    $ filter (filterByPrec g s)
    $ lookUp (parseMap m) k

compl :: GlobalAnnos -> ParseMap -> [PState] -> [PState]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (PState _ _ _ _ ts _) -> null ts) l

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
    if i /= 0 && any (\ (PState _ _ _ _ ts _) -> not (null ts) 
			 && head ts == termTok) 
		 (lookUp m i)
		 then let (ps, c2) = runState (initialState g is i) 
				     (varCount cm)
		      in cm { varCount = c2
			    , parseMap = Map.insertWith (++) i ps m }
		 else cm

type Chart = (Int, [Diagnosis], ParseMap)

nextState :: GlobalAnnos -> [(Id, OpInfo)] -> Term -> Chart -> Chart
nextState g is trm (i, ds, m) =
    let cm1 = predict g is i m
        cm2 = complete g (i+1) $
		 scan trm i cm1
    in if null (lookUp (parseMap cm2) (i+1)) && null ds
		    then (i+1, mkDiag Error "unexpected mixfix token" trm
			       : ds, m)
       else (i+1, ds, cm2)

iterateStates :: GlobalAnnos -> [(Id, OpInfo)] -> [Term] -> Chart -> Chart
iterateStates g ops terms c = 
    let self = iterateStates g ops
        _resolveTerm = resolve g ops
    in if null terms then c
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) c
            BracketTerm _ ts ps -> 
		self (expand "[" "]" ts ps ++ tail terms) c
	    t ->  self (tail terms) (nextState g ops t c)
  where expand = expandPos TermToken 

getAppls :: GlobalAnnos -> Int -> ParseMap -> [Term]
getAppls g i m = 
    map (toAppl g) $ 
	filter (\ (PState _ _ _ _ ts k) -> null ts && k == 0) $ 
	     lookUp (parseMap m) i

resolve :: GlobalAnnos -> [(Id, OpInfo)] -> ParseMap -> Term -> Result Term
resolve g ops p trm =
    let (ps, c2) = runState (initialState g ops 0) (varCount p)
        (i, ds, m) = iterateStates g ops [trm] 
		     (0, [], p { varCount = c2, parseMap =  
				 Map.single 0 $ ps} ) 
        ts = getAppls g i m
    in if null ts then if null ds then 
                        plain_error trm ("no resolution for term: "
					     ++ show trm)
					    (nullPos)
		       else Result ds (Just trm)
       else if null $ tail ts then Result ds (Just (head ts))
	    else Result (Diag Error ("ambiguous mixfix term\n\t" ++ 
			 (concat  
			 $ intersperse "\n\t" 
			 $ map (show) 
			 $ take 5 ts)) (nullPos) : ds) (Just trm)

asAppl :: Id -> [Term] -> Pos -> Term
asAppl f args p = let pos = if null args then [] else [p]
		  in ApplTerm (QualOp (InstOpId f [] [])
			       (simpleTypeScheme $ MixfixType []) 
			       []) (TupleTerm args []) pos
