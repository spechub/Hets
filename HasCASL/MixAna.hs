
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
import Common.GlobalAnnotations
import Common.GlobalAnnotationsFunctions
import CASL.MixfixParser (expandPos, getTokenList)
import Common.Result
import Common.Id
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import Control.Monad
import qualified Char as C
import Data.List(intersperse)

-- Earley Algorithm

data State = State Id
                   [Pos]    -- positions of Id tokens
                   [Term]   -- currently collected arguments 
		                               -- both in reverse order
		   [Token]  -- only tokens after the "dot" are given 
		   Int      -- index into the ParseMap/input string

instance Eq State where
    State r1 _ _ t1 p1 == State r2 _ _ t2 p2 =
	r1 == r2 && t1 == t2 && p1 == p2

instance Ord State where
    State r1 _ _ t1 p1 <= State r2 _ _ t2 p2 =
	if r1 == r2 then
	       if t1 == t2 then p1 <= p2
	       else t1 <= t2
	else r1 <= r2

instance Show State where
    showsPrec _ (State r _ _ d p) = showChar '{' 
				 . showSepList (showString "") showTok first
				 . showChar '.' 
				 . showSepList (showString "") showTok d
				 . shows p . showChar '}'
	where first = take (length v - length d) v
	      v = getTokenList True r


commaTok, parenTok, termTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId "(T)"
parenTok = mkSimpleId "(..)" 

colonTok, asTok, varTok, opTok, predTok, inTok :: Token
colonTok = mkSimpleId ":"
asTok = mkSimpleId "as"
inTok = mkSimpleId "in"
varTok = mkSimpleId "(v)"
opTok = mkSimpleId "(o)"
predTok = mkSimpleId "(p)"

mkState :: Int -> Id -> State 
mkState i ide = State ide [] [] (getTokenList False ide) i

mkApplState :: Int -> Id -> State
mkApplState i ide = State ide [] [] 
		    (getTokenList True ide ++ [parenTok]) i

listId :: Id
-- unique id (usually "[]" yields two tokens)
listId = Id [mkSimpleId "[]"] [] []

getListBrackets :: Id -> ([Token], [Token])
getListBrackets (Id b _ _) = 
    let (b1, rest) = break isPlace b
	b2 = if null rest then [] 
	     else filter (not . isPlace) rest
    in (b1, b2)

listStates :: GlobalAnnos -> Int -> [State]
-- no empty list (can be written down directly)
listStates g i = 
    let listState toks = State listId [] [] toks i
    in case list_lit (literal_annos g) of
		Nothing -> []
		Just (bs, c, _) -> 
		    let (b1, b2) = getListBrackets bs
			el = b1++b2
		        ls = [ listState (b1 ++ [termTok] ++ b2) 
			     , listState (b1 ++ [termTok, commaTok] ++ b2)]
		     in if c == Id el [] [] then ls 
		        -- don't put in empty list twice
			else listState el : ls

-- these are the possible matches for the nonterminal TERM
-- the same states are used for the predictions  

initialState :: GlobalAnnos -> Set.Set Id -> Int -> [State]
initialState g ids i = 
    let mkTokState toks = State (Id toks [] []) [] [] toks i
        is = Set.toList ids
    in mkTokState [parenTok] : 
       mkTokState [termTok, colonTok] :
       mkTokState [termTok, asTok] :
       mkTokState [termTok, inTok] :
       mkTokState [varTok] :
       mkTokState [opTok] :
       mkTokState [opTok, parenTok] :
       mkTokState [predTok] :
       mkTokState [predTok, parenTok] :
       listStates g i ++
       map (mkState i) is ++ 
       map (mkApplState i) is

type ParseMap = Map.Map Int [State]

lookUp :: (Ord a, MonadPlus m) => Map.Map a (m b) -> a -> (m b)
lookUp ce k = Map.findWithDefault mzero k ce

-- match (and shift) a token (or partially finished term)

scan :: Term -> Int -> ParseMap -> ParseMap
scan trm i m = 
  let t = case trm of 
	  TermToken x -> x
  in
    Map.insert (i+1) ( 
       foldr (\ (State o b a ts k) l ->
	      if null ts || head ts /= t then l 
	      else let p = tokPos t : b in 
                   if t == commaTok && o == listId then 
	      -- list elements separator
	             (State o p a 
		      (termTok : commaTok : tail ts) k)
                     : (State o p a (termTok : tail ts) k) : l
              else if t == parenTok then
                     (State o b (trm : a) (tail ts) k) : l
              else if t == varTok || t == opTok || t == predTok then
                     (State o b [trm] (tail ts) k) : l
	      else if t == colonTok || t == asTok then
	             (State o b [mkTerm $ head a] [] k) : l
	           else (State o p a (tail ts) k) : l) [] 
	      (lookUp m i)) m
     where mkTerm t1 = case trm of 
			  _ -> t1
	      
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
	  
filterByPrec :: GlobalAnnos -> State -> State -> Bool
filterByPrec _ _ (State _ _ _ [] _) = False 
filterByPrec g (State argIde _ _ _ _) (State opIde _ args (hd:_) _) = 
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

-- reconstructing positions 

setPlainIdePos :: Id -> [Pos] -> (Id, [Pos]) 
setPlainIdePos (Id ts cs _) ps =
   let (places, toks) = span isPlace (reverse ts) 
       pls = reverse places
       f = zipWith (\ a b -> up_pos (const b) a)
       (ps1, ps2) = splitAt (length toks) ps
       front = f (reverse toks) ps1
   in if null cs then 
      let (ps3, ps4) = splitAt (length pls) ps2
      in (Id (front ++ f pls ps3) [] [], ps4)
      else let (newCs, ps3, ps4) = foldl (\ (prevCs, seps, rest) a -> 
				  let (c1, qs) = setPlainIdePos a rest
				  in (c1: prevCs, head qs : seps, tail qs))
			   ([], [head ps2], tail ps2) cs
	       (ps6, ps7) = splitAt (length pls) ps4
           in (Id (front ++ f pls ps6) (reverse newCs) (reverse ps3), ps7)

stateToAppl :: State -> Term
stateToAppl (State ide rs a _ _) = 
    let vs = getTokenList True ide 
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

asListAppl :: GlobalAnnos -> State -> Term
asListAppl g s@(State i bs a _ _) =
    if i == listId then    
       case list_lit $ literal_annos g of
       Nothing -> error "asListAppl" 
       Just (b, c, f) -> 
	   let (b1, b2) = getListBrackets b
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
		   else error "asListAppl"
    else stateToAppl s

-- final complete/reduction phase 
-- when a grammar rule (mixfix Id) has been fully matched

collectArg :: GlobalAnnos -> ParseMap -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ k) = 
    map (\ (State o b a ts k1) ->
	 State o b (asListAppl g s : a) 
	 (tail ts) k1)
    $ filter (filterByPrec g s)
    $ lookUp m k

compl :: GlobalAnnos -> ParseMap -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ ts _) -> null ts) l

complRec :: GlobalAnnos -> ParseMap -> [State] -> [State]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> ParseMap -> ParseMap
complete g i m = Map.insert i (complRec g m $ lookUp m i) m

-- predict which rules/ids might match for (the) nonterminal(s) (termTok)
-- provided the "dot" is followed by a nonterminal 

predict :: GlobalAnnos -> Set.Set Id -> Int -> ParseMap -> ParseMap
predict g is i m = if i /= 0 && any (\ (State _ _ _ ts _) -> not (null ts) 
			 && head ts == termTok) 
		 (lookUp m i)
		 then Map.insertWith (++) i (initialState g is i) m
		 else m 

type Chart = (Int, [Diagnosis], ParseMap)

nextState :: GlobalAnnos -> Set.Set Id -> Term -> Chart -> Chart
nextState g is trm (i, ds, m) = 
    let m1 = complete g (i+1) $
		 scan trm i $
		 predict g is i m
    in if null (lookUp m1 (i+1)) && null ds
		    then (i+1, Diag Error ("unexpected mixfix token: " 
				      ++ show  trm)
			       (nullPos) : ds, m)
       else (i+1, ds, m1)

iterateStates :: GlobalAnnos -> Set.Set Id -> [Term] -> Chart -> Chart
iterateStates g ops terms c = 
    let self = iterateStates g ops
        _resolveTerm = resolveMixfix g ops
    in if null terms then c
       else case head terms of
            MixfixTerm ts -> self (ts ++ tail terms) c
            BracketTerm _ ts ps -> 
		self (expand "[" "]" ts ps ++ tail terms) c
	    t ->  self (tail terms) (nextState g ops t c)
  where expand = expandPos TermToken 

getAppls :: GlobalAnnos -> Int -> ParseMap -> [Term]
getAppls g i m = 
    map (asListAppl g) $ 
	filter (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     lookUp m i

resolveMixfix :: GlobalAnnos -> Set.Set Id -> Term -> Result Term
resolveMixfix g ops trm =
    let (i, ds, m) = iterateStates g ops [trm] 
		     (0, [], Map.single 0 $ initialState g ops 0) 
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
