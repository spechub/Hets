
{- HetCATS/CASL/MixfixParser.hs
   $Id$
   Author:  Christian Maeder
   Year:    2002

   Mixfix analysis of terms
-}

module MixfixParser where

import AS_Basic_CASL 
import GlobalAnnotations
import Result
import Id
import FiniteMap
import Set
import Lexer (caslChar)
import ParsecPrim
import qualified Char as C
import List(intersperse)

-- for testing
import Token
import Formula
import PrettyPrint
import Print_AS_Basic
import GlobalAnnotationsFunctions
import Anno_Parser

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

-- Earley Algorithm

-- after matching one place literally all places must match literally
-- and arguments must follow in parenthesis

data State = State { rule :: Id
                   , posList :: [Pos]    -- positions of Id tokens
                   , arglist :: [TERM]   -- currently collected arguments 
		                          -- both in reverse order
		   , dotPos :: [Token]
		   , rulePos :: Int
		   }

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

instance (Show a) => Show (Set a) where
    showsPrec _ = shows . setToList

commaTok, parenTok, termTok :: Token
commaTok = mkSimpleId "," -- for list elements 
termTok = mkSimpleId "(T)"
parenTok = mkSimpleId "(..)" 

colonTok, asTok, varTok, opTok, predTok :: Token
colonTok = mkSimpleId ":"
asTok = mkSimpleId "as"
varTok = mkSimpleId "(v)"
opTok = mkSimpleId "(o)"
predTok = mkSimpleId "(p)"

expandPos :: (Token -> a) -> String -> String -> [a] -> [Pos] -> [a]
expandPos f o c ts ps =
          let n = length ts 
              j = length ps
              cutOuterPos i l = let k = length l in 
				if k == i+1 then l
				else cutOuterPos (i - 2) 
					      $ init (tail l)
              ps1 = if j > n  && even (j - (n+1)) then cutOuterPos n ps
		    else if j > 1 then 
			 head ps : replicate (n - 1) nullPos 
			      ++ [last ps]
		    else replicate (n + 1) nullPos
	      seps = map f
		(zipWith Token (o : replicate (n - 1) "," ++ [c]) ps1)
	  in head seps : concat (zipWith (\ t s -> [t,s]) ts (tail seps))
	    		    
getTokenList :: Bool -> Id -> [Token]
getTokenList asLiteral (Id ts cs ps) = 
    let (pls, toks) = span isPlace (reverse ts) 
        cts = if null cs then [] else concat 
	      $ expandPos (:[]) "[" "]" (map (getTokenList True) cs) ps
	      -- although positions will be replaced (by scan)
        convert = if asLiteral then reverse else 
		  map (\ t -> if isPlace t then termTok else t) . reverse 
    in convert toks ++ cts ++ convert pls

mkState :: Int -> Id -> State 
mkState i ide = State ide [] [] (getTokenList False ide) i

mkApplState :: Int -> Id -> State
mkApplState i ide = State ide [] [] 
		    (getTokenList True ide ++ [parenTok]) i


listId :: Id
-- unique id (usually "[]" yields two tokens)
listId = Id [mkSimpleId "[]"] [] []

listStates :: GlobalAnnos -> Int -> Set State
listStates g i = 
    let listState toks = State listId [] [] toks i
    in case list_lit (literal_annos g) of
		Nothing -> emptySet
		Just (Id b _ _, _, _) -> 
		    let (b1, rest) = break isPlace b
			b2 = if null rest then [] 
			     else filter (not . isPlace) rest
		    in mkSet [ listState (b1 ++ b2)
			     , listState (b1 ++ [termTok] ++ b2)
			     , listState (b1 ++ [termTok, commaTok] ++ b2)]

initialState :: GlobalAnnos -> Set Id -> Int -> Set State
initialState g is i = 
    let mkTokState toks = State (Id toks [] []) [] [] toks i
    in mapSet (mkApplState i) is `union` 
       mapSet (mkState i) is `union` 
       listStates g i `addToSet` 
       mkTokState [parenTok] `addToSet`
       mkTokState [termTok, colonTok] `addToSet`
       mkTokState [termTok, asTok] `addToSet`
       mkTokState [varTok] `addToSet`
       mkTokState [opTok] `addToSet`
       mkTokState [opTok, parenTok] `addToSet`
       mkTokState [predTok] `addToSet`
       mkTokState [predTok, parenTok]

type ParseMap = FiniteMap Int (Set State)

lookUp :: (Ord key) => FiniteMap key (Set a) -> key -> Set a
lookUp m i = lookupWithDefaultFM m emptySet i

scan :: TERM -> Int -> ParseMap -> ParseMap
scan trm i m = 
  let t = case trm of 
	  Mixfix_token x -> x
	  Mixfix_sorted_term _ _ -> colonTok
	  Mixfix_cast _ _ -> asTok
          Mixfix_parenthesized _ _ -> parenTok
	  Application (Qual_op_name _ _ _) [] _ -> opTok
          Mixfix_qual_pred _ -> predTok
          _ -> varTok
  in
    addToFM m (i+1) (mkSet $ 
       foldr (\ (State o b a ts k) l ->
	      if null ts || head ts /= t then l 
	      else let p = tokPos t : b in 
                   if t == commaTok then -- list elements separator
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
	      (setToList $ lookUp m i))
     where mkTerm t1 = case trm of 
	                  Mixfix_sorted_term s ps -> Sorted_term t1 s ps
	                  Mixfix_cast s ps -> Cast t1 s ps
			  _ -> t1
	      
compl :: GlobalAnnos -> ParseMap -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ ts _) -> null ts) l

collectArg :: GlobalAnnos -> ParseMap -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ k) = 
    map (\ (State o b a ts k1) ->
	 State o b (asListAppl g s : a) 
	 (tail ts) k1)
    $ filter (filterByPrec g s)
    $ setToList $ lookUp m k

filterByPrec :: GlobalAnnos -> State -> State -> Bool
filterByPrec _ _ (State _ _ _ [] _) = False 
filterByPrec g (State argIde _ _ _ _) (State opIde _ args (hd:ts) _) = 
       if hd == termTok then 
	  if opIde == listId || argIde == listId then True
	  else if not (null ts) && head ts == commaTok then True
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

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  

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
      else let (newCs, ps3, ps4) = foldr (\ a (prevCs, seps, rest) -> 
				  let (c1, qs) = setPlainIdePos a rest
				  in (c1: prevCs, head qs : seps, tail qs))
			   ([], [head ps2], tail ps2) cs
	       ps5 = tail ps4
	       (ps6, ps7) = splitAt (length pls) ps5
           in (Id (front ++ f pls ps6) 
	       (reverse newCs)  
	       (reverse (head ps4 : ps3)), ps7)

setIdePos :: Id -> [TERM] -> [Pos] -> Id
setIdePos i@(Id ts _ _) ar ps =
   let nt = length $ getTokenList True i 
       np = length ps
       na = length $ filter isPlace ts       
       (_, toks) = span isPlace (reverse ts) 
   in if nt == np then  -- literal places
         let (newId, []) = setPlainIdePos i ps
         in newId
      else if np + na == nt && na == length ar then -- mixfix
         let (newTps, rargs, rqs) = mergePos (reverse toks) ar ps 
             (newId, []) = setPlainIdePos i 
			  (newTps ++ rqs ++ map posOfTerm rargs)
         in newId
      else error "setIdePos"
   where mergePos [] args qs = ([], args, qs)
	 mergePos (t:rs) args qs = 
	     if isPlace t then
                let (tokps, rargs, rqs) = mergePos rs (tail args) qs
 		in (posOfTerm (head args) : tokps, rargs, rqs)
		else let (tokps, rargs, rqs) = mergePos rs args (tail qs)
		     in (head qs : tokps, rargs, rqs)
 
stateToAppl :: State -> TERM
stateToAppl (State ide rs a _ _) = 
    let vs = getTokenList True ide 
        ar = reverse a
        qs = reverse rs
    in if  vs == [termTok, colonTok] 
	   || vs == [termTok, asTok] 
	   || vs == [varTok] 
           || vs == [opTok]
           || vs == [predTok]
           || vs == [parenTok]
       then head ar
       else if vs == [opTok, parenTok]
		 then let Application q _ _ = head ar
                          Mixfix_parenthesized ts ps = head a
                      in Application q ts ps 
		 else if vs == [predTok, parenTok] 
		      then Mixfix_term [head ar, head a] 
                      else case ar of 
		           [Mixfix_parenthesized ts ps] -> 
			       Application (Op_name 
					    (setIdePos ide ts qs))
				ts ps
			   _ -> let newIde@(Id (t:_) _ _) = setIdePos ide ar qs
                                    pos = if isPlace t then posOfTerm $ head ar
					  else tokPos t
			        in Application (Op_name newIde) ar [pos]
				   -- true mixfix

asListAppl :: GlobalAnnos -> State -> TERM
asListAppl g s@(State i _ a _ _) =
    case list_lit $ literal_annos g of
    Nothing -> stateToAppl s 
    Just (_, c, f) -> 
	if i == listId then mkList (reverse a)
	   else stateToAppl s
        where mkList [] = asAppl c [] nullPos
	      mkList (hd:tl) = asAppl f [hd, mkList tl] nullPos

complRec :: GlobalAnnos -> ParseMap -> [State] -> [State]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> ParseMap -> ParseMap
complete g i m = addToFM m i $ mkSet $ complRec g m $ setToList $ lookUp m i 

predict :: GlobalAnnos -> Set Id -> Int -> ParseMap -> ParseMap
predict g is i m = if any (\ (State _ _ _ ts _) -> not (null ts) 
			 && head ts == termTok) 
		 (setToList $ lookUp m i)
		 then addToFM_C union m i (initialState g is i)
		 else m 

type Chart = (Int, [Diagnosis], ParseMap)

nextState :: GlobalAnnos -> Set Id -> TERM -> Chart -> Chart
nextState g is trm (i, ds, m) = 
    let m1 = complete g (i+1) $
		 scan trm i $
		 predict g is i m
    in if isEmptySet $ lookUp m1 (i+1) 
		    then (i+1, Error ("unexpected term or token: " 
				      ++ show (printText0 g trm))
			       (posOfTerm trm) : ds, m)
       else (i+1, ds, m1)

iterateStates :: GlobalAnnos -> Set Id -> Set Id -> [TERM] -> Chart -> Chart
iterateStates g ops preds terms c@(i, ds, m) = 
    let self = iterateStates g ops preds 
        resolveTerm = resolveMixfix g ops preds False
    in if null terms then c
       else case head terms of
            Mixfix_term ts -> self (ts ++ tail terms) c
            Mixfix_bracketed ts ps -> 
		self (expand "[" "]" ts ps ++ tail terms) c
	    Mixfix_braced ts ps -> 
		self (expand "{" "}" ts ps ++ tail terms) c
	    Mixfix_parenthesized ts ps -> 
		let Result mds v = 
			do tsNew <- mapM resolveTerm ts
			   return (Mixfix_parenthesized tsNew ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		in self (tail terms) (nextState g ops tNew (i, ds++mds, m))
	    Conditional t1 f2 t3 ps -> 
                let Result mds v = 
			do t4 <- resolveTerm t1
			   f5 <- resolveFormula g ops preds f2 		 
			   t6 <- resolveTerm t3 
			   return (Conditional t4 f5 t6 ps)
                    tNew = case v of Nothing -> head terms
				     Just x -> x
		in self (tail terms) (nextState g ops tNew (i, ds++mds, m)) 
            t -> self (tail terms) (nextState g ops t c)
  where expand = expandPos Mixfix_token 

posOfTerm :: TERM -> Pos
posOfTerm trm =
    case trm of
	      Mixfix_token t -> tokPos t
	      Mixfix_term ts -> posOfTerm (head ts)
	      Simple_id i -> tokPos i
	      Mixfix_qual_pred _ -> nullPos 
	      _ -> case get_pos_l trm of 
		   Nothing -> nullPos
		   Just l -> if null l then nullPos else head l

getAppls :: GlobalAnnos -> Int -> ParseMap -> [TERM]
getAppls g i m = 
    map (asListAppl g) $ 
	filter (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m i

resolveMixfix :: GlobalAnnos -> Set Id -> Set Id -> Bool -> TERM -> Result TERM
resolveMixfix g ops preds mayBeFormula trm =
    let (i, ds, m) = iterateStates g ops preds [trm] 
		     (0, [], unitFM 0 $ initialState g 
		      (if mayBeFormula then ops `union` preds else ops) 0)
        ts = getAppls g i m
    in if null ts then if null ds then 
                        non_fatal_error trm ("no resolution for term: "
					     ++ show (printText0 g trm))
					    (posOfTerm trm)
		       else Result ds (Just trm)
       else if null $ tail ts then return $ head ts
	    else non_fatal_error trm ("ambiguous mixfix term\n\t" ++ 
			 (concat  
			 $ intersperse "\n\t" 
			 $ map (show . printText0 g) 
			 $ take 5 ts)) (posOfTerm trm)

resolveFormula :: GlobalAnnos -> Set Id -> Set Id -> FORMULA -> Result FORMULA
resolveFormula g ops preds frm =
    let self = resolveFormula g ops preds 
	resolveTerm = resolveMixfix g ops preds False in
    case frm of 
       Quantification q vs fOld ps -> 
	   do fNew <- self fOld 
	      return $ Quantification q vs fNew ps
       Conjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Conjunction fsNew ps
       Disjunction fsOld ps -> 
	   do fsNew <- mapM self fsOld  
	      return $ Disjunction fsNew ps
       Implication f1 f2 ps -> 
	   do f3 <- self f1 
	      f4 <- self f2
	      return $ Implication f3 f4 ps
       Equivalence f1 f2 ps -> 
	   do f3 <- self f1 
	      f4 <- self f2
	      return $ Equivalence f3 f4 ps
       Negation fOld ps -> 
	   do fNew <- self fOld  
	      return $ Negation fNew ps
       Predication sym tsOld ps -> 
	   do tsNew <- mapM resolveTerm tsOld  
	      return $ Predication sym tsNew ps
       Definedness tOld ps -> 
	   do tNew <- resolveTerm tOld  
	      return $ Definedness tNew ps
       Existl_equation t1 t2 ps -> 
	   do t3 <- resolveTerm t1 
	      t4 <- resolveTerm t2
	      return $ Existl_equation t3 t4 ps
       Strong_equation t1 t2 ps -> 
	   do t3 <- resolveTerm t1 
	      t4 <- resolveTerm t2
	      return $ Strong_equation t3 t4 ps
       Membership tOld s ps -> 
	   do tNew <- resolveTerm tOld  
	      return $ Membership tNew s ps
       Mixfix_formula tOld -> 
	   do tNew <- resolveMixfix g ops preds True tOld
	      mkPredication tNew
         where mkPredication t = 
	         case t of 
		 Mixfix_parenthesized [t0] ps ->
		  do p <- mkPredication t0
		     return $ if null ps then p 
                            else updFormulaPos (head ps) (last ps) p
		 Application (Op_name ide) args ps -> 
		  return $ Predication (Pred_name ide) args ps
		 Mixfix_qual_pred qide ->
		  return $ Predication qide [] []
		 Mixfix_term [Mixfix_qual_pred qide, 
			      Mixfix_parenthesized ts ps] ->
		  return $ Predication qide ts ps
		 _ -> non_fatal_error (Mixfix_formula t)
	                ("unresolved formula: " ++ show (printText0 g tOld))
			(posOfTerm tOld)
       f -> return f

-- start testing

testForm l r t = 
    let g = addGlobalAnnos emptyGlobalAnnos 
			 $ map (parseString annotationL) l
	in 
	   resolveFormula g (mkSet $ map (parseString parseId) r)
		      emptySet (parseString formula t)

myAnnos = [ "%prec({__+__} < {__*__})%", "%prec({__*__} < {__^__})%"
	  , "%left_assoc(__+__)%"
	  , "%list([__], [], __::__)%"]

myIs = ["__^__", "__*__", "__+__", "[__]", "____p", "q____","____x____",
        "{____}","__-__",
	"x", "0", "1", "2", "3", "4", "5", "a", "b", "-__", "__!"]

polynom = "4*x^4+3*x^3+2*x^2+1*x^1+0*x^0=0"

testAppl t = testForm myAnnos myIs t 

-- --------------------------------------------------------------- 
-- convert literals 
-- --------------------------------------------------------------- 

-- isChar :: Token -> Bool
-- isChar t = head (tokStr t) == '\''

isString :: Token -> Bool
isString t = head (tokStr t) == '\"'
isNumber :: Token -> Bool
isNumber t = let s = tokStr t in length s > 1 && C.isDigit (head s)
isFloating :: Token -> Bool
-- precondition: isNumber
isFloating t = any (\c -> c == '.' || c == 'E') (tokStr t)

parseString :: Parser a -> String -> a
parseString p s = case parse p "" s of
		  Left _ -> error "parseString"
		  Right x -> x

split :: Parser a -> String -> (a, String)
split p s = let ph = do hd <- p;
		        tl <- getInput;
                        return (hd, tl) 
            in parseString ph s

makeStringTerm :: Id -> Id -> Token -> TERM
makeStringTerm c f tok = 
  makeStrTerm (line, colm + 1) str
  where 
  (line, colm) = tokPos tok
  str = init (tail (tokStr tok))
  makeStrTerm p@(lin, col) l = 
    if null l then asAppl c [] p
    else let (hd, tl) = split caslChar l
	     real = if hd == "'" then "'\\''" else "'" ++ hd ++ "'"
             -- convert "'" to "\'" and lookup character '\''
         in asAppl f [asAppl (Id [Token real p] [] []) [] p, 
		      makeStrTerm (lin, col + length hd) tl] p

makeNumberTerm :: Id -> Token -> TERM
makeNumberTerm f t@(Token n p@(lin, col)) =
    case n of
           [] -> error "makeNumberTerm"
	   [_] -> asAppl (Id [t] [] []) [] p
	   hd:tl -> asAppl f [asAppl (Id [Token [hd] p] [] []) [] p, 
			      makeNumberTerm f (Token tl (lin, col+1))] p

makeFraction :: Id -> Id -> Token -> TERM
makeFraction f d t@(Token s p@(lin, col)) = 
    let (n, r) = span (\c -> c /= '.') s
        dotcol = col + length n 
    in if null r then makeNumberTerm f t
       else asAppl d [makeNumberTerm f (Token n p),
		      makeNumberTerm f (Token (tail r) (lin, dotcol + 1))] 
            (lin, dotcol)

makeSignedNumber :: Id -> Token -> TERM
makeSignedNumber f t@(Token n p@(lin, col)) = 
  case n of 
  [] -> error "makeSignedNumber"
  hd:tl ->   
    if hd == '-' || hd == '+' then
       asAppl (Id [Token [hd] p] [] []) 
		  [makeNumberTerm f (Token tl (lin, col+1))] p
    else makeNumberTerm f t

makeFloatTerm :: Id -> Id -> Id -> Token -> TERM
makeFloatTerm f d e t@(Token s p@(lin, col)) = 
    let (m, r) = span (\c -> c /= 'E') s
        ecol = col + length m
    in if null r then makeFraction f d t
       else asAppl e [makeFraction f d (Token m p),
		      makeSignedNumber f (Token (tail r) (lin, ecol + 1))]
		(lin, ecol)

asAppl :: Id -> [TERM] -> Pos -> TERM
asAppl f args p = let pos = if null args then [] else [p]
		  in Application (Op_name f) args pos

-- analyse Mixfix_token
convertMixfixToken::  LiteralAnnos -> Token  -> Result TERM 
convertMixfixToken ga t = 
     if isString t then 
	case string_lit ga of
	Nothing -> err "string"
        Just (c, f) -> return $ makeStringTerm c f t
     else if isNumber t then 
	  case number_lit ga of
	  Nothing -> err "number"
	  Just f -> if isFloating t then
		        case float_lit ga of
			Nothing -> err "floating"
			Just (d, e) -> return $ makeFloatTerm f d e t
		    else return $ makeNumberTerm f t
     else return te
    where te =  Mixfix_token t
          err s = non_fatal_error te
		  ("missing %" ++ s ++ " annotation") (tokPos t)






