
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
import PrettyPrint
import Print_AS_Basic
import GlobalAnnotationsFunctions
import Anno_Parser

-- precedence graph stuff

precAnnos = [ "%prec({__+__} < {__*__})%", "%prec({__*__} < {__^__})%" ]
assocAnnos = ["%left_assoc(__+__)%"]
listAnnos = "%list([__], [], __::__)%"
-- don't put in list ids twice! (no danger!)

testAnnos = addGlobalAnnos emptyGlobalAnnos 
	    $ map (parseString annotationL) 
	    (listAnnos:precAnnos ++ assocAnnos)

checkArg :: GlobalAnnos -> AssocEither -> Id -> Id -> Bool
checkArg g dir op arg = 
    if arg == op 
       then isAssoc dir (assoc_annos g) op
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
                   , matchTerm ::Bool  -- false (literally match place) 
		                       -- or false (treat as non-terminal)
                   , arglist :: [TERM]   -- currently collected arguments 
		                          -- in reverse order
		   , dotPos :: [Token]
		   , rulePos :: Int
		   }

instance Eq State where
    State r1 b1 _ t1 p1 == State r2 b2 _ t2 p2 =
	r1 == r2 && t1 == t2 && p1 == p2 && b1 == b2

instance Ord State where
    State r1 b1 _ t1 p1 <= State r2 b2 _ t2 p2 =
	if r1 == r2 then
	       if t1 == t2 then
		      if p1 == p2 then b1 <= b2
		      else p1 <= p2
	       else t1 <= t2
	else r1 <= r2

instance Show State where
    showsPrec _ (State r b _ d p) = showChar '{' 
				 . showSepList (showString "") showTok first
				 . showChar '.' 
				 . showSepList (showString "") showTok d
                                 . showParen True (showMatch b)
				 . shows p . showChar '}'
	where first = take (length v - length d) v
	      v = getTokenList r
	      showMatch x = showString $ if x then "" else place

instance (Show a) => Show (Set a) where
    showsPrec _ = shows . setToList

commaTok, placeTok, openParenTok, closeParenTok :: Token
commaTok = mkSimpleId ","
placeTok = mkSimpleId place
openParenTok = mkSimpleId "("
closeParenTok = mkSimpleId ")"

getTokenList :: Id -> [Token]
getTokenList (Id ts cs _) = 
    let (pls, toks) = span isPlace (reverse ts) 
        cts = if null cs then [] else mkSimpleId "[" :
	      concat (intersperse [commaTok]
	      (map getTokenList cs)) ++ [mkSimpleId "]"]
    in reverse toks ++ cts ++ reverse pls

mkState :: Int -> Id -> State 
mkState n ide = State ide True [] (getTokenList ide) n

bracketToks :: [Token]
bracketToks = [openParenTok, closeParenTok]

mkApplState :: Int -> Id -> State
mkApplState n ide = State ide False [] 
		    (getTokenList ide ++ bracketToks) n

type Chart = FiniteMap Int (Set State)

initialState :: Set Id -> GlobalAnnos -> Int -> Set State
initialState is g i = 
       mapSet (mkApplState i) is `union` 
       mapSet (mkState i) is `union` 
       listStates g i `addToSet` 
       bracketTerm i 

-- qualified names not handled yet

bracketTerm :: Int -> State 
bracketTerm i = let v = Id bracketToks [] []
		    in State v True [] (getTokenList v) i


listId :: Id
-- unique id (usually "[]" yield two tokens)
listId = Id [mkSimpleId "[]"] [] []

listStates :: GlobalAnnos -> Int -> Set State
listStates g i = case list_lit (literal_annos g) of
		Nothing -> emptySet
		Just (Id b _ _, _, _) -> 
		    let (b1, rest) = break isPlace b
			b2 = if null rest then [] 
			     else filter (not . isPlace) rest
		    in mkSet [ State listId True [] (b1++b2) i
			     , State listId True [] 
				      (b1 ++ [placeTok] ++ b2) i
			     , State listId True [] 
			       (b1 ++ [placeTok, commaTok]
			       ++ b2) i
			     ]

scan :: Token -> Int -> Chart -> Chart
scan t i m = 
    addToFM m (i+1) (mkSet $ 
       foldr (\ (State o b a ts k) l ->
	      if null ts || head ts /= t 
	         || isPlace t && b then l 
	      else if t == commaTok || t == openParenTok then 
	             (State o True a 
		      (placeTok : commaTok : tail ts) k)
                     : (State o True a (placeTok : tail ts) k) : l
	           else (State o b a (tail ts) k) : l) [] 
	      (setToList $ lookUp m i))

lookUp :: (Ord key) => FiniteMap key (Set a) -> key -> Set a
lookUp m i = lookupWithDefaultFM m emptySet i

compl :: GlobalAnnos -> Chart -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ ts _) -> null ts) l

collectArg :: GlobalAnnos -> Chart -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ k) = 
    map (\ (State o _ a ts k1) ->
	 State o True (asListAppl g s : a) 
	 (tail ts) k1)
    $ filter (filterByPrec g s)
    $ setToList $ lookUp m k

filterByPrec :: GlobalAnnos -> State -> State -> Bool
filterByPrec _ _ (State _ _ _ [] _) = False 
filterByPrec g (State argIde _ _ _ _) (State opIde b args (hd:ts) _) = 
       if isPlace hd && b then 
	  if opIde == listId || argIde == listId then True
	  else if not (null ts) && (head ts == commaTok 
				    || head ts == closeParenTok) then True
	       else let n = length args in
		    if isLeftArg opIde n then 
		       if isPostfix opIde && not (isPostfix argIde) then False
		       else checkArg g ALeft opIde argIde 
		    else if isRightArg opIde n then 
                            if isPrefix opIde && isMixfix argIde then False
	                    else checkArg g ARight opIde argIde
                         else checkAnyArg g opIde argIde
       else False

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
complRec :: GlobalAnnos -> Chart -> [State] -> [State]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> Chart -> Chart
complete g i m = addToFM m i $ mkSet $ complRec g m $ setToList $ lookUp m i 

predict :: Set Id -> GlobalAnnos -> Int -> Chart -> Chart
predict ms g i m = if any (\ (State _ b _ ts _) -> not (null ts) 
			 && isPlace (head ts) && b) 
		 (setToList $ lookUp m i)
		 then addToFM_C union m i (initialState ms g i)
		 else m 

nextState :: Set Id -> GlobalAnnos -> [Token] -> Int -> Chart -> Chart
nextState rules pG toks pos chart = 
    if null toks then chart
    else let c1 = predict rules pG pos chart
             c2 = scan (head toks) pos c1
	 in if isEmptySet $ lookUp c2 (pos + 1) then c2
	    else nextState rules pG (tail toks) (pos + 1) 
		     (complete pG (pos + 1) c2)

mkChart :: Set Id -> GlobalAnnos -> [Token] -> Chart
mkChart rules g toks = nextState rules g toks 0 
		     (unitFM 0 $ initialState rules g 0)

sucChart :: Chart -> Bool
sucChart m = any (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1


getAppls :: GlobalAnnos -> Chart -> [TERM]
getAppls g m = 
    map (asListAppl g) $ 
	filter (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1

stateToAppl :: State -> TERM
stateToAppl (State i _ a _ _) = asAppl i (reverse a) nullPos

asListAppl :: GlobalAnnos -> State -> TERM
asListAppl g s@(State i _ a _ _) =
    case list_lit $ literal_annos g of
    Nothing -> stateToAppl s 
    Just (_, c, f) -> 
	if i == listId then mkList (reverse a)
	   else stateToAppl s
        where mkList [] = asAppl c [] nullPos
	      mkList (hd:tl) = asAppl f [hd, mkList tl] nullPos

-- start testing

myRules = ["__^__", "__*__", "__+__", "[__]",
	   "x", "0", "1", "2", "3", "4", "5", "a", "b"]

myTokens = "4*x^4+3*x^3+2*x^2+1*x^1+0*x^0"


myChart g r t = mkChart (mkSet $ map (parseString parseId) r) g
		  (map (\ c -> mkSimpleId $ if c == '_' then place 
			else [c]) t)

myAppls g r t = map (printText g)
	      $ getAppls g (myChart g r t)

testAppls = myAppls testAnnos myRules myTokens

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
        Just (c, f) -> erg $ makeStringTerm c f t
--     else if isChar t then erg $ asAppl (Id [t] [] []) [] (tokPos t) 
     else if isNumber t then 
	  case number_lit ga of
	  Nothing -> err "number"
	  Just f -> if isFloating t then
		        case float_lit ga of
			Nothing -> err "floating"
			Just (d, e) -> erg $ makeFloatTerm f d e t
		    else erg $ makeNumberTerm f t
     else erg $ Mixfix_token t
    where err s = Result([Error ("missing %" ++ s ++ " annotation") (tokPos t)],
			 Just (Mixfix_token t))
          erg r = Result([], Just r) 





