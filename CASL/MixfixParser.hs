
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
import Graph (empty)
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

testAnnos = addGlobalAnnos emptyGlobalAnnos 
	    $ map (parseString annotationL) (precAnnos ++ assocAnnos)

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
                   , matchList :: Bool        -- usually False 
                   , matchPlace :: Maybe Bool -- no "__" encountered yet,
		                              -- or true (literal match of place) 
		                              -- or false (treat as non-terminal)
                   , arglist :: [State]       -- currently collected arguments 
		                              -- in reverse order
		   , dotPos :: [Token]
		   , rulePos :: Int
		   } deriving (Eq, Ord)


shortShowState:: State -> ShowS
shortShowState s = showId $ rule s 

instance Show State where
    showsPrec _ (State r l b a d p) = showChar '{' . showList l 
				 . showSepList (showString "") showTok first
				 . showChar '.' 
				 . showSepList (showString "") showTok d
                                 . showParen True (showMatch b)
                                 . showSepList (showChar ',') shortShowState a
				 . shows p . showChar '}'
	where first = take (length v - length d) v
	      v = getTokenList r
	      showMatch Nothing = showString "" 
	      showMatch (Just x) = showString $ if x then place else "TERM"
	      showList l = if l then showString "L " else showString ""

instance (Show a) => Show (Set a) where
    showsPrec _ = shows . setToList

prefix :: Id -> Bool
prefix (Id ts _ _) = if null ts then False else not $ isPlace $ head ts

getTokenList :: Id -> [Token]
getTokenList (Id ts cs _) = 
    let (pls, toks) = span isPlace (reverse ts) 
        cts = if null cs then [] else mkSimpleId "[" :
	      concat (intersperse [mkSimpleId ","]
	      (map getTokenList cs)) ++ [mkSimpleId "]"]
    in reverse toks ++ cts ++ reverse pls

mkState :: Int -> Id -> State 
mkState n ide = State ide False Nothing [] (getTokenList ide) n

type Chart = FiniteMap Int (Set State)

initialState :: Set Id -> Chart
initialState is = unitFM 0 (mapSet (mkState 0) is)

dontMatchPlace, doMatchPlace, mayMatchNT :: Maybe Bool -> Bool
dontMatchPlace Nothing = False
dontMatchPlace (Just x) = not x 
doMatchPlace Nothing = False
doMatchPlace (Just x) = x 
mayMatchNT = not . doMatchPlace

scan :: Token -> Int -> Chart -> Chart
scan t i m = 
    addToFM m (i+1) (mkSet $ 
       foldr (\ (State o z b a ts k) l ->
	      if null ts || head ts /= t || isPlace t && dontMatchPlace b then l 
	      else (State o z (if isPlace t then Just True else b) 
		    a (tail ts) k) : l) [] 
	      (setToList $ lookUp m i))

lookUp :: (Ord key) => FiniteMap key (Set a) -> key -> Set a
lookUp m i = lookupWithDefaultFM m emptySet i

compl :: GlobalAnnos -> Chart -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ _ ts _) -> null ts) l

collectArg :: GlobalAnnos -> Chart -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ _ k) = 
    map (\ (State o z _ a ts k1) ->
	      State o z (Just False) (s:a) (tail ts) k1)
    $ filter (filterByPrec g s)
    $ filter (\ (State _ _ b _ ts _) -> not (null ts) 
		       && isPlace (head ts) && mayMatchNT b)
    $ setToList $ lookUp m k

filterByPrec :: GlobalAnnos -> State -> State -> Bool
filterByPrec g (State argIde _ _ _ _ _) (State opIde _ _ args _ _) = 
       let n = length args in
       if isLeftArg opIde n then 
	  if isPostfix opIde && not (isPostfix argIde) then False
	     else checkArg g ALeft opIde argIde 
       else if isRightArg opIde n then 
            if isPrefix opIde && isMixfix argIde then False
	    else checkArg g ARight opIde argIde
       else checkAnyArg g opIde argIde

isLeftArg, isRightArg :: Id -> Int -> Bool
isLeftArg (Id ts _ _) n = n + 1 == (length $ takeWhile isPlace ts)

isRightArg (Id ts _ _) n = n == (length $ filter isPlace ts) - 
	      (length $ takeWhile isPlace (reverse ts))
	  
complRec :: GlobalAnnos -> Chart -> [State] -> [State]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: GlobalAnnos -> Int  -> Chart -> Chart
complete g i m = addToFM m i $ mkSet $ complRec g m $ setToList $ lookUp m i 

predict :: Set Id -> Int -> Chart -> Chart
predict ms i m = if any (\ (State _ _ b _ ts _) -> not (null ts) 
			 && isPlace (head ts) && mayMatchNT b) 
		 (setToList $ lookUp m i)
		 then addToFM_C union m i (mapSet (mkState i) ms)
		 else m 

nextState :: Set Id -> GlobalAnnos -> [Token] -> Int -> Chart -> Chart
nextState rules pG toks pos chart = 
    if null toks then chart
    else let c1 = predict rules pos chart
             c2 = scan (head toks) pos c1
	 in if isEmptySet $ lookUp c2 (pos + 1) then c2
	    else nextState rules pG (tail toks) (pos + 1) 
		     (complete pG (pos + 1) c2)

mkChart :: Set Id -> [Token] -> Chart
mkChart rules toks = nextState rules testAnnos toks 0 (initialState rules)

sucChart :: Chart -> Bool
sucChart m = any (\ (State _ _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1


getAppls :: Chart -> [TERM]
getAppls m = 
    map stateToAppl $ 
	filter (\ (State _ _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1

stateToAppl :: State -> TERM
stateToAppl (State i _ _ a _ _) = Application (Op_name i) 
				  (reverse (map stateToAppl a)) []

-- start testing

myRules = ["__^__", "__*__", "__+__", 
	   "x", "0", "1", "2", "3", "4", "5", "a", "b"]

myTokens = "4*x^4+3*x^3+2*x^2+1*x^1+0*x^0"

testChart = myChart myRules myTokens

myChart r t = mkChart (mkSet $ map (parseString parseId) r)
		  (map (mkSimpleId . (: [])) t)

testAppls = map (printText testAnnos)
	    $ getAppls testChart

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





