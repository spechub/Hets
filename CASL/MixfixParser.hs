
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

type Prec = (PrecedenceGraph, AssocMap)

emptyPrec :: Prec
emptyPrec = ((emptyFM, empty), emptyFM)


mkPrecGraph :: [String] -> PrecedenceGraph
mkPrecGraph s = store_prec_annos (emptyFM, empty) $
	      map (parseString annotationL) s

mkAssocMap :: [String] -> AssocMap
mkAssocMap s = store_assoc_annos emptyFM $
    map (parseString annotationL) s

mkPrec :: [String] -> [String] -> Prec
mkPrec precs assocs = (mkPrecGraph precs, mkAssocMap assocs)

precAnnos = [ "%prec({__+__} < {__*__})%", "%prec({__*__} < {__^__})%" ]
assocAnnos = ["%left_assoc(__+__)%"]

testPrec = mkPrec precAnnos assocAnnos

checkLeft :: Prec -> Id -> Id -> Bool
checkLeft g left top = isOrdAppl left || 
		       case precRel (fst g) top left of 
		       Lower -> True
		       _ -> if left == top then isLAssoc (snd g) left
			    else False

checkRight :: Prec -> Id -> Id -> Bool
checkRight g top right = isOrdAppl right || 
			 case precRel (fst g) top right of 
			 Lower -> True
			 _ -> if right == top then isRAssoc (snd g) right
			      else False



-- Earley Algorithm

-- after matching one place literally all places must match literally
-- and arguments must follow in parenthesis

data State = State { rule :: Id
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
    showsPrec _ (State r b a d p) = showChar '{' 
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
mkState n ide = State ide Nothing [] (getTokenList ide) n

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
       foldr (\ (State o b a ts k) l ->
	      if null ts || head ts /= t || isPlace t && dontMatchPlace b then l 
	      else (State o (if isPlace t then Just True else b) 
		    a (tail ts) k) : l) [] 
	      (setToList $ lookUp m i))

lookUp :: (Ord key) => FiniteMap key (Set a) -> key -> Set a
lookUp m i = lookupWithDefaultFM m emptySet i

compl :: Prec -> Chart -> [State] -> [State]
compl g m l = 
  concat $ map (collectArg g m) 
  $ filter (\ (State _ _ _ ts _) -> null ts) l

collectArg :: Prec -> Chart -> State -> [State]
-- pre: finished rule 
collectArg g m s@(State _ _ _ _ k) = 
-- insert filter by precedence (if all arguments are given)
    map (\ (State o _ a ts k1) ->
	      State o (Just False) (s:a) (tail ts) k1)
    $ filter (filterByPrec g s)
    $ filter (\ (State _ b _ ts _) -> not (null ts) 
		       && isPlace (head ts) && mayMatchNT b)
    $ setToList $ lookUp m k

filterByPrec :: Prec -> State -> State -> Bool
filterByPrec g (State argIde _ _ _ _) (State opIde b args ts k) = 
    if null args then checkLeft g argIde opIde 
       else checkRight g opIde argIde

complRec :: Prec -> Chart -> [State] -> [State]
complRec g m l = let l1 = compl g m l in 
    if null l1 then l else complRec g m l1 ++ l

complete :: Prec -> Int  -> Chart -> Chart
complete g i m = addToFM m i $ mkSet $ complRec g m $ setToList $ lookUp m i 

predict :: Set Id -> Int -> Chart -> Chart
predict ms i m = if any (\ (State _ b _ ts _) -> not (null ts) 
			 && isPlace (head ts) && mayMatchNT b) 
		 (setToList $ lookUp m i)
		 then addToFM_C union m i (mapSet (mkState i) ms)
		 else m 

nextState :: Set Id -> Prec -> [Token] -> Int -> Chart -> Chart
nextState rules pG toks pos chart = 
    if null toks then chart
    else let c1 = predict rules pos chart
             c2 = scan (head toks) pos c1
	 in if isEmptySet $ lookUp c2 (pos + 1) then c2
	    else nextState rules pG (tail toks) (pos + 1) 
		     (complete pG (pos + 1) c2)

mkChart :: Set Id -> [Token] -> Chart
mkChart rules toks = nextState rules testPrec toks 0 (initialState rules)

sucChart :: Chart -> Bool
sucChart m = any (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1


getAppls :: Chart -> [TERM]
getAppls m = 
    map stateToAppl $ 
	filter (\ (State _ _ _ ts k) -> null ts && k == 0) $ 
	     setToList $ lookUp m $ sizeFM m - 1

stateToAppl :: State -> TERM
stateToAppl (State i _ a _ _) = Application (Op_name i) 
				(reverse (map stateToAppl a)) []

-- start testing

myRules = ["__^__", "__*__", "__+__", 
	   "x", "0", "1", "2", "3", "4", "5", "a", "b"]

myTokens = "4*x^4+3*x^3+2*x^2+1*x^1+0*x^0"

testChart = myChart myRules myTokens

myChart r t = mkChart (mkSet $ map (parseString parseId) r)
		  (map (mkSimpleId . (: [])) t)

testAppls = map (printText 
		 (addGlobalAnnos emptyGlobalAnnos 
		  (map (parseString annotationL) (precAnnos ++ assocAnnos))))
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





