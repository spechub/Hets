
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
import List(intersperse, partition)


-- Earley Algorithm
-- the single non-terminal (forall terms) will be "()"

nT = Token "()" nullPos
isNT (Token s _) =  s == "()"

-- all ids are duplicate replacing "__" with "()"

data State = State { rule :: Id
		   , dotPos :: [Token]
		   , rulePos :: Int
		   } deriving (Eq, Ord)

prefix :: Id -> Bool
prefix (Id ts _ _) = if null ts then False else not $ isPlace $ head ts

placeToNT :: Id -> Id
placeToNT (Id ts cs ps) = Id (map (\t -> if isPlace t then nT else t) ts) cs ps

initialState :: Set Id -> (Set Id, FiniteMap Int (Set State))
initialState is = let (ps, ms) = partition prefix $ setToList is
		      mis = map placeToNT ms
		      pis = map placeToNT ps
                      states = map (\i -> State i (getTokenList i) 0) mis
		  in (mkSet $ ps ++ pis ++ ms ++ mis, unitFM 0 (mkSet states))

getTokenList :: Id -> [Token]
getTokenList (Id ts cs _) = 
    let (pls, toks) = span isPlace (reverse ts) 
        cts = if null cs then [] else (Token "[" nullPos) :
	      concat (intersperse [Token "," nullPos]
	      (map getTokenList cs)) ++ [Token "]" nullPos]
    in reverse toks ++ cts ++ reverse pls

{-
predict :: [Id] -> State -> [State]
predict is (State ts d p _) =
    if isPlace (ts !! d) then 
       map (\i -> State (getTokenList i) 0 p p) 
	       (filter prefix is) 
    else []

scan :: Token -> State -> [State]
scan i (State ts d p k) = 
    if ts !! d == i then [State ts (d+1) (p+1) k] else []

complete :: State -> State -> [State]
complete (State ts1 d1 p1 _) (State ts2 d2 p2 k2) =
    if d1 >= length ts1 && isPlace (ts2 !! d2) && p2 <= p1
       then [State ts2 (d2+1) p1 k2] else []
-}
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

split ::  GenParser Char () String -> String -> (String, String)
split p s = let ph = do hd <- p;
		        tl <- getInput;
                        return (hd, tl) 
            in case parse ph "" s of
               Left _ -> error"split" 
	       Right x -> x

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





