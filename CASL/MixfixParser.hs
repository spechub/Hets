module MixfixParser where

import AS_Basic_CASL 
import GlobalAnnotations
import Result
import Id
import Lexer (caslChar)
import ParsecPrim
import qualified Char as C


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





