module Haskell.Hatchet.HsParseMonad where

import Haskell.Hatchet.HsSyn


data ParseResult a = Ok ParseState a | Failed String
	deriving Show

data LexContext = NoLayout | Layout Int
	deriving (Eq,Ord,Show)

type ParseState = [LexContext]

type P a
     =  String			-- input string
     -> SrcLoc			-- location of last token read
     -> Int			-- current column
     -> ParseState		-- layout info.
     -> ParseResult a

thenP :: P a -> (a -> P b) -> P b
m `thenP` k = \i l c s -> 
	case m i l c s of 
	    Failed s -> Failed s
	    Ok s' a -> case k a of k' -> k' i l c s'

m `thenP_` k = m `thenP` \_ -> k

mapP :: (a -> P b) -> [a] -> P [b]
mapP f [] = returnP []
mapP f (a:as) = 
     f a `thenP` \b ->
     mapP f as `thenP` \bs ->
     returnP (b:bs)

returnP a = \i l c s -> Ok s a

failP :: String -> P a
failP err = \i l c s -> Failed err

getSrcLoc :: P SrcLoc
getSrcLoc = \i l c s -> Ok s l

getContext :: P [LexContext]
getContext = \i l c s -> Ok s s

pushContext :: LexContext -> P ()
pushContext ctxt = 
--        trace ("pushing lexical scope: " ++ show ctxt ++"\n") $
	\i l c s -> Ok (ctxt:s) ()

popContext :: P ()
popContext = \i l c stk ->
      case stk of
        (_:s) -> 
     -- trace ("popping lexical scope, context now "++show s ++ "\n") $
           Ok s ()
        []    -> error "Internal error: empty context in popContext"

