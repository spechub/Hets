
{- HetCATS/CASL/Token.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for CASL IDs
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts

SIMPLE-ID       ::= WORDS
ID              ::= TOKEN-ID  |  MIXFIX-ID
TOKEN-ID        ::= TOKEN
MIXFIX-ID       ::= TOKEN-ID PLACE-TOKEN-ID ... PLACE-TOKEN-ID
                  |          PLACE-TOKEN-ID ... PLACE-TOKEN-ID
PLACE-TOKEN-ID  ::= PLACE TOKEN-ID
                  | PLACE
PLACE           ::= __

TOKEN           ::= WORDS  |  DOT-WORDS  |  DIGIT  |  QUOTED-CHAR 
                  | SIGNS

   SIGNS are adapted here and more permissive as in the summary
   WORDS and NO-BRACKET-SIGNS are treated equally
   legal are, ie. "{a}", "{+}", "a{}="
   illegal is "a=" (no two SIMPLE-TOKEN stay beside each other)
 
   SIMPLE-TOKEN ::= WORDS  |  DOT-WORDS  |  DIGIT  |  QUOTED-CHAR   
                  | NO-BRACKET-SIGNS
  
   SIGNS = BRACKETS SIMPLE-TOKEN BRACKETS ... BRACKETS SIMPLE-TOKEN
         | BRACKETS SIMPLE-TOKEN BRACKETS ... BRACKETS SIMPLE-TOKEN BRACKETS
	 | SIMPLE-TOKEN BRACKETS ... BRACKETS SIMPLE-TOKEN
	 | SIMPLE-TOKEN BRACKETS ... BRACKETS SIMPLE-TOKEN BRACKETS
	 | BRACKETS
	 | SIMPLE-TOKEN

   A SIMPLE-TOKEN followed by "[" outside nested brackets 
   will be taken as the beginning of a compound list.
   Within SIGNS brackets need not be balanced, 
   only after their composition to a MIXFIX-ID.

   BRACKETS = BRACKET ... BRACKET
   BRACKET         ::= [  |  ]  |  {  |  }

   2.4 Identifiers
   brackets/braces within MIXFIX-ID must be balanced

   C.2.2 Structured Specifications

   TOKEN-ID        ::= ...  |  TOKEN [ ID ,..., ID ]

   A compound list must follow the last TOKEN within MIXFIX-ID,
   so a compound list is never nested within (balanced) mixfix BRACKETS.
   Only PLACEs may follow a compound list.
   The IDs within the compound list may surely be compound IDs again.
-}

module Token (scanWords, scanSigns, parseId, sortId, varId) 
    where

import Keywords
import Lexer
import Id (Id(Id), Token(..), Pos, isPlace)
import ParsecPrim (GenParser, (<?>), (<|>), many)
import ParsecCombinator (many1, option)

-- ----------------------------------------------
-- casl keyword handling
-- ----------------------------------------------

scanTermSigns = reserved casl_reserved_ops scanAnySigns

scanSigns = reserved formula_ops scanTermSigns

scanTermWords = reserved casl_reserved_words scanAnyWords 

scanWords = reserved formula_words scanTermWords


-- ----------------------------------------------
-- bracket-token (for ids)
-- ----------------------------------------------


-- simple id (but more than only words)
sid = pToken (scanQuotedChar <|> scanDotWords 
		 <|> scanDigit <|> scanSigns 
		 <|> scanWords <?> "simple-id")

-- balanced mixfix-components {...}, [...]
braced = begDoEnd oBraceT innerList cBraceT
noComp = begDoEnd oBracketT innerList cBracketT

-- alternating sid and other mixfix components (including places)
-- no two sid stand side by side
innerMix1 = sid <:> option [] innerMix2
innerMix2 = flat (many1 (braced <|> noComp <|> many1 placeT))
            <++> option [] innerMix1

-- ingredients starting either with an sid or brackets, braces or place 
innerList =  option [] (innerMix1 <|> innerMix2 <?> "token")

-- a mixfix component starting with an sid (outside innerList)
topMix1 = sid <:> option [] topMix2

-- following an sid only braced mixfix-components are acceptable
-- square brackets after an sid will be taken as compound part
topMix2 = flat (many1 braced) <++> option [] topMix1

-- square brackets (as mixfix component) are ok following a place 
topMix3 = noComp <++> flat (many braced) <++> option [] topMix1

afterPlace = topMix1 <|> topMix2 <|> topMix3

-- places and something balanced possibly including places as well  
middle = many1 placeT <++> option [] afterPlace  

-- balanced stuff interspersed with places  
tokStart = afterPlace <++> flat (many middle)

-- at least two places on its own or a non-place possibly preceded by places 
start = tokStart <|> placeT <:> (tokStart <|> 
				 many1 placeT <++> option [] tokStart)
        <?> "id"

-- ----------------------------------------------
-- Mixfix Ids
-- ----------------------------------------------

-- a compound list
comps :: GenParser Char st ([Id], [Pos])
comps = do { o <- oBracketT 
	   ; (is, cs) <- parseId `separatedBy` commaT
	   ; c <- cBracketT
	   ; return (is, tokPos o : map tokPos cs ++ [tokPos c])
	   } <?> "[<id>,...,<id>]"

-- a compound list does not follow a place
-- but after a compound list further places may follow
parseId :: GenParser Char st Id
parseId = do { l <- start
             ; if isPlace (last l) then return (Id l [] [])
	       else (do { (c, p) <- option ([], []) comps
			; u <- many placeT
			; return (Id (l++u) c p)
			})
	     }

-- ----------------------------------------------
-- SORT Ids
-- ----------------------------------------------

-- at least some no-bracket-signs should be disallowed for sorts
-- obsolete isSortId (t) =  tokStr t `notElem` non_sort_signs

-- sortIds are words, but possibly compound ids
sortId :: GenParser Char st Id
sortId = do { s <- pToken scanWords
	    ; (c, p) <- option ([], []) comps
	    ; return (Id [s] c p)
	    }

-- ----------------------------------------------
-- VAR Ids
-- ----------------------------------------------
-- no compound ids (just a word) 
varId :: GenParser Char st Token
varId = pToken scanWords
