
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
  
   STB ::= SIMPLE-TOKEN BRACKETS
   BST ::= BRACKETS SIMPLE-TOKEN
  
   SIGNS ::= BRACKETS 
           | BRACKETS STB ... STB
           | BRACKETS STB ... STB SIMPLE-TOKEN
           | SIMPLE-TOKEN
           | SIMPLE-TOKEN BST ... BST 
           | SIMPLE-TOKEN BST ... BST BRACKETS

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

module Token ( casl_reserved_ops, casl_reserved_words
             , formula_ops, formula_words
	     , casl_reserved_fops, casl_reserved_fwords
             , start, mixId, parseId, sortId, varId) 
    where

import Keywords
import Lexer
import Id (Id(Id), Token(..), Pos, toPos, isPlace)
import ParsecPrim (GenParser, (<?>), (<|>), many)
import ParsecCombinator (many1, option)

-- ----------------------------------------------
-- casl keyword handling
-- ----------------------------------------------

casl_reserved_ops, formula_ops, casl_reserved_fops :: [String]
casl_reserved_ops = [colonS, colonS++quMark, defnS, dotS, cDot, barS, mapsTo]

-- these signs are legal in terms, but illegal in declarations
formula_ops = [equalS, implS, equivS, lOr, lAnd, negS] 
casl_reserved_fops = formula_ops ++ casl_reserved_ops

-- letter keywords
casl_reserved_words, formula_words, casl_reserved_fwords :: [String]
casl_reserved_words =
    [andS, archS, asS, assocS, axiomS, axiomS ++ sS, closedS, commS, endS, 
    existsS, fitS, forallS, freeS, fromS, generatedS, getS, givenS,
    hideS, idemS, inS, lambdaS, libraryS, localS, 
    opS, opS ++ sS, predS, predS ++ sS, resultS, revealS, sortS, 
    sortS ++ sS, specS, thenS, toS, typeS, typeS ++ sS, 
    unitS, unitS ++ sS, varS, varS ++ sS, versionS, viewS, withS, withinS]

-- these words are legal in terms, but illegal in declarations

formula_words = [defS, elseS, ifS, whenS, falseS, notS, trueS]
casl_reserved_fwords = formula_words ++ casl_reserved_words

-- ----------------------------------------------
-- bracket-token (for ids)
-- pass list of key symbols and keuwords as parameter
-- ----------------------------------------------

-- simple id (but more than only words)
sid :: ([String], [String]) -> GenParser Char st Token
sid (kOps, kWords) = pToken (scanQuotedChar <|> scanDotWords 
		<|> scanDigit <|> reserved kOps scanAnySigns 
		<|> reserved kWords scanAnyWords <?> "simple-id")

-- balanced mixfix-components {...}, [...]
braced, noComp :: ([String], [String]) -> GenParser Char st [Token]
braced l = begDoEnd oBraceT (innerList l) cBraceT
noComp l = begDoEnd oBracketT (innerList l) cBracketT

-- alternating sid and other mixfix components (including places)
-- no two sid stand side by side
innerMix1, innerMix2 :: ([String], [String]) -> GenParser Char st [Token]
innerMix1 l = sid l <:> option [] (innerMix2 l)
innerMix2 l = flat (many1 (braced l <|> noComp l<|> many1 placeT))
            <++> option [] (innerMix1 l)

-- ingredients starting either with an sid or brackets, braces or place 
innerList :: ([String], [String]) -> GenParser Char st [Token]
innerList l =  option [] (innerMix1 l <|> innerMix2 l <?> "token")

-- a mixfix component starting with an sid (outside innerList)
topMix1, topMix2, topMix3 :: ([String], [String]) -> GenParser Char st [Token]
topMix1 l = sid l <:> option [] (topMix2 l)

-- following an sid only braced mixfix-components are acceptable
-- square brackets after an sid will be taken as compound part
topMix2 l = flat (many1 (braced l)) <++> option [] (topMix1 l)

-- square brackets (as mixfix component) are ok following a place 
topMix3 l = noComp l <++> flat (many (braced l)) <++> option [] (topMix1 l)

afterPlace, middle :: ([String], [String]) -> GenParser Char st [Token]
afterPlace l = topMix1 l <|> topMix2 l<|> topMix3 l

-- places and something balanced possibly including places as well  
middle l = many1 placeT <++> option [] (afterPlace l)  

-- balanced stuff interspersed with places  
tokStart, start :: ([String], [String]) -> GenParser Char st [Token]
tokStart l = afterPlace l <++> flat (many (middle l))

-- at least two places on its own or a non-place possibly preceded by places 
start l = tokStart l <|> placeT <:> (tokStart l <|> 
				 many1 placeT <++> option [] (tokStart l))
				     <?> "id"

-- ----------------------------------------------
-- mixfix and compound ids
-- ----------------------------------------------

-- a compound list
comps :: ([String], [String]) -> GenParser Char st ([Id], [Pos])
comps keys = do o <- oBracketT
	        (ts, ps) <- mixId keys keys `separatedBy` commaT
	        c <- cBracketT
	        return (ts, toPos o ps c)
	     <?> "[<id>,...,<id>]"

-- a compound list does not follow a place
-- but after a compound list further places may follow
-- keywords within components may be different
mixId :: ([String], [String]) -> ([String], [String]) -> GenParser Char st Id
mixId keys idKeys = 
    do l <- start keys
       if isPlace (last l) then return (Id l [] [])
	  else do (c, p) <- option ([], []) (comps idKeys)
		  u <- many placeT
		  return (Id (l++u) c p)

-- ----------------------------------------------
-- CASL mixfix Ids
-- ----------------------------------------------

parseId :: GenParser Char st Id
parseId = mixId (casl_reserved_fops, casl_reserved_fwords) 
	  (casl_reserved_fops, casl_reserved_fwords)

-- ----------------------------------------------
-- VAR Ids
-- ----------------------------------------------

-- no compound ids (just a word) 
varId :: GenParser Char st Token
varId = pToken (reserved casl_reserved_fwords scanAnyWords)

-- ----------------------------------------------
-- SORT Ids
-- ----------------------------------------------

-- sortIds are words, but possibly compound ids
sortId :: GenParser Char st Id
sortId = do s <- varId
	    (c, p) <- option ([], []) 
		      (comps (casl_reserved_fops, casl_reserved_fwords))
	    return (Id [s] c p)
