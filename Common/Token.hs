
{- |
Module      :  $Header$
Description :  parser for CASL 'Id's based on "Common.Lexer"
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parser for CASL 'Id's based on "Common.Lexer"

-}
{- http://www.cofi.info/Documents/CASL/Summary/
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

module Common.Token where

import Common.Keywords
import Common.Lexer
import Common.Id
import Text.ParserCombinators.Parsec
import Data.List (delete)

-- * Casl keyword lists

-- | reserved signs
casl_reserved_ops :: [String]
casl_reserved_ops = [colonS, colonQuMark, defnS, dotS, cDot, mapsTo]

-- | these formula signs are legal in terms, but illegal in declarations
formula_ops :: [String]
formula_ops = [equalS, implS, equivS, lOr, lAnd, negS]

-- | all reseverd signs
casl_reserved_fops :: [String]
casl_reserved_fops = formula_ops ++ casl_reserved_ops

-- | reserved keywords
casl_basic_reserved_words :: [String]
casl_basic_reserved_words =
    [axiomS, axiomS ++ sS, cogeneratedS, cotypeS, cotypeS ++ sS,
     esortS, esortS ++ sS, etypeS, etypeS ++ sS,
     existsS, forallS, freeS, generatedS,
     opS, opS ++ sS, predS, predS ++ sS,
     sortS, sortS ++ sS, typeS, typeS ++ sS, varS, varS ++ sS]

-- | reserved keywords
casl_structured_reserved_words :: [String]
casl_structured_reserved_words =
    [andS, archS, behaviourallyS, closedS, cofreeS, endS,
     fitS, freeS, fromS,  getS, givenS,
     hideS,  lambdaS, libraryS, localS, logicS,
     refinedS, refinementS,
     resultS, revealS, specS, thenS, toS,
     unitS, unitS ++ sS, versionS, viewS, withS, withinS]

-- | reserved keywords
casl_reserved_words :: [String]
casl_reserved_words =
   casl_basic_reserved_words++ casl_structured_reserved_words

-- | these formula words are legal in terms, but illegal in declarations
formula_words :: [String]
formula_words = [asS, defS, elseS, ifS, inS, whenS, falseS, notS, trueS]

-- | all reserved words
casl_reserved_fwords :: [String]
casl_reserved_fwords = formula_words ++ casl_reserved_words

-- * a single 'Token' parser taking lists of key symbols and words as parameter

-- | a simple 'Token' parser depending on reserved signs and words
-- (including a quoted char, dot-words or a single digit)
sid :: ([String], [String]) -> GenParser Char st Token
sid (kOps, kWords) = pToken (scanQuotedChar <|> scanDotWords
                <|> scanDigit <|> reserved kOps scanAnySigns
                <|> reserved kWords scanAnyWords <?> "simple-id")

-- * 'Token' lists parsers

-- | balanced mixfix components within braces
braceP :: GenParser Char st [Token] -> GenParser Char st [Token]
braceP p = begDoEnd oBraceT p cBraceT <|> try (oBracketT <:> single cBracketT)
-- | balanced mixfix components within square brackets
bracketP :: GenParser Char st [Token] -> GenParser Char st [Token]
bracketP p = begDoEnd oBracketT p cBracketT

-- | an 'sid' optionally followed by other mixfix components
-- (without no two consecutive 'sid's)
innerMix1 :: ([String], [String]) -> GenParser Char st [Token]
innerMix1 l = sid l <:> option [] (innerMix2 l)

-- | mixfix components not starting with a 'sid' (possibly places)
innerMix2 :: ([String], [String]) -> GenParser Char st [Token]
innerMix2 l = let p = innerList l in
                  flat (many1 (braceP p <|> bracketP p <|> many1 placeT))
                           <++> option [] (innerMix1 l)

-- | any mixfix components within braces or brackets
innerList :: ([String], [String]) -> GenParser Char st [Token]
innerList l = option [] (innerMix1 l <|> innerMix2 l <?> "token")

-- | mixfix components starting with a 'sid' (outside 'innerList')
topMix1 :: ([String], [String]) -> GenParser Char st [Token]
topMix1 l = sid l <:> option [] (topMix2 l)

-- | mixfix components starting with braces ('braceP')
-- that may follow 'sid' outside 'innerList'.
-- (Square brackets after a 'sid' will be taken as a compound list.)
topMix2 :: ([String], [String]) -> GenParser Char st [Token]
topMix2 l = flat (many1 (braceP $ innerList l)) <++> option [] (topMix1 l)

-- | mixfix components starting with square brackets ('bracketP')
-- that may follow a place ('placeT') (outside 'innerList')
topMix3 :: ([String], [String]) -> GenParser Char st [Token]
topMix3 l = let p = innerList l in
                bracketP p <++> flat (many (braceP p))
                             <++> option [] (topMix1 l)

-- | any ('topMix1', 'topMix2', 'topMix3') mixfix components
-- that may follow a place ('placeT') at the top level
afterPlace :: ([String], [String]) -> GenParser Char st [Token]
afterPlace l = topMix1 l <|> topMix2 l<|> topMix3 l

-- | places possibly followed by other ('afterPlace') mixfix components
middle :: ([String], [String]) -> GenParser Char st [Token]
middle l = many1 placeT <++> option [] (afterPlace l)

-- | many (balanced, top-level) mixfix components ('afterPlace')
-- possibly interspersed with multiple places ('placeT')
tokStart :: ([String], [String]) -> GenParser Char st [Token]
tokStart l = afterPlace l <++> flat (many (middle l))

-- | any (balanced, top-level) mixfix components
-- possibly starting with places but no single 'placeT' only.
start :: ([String], [String]) -> GenParser Char st [Token]
start l = tokStart l <|> placeT <:> (tokStart l <|>
                                 many1 placeT <++> option [] (tokStart l))
                                     <?> "id"

-- * parser for mixfix and compound 'Id's

-- | parsing a compound list
comps :: ([String], [String]) -> GenParser Char st ([Id], Range)
comps keys = do o <- oBracketT
                (ts, ps) <- mixId keys keys `separatedBy` commaT
                c <- cBracketT
                return (ts, toRange o ps c)

{- | parse mixfix components ('start') and an optional compound list ('comps')
   if the last token was no place. Accept possibly further places.
   Key strings (second argument) within compound list may differ from
   top-level key strings (first argument)!
-}
mixId :: ([String], [String]) -> ([String], [String]) -> GenParser Char st Id
mixId keys idKeys =
    do l <- start keys
       if isPlace (last l) then return (Id l [] nullRange)
          else do (c, p) <- option ([], nullRange) (comps idKeys)
                  u <- many placeT
                  return (Id (l++u) c p)

-- | the Casl key strings (signs first) with additional keywords
casl_keys :: [String] -> ([String], [String])
casl_keys ks = (ks ++ casl_reserved_fops, ks ++ casl_reserved_fwords)

-- | Casl ids for operations and predicates
parseId :: [String] -> GenParser Char st Id
parseId ks = mixId (casl_keys ks) (casl_keys ks)

-- | disallow 'barS' within the top-level of constructor names
consId :: [String] -> GenParser Char st Id
consId ks = mixId (barS : ks ++ casl_reserved_fops,
                   ks ++ casl_reserved_fwords) $ casl_keys ks

-- | Casl sorts are simple words ('varId'),
-- but may have a compound list ('comps')
sortId :: [String] -> GenParser Char st Id
sortId ks =
    do s <- varId ks
       (c, p) <- option ([], nullRange) (comps $ casl_keys ks)
       return (Id [s] c p)

-- * parser for simple 'Id's

-- | parse a simple word not in 'casl_reserved_fwords'
varId :: [String] -> GenParser Char st Token
varId ks = pToken (reserved (ks++casl_reserved_fwords) scanAnyWords)

-- | like 'varId'.  'Common.Id.SIMPLE_ID' for spec- and view names
simpleId :: GenParser Char st Token
simpleId = pToken (reserved casl_structured_reserved_words scanAnyWords)

-- * parser for key 'Token's

-- | parse a question mark key sign ('quMark')
quMarkT :: GenParser Char st Token
quMarkT = pToken $ toKey quMark

-- | parse a 'colonS' possibly immediately followed by a 'quMark'
colonST :: GenParser Char st Token
colonST = pToken $ try $ string colonS << notFollowedBy
    (oneOf $ delete '?' signChars)

-- | parse the product key sign ('prodS' or 'timesS')
crossT :: GenParser Char st Token
crossT = pToken (toKey prodS <|> toKey timesS) <?> "cross"
