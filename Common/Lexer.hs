{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

   scanner for Casl tokens using Parsec <http://www.cs.uu.nl/~daan/parsec.html>
   
   <http://www.cofi.info/Documents/CASL/Summary/>
   from 25 March 2001
   C.4 Lexical Syntax
-}

module Common.Lexer where

import Data.Char (digitToInt, isDigit)
import Common.Id -- (Token(..), place)
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Pos as Pos

-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)


-- | no-bracket-signs
signChars :: String
signChars = "!#$&*+-./:<=>?@\\^|~" ++ "°¢£ß©¨∞±≤≥µ∂∑πø◊˜"

-- "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"
-- \172 neg \183 middle dot \215 times 

scanAnySigns :: GenParser Char st String
scanAnySigns = many1 (oneOf signChars <?> "casl sign") <?> "signs"

-- | casl letters
caslLetters :: String
caslLetters = ['A'..'Z'] ++ ['a'..'z'] ++ 
              "¿¡¬√ƒ≈∆«»… ÀÃÕŒœ—“”‘’÷ÿŸ⁄€‹›ﬂ‡·‚„‰ÂÊÁËÈÍÎÏÌÓÔÒÚÛÙıˆ¯˘˙˚¸˝ˇ"

-- see <http://www.htmlhelp.com/reference/charset/> starting from \192
-- \208 ETH \215 times \222 THORN \240 eth \247 divide \254 thorn

caslLetter :: GenParser Char st Char
caslLetter = oneOf caslLetters <?> "casl letter"

prime :: GenParser Char st Char
prime = char '\'' -- also used for quoted chars

scanLPD :: GenParser Char st Char
scanLPD = caslLetter <|> digit <|> prime <?> "casl char"

-- ----------------------------------------------
-- * Monad and Functor extensions
-- ----------------------------------------------

bind :: (Monad m) => (a -> b -> c) -> m a -> m b -> m c
bind f p q = do { x <- p; y <- q; return (f x y) }

infixl <<

(<<) :: (Monad m) => m a -> m b -> m a
(<<) = bind const

infixr 5 <:>

(<:>) :: (Monad m) => m a -> m [a] -> m [a]
(<:>) = bind (:)

infixr 5 <++>

(<++>) :: (Monad m) => m [a] -> m [a] -> m [a]
(<++>) = bind (++)

-- Functor extension
single :: (Functor f, Monad m) => f a -> f (m a)
single = fmap return

flat :: (Functor f) => f [[a]] -> f [a]
flat = fmap concat

-- ----------------------------------------------
-- * ParsecCombinator extension
-- ----------------------------------------------

followedWith :: GenParser tok st a -> GenParser tok st b -> GenParser tok st a
p `followedWith` q = try (p << lookAhead q)

begDoEnd :: (Monad f, Functor f) => f a -> f [a] -> f a -> f [a]
begDoEnd open p close = open <:> p <++> single close  

enclosedBy :: (Monad f, Functor f) => f [a] -> f a -> f [a]
p `enclosedBy` q = begDoEnd q p q

checkWith :: (Show a) => GenParser tok st a -> (a -> Bool) 
          -> GenParser tok st a
p `checkWith` f = do x <- p
                     if f x then return x else unexpected (show x)

separatedBy :: GenParser tok st a -> GenParser tok st b 
            -> GenParser tok st ([a], [b])
p `separatedBy`  s = do r <- p
                        option ([r], []) 
                          (do t <- s
                              (es, ts) <- separatedBy p s
                              return (r:es, t:ts))

-- ----------------------------------------------
-- * casl words
-- ----------------------------------------------

scanLetterWord :: GenParser Char st String
scanLetterWord = caslLetter <:> many scanLPD <?> "letter word"

singleUnderline :: GenParser Char st Char
singleUnderline = char '_' `followedWith` scanLPD

scanUnderlineWord :: GenParser Char st String
scanUnderlineWord = singleUnderline <:> many1 scanLPD

scanAnyWords, casl_words :: GenParser Char st String
scanAnyWords = flat (scanLetterWord <:> many scanUnderlineWord) <?> "words"
casl_words = scanAnyWords

scanDot :: GenParser Char st Char
scanDot = char '.' `followedWith` caslLetter

scanDotWords :: GenParser Char st String
scanDotWords = scanDot <:> scanAnyWords

-- ----------------------------------------------
-- * casl escape chars for quoted chars and literal strings
-- ----------------------------------------------

-- see ParsecToken.number
value :: Int -> String -> Int
value base s = foldl (\x d -> base*x + (digitToInt d)) 0 s

simpleEscape :: GenParser Char st String
simpleEscape = single (oneOf "'\"\\ntrvbfa?")

decEscape :: GenParser Char st String
decEscape = count 3 digit `checkWith` \s -> value 10 s <= 255

hexEscape :: GenParser Char st String
hexEscape = char 'x' <:> count 2 hexDigit -- cannot be too big

octEscape :: GenParser Char st String
octEscape = char 'o' <:> 
            count 3 octDigit `checkWith` \s -> value 8 s <= 255

escapeChar :: GenParser Char st String
escapeChar = char '\\' <:> 
             (simpleEscape <|> decEscape <|> hexEscape <|> octEscape)

-- ----------------------------------------------
-- * chars for quoted chars and literal strings
-- ----------------------------------------------

printable :: GenParser Char st String
printable = single (satisfy (\c -> (c /= '\'')  && (c /= '"') 
                              && (c /= '\\') && (c > '\026')))

caslChar :: GenParser Char st String
caslChar = escapeChar <|> printable

scanQuotedChar :: GenParser Char st String
scanQuotedChar = (caslChar <|> (char '"' >> return "\\\"")) 
                 `enclosedBy` prime <?> "quoted char"

-- convert '"' to '\"' and "'" to "\'" (no support for ''')

scanString :: GenParser Char st String
scanString = flat (many (caslChar <|> (char '\'' >> return "\\\'"))) 
             `enclosedBy` char '"' <?> "literal string"

isString :: Token -> Bool
isString t = take 1 (tokStr t) == "\""

parseString :: Parser a -> String -> a
parseString p s = case parse p "" s of
                  Left _ -> error "parseString"
                  Right x -> x

splitString :: Parser a -> String -> (a, String)
splitString p s = 
    let ph = do hd <- p;
                tl <- getInput;
                return (hd, tl) 
        in parseString ph s

-- ----------------------------------------------
-- * digit, number, fraction, float
-- ----------------------------------------------

getNumber :: GenParser Char st String
getNumber = many1 digit

scanFloat :: GenParser Char st String
scanFloat = getNumber <++> (option "" 
             (char '.' <:> getNumber)
              <++> option "" 
              (char 'E' <:> option "" (single (oneOf "+-"))
               <++> getNumber))

scanDigit :: GenParser Char st String
scanDigit = single digit

isNumber :: Token -> Bool
isNumber t = case tokStr t of 
                           c:_:_ -> isDigit c
                           _     -> False

isFloating :: Token -> Bool
-- precondition: isNumber
isFloating t = any (\c -> c == '.' || c == 'E') (tokStr t)

isLitToken :: Token -> Bool
isLitToken t = case tokStr t of 
               c:_ -> c == '\"' || c == '\'' || isDigit c
               _ -> False

-- ----------------------------------------------
-- * nested comment outs
-- ----------------------------------------------

notEndText :: Char -> GenParser Char st Char
notEndText c = try (char c << notFollowedBy (char '%'))

nestCommentOut :: GenParser Char st Char
nestCommentOut = try (string "%[") >> 
                 many (noneOf "]%" 
                       <|> notEndText ']'
                          <|> nestCommentOut 
                          <|> char '%')
                 >> char ']' >> char '%'

-- ----------------------------------------------
-- * skip whitespaces and nested comment out
-- ----------------------------------------------

whiteChars :: String
whiteChars = "\n\r\t\v\f \160" -- non breaking space

skip :: GenParser Char st ()
skip = skipMany(oneOf (whiteChars) 
                       <|> nestCommentOut <?> "") >> return () 

fromSourcePos :: Pos.SourcePos -> Pos
fromSourcePos p = 
    newPos (Pos.sourceName p) (Pos.sourceLine p) (Pos.sourceColumn p)

getPos :: GenParser tok st Pos
getPos = fmap fromSourcePos getPosition

-- only skip to an annotation if it's on the same or next line
skipSmart :: GenParser Char st ()
skipSmart = do p <- getPosition
               try (do skip
                       q <- getPosition
                       if Pos.sourceLine q <= Pos.sourceLine p + 1 
                           then return ()
                           else notFollowedBy (char '%') >> return ()
                   )
                <|> return ()

-- ----------------------------------------------
-- * keywords WORDS or NO-BRACKET-SIGNS 
-- ----------------------------------------------

keyWord :: GenParser Char st a -> GenParser Char st a
keyWord p = try(p << notFollowedBy (scanLPD <|> singleUnderline))

keySign :: GenParser Char st a -> GenParser Char st a
keySign p = try(p << notFollowedBy (oneOf signChars))

reserved :: [String] -> GenParser Char st String -> GenParser Char st String
-- "try" to avoid reading keywords 
reserved l p = try (p `checkWith` \r -> r `notElem` l)

-- ----------------------------------------------
-- * lexical tokens with position
-- ----------------------------------------------

pToken :: GenParser Char st String -> GenParser Char st Token
pToken parser = bind (\ p s -> Token s [p]) getPos (parser << skipSmart)

pluralKeyword :: String -> GenParser Char st Token
pluralKeyword s = pToken (keyWord (string s <++> option "" (string "s")))

-- | check for keywords (depending on lexem class)
toKey :: String -> GenParser Char st String
toKey s = let p = string s in 
              if last s `elem` "[]{}(),;" then p 
                 else if last s `elem` signChars then keySign p 
                      else keyWord p

-- * some separator parsers

asSeparator :: String -> GenParser Char st Token
asSeparator = pToken . string

commaT, semiT :: GenParser Char st Token
commaT = asSeparator ","
semiT = asSeparator ";"

oBraceT, cBraceT :: GenParser Char st Token
oBraceT = asSeparator "{" 
cBraceT = asSeparator "}"

oBracketT, cBracketT, oParenT, cParenT :: GenParser Char st Token
oBracketT = asSeparator "["
cBracketT = asSeparator "]"
oParenT = asSeparator "("
cParenT = asSeparator ")"

braces :: GenParser Char st a -> GenParser Char st a
braces p = oBraceT >> p << cBraceT

commaSep1 :: GenParser Char st a -> GenParser Char st [a]
commaSep1 p = fmap fst $ separatedBy p commaT

placeS :: GenParser Char st String
placeS = try (string place) <?> place

placeT :: GenParser Char st Token
placeT = pToken placeS

