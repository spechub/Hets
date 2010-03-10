{- |
Module      :  $Header$
Description :  scan tokens of Haskell sources
Copyright   :  (c) C. Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

-}

module Haskell.Scanner where

import Haskell.Wrapper

import Text.ParserCombinators.Parsec
import Common.Parsec

number :: Parser String
number =
    try (char '0' <:> single (oneOf "oO")) <++> many octDigit
  <|>
    try (char '0' <:> single (oneOf "xX")) <++> many hexDigit
  <|> many1 digit
          <++> optionL (char '.' <:> many digit)
          <++> optionL (oneOf "eE" <:> optionL (single  $ oneOf "+-")
                        <++> many digit)

hChar :: Parser Char
hChar = alphaNum <|> oneOf "_'"

uL :: Parser Char
uL = char '_'

lId :: Parser String
lId = (uL <|> lower) <:> many hChar

uId :: Parser String
uId = upper <:> many hChar

opSym :: Parser Char
opSym = oneOf "!#$%&*+-./:<=>?@\\^|~"

op :: Parser String
op = many1 opSym

data QualElem = Var | Sym | Cons

data QualName = Name Bool QualElem String

instance Show QualName where
  show (Name _ _ s) = s

qId :: Parser QualName
qId = fmap (Name False Var) lId
  <|> fmap (Name False Sym) op
  <|> do
    n <- uId
    option (Name False Cons n) $ do
      d <- try (char '.' << lookAhead (uL <|> letter <|> opSym))
      Name _ k r <- qId
      return $ Name True k $ n ++ d : r

infixOp :: Parser String
infixOp = enclosedBy (fmap show qId) $ char '`'

seps :: String
seps = "[({,;})]"

data TokenKind = Comment | Literal | Infix

data Token
  = QualName QualName
  | Sep Char
  | Token TokenKind String

instance Show Token where
  show t = case t of
    QualName q -> show q
    Sep c -> [c]
    Token _ s -> s

white :: Parser String
white = many space

tok :: Parser Token
tok = fmap (Token Comment) (nestComment <|> lineComment)
  <|> fmap QualName qId
  <|> fmap Sep (oneOf seps)
  <|> fmap (Token Literal) (charLit <|> stringLit <|> number)
  <|> fmap (Token Infix) infixOp

tokPos :: Parser (SourcePos, Token)
tokPos = pair getPosition tok

scan :: Parser (String, [((SourcePos, Token), String)])
scan = pair white (many $ pair tokPos white) << eof

showScan :: (String, [((SourcePos, Token), String)]) -> String
showScan (a, l) = a ++ concatMap (\ ((_, t), w) -> show t ++ w) l
