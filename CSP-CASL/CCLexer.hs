module CCLexer where

import CCKeywords

import Parsec
import Id (Token(..))

import Lexer



extChoiceT, intChoiceT :: GenParser Char st Token
extChoiceT = asKey extChoiceS
intChoiceT = asKey intChoiceS