module BParser where

import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

lexer :: T.TokenParser st
lexer = T.makeTokenParser gmpDef

whiteSpace :: CharParser st ()
whiteSpace = T.whiteSpace lexer

gmpDef :: LanguageDef st
gmpDef
    = haskellStyle
    { identStart        = letter
    , identLetter       = alphaNum <|> oneOf "_'"
    , opStart           = opLetter gmpDef
    , opLetter          = oneOf "\\-<>/~[]"
    , reservedOpNames   = ["~","->","<-","<->","/\\","\\/","[]","<>"]
    }
lwb2sf :: Parser String
lwb2sf = -- parse lwb formulae as string and transform it to standard
    do try(string "box")
       whiteSpace
       return "[]"
    do try (string "dia")
       whiteSpace
       return "<>"
    do try(string "&")
       whiteSpace
       return "/\\"
    do try(string "v")
       whiteSpace
       return "\\/"
    do try string
