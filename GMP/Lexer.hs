module Lexer where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as T

-------------------------------------------------------------------------------
-- The lexer
-------------------------------------------------------------------------------
lexer            = T.makeTokenParser gmpDef

lexeme          = T.lexeme lexer
parens          = T.parens lexer
braces          = T.braces lexer
semiSep         = T.semiSep lexer
semiSep1        = T.semiSep1 lexer
commaSep        = T.commaSep lexer
commaSep1       = T.commaSep1 lexer
whiteSpace      = T.whiteSpace lexer
symbol          = T.symbol lexer
identifier      = T.identifier lexer
reserved        = T.reserved lexer
natural         = T.natural lexer


gmpDef
    = haskellStyle
    { identStart        = letter
    , identLetter       = alphaNum <|> oneOf "_'" -- ???
    , opStart           = opLetter gmpDef
    , opLetter          = oneOf "\\-</~[]"
    , reservedOpNames   = ["~","->","<-","<->","/\\","\\/","[]"]
    }
-------------------------------------------------------------------------------
-------------------------------------------------------------------------------

