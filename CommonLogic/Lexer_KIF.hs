module CommonLogic.Lexer_KIF where

import CommonLogic.AS_CommonLogic
import Common.Id as Id
import qualified Common.Lexer as Lexer
import Common.Parsec
import Common.Keywords

import Text.ParserCombinators.Parsec as Parsec
import Data.Char (ord)
import Control.Monad (liftM)

-- literally from Lexer_CLIF.hs -- abstract?
pToken :: CharParser st String -> CharParser st Token
pToken p = Lexer.pToken p << many white

oParenT :: CharParser st Token
oParenT = Lexer.oParenT << many white

cParenT :: CharParser st Token
cParenT = Lexer.cParenT << many white

parens :: CharParser st a -> CharParser st a
parens p = oParenT >> p << cParenT

commentLineStart :: String
commentLineStart = ";"

newLinec :: String
newLinec = "\n\r"

whitec :: String
whitec = newLinec ++ "\t\v\f "

whiteSpace :: CharParser st String
whiteSpace = many1 $ oneOf whitec

andKey :: CharParser st Id.Token
andKey = pToken (string andS) <?> "conjunction"

notKey :: CharParser st Id.Token
notKey = pToken (string notS) <?> "negation"

orKey :: CharParser st Id.Token
orKey = pToken (string orS) <?> "disjunction"

ifKey :: CharParser st Id.Token
ifKey = pToken (string implS) <?> "implication"

iffKey :: CharParser st Id.Token
iffKey = pToken (string equivS) <?> "equivalence"

forallKey :: CharParser st Id.Token
forallKey = pToken (string forallS) <?> "universal quantification"

existsKey :: CharParser st Id.Token
existsKey = pToken (string existsS) <?> "existential quantification"

equalsKey :: CharParser st Id.Token
equalsKey = pToken (string "=") <?> "equation"

notEqualKey :: CharParser st Id.Token
notEqualKey = pToken (string "/=") <?> "inequality"

word :: CharParser st String
word = do c <- satisfy kifInitialChar
          s <- many (satisfy kifWordChar)
          return $ c:s

quotedChar :: CharParser st Char
quotedChar = do
  try (satisfy kifChar) <|> try (satisfy kifUnofficial)
  <|> try (char '\\' >> char '\"')

quotedString :: CharParser st String
quotedString = do
  q1 <- char '\"'
  s  <- many quotedChar
  q2 <- char '\"'
  return $ q1:s++[q2]

variable :: CharParser st String
variable = do
  c <- oneOf "?@"
  s <- word
  return $ c:s

sign :: Num a => CharParser st a
sign = liftM (maybe 1 (const (-1))) (optionMaybe $ char '-')

number :: CharParser st String
number = do sgn <- sign
            prePoint <- many1 (satisfy kifDigit)
            postPoint <- optionMaybe $ try $ char '.' >> many1 (satisfy kifDigit)
            ex <- optionMaybe $ try $ liftM fromIntegral expo
            return $ show $ (sgn::Double) * case (postPoint, ex) of
              (Just pp, Just e)  -> (read $ prePoint ++ '.' : pp) * 10**e
              (Just pp, Nothing) -> (read $ prePoint ++ '.' : pp)
              (Nothing, Just e)  -> (read prePoint) * 10**e
              (Nothing, Nothing) -> read prePoint

expo :: CharParser st Int
expo = do char 'e'
          sgn <- sign
          e <- many1 (satisfy kifDigit)
          return $ sgn*(read e)

kifUpper :: Char -> Bool
kifUpper ch = let c = ord ch in c >= 65 && c <= 90

kifLower :: Char -> Bool
kifLower ch = let c = ord ch in c >= 97 && c <= 122

kifSpecial :: Char -> Bool
kifSpecial ch = ch `elem` "!$%&*+-,./<=>?@_~"

-- These characters are used in documentation texts in SUMO.
kifUnofficial :: Char -> Bool
kifUnofficial ch = ch `elem` ",()#':{}`;^"

kifWordChar :: Char -> Bool
kifWordChar ch = kifUpper ch || kifLower ch || kifSpecial ch || kifDigit ch
                 || ch == '-'

kifChar :: Char -> Bool
kifChar ch = kifUpper ch || kifLower ch || kifSpecial ch || kifDigit ch
             || ch `elem` whitec

kifInitialChar :: Char -> Bool
kifInitialChar ch = kifUpper ch || kifLower ch

kifDigit :: Char -> Bool
kifDigit ch = ch `elem` "0123456789"

commentLine :: CharParser st String
commentLine =
  string commentLineStart >> many (noneOf newLinec) <?> ""

white :: CharParser st String
white =
    whiteSpace
  <|>
    commentLine
