{- |
Module      :  $Header$
Description :  A parser for the TPTP Input Syntax
Copyright   :  (c) C.Maeder, DFKI Lab Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

A parser for the TPTP Input Syntax taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module Softfol.ParseTPTP where

import Text.ParserCombinators.Parsec
import SoftFOL.Sign (SPTerm)
import Common.Lexer ((<<))
import Data.Char (ord, toLower)

data TPTP =
    FormAnno FormKind Name Role SPTerm (Maybe Annos)
  | Include FileName [Name]
  | CommentLine String  -- collect top-level comment lines

data Name = Name String

data AWord = AWord String

data FileName = FileName String

data FormKind = FofKind | CnfKind | FotKind

instance Show FormKind where
    show k = case k of
        FofKind -> "fof"
        CnfKind -> "cnf"
        FotKind -> "fot"

data Role =
    Axiom
  | Hypothesis
  | Definition
  | Assumption
  | Lemma
  | Theorem
  | Conjecture
  | Negated_conjecture
  | Plain
  | Fi_domain
  | Fi_functors
  | Fi_predicates
  | Type
  | Unknown
    deriving Show

allRoles :: [Role]
allRoles =
  [ Axiom
  , Hypothesis
  , Definition
  , Assumption
  , Lemma
  , Theorem
  , Conjecture
  , Negated_conjecture
  , Plain
  , Fi_domain
  , Fi_functors
  , Fi_predicates
  , Type
  , Unknown ]

data Annos = Annos Source (Maybe Info)

data Source = Source GenTerm

data GenTerm =
    GenTerm GenData (Maybe GenTerm)
  | GenTermList [GenTerm]

data GenData =
    GenData AWord (Maybe [GenTerm])
  | OtherGenData String  -- variable, number, distinct_object
  | GenFormData FormData

data FormData = FormData FormKind SPTerm

data Info = Info [GenTerm]

tptp :: Parser [TPTP]
tptp = skip >> many (headerLine <|> include <|> formAnno)

commentLine :: Parser String
commentLine = char '%' >> manyTill anyChar newline

headerLine :: Parser TPTP
headerLine = fmap CommentLine $ commentLine << skip

commentBlock :: Parser ()
commentBlock = do
  string "/*"
  skipMany (satisfy (/= '*') <|> (char '*' << notFollowedBy (char '/')))
  string "*/"
  return ()

whiteSpace :: Parser ()
whiteSpace = space >> return ()

skip :: Parser ()
skip = skipMany $ whiteSpace <|> commentBlock

skipAll :: Parser ()
skipAll = skipMany $ whiteSpace <|> commentBlock <|> (commentLine >> return ())

lexeme :: Parser a -> Parser a
lexeme p = p << skipAll

key :: Parser a -> Parser ()
key p = p >> skipAll

comma :: Parser ()
comma = key $ char ','

oParen :: Parser ()
oParen = key $ char '('

include :: Parser TPTP
include = do
  key $ try $ string "include"
  oParen
  a <- atomicWord
  m <- option [] $ do
    comma
    sepBy1 name comma
  char ')'
  skip
  return $ Include (FileName a) m

-- | also allows leading zeros
unsignedInt :: Parser String
unsignedInt = many1 digit << skipAll

name :: Parser Name
name = fmap Name (atomicWord <|> unsignedInt)

atomicWord :: Parser String
atomicWord = lowerWord <|> singleQuoted

luWord :: Parser Char -> Parser String
luWord p = do
  c <- p
  r <- many $ alphaNum <|> char '_'
  skipAll
  return $ c : r

lowerWord :: Parser String
lowerWord = luWord lower

upperWord :: Parser String
upperWord = luWord upper

singleQuoted :: Parser String
singleQuoted = do
  let quote = '\''
  char quote
  s <- many1 $ try (string "\\'") <|> fmap (: "")
       (satisfy $ \ c -> let i = ord c in i >= 32 && i <= 126 && c /= quote)
  char quote
  skipAll
  return $ concat s

formKind :: Parser FormKind
formKind = choice $ map (\ k -> key (try $ string $ show k) >> return k)
    [FofKind, CnfKind, FotKind]

role :: Parser Role
role = choice $ map (\ r -> key (try $ string $ map toLower $ show r)
                     >> return r) allRoles

formAnno :: Parser TPTP
formAnno = do
  k <- formKind
  oParen
  n <- name
  comma
  r <- role
  comma
  f <- form
  m <- optionMaybe $ do
    comma
    gt <- fmap Source genTerm
    i <- optionMaybe $ do
      comma
      fmap Info genList
    return $ Annos gt i
  char ')'
  skip
  return $ FormAnno k n r f m

genTerm :: Parser GenTerm
genTerm = fmap GenTermList genList <|> do
  gd <- genData
  m <- optionMaybe $ do
    key $ char ':'
    genTerm
  return $ GenTerm gd m

genData :: Parser GenData
genData = formData <|> otherData <|> do
  a <- fmap AWord atomicWord
  m <- optionMaybe $ parens $ sepBy1 genTerm comma
  return $ GenData a m

otherData :: Parser GenData
otherData = fmap OtherGenData upperWord -- or number or distinct_object 

formData :: Parser GenData
formData = do
  char '$'
  k <- formKind
  f <- parens form
  return $ GenFormData $ FormData k f

form :: Parser SPTerm
form = undefined

brackets :: Parser a -> Parser a
brackets p = do
  key $ char '['
  a <- p
  key $ char ']'
  return a

parens :: Parser a -> Parser a
parens p = do
  oParen
  a <- p
  key $ char ')'
  return a

genList :: Parser [GenTerm]
genList = brackets $ sepBy genTerm comma
