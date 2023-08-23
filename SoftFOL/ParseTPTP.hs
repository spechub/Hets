{- |
Module      :  ./SoftFOL/ParseTPTP.hs
Description :  A parser for the TPTP Input Syntax
Copyright   :  (c) C.Maeder, DFKI Lab Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

A parser for the TPTP Input Syntax v3.4.0.1 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module SoftFOL.ParseTPTP
  ( tptp
  , singleQuoted
  , form
  , genList
  , genTerm
  , GenTerm (..)
  , GenData (..)
  , AWord (..)
  , prTPTPs
  , tptpModel
  , ppGenTerm
 ) where

import Text.ParserCombinators.Parsec
import SoftFOL.Sign
import SoftFOL.PrintTPTP

import qualified Common.Doc as Doc
import Common.Id
import Common.Lexer (getPos)
import Common.Parsec

import Control.Monad
import Data.Char (ord, toLower, isAlphaNum)
import Data.Maybe

showRole :: Role -> String
showRole = map toLower . show

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

tptp :: Parser [TPTP]
tptp = skip >> many (headerLine <|> include <|> formAnno
   <|> (newline >> skip >> return EmptyLine)) << eof

blank :: Parser p -> Parser ()
blank = (>> skipMany1 whiteSpace)

szsOutput :: Parser ()
szsOutput = blank (string "SZS") >> blank (string "output")

iproverSzsEnd :: Parser ()
iproverSzsEnd = try $ char '%' >> skipMany whiteSpace >> szsOutput

otherCommentLine :: Parser ()
otherCommentLine = (lookAhead iproverSzsEnd >> forget (char '%'))
  <|> forget commentLine

skipAllButEnd :: Parser ()
skipAllButEnd = skipMany $ whiteSpace <|> commentBlock <|> otherCommentLine
  <|> forget newline

tptpModel :: Parser [(String, SPTerm)]
tptpModel = do
  _ <- manyTill anyChar
    (try (szsOutput >> blank (string "start"))
     <|> try (blank $ string "START OF MODEL"))
  _ <- manyTill anyChar newline
  skipAllButEnd
  ts <- many1 (formAnno << skipAllButEnd)
  (szsOutput >> blank (string "end"))
    <|> forget (string "END OF MODEL")
  return $ foldr (\ t l -> case t of
    FormAnno _ (Name n) _ e _ -> (n, e) : l
    _ -> l) [] ts

printable :: Char -> Bool
printable c = let i = ord c in i >= 32 && i <= 126

commentLine :: Parser String
commentLine = (char '%' <|> char '#') >> manyTill (satisfy printable) newline

headerLine :: Parser TPTP
headerLine = fmap CommentLine $ commentLine << skip

commentBlock :: Parser ()
commentBlock = forget $ plainBlock "/*" "*/"

whiteSpace :: Parser ()
whiteSpace = forget $ oneOf "\r\t\v\f "

skip :: Parser ()
skip = skipMany $ whiteSpace <|> commentBlock

skipAll :: Parser ()
skipAll = skipMany $ whiteSpace <|> commentBlock <|> forget commentLine
  <|> forget newline

lexeme :: Parser a -> Parser a
lexeme = (<< skipAll)

key :: Parser a -> Parser ()
key = (>> skipAll)

keyChar :: Char -> Parser ()
keyChar = key . char

comma :: Parser ()
comma = keyChar ','

oParen :: Parser ()
oParen = keyChar '('

cDotParen :: Parser ()
cDotParen = string ")." >> skip >> option () (newline >> skip)

include :: Parser TPTP
include = do
  key $ tryString "include"
  oParen
  a <- atomicWord
  m <- optionL $ do
    comma
    sepBy1 aname comma
  cDotParen
  return $ Include (FileName a) m

-- | does not allow leading zeros
natural :: Parser String
natural = string "0" <|> many1 digit

aname :: Parser Name
aname = fmap Name (atomicWord <|> lexeme natural)

atomicWord :: Parser String
atomicWord = lexeme $ lowerWord <|> singleQuoted

isUAlphaNum :: Char -> Bool
isUAlphaNum c = isAlphaNum c || elem c "_$"

luWord :: Parser Char -> Parser String
luWord p = do
  c <- p
  r <- many $ satisfy isUAlphaNum
  return $ c : r

lowerWord :: Parser String
lowerWord = luWord lower

upperWord :: Parser String
upperWord = luWord upper

singleQuoted :: Parser String
singleQuoted =
  let quote = '\'' in fmap concat $
  char quote
  >> many (tryString "\\'" <|> single
       (satisfy $ \ c -> printable c && c /= quote))
  << char quote

formKind :: Parser FormKind
formKind = choice $ map (\ k -> key (tryString $ show k) >> return k)
    [FofKind, CnfKind, FotKind]

role :: Parser Role
role = choice $ map (\ r -> key (tryString $ showRole r)
                     >> return r) allRoles

formAnno :: Parser TPTP
formAnno = do
  k <- formKind
  oParen
  n <- aname
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
  cDotParen
  return $ FormAnno k n r f m

colon :: Parser ()
colon = keyChar ':'

genTerm :: Parser GenTerm
genTerm = fmap GenTermList genList <|> do
  gd <- genData
  m <- optionMaybe $ do
    keyChar ':'
    genTerm
  return $ GenTerm gd m

genData :: Parser GenData
genData = formData <|> otherData <|> do
  a <- fmap AWord atomicWord
  l <- optionL $ parens $ sepBy1 genTerm comma
  return $ GenData a l

otherData :: Parser GenData
otherData = fmap OtherGenData $ (upperWord <|> real <|> distinct) << skipAll

distinct :: Parser String
distinct =
  let dquot = '"' in
  enclosedBy (flat $ many1 $ tryString "\\\"" <|> single (satisfy (/= dquot)))
  $ char dquot

decimal :: Parser String
decimal = optionL (single $ oneOf "-+") <++> natural

real :: Parser String
real = do
  d <- decimal
  f <- optionL $ char '.' <:> many1 digit
  e <- optionL $ oneOf "eE" <:> decimal
  return $ d ++ f ++ e

formData :: Parser GenData
formData =
  liftM GenFormData $ liftM2 FormData (char '$' >> formKind) $ parens form

orOp :: Parser ()
orOp = keyChar '|'

andOp :: Parser ()
andOp = keyChar '&'

pToken :: Parser String -> Parser Token
pToken = liftM2 (\ p s -> Token s (Range [p])) getPos . (<< skipAll)

form :: Parser SPTerm
form = do
  u <- unitary
  do orOp
     us <- sepBy1 unitary orOp
     return $ compTerm SPOr $ u : us
    <|> do
      andOp
      us <- sepBy1 unitary andOp
      return $ compTerm SPAnd $ u : us
    <|> do
      o <- choice $ map (pToken . tryString)
           ["<=>", "=>", "<=", "<~>", "~|", "~&"]
      u2 <- unitary
      let s = tokStr o
          a = [u, u2]
      return $ case lookup s $ zip ["<=>", "=>", "<="]
         [SPEquiv, SPImplies, SPImplied] of
           Just ks -> compTerm ks a
           Nothing -> case lookup s $ zip ["<~>", "~|", "~&"]
             [SPEquiv, SPOr, SPAnd] of
               Just ks -> compTerm SPNot [compTerm ks a]
               Nothing -> compTerm (SPCustomSymbol o) a
    <|> return u

unitary :: Parser SPTerm
unitary = parens form <|> quantForm <|> unaryForm <|> atomicForm

quantForm :: Parser SPTerm
quantForm = do
  q <- lexeme $ (char '!' >> return SPForall)
            <|> (char '?' >> return SPExists)
  vs <- brackets $ sepBy1 variable comma
  colon
  u <- unitary
  return SPQuantTerm
    { quantSym = q
    , variableList = vs
    , qFormula = u }

unaryForm :: Parser SPTerm
unaryForm = do
  keyChar '~'
  u <- unitary
  return $ compTerm SPNot [u]

atomicForm :: Parser SPTerm
atomicForm = do
  t <- term
  do key $ try $ char '=' << notFollowedBy (char '>' )
     t2 <- term
     return $ mkEq t t2
    <|> do
      key $ tryString "!="
      t2 <- term
      return $ compTerm SPNot [mkEq t t2]
    <|> return t

variable :: Parser SPTerm
variable = fmap (simpTerm . SPCustomSymbol) $ pToken upperWord

definedAtom :: Parser SPTerm
definedAtom = fmap (simpTerm . SPCustomSymbol) $ pToken $ real <|> distinct

functor :: Parser SPSymbol
functor = fmap (\ t -> fromMaybe (SPCustomSymbol t)
    $ lookup (tokStr t)
    $ zip ["$true", "$false", "$equal"] [SPTrue, SPFalse, SPEqual])
  $ pToken
  $ lowerWord <|> singleQuoted <|> dollarWord

-- system and defined words
dollarWord :: Parser String
dollarWord = do
  d <- tryString "$$" <|> string "$"
  w <- lowerWord
  return $ d ++ w

-- mixed plain, defined and system terms
term :: Parser SPTerm
term = variable <|> definedAtom <|> do
  f <- functor
  as <- optionL $ parens $ sepBy1 term comma
  return $ compTerm f as

brackets :: Parser a -> Parser a
brackets p = do
  keyChar '['
  a <- p
  keyChar ']'
  return a

parens :: Parser a -> Parser a
parens p = do
  oParen
  a <- p
  keyChar ')'
  return a

genList :: Parser [GenTerm]
genList = brackets $ sepBy genTerm comma

prTPTPs :: [TPTP] -> Doc.Doc
prTPTPs = Doc.vcat . map prTPTP

prTPTP :: TPTP -> Doc.Doc
prTPTP p = case p of
  FormAnno k (Name n) r t m ->
      Doc.text (show k)
      <> Doc.parens
      (Doc.sepByCommas $
       [ Doc.text n
       , Doc.text $ showRole r
       , printTPTP t]
       ++ maybe [] ppAnnos m)
      <> Doc.dot
  Include (FileName f) ns ->
      Doc.text "include"
      <> Doc.parens
      (Doc.sepByCommas $
       ppName f : if null ns then [] else
          [Doc.brackets $ Doc.sepByCommas $ map ppAName ns])
      <> Doc.dot
  CommentLine l -> Doc.text $ '%' : l
  EmptyLine -> Doc.text ""

ppName :: String -> Doc.Doc
ppName s = (if all isUAlphaNum s then id else Doc.quotes) $ Doc.text s

ppAName :: Name -> Doc.Doc
ppAName (Name n) = ppName n

ppAnnos :: Annos -> [Doc.Doc]
ppAnnos (Annos (Source gt) m) = ppGenTerm gt : maybe [] ppInfo m

ppInfo :: Info -> [Doc.Doc]
ppInfo (Info l) = [ppGenList l]

ppList :: [GenTerm] -> Doc.Doc
ppList = Doc.sepByCommas . map ppGenTerm

ppGenList :: [GenTerm] -> Doc.Doc
ppGenList = Doc.brackets . ppList

ppGenTerm :: GenTerm -> Doc.Doc
ppGenTerm gt = case gt of
  GenTerm gd m -> let d = ppGenData gd in case m of
    Just t -> Doc.fsep [d <> Doc.colon, ppGenTerm t]
    Nothing -> d
  GenTermList l -> ppGenList l

ppGenData :: GenData -> Doc.Doc
ppGenData gd = case gd of
  GenData (AWord aw) l -> ppName aw <>
    if null l then Doc.empty else Doc.parens $ ppList l
  OtherGenData s -> Doc.text s
  GenFormData (FormData k t) ->
     Doc.text ('$' : show k)
     <> Doc.parens (printTPTP t)
