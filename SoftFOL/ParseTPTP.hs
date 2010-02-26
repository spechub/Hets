{- |
Module      :  $Header$
Description :  A parser for the TPTP Input Syntax
Copyright   :  (c) C.Maeder, DFKI Lab Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

A parser for the TPTP Input Syntax v3.4.0.1 taken from
<http://www.cs.miami.edu/~tptp/TPTP/SyntaxBNF.html>
-}

module SoftFOL.ParseTPTP
  ( tptp
  , prTPTPs
  , tptpModel
  ) where

import Text.ParserCombinators.Parsec
import SoftFOL.Sign
import SoftFOL.PrintTPTP

import qualified Common.Doc as Doc
import Common.Id
import Common.Lexer ((<<), (<:>), (<++>), getPos, single)

import Control.Monad
import Data.Char (ord, toLower, isAlphaNum)

data TPTP =
    FormAnno FormKind Name Role SPTerm (Maybe Annos)
  | Include FileName [Name]
  | CommentLine String  -- collect top-level comment lines
  | EmptyLine -- and blank lines
    deriving Show

data Name = Name String deriving Show

data AWord = AWord String deriving Show

data FileName = FileName String deriving Show

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

data Annos = Annos Source (Maybe Info) deriving Show

data Source = Source GenTerm deriving Show

data GenTerm =
    GenTerm GenData (Maybe GenTerm)
  | GenTermList [GenTerm]
    deriving Show

data GenData =
    GenData AWord [GenTerm]
  | OtherGenData String  -- variable, number, distinct_object
  | GenFormData FormData
    deriving Show

data FormData = FormData FormKind SPTerm deriving Show

data Info = Info [GenTerm] deriving Show

tptp :: Parser [TPTP]
tptp = skip >> many (headerLine <|> include <|> formAnno
   <|> (newline >> skip >> return EmptyLine)) << eof

blank :: Parser p -> Parser ()
blank = (>> skipMany1 whiteSpace)

szsOutput :: Parser ()
szsOutput = blank (string "SZS") >> blank (string "output")

tptpModel :: Parser [(String, SPTerm)]
tptpModel = do
  manyTill anyChar $ try $ szsOutput >> blank (string "start")
  manyTill anyChar newline
  skipAll
  ts <- many1 (formAnno << skipAll)
  szsOutput >> blank (string "end")
  return $ map (\ (FormAnno _ (Name n) _ t _) -> (n, t)) ts

printable :: Char -> Bool
printable c = let i = ord c in i >= 32 && i <= 126

commentLine :: Parser String
commentLine = char '%' >> manyTill (satisfy printable) newline

headerLine :: Parser TPTP
headerLine = fmap CommentLine $ commentLine << skip

commentBlock :: Parser ()
commentBlock = do
  string "/*"
  manyTill anyChar $ try $ string "*/"
  return ()

whiteSpace :: Parser ()
whiteSpace = oneOf "\r\t\v\f " >> return ()

skip :: Parser ()
skip = skipMany $ whiteSpace <|> commentBlock

skipAll :: Parser ()
skipAll = skipMany $ whiteSpace <|> commentBlock <|> (commentLine >> return ())
  <|> (newline >> return ())

lexeme :: Parser a -> Parser a
lexeme = (<< skipAll)

key :: Parser a -> Parser ()
key = (>> skipAll)

comma :: Parser ()
comma = key $ char ','

oParen :: Parser ()
oParen = key $ char '('

cDotParen :: Parser ()
cDotParen = string ")." >> skip >> option () (newline >> skip)

include :: Parser TPTP
include = do
  key $ try $ string "include"
  oParen
  a <- atomicWord
  m <- option [] $ do
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
isUAlphaNum c = isAlphaNum c || c == '_'

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
singleQuoted = do
  let quote = '\''
  char quote
  s <- many1 $ try (string "\\'") <|> single
       (satisfy $ \ c -> printable c && c /= quote)
  char quote
  return $ concat s

formKind :: Parser FormKind
formKind = choice $ map (\ k -> key (try $ string $ show k) >> return k)
    [FofKind, CnfKind, FotKind]

role :: Parser Role
role = choice $ map (\ r -> key (try $ string $ showRole r)
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
colon = key $ char ':'

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
  l <- option [] $ parens $ sepBy1 genTerm comma
  return $ GenData a l

otherData :: Parser GenData
otherData = fmap OtherGenData $ (upperWord <|> real <|> distinct) << skipAll

distinct :: Parser String
distinct = do
  let dquot = '"'
  a <- char dquot
  s <- many1 $ try (string "\\\"") <|> single (satisfy (/= dquot))
  e <- char dquot
  return $ a : concat s ++ [e]

decimal :: Parser String
decimal = option "" $ single (oneOf "-+") <++> natural

real :: Parser String
real = do
  d <- decimal
  f <- option "" $ char '.' <:> many1 digit
  e <- option "" $ oneOf "eE" <:> decimal
  return $ d ++ f ++ e

formData :: Parser GenData
formData = do
  char '$'
  k <- formKind
  f <- parens form
  return $ GenFormData $ FormData k f

orOp :: Parser ()
orOp = key $ char '|'

andOp :: Parser ()
andOp = key $ char '&'

pToken :: Parser String -> Parser Token
pToken = liftM2 (\ p s -> Token s (Range [p])) getPos . (<< skipAll)

form :: Parser SPTerm
form = do
  u <- unitary
  do  orOp
      us <- sepBy1 unitary orOp
      return $ compTerm SPOr $ u : us
    <|> do
      andOp
      us <- sepBy1 unitary andOp
      return $ compTerm SPAnd $ u : us
    <|> do
      o <- choice $ map (pToken . try . string)
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
  key $ char '~'
  u <- unitary
  return $ compTerm SPNot [u]

atomicForm :: Parser SPTerm
atomicForm = do
  t <- term
  do  key $ try $ char '=' << notFollowedBy (char '>' )
      t2 <- term
      return $ mkEq t t2
    <|> do
      key $ try $ string "!="
      t2 <- term
      return $ compTerm SPNot [mkEq t t2]
    <|> return t

variable :: Parser SPTerm
variable = fmap (simpTerm . SPCustomSymbol) $ pToken upperWord

definedAtom :: Parser SPTerm
definedAtom = fmap (simpTerm . SPCustomSymbol) $ pToken $ real <|> distinct

functor :: Parser SPSymbol
functor = fmap (\ t -> case lookup (tokStr t) $ zip
  ["$true", "$false", "$equal"] [SPTrue, SPFalse, SPEqual] of
  Just ks -> ks
  Nothing -> SPCustomSymbol t) $ pToken
  $ lowerWord <|> singleQuoted <|> dollarWord

-- system and defined words
dollarWord :: Parser String
dollarWord = do
  d <- try (string "$$") <|> string "$"
  w <- lowerWord
  return $ d ++ w

-- mixed plain, defined and system terms
term :: Parser SPTerm
term = variable <|> definedAtom <|> do
  f <- functor
  as <- option [] $ parens $ sepBy1 term comma
  return $ compTerm f as

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

prTPTPs :: [TPTP] -> Doc.Doc
prTPTPs = Doc.vcat . map prTPTP

prTPTP :: TPTP -> Doc.Doc
prTPTP p = case p of
  FormAnno k (Name n) r t m ->
      Doc.text (show k)
      Doc.<> Doc.parens
      (Doc.sepByCommas $
       [ Doc.text n
       , Doc.text $ showRole r
       , printTPTP t]
       ++ maybe [] ppAnnos m)
      Doc.<> Doc.dot
  Include (FileName f) ns ->
      Doc.text "include"
      Doc.<> Doc.parens
      (Doc.sepByCommas $
       ppName f : if null ns then [] else
          [Doc.brackets $ Doc.sepByCommas $ map ppAName ns])
      Doc.<> Doc.dot
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
    Just t -> Doc.fsep [d Doc.<> Doc.colon, ppGenTerm t]
    Nothing -> d
  GenTermList l -> ppGenList l

ppGenData :: GenData -> Doc.Doc
ppGenData gd = case gd of
  GenData (AWord aw) l -> ppName aw Doc.<>
    if null l then Doc.empty else Doc.parens $ ppList l
  OtherGenData s -> Doc.text s
  GenFormData (FormData k t) ->
     Doc.text ('$' : show k)
     Doc.<> Doc.parens (printTPTP t)
