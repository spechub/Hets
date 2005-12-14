{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse the outer syntax of an Isabelle theory file
-}

module Isabelle.IsaParse where

import Common.Lexer
import Text.ParserCombinators.Parsec

latin :: CharParser st String
latin = single letter <?> "latin"

greek :: CharParser st String
greek = string "\\<" <++> 
         option "" (string "^") -- isup or isup
         <++> many1 letter <++> string ">" <?> "greek"

isaLetter :: CharParser st String
isaLetter = latin <|> greek

quasiletter :: CharParser st String
quasiletter = single (digit <|> prime <|> char '_' ) <|> isaLetter
              <?> "quasiletter"

restident :: CharParser st String
restident = flat (many quasiletter)

ident :: CharParser st String
ident = isaLetter <++> restident

longident :: CharParser st String
longident = ident <++> flat (many $ char '.' <:> ident)

symident :: CharParser st String
symident = many1 (oneOf "!#$&*+-/:<=>?@^_|~" <?> "sym") <|> greek

isaString :: CharParser st String
isaString = enclosedBy (flat $ many (single (noneOf "\\\"")
                                 <|> char '\\' <:> single anyChar))
            (char '\"')

verbatim :: CharParser st String
verbatim = plainBlock "{*" "*}"

nestComment :: CharParser st String
nestComment = nestedComment "(*" "*)"

nat :: CharParser st String
nat = many1 digit <?> "nat"

name :: CharParser st String
name = ident <|> symident <|> isaString <|> nat

nameref :: CharParser st String -- sort
nameref = longident <|> symident <|> isaString <|> nat

text :: CharParser st String 
text = nameref <|> verbatim

typefree :: CharParser st String
typefree = prime <:> ident

indexsuffix :: CharParser st String
indexsuffix =  option "" (char '.' <:> nat)

typevar :: CharParser st String
typevar = try (string "?'") <++> ident <++> option "" (char '.' <:> nat)

typeP :: CharParser st String
typeP = typefree <|> typevar <|> nameref

var :: CharParser st String
var = try (char '?' <:> isaLetter) <++> restident <++> indexsuffix

term :: CharParser st String -- prop
term = var <|> nameref

markups :: [String]
markups = ["--", "chapter"
          , "section", "subsection", "subsubsection", "text", "text_raw"
          , "sect", "subsect", "subsubsect", "txt", "txt_raw"]

isaSkip :: CharParser st ()
isaSkip = skipMany (many1 space <|> nestComment <?> "")

lexP :: CharParser st a -> CharParser st a
lexP p = p << isaSkip

lexS :: String -> CharParser st String
lexS = lexP . try . string

locale :: CharParser st String
locale = lexS "(" <++> lexS "in" <++> lexP name <++> lexS ")"

markupP :: CharParser st String
markupP = choice (map lexS markups) <++> option "" locale <++> lexP text
         
endS :: String
endS = "end"

headerS :: String
headerS = "header"

headerP :: CharParser st String 
headerP = lexS headerS >> lexP text

theoryS :: String
theoryS = "theory"

importsS :: String
importsS = "imports"

usesS :: String
usesS = "uses"

beginS :: String
beginS = "begin"

contextS :: String
contextS = "context"

axiomsS :: String
axiomsS = "axioms"

defsS :: String
defsS = "defs"

oopsS :: String
oopsS = "oops"

mlS :: String
mlS = "ML"

andS :: String
andS = "and"

lemmaS :: String
lemmaS = "lemma"

refuteS :: String
refuteS = "refute"

theoremS :: String
theoremS = "theorem"

axclassS :: String
axclassS = "axclass"

instanceS :: String
instanceS = "instance"

typedeclS :: String
typedeclS = "typedecl"

constsS :: String
constsS = "consts"

domainS :: String
domainS = "domain" 

datatypeS :: String
datatypeS = "datatype"

isaKeywords :: [String]
isaKeywords = markups ++
    [ importsS
    , usesS
    , beginS
    , contextS
    , mlS
    , axiomsS
    , defsS
    , lemmaS
    , theoremS
    , axclassS
    , instanceS
    , typedeclS
    , constsS
    , domainS
    , datatypeS
    , endS] 

nameP :: CharParser st String 
nameP = reserved isaKeywords $ lexP name 

namerefP :: CharParser st String 
namerefP = reserved isaKeywords $ lexP nameref 

parname :: CharParser st String 
parname = lexS "(" <++> lexP name <++> lexS ")"

data TheoryHead = TheoryHead 
   { header :: Maybe String 
   , theoryname :: String
   , imports :: [String]
   , uses :: [String]
   , context :: Maybe String
   }

theoryHead :: CharParser st TheoryHead
theoryHead = do
    oh <- option Nothing $ fmap Just headerP 
    lexS theoryS
    th <- nameP 
    is <- option [] (lexS importsS >> many nameP)
    us <- option [] (lexS usesS >> many (nameP <|> parname))   
    lexS beginS
    oc <- option Nothing $ fmap Just nameP
    return $ TheoryHead oh th is us oc

commalist :: CharParser st a -> CharParser st [a]
commalist p = fmap fst $ lexP p `separatedBy` lexS ","

parensP :: CharParser st a -> CharParser st a
parensP p = do 
    lexS "("
    a <- p
    lexS ")"
    return a

bracketsP :: CharParser st a -> CharParser st a
bracketsP p = do 
    lexS "["
    a <- p
    lexS "]"
    return a

infixP :: CharParser st ()
infixP = do 
    choice $ map lexS ["infix", "infixl", "infixr"]
    option "" $ lexP isaString
    lexP nat
    return ()

mixfixSuffix :: CharParser st ()
mixfixSuffix = do
    lexP isaString
    option [] $ bracketsP $ commalist nat -- prios
    option "" $ lexP nat
    return ()

mixfix :: CharParser st ()
mixfix = lexS "(" >> 
    (infixP <|> mixfixSuffix <|> (lexS "binder" >> mixfixSuffix) 
     <|> (lexS "structure" >> return ())) << lexS ")"

atom :: CharParser st String
atom = var <|> typeP -- nameref covers nat and symident keywords

args :: CharParser st [String]
args = many $ lexP atom   

arg :: CharParser st [String]
arg = fmap (:[]) (lexP atom) <|> parensP args <|> bracketsP args

attributes :: CharParser st ()
attributes = bracketsP (commalist $ lexP nameref >> args) >> return ()

classdecl :: CharParser st [String]
classdecl = do 
    n <- nameP
    lexS "<" <|> lexS "\\<subseteq>"
    ns <- commalist nameref
    return $ n : ns

classes :: CharParser st ()
classes = lexS "classes" >> many1 classdecl >> return ()

typespec :: CharParser st [String]
typespec = fmap (:[]) namerefP <|> do
    ns <- parensP (commalist typefree) <|> fmap (:[]) (lexP typefree)
    n <- namerefP
    return $ n : ns

optinfix :: CharParser st ()
optinfix = option () $ parensP infixP

types :: CharParser st [[String]]
types = lexS "types" >> many1 (typespec << (lexS "=" >> typeP >> optinfix))

typedecl :: CharParser st [[String]]
typedecl = lexS "typedecl" >> many1 (typespec << optinfix)

arity :: CharParser st [String]
arity = fmap (:[]) namerefP <|> do
    ns <- parensP $ commalist nameref
    n <- namerefP
    return $ n : ns

arities :: CharParser st [[String]]
arities = lexS "arities" >> many1 (namerefP <:> (lexS "::" >> arity))

