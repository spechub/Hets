{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse the outer syntax of an Isabelle theory file
-}

module Main where

import System.Environment
import Data.List
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

lemmasS :: String
lemmasS = "lemmas"

lemmaS :: String
lemmaS = "lemma"

corollaryS :: String
corollaryS = "corollary"

refuteS :: String
refuteS = "refute"

theoremsS :: String
theoremsS = "theorems"

theoremS :: String
theoremS = "theorem"

axclassS :: String
axclassS = "axclass"

classesS :: String
classesS = "classes"

instanceS :: String
instanceS = "instance"

typedeclS :: String
typedeclS = "typedecl"

typesS :: String
typesS = "types"

constsS :: String
constsS = "consts"

domainS :: String
domainS = "domain" 

datatypeS :: String
datatypeS = "datatype"

fixrecS :: String
fixrecS = "fixrec"

isaKeywords :: [String]
isaKeywords = markups ++
    [ importsS
    , usesS
    , beginS
    , contextS
    , mlS
    , axiomsS
    , defsS
    , lemmasS
    , theoremsS
    , lemmaS
    , corollaryS
    , theoremS
    , axclassS
    , instanceS
    , typedeclS
    , constsS
    , domainS
    , datatypeS
    , fixrecS
    , andS
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

locale :: CharParser st String
locale = parensP $ lexS "in" >> nameP

markupP :: CharParser st String
markupP = choice (map lexS markups) <++> option "" locale <++> lexP text
         

infixP :: CharParser st ()
infixP = forget $ choice (map lexS ["infix", "infixl", "infixr"])
         >> option "" (lexP isaString) >> lexP nat

mixfixSuffix :: CharParser st ()
mixfixSuffix = forget $ lexP isaString 
    >> option [] (bracketsP $ commalist nat) >> option "" (lexP nat) -- prios

mixfix :: CharParser st ()
mixfix = lexS "(" >> 
    (infixP <|> mixfixSuffix <|> (lexS "binder" >> mixfixSuffix) 
     <|> (forget $ lexS "structure")) << lexS ")"

atom :: CharParser st String
atom = var <|> typeP -- nameref covers nat and symident keywords

args :: CharParser st [String]
args = many $ lexP atom   

arg :: CharParser st [String]
arg = fmap (:[]) (lexP atom) <|> parensP args <|> bracketsP args

attributes :: CharParser st ()
attributes = forget (bracketsP $ commalist $ lexP nameref >> args)

lessOrEq :: CharParser st String
lessOrEq = lexS "<" <|> lexS "\\<subseteq>"

classdecl :: CharParser st [String]
classdecl = do 
    n <- nameP
    lessOrEq
    ns <- commalist nameref
    return $ n : ns

classes :: CharParser st ()
classes = forget $ lexS classesS >> many1 classdecl

typespec :: CharParser st [String]
typespec = fmap (:[]) namerefP <|> do
    ns <- parensP (commalist typefree) <|> fmap (:[]) (lexP typefree)
    n <- namerefP
    return $ n : ns

optinfix :: CharParser st ()
optinfix = option () $ parensP infixP

types :: CharParser st [[String]]
types = lexS typesS >> many1 (typespec << (lexS "=" >> lexP typeP >> optinfix))

typedecl :: CharParser st [[String]]
typedecl = lexS typedeclS >> many1 (typespec << optinfix)

arity :: CharParser st [String]
arity = fmap (:[]) namerefP <|> do
    ns <- parensP $ commalist nameref
    n <- namerefP
    return $ n : ns

arities :: CharParser st [[String]]
arities = lexS "arities" >> many1 (namerefP <:> (lexS "::" >> arity))

consts :: CharParser st [String]
consts = lexS constsS >> many1 (nameP << (lexS "::" >> lexP typeP 
                                          >> option () mixfix))

axmdecl :: CharParser st String
axmdecl = (nameP << option () attributes) << lexS ":" 

prop :: CharParser st String 
prop = reserved isaKeywords $ lexP term

defs :: CharParser st [String]
defs = lexS defsS >> option "" (parensP $ lexS "overloaded") >>
       many1 (axmdecl << prop)

axioms :: CharParser st [String]
axioms = lexS axiomsS >> many1 (axmdecl << prop)

thmbind :: CharParser st String
thmbind = (nameP << option () attributes) <|> (attributes >> return "")

selection :: CharParser st ()
selection = forget . parensP . commalist $
  lexP nat >> option "" (lexS "-" >> option "" (lexP nat))

thmref :: CharParser st String 
thmref = namerefP << (option () selection >> option () attributes)

thmrefs :: CharParser st [String] 
thmrefs = many1 thmref

thmdef :: CharParser st String 
thmdef = try $ thmbind << lexS "="

thmdecl :: CharParser st String 
thmdecl = try $ thmbind << lexS ":"

theorems :: CharParser st ()
theorems = forget $ (lexS theoremsS <|> lexS lemmasS) >> option "" locale 
    >> separatedBy (option "" thmdef >> thmrefs) (lexS andS)  

proppat :: CharParser st ()
proppat = forget . parensP . many1 $ lexP term

props :: CharParser st String 
props = option "" thmdecl << many1 (prop >> option () proppat)

goal :: CharParser st [String]
goal = fmap fst $ separatedBy props (lexS andS)
     
lemma :: CharParser st [String]
lemma = choice (map lexS [lemmaS, theoremS, corollaryS])
    >> option "" locale >> goal -- longgoal ignored

instanceP :: CharParser st String
instanceP = 
    lexS instanceS >> namerefP << (lexS "::" << arity <|> lessOrEq << namerefP)

axclass :: CharParser st [String]
axclass = lexS axclassS >> classdecl << many1 (axmdecl >> prop)

mltext :: CharParser st String
mltext = lexS mlS >> lexP text

-- allow '.' in proofs
anyP :: CharParser st String
anyP = lexP $ atom <|> many1 (char '.')

-- allow "and" in unknown proofs
unknown :: CharParser st ()
unknown = skipMany1 $ forget (reserved (delete andS isaKeywords) anyP)
          <|> forget (parensP rec) <|> forget (bracketsP rec)
          where rec = commalist $ unknown <|> forget anyP 

theoryBody :: CharParser st ()
theoryBody = skipMany $
    forget typedecl
    <|> forget types
    <|> forget consts
    <|> forget defs
    <|> forget classes
    <|> forget markupP
    <|> forget theorems
    <|> forget axioms
    <|> forget instanceP
    <|> forget lemma
    <|> forget axclass
    <|> forget mltext 
    <|> (choice (map lexS [datatypeS, domainS, fixrecS]) >> skipMany unknown)
    <|> unknown

parseTheory :: CharParser st ()
parseTheory = theoryHead >> theoryBody << lexS endS

main :: IO ()
main = getArgs >>= mapM_ process

process :: String -> IO ()
process f = do
  s <- readFile f
  putStrLn $ case parse (parseTheory << eof) f s of
             Right _ -> "succeeded"
             Left err -> show err
