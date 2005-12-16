{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

parse the outer syntax of an Isabelle theory file
-}

module Isabelle.IsaParse
    (parseTheory
    , Body
    , TheoryHead(..)
    , compatibleBodies) where

import Data.List
import Common.Lexer
import Text.ParserCombinators.Parsec
import qualified Common.Lib.Map as Map
import Isabelle.IsaConsts
import Common.Id
import Common.Result

latin :: Parser String
latin = single letter <?> "latin"

greek :: Parser String
greek = string "\\<" <++>
         option "" (string "^") -- isup or isup
         <++> many1 letter <++> string ">" <?> "greek"

isaLetter :: Parser String
isaLetter = latin <|> greek

quasiletter :: Parser String
quasiletter = single (digit <|> prime <|> char '_' ) <|> isaLetter
              <?> "quasiletter"

restident :: Parser String
restident = flat (many quasiletter)

ident :: Parser String
ident = isaLetter <++> restident

longident :: Parser String
longident = ident <++> flat (many $ char '.' <:> ident)

symident :: Parser String
symident = many1 (oneOf "!#$&*+-/:<=>?@^_|~" <?> "sym") <|> greek

isaString :: Parser String
isaString = enclosedBy (flat $ many (single (noneOf "\\\"")
                                 <|> char '\\' <:> single anyChar))
            (char '\"')

verbatim :: Parser String
verbatim = plainBlock "{*" "*}"

nestComment :: Parser String
nestComment = nestedComment "(*" "*)"

nat :: Parser String
nat = many1 digit <?> "nat"

name :: Parser String
name = ident <|> symident <|> isaString <|> nat

nameref :: Parser String -- sort
nameref = longident <|> symident <|> isaString <|> nat

text :: Parser String
text = nameref <|> verbatim

typefree :: Parser String
typefree = prime <:> ident

indexsuffix :: Parser String
indexsuffix =  option "" (char '.' <:> nat)

typevar :: Parser String
typevar = try (string "?'") <++> ident <++> option "" (char '.' <:> nat)

typeP :: Parser String
typeP = typefree <|> typevar <|> nameref

var :: Parser String
var = try (char '?' <:> isaLetter) <++> restident <++> indexsuffix

term :: Parser String -- prop
term = var <|> nameref

isaSkip :: Parser ()
isaSkip = skipMany (many1 space <|> nestComment <?> "")

lexP :: Parser a -> Parser a
lexP p = p << isaSkip

lexS :: String -> Parser String
lexS = lexP . try . string

headerP :: Parser String
headerP = lexS headerS >> lexP text

nameP :: Parser String
nameP = reserved isaKeywords $ lexP name

namerefP :: Parser String
namerefP = reserved isaKeywords $ lexP nameref

parname :: Parser String
parname = lexS "(" <++> lexP name <++> lexS ")"

data TheoryHead = TheoryHead
   { theoryname :: String
   , imports :: [String]
   , uses :: [String]
   , context :: Maybe String
   } deriving Eq

theoryHead :: Parser TheoryHead
theoryHead = do
    option () isaSkip
    option Nothing $ fmap Just headerP
    lexS theoryS
    th <- nameP
    is <- option [] (lexS importsS >> many nameP)
    us <- option [] (lexS usesS >> many (nameP <|> parname))
    lexS beginS
    oc <- option Nothing $ fmap Just nameP
    return $ TheoryHead th is us oc

commalist :: Parser a -> Parser [a]
commalist p = fmap fst $ lexP p `separatedBy` lexS ","

parensP :: Parser a -> Parser a
parensP p = do
    lexS "("
    a <- p
    lexS ")"
    return a

bracketsP :: Parser a -> Parser a
bracketsP p = do
    lexS "["
    a <- p
    lexS "]"
    return a

bracesP :: Parser a -> Parser a
bracesP p = do
    lexS "{"
    a <- p
    lexS "}"
    return a

recordP :: Parser a -> Parser a
recordP p = do
    lexS "(|"
    a <- p
    lexS "|)"
    return a

locale :: Parser String
locale = parensP $ lexS "in" >> nameP

markupP :: Parser String
markupP = choice (map lexS markups) <++> option "" locale <++> lexP text

infixP :: Parser ()
infixP = forget $ choice (map lexS ["infix", "infixl", "infixr"])
         >> option "" (lexP isaString) >> lexP nat

mixfixSuffix :: Parser ()
mixfixSuffix = forget $ lexP isaString
    >> option [] (bracketsP $ commalist nat) >> option "" (lexP nat) -- prios

mixfix :: Parser ()
mixfix = lexS "(" >>
    (infixP <|> mixfixSuffix <|> (lexS "binder" >> mixfixSuffix)
     <|> (forget $ lexS "structure")) << lexS ")"

atom :: Parser String
atom = var <|> typeP -- nameref covers nat and symident keywords

args :: Parser [String]
args = many $ lexP atom

{-
arg :: Parser [String]
arg = fmap (:[]) (lexP atom) <|> parensP args <|> bracketsP args
-}

attributes :: Parser ()
attributes = forget (bracketsP $ commalist $ lexP nameref >> args)

lessOrEq :: Parser String
lessOrEq = lexS "<" <|> lexS "\\<subseteq>"

classdecl :: Parser [String]
classdecl = do
    n <- nameP
    lessOrEq
    ns <- commalist nameref
    return $ n : ns

classes :: Parser ()
classes = forget $ lexS classesS >> many1 classdecl

typespec :: Parser [String]
typespec = fmap (:[]) namerefP <|> do
    ns <- parensP (commalist typefree) <|> fmap (:[]) (lexP typefree)
    n <- namerefP
    return $ n : ns

optinfix :: Parser ()
optinfix = option () $ parensP infixP

types :: Parser [[String]]
types = lexS typesS >> many1 (typespec << (lexS "=" >> lexP typeP >> optinfix))

typedecl :: Parser [[String]]
typedecl = lexS typedeclS >> many1 (typespec << optinfix)

arity :: Parser [String]
arity = fmap (:[]) namerefP <|> do
    ns <- parensP $ commalist nameref
    n <- namerefP
    return $ n : ns

{-
arities :: Parser [[String]]
arities = lexS "arities" >> many1 (namerefP <:> (lexS "::" >> arity))
-}

data Const = Const String String

consts :: Parser [Const]
consts = lexS constsS >> many1 (bind Const nameP (lexS "::" >> lexP typeP
                                          << option () mixfix))

axmdecl :: Parser String
axmdecl = (nameP << option () attributes) << lexS ":"

prop :: Parser String
prop = reserved isaKeywords $ lexP term

data Axiom = Axiom String String

axiomsP :: Parser [Axiom]
axiomsP = many1 (bind Axiom axmdecl prop)

defs :: Parser [Axiom]
defs = lexS defsS >> option "" (parensP $ lexS "overloaded") >>
       axiomsP

axioms :: Parser [Axiom]
axioms = lexS axiomsS >> axiomsP

thmbind :: Parser String
thmbind = (nameP << option () attributes) <|> (attributes >> return "")

selection :: Parser ()
selection = forget . parensP . commalist $
  lexP nat >> option "" (lexS "-" >> option "" (lexP nat))

thmref :: Parser String
thmref = namerefP << (option () selection >> option () attributes)

thmrefs :: Parser [String]
thmrefs = many1 thmref

thmdef :: Parser String
thmdef = try $ thmbind << lexS "="

thmdecl :: Parser String
thmdecl = try $ thmbind << lexS ":"

theorems :: Parser ()
theorems = forget $ (lexS theoremsS <|> lexS lemmasS) >> option "" locale
    >> separatedBy (option "" thmdef >> thmrefs) (lexS andS)

proppat :: Parser ()
proppat = forget . parensP . many1 $ lexP term

data Goal = Goal String [String]

props :: Parser Goal
props = bind Goal (option "" thmdecl) $ many1 (prop << option () proppat)

goal :: Parser [Goal]
goal = fmap fst $ separatedBy props (lexS andS)

lemma :: Parser [Goal]
lemma = choice (map lexS [lemmaS, theoremS, corollaryS])
    >> option "" locale >> goal -- longgoal ignored

instanceP :: Parser String
instanceP =
    lexS instanceS >> namerefP << (lexS "::" << arity <|> lessOrEq << namerefP)

axclass :: Parser [String]
axclass = lexS axclassS >> classdecl << many (axmdecl >> prop)

mltext :: Parser String
mltext = lexS mlS >> lexP text

-- allow '.' sequences in unknown parts
anyP :: Parser String
anyP = lexP $ atom <|> many1 (char '.')

-- allow "and", etc. in unknown parts
unknown :: Parser ()
unknown = skipMany1 $ forget (reserved usedTopKeys anyP)
          <|> forget (recordP rec)
          <|> forget (parensP rec)
          <|> forget (bracketsP rec)
          <|> forget (bracesP rec)
          where rec = commalist $ unknown <|> forget anyP

data BodyElem = Axioms [Axiom]
              | Goals [Goal]
              | Consts [Const]
              | Ignored

ignore :: Functor f => f a -> f BodyElem
ignore = fmap $ const Ignored

theoryBody :: Parser [BodyElem]
theoryBody = many $
    ignore typedecl
    <|> ignore types
    <|> fmap Consts consts
    <|> fmap Axioms defs
    <|> ignore classes
    <|> ignore markupP
    <|> ignore theorems
    <|> fmap Axioms axioms
    <|> ignore instanceP
    <|> fmap Goals lemma
    <|> ignore axclass
    <|> ignore mltext
    <|> ignore (choice (map lexS ignoredKeys) >> skipMany unknown)
    <|> ignore unknown

-- | extracted theory information
data Body = Body
    { axiomsF :: Map.Map String String
    , goalsF :: Map.Map String [String]
    , constsF :: Map.Map String String
    } deriving Show

addAxiom :: Axiom -> Map.Map String String -> Map.Map String String
addAxiom (Axiom n a) m = Map.insert n a m

addGoal :: Goal -> Map.Map String [String] -> Map.Map String [String]
addGoal (Goal n a) m = Map.insert n a m

addConst :: Const -> Map.Map String String -> Map.Map String String
addConst (Const n a) m = Map.insert n a m

emptyBody :: Body
emptyBody = Body
    { axiomsF = Map.empty
    , goalsF = Map.empty
    , constsF = Map.empty
    }

concatBodyElems :: BodyElem -> Body -> Body
concatBodyElems x b = case x of
    Axioms l -> b { axiomsF = foldr addAxiom (axiomsF b) l }
    Goals l -> b { goalsF = foldr addGoal (goalsF b) l }
    Consts l -> b { constsF = foldr addConst (constsF b) l }
    Ignored -> b

parseTheory :: Parser (TheoryHead, Body)
parseTheory = bind (,)
    theoryHead (fmap (foldr concatBodyElems emptyBody) theoryBody)
    << lexS endS << eof

compatibleBodies :: Body -> Body -> [Diagnosis]
compatibleBodies b1 b2 =
    (map (\ (k, _) ->
          Diag Error ("added (or changed) axiom " ++ show k) nullRange)
    $ Map.toList $ Map.differenceWith eqN (axiomsF b2) $ axiomsF b1)
    ++ (map (\ (k, _) ->
             Diag Error ("added (or changed) constant " ++ show k) nullRange)
       $ Map.toList $ Map.differenceWith eqN (constsF b2) $ constsF b1)
    ++ (map (\ (k, _) ->
             Diag Error ("deleted (or changed) goal " ++ show k) nullRange)
       $ Map.toList $ Map.differenceWith eqN (goalsF b1) $ goalsF b2)
    where eqN a b = if a == b then Nothing else Just a
