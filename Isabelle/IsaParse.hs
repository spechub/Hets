{- |
Module      :  ./Isabelle/IsaParse.hs
Description :  parser for an Isabelle theory
Copyright   :  (c) C. Maeder and Uni Bremen 2005-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

parse the outer syntax of an Isabelle theory file. The syntax is taken from
 <http://isabelle.in.tum.de/dist/Isabelle/doc/isar-ref.pdf> for Isabelle2005
and is adjusted for Isabelle2011-1.
-}

module Isabelle.IsaParse
    ( parseTheory
    , Body (..)
    , TheoryHead (..)
    , SimpValue (..)
    , warnSimpAttr
    , compatibleBodies)
    where

import Isabelle.IsaConsts

import Common.DocUtils
import Common.Id
import Common.Lexer
import Common.Parsec
import Common.Result

import Text.ParserCombinators.Parsec

import Control.Monad

import Data.List
import qualified Data.HashMap.Lazy as Map
import Data.Hashable

-- | should be only ascii letters
latin :: Parser String
latin = single letter <?> "latin"

{- | this is a slash and an ident in angle brackets
(not just some greek letters spelled out). -}
greek :: Parser String
greek = string "\\<" <++>
         optionL (string "^") -- isup
         <++> ident <++> string ">" <?> "greek"

isaLetter :: Parser String
isaLetter = latin <|> greek

quasiletter :: Parser String
quasiletter = single (digit <|> char '\'' <|> char '_' ) <|> isaLetter
              <?> "quasiletter"

restident :: Parser String
restident = flat (many quasiletter)

ident :: Parser String
ident = isaLetter <++> restident

longident :: Parser String
longident = ident <++> flat (many $ char '.' <:> ident)

symident :: Parser String
symident = many1 (oneOf "!#$%&*+-/<=>?@^_|~" <?> "sym") <|> greek

strContent :: Char -> Parser String
strContent c = flat $ many (single (noneOf $ c : "\\")
                                 <|> char '\\' <:> single anyChar)

genString :: Char -> Parser String
genString c = enclosedBy (strContent c) $ char c

isaString :: Parser String
isaString = genString '"'

altString :: Parser String
altString = genString '`'

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

isaText :: Parser String
isaText = nameref <|> verbatim

typefree :: Parser String
typefree = char '\'' <:> ident

indexsuffix :: Parser String
indexsuffix = optionL (char '.' <:> nat)

typevar :: Parser String
typevar = tryString "?'" <++> ident <++> optionL (char '.' <:> nat)

typeP :: Parser Token
typeP = lexP typefree <|> lexP typevar <|> namerefP

var :: Parser String
var = try (char '?' <:> isaLetter) <++> restident <++> indexsuffix

term :: Parser String -- prop
term = var <|> nameref

isaSkip :: Parser ()
isaSkip = skipMany (many1 space <|> nestComment <?> "")

lexP :: Parser String -> Parser Token
lexP = liftM2 (\ p s -> Token s (Range [p])) getPos . (<< isaSkip)

lexS :: String -> Parser String
lexS = (<< isaSkip) . tryString

headerP :: Parser Token
headerP = lexS headerS >> lexP isaText

nameP :: Parser Token
nameP = lexP $ reserved isaKeywords name

namerefP :: Parser Token
namerefP = lexP $ reserved isaKeywords nameref

parname :: Parser Token
parname = lexS "(" >> lexP name << lexS ")"

-- | the theory part before and including the begin keyword with a context
data TheoryHead = TheoryHead
   { theoryname :: Token
   , imports :: [Token]
   , uses :: [Token]
   , context :: Maybe Token
   } deriving Eq

theoryHead :: Parser TheoryHead
theoryHead = do
    isaSkip
    optionMaybe headerP
    lexS theoryS
    th <- nameP
    is <- lexS importsS >> many1 nameP
    us <- optionL (lexS usesS >> many1 (nameP <|> parname))
    lexS beginS
    us2 <- optionL (lexS mlFileS >> many1 nameP)
    oc <- optionMaybe nameP
    return $ TheoryHead th is (us ++ us2) oc

commalist :: Parser a -> Parser [a]
commalist = flip sepBy1 (lexS ",")

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

locale :: Parser Token
locale = parensP $ lexS "in" >> nameP

markupP :: Parser Token
markupP = choice (map lexS markups) >> optional locale >> lexP isaText

infixP :: Parser ()
infixP = choice (map lexS ["infixl", "infixr", "infix"])
         >> optional (lexP isaString) << lexP nat

mixfixSuffix :: Parser ()
mixfixSuffix = lexP isaString
    >> optionL (bracketsP $ commalist $ lexP nat)
           >> optional (lexP nat)

structureL :: Parser ()
structureL = forget $ lexS structureS

genMixfix :: Bool -> Parser ()
genMixfix b = parensP $
    (if b then id else (<|> structureL)) $
        infixP <|> mixfixSuffix <|> (lexS "binder" >> mixfixSuffix)

mixfix :: Parser ()
mixfix = genMixfix False

-- ignores float that may start with "-"
atom :: Parser String
atom = var <|> typefree <|> typevar <|> nameref
        -- nameref covers nat and symident keywords

arg :: Parser [Token]
arg = fmap (: []) (lexP atom) <|> parensP args <|> bracketsP args

args :: Parser [Token]
args = flat $ many arg

-- | look for the simp attribute
attributes :: Parser [Bool]
attributes = bracketsP . optionL . commalist $
             liftM2 (\ n l -> null l && show n == simpS) namerefP args

lessOrEq :: Parser String
lessOrEq = lexS "<" <|> lexS "\\<subseteq>"

classdecl :: Parser [Token]
classdecl = do
    n <- nameP
    lessOrEq
    ns <- commalist namerefP
    return $ n : ns

classes :: Parser [[Token]]
classes = lexS classesS >> many1 classdecl

data Typespec = Typespec [(Token, Maybe Token)] Token

typespec :: Parser Typespec
typespec = typespecSort False

typespecSort :: Bool -> Parser Typespec
typespecSort b = fmap (Typespec []) namerefP
  <|> liftM2 Typespec
      (parensP (commalist typefreeP) <|> fmap (: []) typefreeP)
      namerefP
    where typefreeP = pair (lexP typefree)
              $ if b then optionMaybe $ lexS "::" >> namerefP
                else return Nothing

optinfix :: Parser ()
optinfix = optional $ parensP infixP

types :: Parser [Typespec]
types = lexS typesS >> many1 (typespec << (lexS "=" >> typeP >> optinfix))

typedecl :: Parser [Typespec]
typedecl = lexS typedeclS >> many1 (typespec << optinfix)

arity :: Parser ([Token], Token)
arity = fmap (\ n -> ([], n)) namerefP
  <|> pair (parensP $ commalist namerefP) namerefP

data Const = Const Token Token

typeSuffix :: Parser Token
typeSuffix = lexS "::" >> typeP

consts :: Parser [Const]
consts = lexS constsS >> many1 (liftM2 Const nameP (typeSuffix
                                          << optional mixfix))

vars :: Parser ()
vars = many1 nameP >> optional typeSuffix

andL :: Parser String
andL = lexS andS

structs :: Parser ()
structs = parensP $ structureL << sepBy1 vars andL

constdecl :: Parser [Const]
constdecl = do
    n <- nameP
    do t <- typeSuffix << optional mixfix
       return [Const n t]
     <|> (lexS "where" >> return [])
  <|> (mixfix >> return [])

constdef :: Parser ()
constdef = optional thmdecl << prop

constdefs :: Parser [[Const]]
constdefs = lexS constdefsS >> optional structs >>
            many1 (optionL constdecl << constdef)

-- | the sentence name plus simp attribute (if True)
data SenDecl = SenDecl Token Bool

emptySen :: SenDecl
emptySen = SenDecl (mkSimpleId "") False

optAttributes :: Parser Bool
optAttributes = fmap or $ optionL attributes

axmdecl :: Parser SenDecl
axmdecl = liftM2 SenDecl nameP optAttributes << lexS ":"

prop :: Parser Token
prop = lexP $ reserved isaKeywords term

data Axiom = Axiom SenDecl Token

axiomP :: Parser Axiom
axiomP = liftM2 Axiom axmdecl prop

axiomsP :: Parser [Axiom]
axiomsP = many1 axiomP

defs :: Parser [Axiom]
defs = lexS defsS >> optionL (parensP $ lexS "overloaded") >>
       axiomsP

axioms :: Parser [Axiom]
axioms = lexS axiomsS >> axiomsP

newAxioms :: Parser [Axiom]
newAxioms = lexS axiomatizationS >> lexS whereS
   >> sepBy axiomP (lexS andS)

thmbind :: Parser SenDecl
thmbind = liftM2 SenDecl nameP optAttributes
          <|> (attributes >> return emptySen)

selection :: Parser [()]
selection = parensP . commalist $
  natP >> optional (lexS "-" >> optional natP)
  where natP = lexP nat

thmref :: Parser Token
thmref = ((namerefP << optional selection) <|> lexP altString)
          << optionL attributes

thmrefs :: Parser [Token]
thmrefs = flat
  $ many1 (single thmref <|> fmap (const []) (bracketsP attributes))

thmdef :: Parser SenDecl
thmdef = try $ thmbind << lexS "="

thmdecl :: Parser SenDecl
thmdecl = try $ thmbind << lexS ":"

theorems :: Parser [[Token]]
theorems = (lexS theoremsS <|> lexS lemmasS)
    >> optional locale
    >> sepBy1 (optional thmdef >> thmrefs) andL

proppat :: Parser [Token]
proppat = parensP . many1 $ lexS "is" >> lexP term

data Goal = Goal SenDecl [Token]

props :: Parser Goal
props = liftM2 Goal (option emptySen thmdecl)
        $ many1 (prop << optional proppat)

goal :: Parser [Goal]
goal = sepBy1 props andL

lemma :: Parser [Goal]
lemma = choice (map lexS [lemmaS, theoremS, corollaryS])
    >> optional locale >> goal -- longgoal ignored

instanceP :: Parser Token
instanceP =
    lexS instanceS >> namerefP <<
    ((lexS "::" << arity) <|> (lessOrEq << namerefP))

axclass :: Parser [Token]
axclass = lexS axclassS >> classdecl << many (axmdecl >> prop)

mltext :: Parser Token
mltext = lexS mlS >> lexP isaText

cons :: Parser [Token]
cons = nameP <:> many typeP << optional mixfix

data Dtspec = Dtspec Typespec [[Token]]

dtspec :: Parser Dtspec
dtspec = do
    optional $ try parname
    t <- typespec
    optinfix
    lexS "="
    cs <- sepBy1 cons $ lexS "|"
    return $ Dtspec t cs

datatype :: Parser [Dtspec]
datatype = lexS datatypeS >> sepBy1 dtspec andL

-- allow '.' sequences or ":" in unknown parts
anyP :: Parser String
anyP = atom <|> many1 (char '.') <|> string ":"

-- allow "and", etc. in unknown parts
unknown :: Parser ()
unknown = skipMany1 $ (lexP (reserved usedTopKeys anyP) >> return [()])
          <|> recordP cus
          <|> parensP cus
          <|> bracketsP cus
          <|> bracesP cus
          where cus = commalist (unknown <|> forget (lexP anyP))

data BodyElem = Axioms [Axiom]
              | Goals [Goal]
              | Consts [Const]
              | Datatype [Dtspec]
              | Ignored

discard :: Functor f => f a -> f BodyElem
discard = fmap $ const Ignored

theoryBody :: Parser [BodyElem]
theoryBody = many $
    discard typedecl
    <|> discard types
    <|> fmap Datatype datatype
    <|> fmap Consts consts
    <|> fmap (Consts . concat) constdefs
    <|> fmap Axioms defs
    <|> discard classes
    <|> discard markupP
    <|> discard theorems
    <|> fmap Axioms axioms
    <|> fmap Axioms newAxioms
    <|> discard instanceP
    <|> fmap Goals lemma
    <|> discard axclass
    <|> discard mltext
    <|> discard (choice (map lexS ignoredKeys) >> skipMany unknown)
    <|> discard unknown

data SimpValue a = SimpValue { hasSimp :: Bool, simpValue :: a }

instance Show a => Show (SimpValue a) where
    show (SimpValue _ a) = show a

instance Pretty a => Pretty (SimpValue a) where
    pretty (SimpValue _ a) = pretty a

instance Eq a => Eq (SimpValue a) where
    SimpValue _ a == SimpValue _ b = a == b

-- | The axioms, goals, constants and data types of a theory
data Body = Body
    { axiomsF :: Map.HashMap Token (SimpValue Token)
    , goalsF :: Map.HashMap Token (SimpValue [Token])
    , constsF :: Map.HashMap Token Token
    , datatypesF :: Map.HashMap Token ([Token], [[Token]])
    } deriving Show

addAxiom :: Axiom -> Map.HashMap Token (SimpValue Token)
         -> Map.HashMap Token (SimpValue Token)
addAxiom (Axiom (SenDecl n b) a) = Map.insert n (SimpValue b a)

addGoal :: Goal -> Map.HashMap Token (SimpValue [Token])
        -> Map.HashMap Token (SimpValue [Token])
addGoal (Goal (SenDecl n b) a) = Map.insert n (SimpValue b a)

addConst :: Const -> Map.HashMap Token Token -> Map.HashMap Token Token
addConst (Const n a) = Map.insert n a

addDatatype :: Dtspec -> Map.HashMap Token ([Token], [[Token]])
            -> Map.HashMap Token ([Token], [[Token]])
addDatatype (Dtspec (Typespec ps n) a) = Map.insert n (map fst ps, a)

emptyBody :: Body
emptyBody = Body
    { axiomsF = Map.empty
    , goalsF = Map.empty
    , constsF = Map.empty
    , datatypesF = Map.empty
    }

concatBodyElems :: BodyElem -> Body -> Body
concatBodyElems x b = case x of
    Axioms l -> b { axiomsF = foldr addAxiom (axiomsF b) l }
    Goals l -> b { goalsF = foldr addGoal (goalsF b) l }
    Consts l -> b { constsF = foldr addConst (constsF b) l }
    Datatype l -> b { datatypesF = foldr addDatatype (datatypesF b) l }
    Ignored -> b

-- | parses a complete isabelle theory file, but skips i.e. proofs
parseTheory :: Parser (TheoryHead, Body)
parseTheory = pair
    theoryHead (fmap (foldr concatBodyElems emptyBody) theoryBody)
    << lexS endS << eof

{- | Check that constants and data type are unchanged and that no axioms
was added and no theorem deleted. -}
compatibleBodies :: Body -> Body -> [Diagnosis]
compatibleBodies b1 b2 =
    diffMap "axiom" LT (axiomsF b2) (axiomsF b1)
    ++ diffMap "constant" EQ (constsF b2) (constsF b1)
    ++ diffMap "datatype" EQ (datatypesF b2) (datatypesF b1)
    ++ diffMap "goal" GT (goalsF b2) (goalsF b1)

warnSimpAttr :: Body -> [Diagnosis]
warnSimpAttr =
    map ( \ a -> Diag Warning
         ("use 'declare " ++ tokStr a
          ++ " [simp]' for proper Isabelle proof details") $ tokPos a)
        . Map.keys . Map.filter hasSimp . axiomsF

diffMap :: (Ord a, Pretty a, GetRange a, Hashable a, Eq b, Show b)
          => String -> Ordering -> Map.HashMap a b -> Map.HashMap a b -> [Diagnosis]
diffMap msg o m1 m2 =
    let k1 = Map.keys m1
        k2 = Map.keys m2
        kd21 = k2 \\ k1
        kd12 = k1 \\ k2
    in if k1 == k2 then
    map ( \ (k, a) -> mkDiag Error
          (msg ++ " entry " ++ show a ++ " was changed for: ") k)
    $ Map.toList $
    Map.differenceWith ( \ a b -> if a == b then Nothing else
                                      Just a) m1 m2
    else let b = case o of
                   EQ -> null kd21
                   GT -> False
                   LT -> True
             kd = if b then kd12 else kd21
               in map (mkDiag Error
                      $ msg ++ " entry illegally " ++
                         if b then "added" else "deleted") kd
