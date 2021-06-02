{- |
Module      :  ./OWL2/ShipSyntax.hs
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

different pretty printing for the SHIP tool
-}

module OWL2.ShipSyntax where

import qualified OWL2.AS as AS

import Common.Doc
import Common.DocUtils
import Common.Parsec

import Control.Monad

import Data.Char

import Text.ParserCombinators.Parsec

data Concept
  = CName String
  | NominalC String
  | NotC Concept
  | JoinedC (Maybe AS.JunctionType) [Concept] -- Nothing denotes disjoint union
  | Quant (Either AS.QuantifierType (AS.CardinalityType, Int)) Role Concept
  deriving (Show, Eq, Ord)

topC :: Concept
topC = CName "T"

data NotOrInverse = NotR | InvR deriving (Show, Eq, Ord)

data Role
  = RName String
  | NominalR String String
  | UnOp NotOrInverse Role
  | JoinedR (Maybe AS.JunctionType) [Role] -- Nothing denotes composition!
  deriving (Show, Eq, Ord)

topR :: Role
topR = RName "TxT"

botR :: Role
botR = UnOp NotR topR

ppJunction :: Bool -> Maybe AS.JunctionType -> Doc
ppJunction c mt = text $ case mt of
  Just t -> case t of
    AS.UnionOf -> "+ "
    AS.IntersectionOf -> "& "
  Nothing -> if c then "<+> " else ". "

pppNegConcept :: Concept -> Doc
pppNegConcept c = case c of
    JoinedC {} -> parens
    _ -> id
  $ ppConcept c

pppConcept :: Bool -> Maybe AS.JunctionType -> Concept -> Doc
pppConcept notLast mt c = case c of
    Quant {} | notLast -> parens
    JoinedC mti _
      | mti /= mt && maybe True (const $ maybe False (/= AS.UnionOf) mt) mti
        -> parens
    _ -> id
  $ ppConcept c

ppConcept :: Concept -> Doc
ppConcept co = case co of
  CName s -> (if co == topC then keyword else text) s
  NominalC s -> braces $ text s
  NotC c -> text "~" <> pppNegConcept c
  JoinedC t l -> case reverse l of
    [] -> ppConcept $ if t == Just AS.IntersectionOf then topC else NotC topC
    f : r -> fsep . prepPunctuate (ppJunction True t)
      . reverse $ pppConcept False t f : map (pppConcept True t) r
  Quant q r c -> fsep [(case q of
    Left v -> keyword (showQuant v)
    Right (n, i) -> text (showCard n) <+> text (show i)
    ) <+> ppRole r, dot <+> ppConcept c]

showQuant :: AS.QuantifierType -> String
showQuant v = case v of
      AS.AllValuesFrom -> "all"
      AS.SomeValuesFrom -> "ex"

showCard :: AS.CardinalityType -> String
showCard n = case n of
      AS.MinCardinality -> ">="
      AS.MaxCardinality -> "<="
      AS.ExactCardinality -> "="

showSame :: AS.SameOrDifferent -> String
showSame s = case s of
  AS.Same -> "=="
  AS.Different -> "!="

pppRole :: Maybe AS.JunctionType -> Role -> Doc
pppRole mt r = case r of
    JoinedR (Just ti) _
      | maybe True (\ to -> ti /= to && ti == AS.UnionOf) mt
        -> parens
    _ -> id
  $ ppRole r

ppRole :: Role -> Doc
ppRole ro = case ro of
  RName s -> (if ro == topR then keyword else text) s
  NominalR s t -> braces $ parens $ text s <> comma <+> text t
  UnOp o r -> (case o of
    NotR -> text "~"
    InvR -> keyword "inv") <> (case r of
      JoinedR {} -> parens
      _ | o == InvR -> parens
      _ -> id) (ppRole r)
  JoinedR t l -> case l of
    [] -> ppRole $ if t /= Just AS.UnionOf then topR else botR
    _ -> fsep . prepPunctuate (ppJunction False t) $ map (pppRole t) l

skip :: CharParser st ()
skip = forget $ many $ single (satisfy isSpace) <|> nestedComment "/*" "*/"
       <|> tryString "//" <++> many (noneOf "\n")

myLetter :: CharParser st Char
myLetter = satisfy $ \ c -> isAlphaNum c || elem c "_"

nominal :: CharParser st String
nominal = reserved
  ["_", "all", "ex", "inv", "not", "if", "effect", "causes", "cond", "exec"]
  (many1 myLetter) << skip

key :: String -> CharParser st ()
key s = forget $ try $ string s >> notFollowedBy myLetter

skipKey :: String -> CharParser st ()
skipKey s = key s << skip

quant :: CharParser st AS.QuantifierType
quant = choice $ map (\ a -> key (showQuant a) >> return a)
        [AS.AllValuesFrom, AS.SomeValuesFrom]

card :: CharParser st AS.CardinalityType
card = choice $ map (\ a -> tryString (showCard a) >> return a)
       [AS.MinCardinality, AS.MaxCardinality, AS.ExactCardinality]

quantOrCard :: CharParser st (Either AS.QuantifierType (AS.CardinalityType, Int))
quantOrCard = fmap Left quant
  <|> do
  c <- card << skip
  i <- many1 digit
  return $ Right (c, read i)

skipChar :: Char -> CharParser st ()
skipChar c = char c >> skip

commaP, colonP, equalP, bulletP :: CharParser st ()
commaP = skipChar ','
colonP = skipChar ':'
equalP = skipChar '='
bulletP = skipChar '.'

primConcept :: CharParser st Concept
primConcept = do
    q <- quantOrCard << skip
    r <- primRole
    bulletP
    fmap (Quant q r) concept
  <|> ((key "not" <|> skipChar '~') >> skip >> fmap NotC primConcept)
  <|> braced (fmap NominalC nominal) -- allow more nominals
  <|> parent concept
  <|> fmap CName nominal

braced :: CharParser st a -> CharParser st a
braced p = skipChar '{' >> p << skipChar '}'

parent :: CharParser st a -> CharParser st a
parent p = skipChar '(' >> p << skipChar ')'

binPP :: ([a] -> a) -> CharParser st sep -> CharParser st a -> CharParser st a
binPP f sp p = do
  a <- p
  l <- many $ sp >> p
  return $ if null l then a else f $ a : l

binP :: ([a] -> a) -> String -> CharParser st a -> CharParser st a
binP f s = binPP f $ tryString s >> skip

binC :: ([a] -> a) -> Char -> CharParser st a -> CharParser st a
binC f c = binPP f $ skipChar c

andConcept :: CharParser st Concept
andConcept = binC (JoinedC $ Just AS.IntersectionOf) '&' primConcept

plus :: CharParser st ()
plus = try $ char '+' >> notFollowedBy (char '>') >> skip

orConcept :: CharParser st Concept
orConcept = binPP (JoinedC $ Just AS.UnionOf) plus andConcept

concept :: CharParser st Concept
concept = binP (JoinedC Nothing) "<+>" orConcept

notOrInv :: CharParser st NotOrInverse
notOrInv = (char '~' >> return NotR)
  <|> (key "inv" >> return InvR)

nomPair :: (String -> String -> a) -> CharParser st a
nomPair f = parent $ liftM2 f nominal $ commaP >> nominal

primRole :: CharParser st Role
primRole = do
    o <- notOrInv << skip
    fmap (UnOp o) primRole
  <|> braced (nomPair NominalR)
  <|> parent role
  <|> fmap RName nominal

compRole :: CharParser st Role
compRole = binC (JoinedR Nothing) '.' primRole

andRole :: CharParser st Role
andRole = binC (JoinedR $ Just AS.IntersectionOf) '&' compRole

role :: CharParser st Role
role = binPP (JoinedR $ Just AS.UnionOf) plus andRole

data EqOrLess = Eq | Less deriving (Show, Eq, Ord)

data RoleType = RoleType Concept Concept deriving (Show, Eq, Ord)

-- a missing rhs may be modelled as "< T" or by no constructors
data ConceptRhs
  = ADTCons [TBoxCons]
  | ConceptRel EqOrLess Concept
  deriving (Show, Eq, Ord)

data TBoxCons = TBoxCons Concept [(Role, Concept)]
  deriving (Show, Eq, Ord)

data TBox
  = ConceptDecl Concept ConceptRhs
  | DisjointCs [Concept]
  deriving (Show, Eq, Ord)

data RBox
  = RoleDecl Role RoleType
  | RoleRel Role EqOrLess Role
  | RoleProp AS.Character Role
  deriving (Show, Eq, Ord)

-- | assertions
data ABox
  = AConcept String Concept
  | ARole String String Role
  | AIndividual String AS.SameOrDifferent String
  deriving (Show, Eq, Ord)

data Box = Box [TBox] [RBox] [ABox]
  deriving (Show, Eq, Ord)

ppEqOrLess :: EqOrLess -> Doc
ppEqOrLess s = case s of
  Eq -> equals
  Less -> less

ppRoleType :: RoleType -> Doc
ppRoleType (RoleType s t) =
  fsep [colon <+> ppConcept s, cross <+> ppConcept t]

ppConceptRhs :: ConceptRhs -> Doc
ppConceptRhs rhs = case rhs of
  ADTCons cs -> if null cs then empty else
     text "::=" <+> vcat (prepPunctuate (text "| ") $ map ppTBoxCons cs)
  ConceptRel o c -> ppEqOrLess o <+> ppConcept c

ppTBoxCons :: TBoxCons -> Doc
ppTBoxCons (TBoxCons c sels) =
  ppConcept c <> if null sels then empty else
    parens . sepByCommas $ map
      (\ (r, a) -> ppRole r <+> colon <+> ppConcept a) sels

ppTBox :: TBox -> Doc
ppTBox b = case b of
  ConceptDecl d m -> ppConcept d <+> ppConceptRhs m
  DisjointCs cs -> keyword "Disjoint" <> parens (sepByCommas $ map ppConcept cs)

ppRBox :: RBox -> Doc
ppRBox b = case b of
  RoleDecl r t -> fsep [ppRole r, ppRoleType t]
  RoleRel r o t -> fsep [ppRole r, ppEqOrLess o <+> ppRole t]
  RoleProp c s -> keyword (showCharacter c) <> parens (ppRole s)

ppABox :: ABox -> Doc
ppABox b = case b of
  AConcept n c -> text n <> colon <> ppConcept c
  ARole s t r -> parens (text s <> comma <+> text t)
    <> colon <> ppRole r
  AIndividual s c t -> text s <> text (showSame c) <> text t

ppBox :: Box -> Doc
ppBox (Box ts rs as) = let ppM c = keyword $ '%' : c : "BOX" in
  vcat $ ppM 'T' : map ppTBox ts ++ ppM 'R' : map ppRBox rs
           ++ ppM 'A' : map ppABox as

showCharacter :: AS.Character -> String
showCharacter c = case c of
    AS.Functional -> "Func"
    AS.InverseFunctional -> "FuncInv"
    AS.Reflexive -> "Ref"
    AS.Irreflexive -> "Irref"
    AS.Symmetric -> "Sym"
    AS.Asymmetric -> "Asym"
    AS.Antisymmetric -> "Dis"
    AS.Transitive -> "Trans"

character :: CharParser st AS.Character
character = choice $ map (\ a -> key (showCharacter a) >> return a)
  [minBound .. maxBound]

eqOrLess :: CharParser st EqOrLess
eqOrLess = (equalP >> return Eq) <|> (skipChar '<' >> return Less)

tbox :: CharParser st TBox
tbox = (key "Disjoint" >> fmap DisjointCs
        (parent $ concept <:> many (commaP >> concept)))
  <|> try (liftM2 ConceptDecl concept
    (liftM2 ConceptRel eqOrLess concept
     <|> fmap ADTCons
     ((tryString "::=" >> skip >> sepBy tboxCons (skipChar '|'))
      <|> (char ':' >> pzero)
      <|> (string "==" >> pzero)
      <|> (string "!=" >> pzero)
      <|> return [])))

tboxCons :: CharParser st TBoxCons
tboxCons = liftM2 TBoxCons concept
  . optionL . parent . flip sepBy commaP
  . pair role $ colonP >> concept

rbox :: CharParser st RBox
rbox = liftM2 RoleProp character (parent role)
  <|> try (do
    r <- role
    liftM2 (RoleRel r) eqOrLess role
      <|> fmap (RoleDecl r) (liftM2 RoleType
        (colonP >> concept)
        $ skipChar '*' >> concept)) -- added try to recognize abox

abox :: CharParser st ABox
abox = liftM2 ($) (nomPair ARole) (colonP >> role)
  <|> do
    n <- nominal
    fmap (AConcept n) (colonP >> concept)
      <|> liftM2 (AIndividual n) (pSame << skip) nominal

pSame :: CharParser st AS.SameOrDifferent
pSame = choice $ map (\ a -> tryString (showSame a) >> return a)
        [AS.Same, AS.Different]

box :: CharParser st Box
box = do
  forget $ many imprts
  optional $ skipKey "%TBOX"
  ts <- many tbox
  optional $ skipKey "%RBOX"
  rs <- many rbox
  optional $ skipKey "%ABOX"
  as <- many abox
  return $ Box ts rs as

imprts :: CharParser st ()
imprts = skipKey "import" << many1 (myLetter <|> char '.') << skip
  << optional rename

rename :: CharParser st ()
rename = do
  skipKey "with"
  optional $ skipKey "concepts" << nmap
  optional $ skipKey "roles" << nmap
  optional $ skipKey "individuals" << nmap
  return ()

nmap :: GenParser Char st [()]
nmap = sepBy1 (nominal >> skipKey "as" << nominal) commaP

ppp :: (a -> Doc) -> CharParser () a -> String -> String
ppp pr pa s = case parse (skip >> pa << eof) "" s of
  Right a -> show $ pr a
  Left e -> show e
