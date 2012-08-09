{- |
Module      :  $Header$
Copyright   :  (c) C. Maeder DFKI GmbH
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

different pretty printing for the SHIP tool
-}

module OWL2.ShipSyntax where

import OWL2.AS

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
  | JoinedC JunctionType [Concept]
  | DisjointC Concept Concept
  | Quant (Either QuantifierType (CardinalityType, Integer)) Role Concept
  deriving (Show, Eq, Ord)

topC :: Concept
topC = CName "T"

data NotOrInverse = NotR | InvR deriving (Show, Eq, Ord)

data Role
  = RName String
  | NominalR String String
  | UnOp NotOrInverse Role
  | JoinedR JunctionType [Role]
  deriving (Show, Eq, Ord)

topR :: Role
topR = RName "TxT"

ppJunction :: JunctionType -> Doc
ppJunction t = text $ case t of
  UnionOf -> "+ "
  IntersectionOf -> "& "

pppConcept :: Bool -> JunctionType -> Concept -> Doc
pppConcept notLast t c = case c of
    Quant {} | notLast -> parens
    DisjointC {} -> parens
    JoinedC UnionOf _ | UnionOf /= t -> parens
    _ -> id
  $ ppConcept c

ppConcept :: Concept -> Doc
ppConcept co = case co of
  CName s -> (if co == topC then keyword else text) s
  NominalC s -> braces $ text s
  NotC c -> keyword "not" <> parens (ppConcept c)
  JoinedC t l -> case reverse l of
    [] -> ppConcept $ if t == IntersectionOf then topC else NotC topC
    f : r -> fsep . prepPunctuate (ppJunction t)
      . reverse $ pppConcept False t f : map (pppConcept True t) r
  DisjointC c1 c2 -> fsep
    [pppConcept True UnionOf c1, text "<+>", ppConcept c2]
  Quant q r c -> fsep [(case q of
    Left v -> keyword (showQuant v)
    Right (n, i) -> text (showCard n ++ show i)
    ) <+> ppRole r, dot <+> ppConcept c]

showQuant :: QuantifierType -> String
showQuant v = case v of
      AllValuesFrom -> "all"
      SomeValuesFrom -> "ex"

showCard :: CardinalityType -> String
showCard n = case n of
      MinCardinality -> ">="
      MaxCardinality -> "<="
      ExactCardinality -> "="

pppRole :: JunctionType -> Role -> Doc
pppRole t r = case r of
    JoinedR UnionOf _ | UnionOf /= t -> parens
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
    [] -> ppRole $ if t == IntersectionOf then topR else UnOp NotR topR
    _ -> fsep . prepPunctuate (ppJunction t) $ map (pppRole t) l

skip :: CharParser st ()
skip = forget $ many $ single (satisfy isSpace) <|> nestedComment "/*" "*/"
       <|> (string "%" <|> tryString "//") <++> many (noneOf "\n")

myLetter :: CharParser st Char
myLetter = satisfy $ \ c -> isAlphaNum c || elem c "_"

nominal :: CharParser st String
nominal = reserved ["all", "ex", "inv", "not"] (many1 myLetter) << skip

key :: String -> CharParser st ()
key s = forget $ try $ string s >> notFollowedBy myLetter

quant :: CharParser st QuantifierType
quant = choice $ map (\ a -> key (showQuant a) >> return a)
        [AllValuesFrom, SomeValuesFrom]

card :: CharParser st CardinalityType
card = choice $ map (\ a -> key (showCard a) >> return a)
       [MinCardinality, MaxCardinality, ExactCardinality]

quantOrCard :: CharParser st (Either QuantifierType (CardinalityType, Integer))
quantOrCard = fmap Left quant
  <|> do
  c <- card << skip
  i <- many1 digit
  return $ Right (c, read i)

skipChar :: Char -> CharParser st ()
skipChar c = char c >> skip

primConcept :: CharParser st Concept
primConcept = do
    q <- quantOrCard << skip
    r <- role
    skipChar '.'
    fmap (Quant q r) concept
  <|> ((key "not" <|> skipChar '~') >> skip >> fmap NotC primConcept)
  <|> braced (fmap NominalC nominal)
  <|> parent concept
  <|> fmap CName nominal

braced :: CharParser st a -> CharParser st a
braced p = skipChar '{' >> p << skipChar '}'

parent :: CharParser st a -> CharParser st a
parent p = skipChar '(' >> p << skipChar ')'

binP :: ([a] -> a) -> Char -> CharParser st a -> CharParser st a
binP f c p = do
  a <- p
  l <- many $ skipChar c >> p
  return $ if null l then a else f $ a : l

andConcept :: CharParser st Concept
andConcept = binP (JoinedC IntersectionOf) '&' primConcept

orConcept :: CharParser st Concept
orConcept = binP (JoinedC UnionOf) '+' andConcept

concept :: CharParser st Concept
concept = do
  c1 <- orConcept
  option c1 $ do
     tryString "<+>" >> skip
     c2 <- concept
     return $ DisjointC c1 c2

notOrInv :: CharParser st NotOrInverse
notOrInv = (char '~' >> return NotR)
  <|> (key "inv" >> return InvR)

primRole :: CharParser st Role
primRole = do
    o <- notOrInv << skip
    fmap (UnOp o) primRole
  <|>
    braced (parent $ liftM2 NominalR nominal $ skipChar ',' >> nominal)
  <|> parent role
  <|> fmap RName nominal

andRole :: CharParser st Role
andRole = binP (JoinedR IntersectionOf) '&' primRole

role :: CharParser st Role
role = binP (JoinedR UnionOf) '+' andRole

data EqOrLess = Eq | Less deriving (Show, Eq, Ord)

data RoleType = RoleType Role Concept Concept deriving (Show, Eq, Ord)

data Box
  = ConceptDecl String (Maybe (EqOrLess, Concept))
  | NominalCDecl String Concept
  | RoleDecl RoleType (Maybe (EqOrLess, RoleType))
  | NominalRDecl String String Role
  | RoleKind Character Role
  deriving (Show, Eq, Ord)

ppEqOrLess :: EqOrLess -> Doc
ppEqOrLess s = case s of
  Eq -> equals
  Less -> less

ppRoleType :: RoleType -> Doc
ppRoleType (RoleType r s t) =
  fsep [ppRole r, colon <+> ppConcept s, cross <+> ppConcept t]

ppBox :: Box -> Doc
ppBox b = case b of
  ConceptDecl s m -> text s <+> case m of
    Nothing -> empty
    Just (o, c) -> ppEqOrLess o <+> ppConcept c
  NominalCDecl n c -> text n <+> colon <+> ppConcept c
  RoleDecl r m -> fsep [ppRoleType r, case m of
    Nothing -> empty
    Just (o, t) -> ppEqOrLess o <+> ppRoleType t]
  NominalRDecl s t r -> parens (text s <> comma <+> text t)
    <+> colon <+> ppRole r
  RoleKind c s -> text (showCharacter c) <> parens (ppRole s)

showCharacter :: Character -> String
showCharacter c = case c of
    Functional -> "Func"
    InverseFunctional -> "Invfun"
    Reflexive -> "Refl"
    Irreflexive -> "Irref"
    Symmetric -> "Sym"
    Asymmetric -> "Asym"
    Antisymmetric -> "Dis"
    Transitive -> "Trans"

ppp :: (a -> Doc) -> CharParser () a -> String -> String
ppp pr pa s = case parse (pa << eof) "" s of
  Right a -> show $ pr a
  Left e -> show e
