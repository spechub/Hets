{- |
Module      :  $Header$
Copyright   :  (c) DFKI GmbH, Uni Bremen 2004-2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Taxonomy.MMiSSOntology)

a function that takes a filename as argument and parses that file for
mmisslatex ontology commands. If it succeeds gives back the whole ontology
structure along with a list of warnings (if class, object or relation
declarations are missing).
-}

module Taxonomy.OntoParser
  ( parseMMiSSOntologyFile
  , ClassDecl (..)
  , ObjectDecl (..)
  , RelationDecl (..)
  , BaseRelationDecl (..)
  , RelationTypeDecl (..)
  , ObjectLink (..)
  , Frag (..)
  ) where

import Control.Monad
import Data.Maybe

import Taxonomy.MMiSSOntology
import Text.ParserCombinators.Parsec

type Other = String

data ClassDecl = ClassDecl {
  className :: String,
  classText :: String,
  super :: Maybe String
} deriving Show

data ObjectDecl = ObjectDecl {
  objName :: String,
  objectText :: String,
  instanceOf :: String
} deriving Show

data RelationDecl = RelationDecl {
  multiplicities :: Maybe String,
  relName :: String,
  relationText :: String,
  source :: String,
  target :: String
} deriving Show

data BaseRelationDecl = BaseRelationDecl {
  baseMultiplicities :: Maybe String,
  baseRelName :: String,
  baseRelationText :: String,
  superRel :: Maybe String
} deriving Show

data RelationTypeDecl = RelationTypeDecl {
  nameOfRel :: String,
  nameOfSource :: String,
  nameOfTarget :: String
} deriving Show

data ObjectLink = ObjectLink {
  sourceObj :: String,
  targetObj :: String,
  linkRelation :: String
} deriving Show

data Frag =
   ClassDeclFrag ClassDecl
 | ObjectDeclFrag ObjectDecl
 | RelationDeclFrag RelationDecl
 | BaseRelationDeclFrag BaseRelationDecl
 | RelationTypeDeclFrag RelationTypeDecl
 | ObjectLinkFrag ObjectLink
 | OtherFrag Other deriving Show

parseMMiSSOntologyFile :: SourceName -> IO(WithError MMiSSOntology)
parseMMiSSOntologyFile s =
 do peFs <- parseFromFile ontoDoc s
    return $ case peFs of
      Right fs -> generateOntology (emptyMMiSSOntology "Test" AutoInsert) fs
      Left err -> hasError (show err)

-- | main function that collects fragments
ontoDoc :: GenParser Char st [Frag]
ontoDoc = do
  fs <- many (frag <?> "Fragment")
  eof
  return fs

generateOntology :: MMiSSOntology -> [Frag] -> WithError MMiSSOntology
generateOntology onto frs = case frs of
  [] -> hasValue onto
  f : fs -> let
    weOnto = case f of
      ClassDeclFrag (ClassDecl name deflTxt sup) ->
          insertClass onto name deflTxt (maybeToList sup) Nothing
      ObjectDeclFrag (ObjectDecl name deflTxt instOf) ->
          insertObject onto name deflTxt instOf
      RelationDeclFrag (RelationDecl cardValue name deflTxt srcCl tgtCl) ->
           let wOnto = insertBaseRelation onto name deflTxt Nothing cardValue
           in weither (const wOnto)
                      ( \ o -> insertRelationType o name srcCl tgtCl)
                      wOnto
      BaseRelationDeclFrag (BaseRelationDecl cardValue name deflTxt supRel) ->
          insertBaseRelation onto name deflTxt supRel cardValue
      RelationTypeDeclFrag (RelationTypeDecl name src tgt) ->
          insertRelationType onto name src tgt
      ObjectLinkFrag (ObjectLink src tgt name) ->
          insertLink onto src tgt name
      _ -> hasValue onto
    in weither (const weOnto) (flip generateOntology fs) weOnto

-- | parse fragments
frag :: GenParser Char st Frag
frag = comment
  <|> do
    backslash
    ontologyElement <|> escapedChar
  <|> other

backslash :: GenParser Char st Char
backslash = char '\\'

escapedChar :: GenParser Char st Frag
escapedChar = do
  c <- anyChar
  return (OtherFrag [c])

other :: GenParser Char st Frag
other = fmap OtherFrag $ many1 (noneOf "\\%")

comment :: GenParser Char st Frag
comment = char '%' >> manyTill anyChar newline >> return (OtherFrag "")

braced :: GenParser Char st a -> GenParser Char st a
braced = between (char '{') (char '}')

-- | maybe empty
value :: GenParser Char st String
value = fmap concat $ many
  $ many1 (noneOf "{}\\")
  <|> fmap (\ v -> '{' : v ++ "}") (braced value)
  <|> liftM2 (\ c1 c2 -> [c1, c2]) (char '\\') anyChar

ontologyElement :: GenParser Char st Frag
ontologyElement = declClassP <|> declObjectP <|> declRelationP
  <|> declBaseRelationP <|> declRelTypeP <|> objRelationP

parseThree :: Bool -> GenParser Char st (String, String, String)
parseThree b = do
  s1 <- braced idParser
  spaces
  s2 <- braced $ if b then value else idParser
  spaces
  s3 <- braced idParser
  return (s1, s2, s3)

nameDeflClass :: GenParser Char st (String, String, String)
nameDeflClass = parseThree True

nameDeflOther :: GenParser Char st (String, String, String)
nameDeflOther = parseThree False

nameSrcTgt :: GenParser Char st (String, String, String)
nameSrcTgt = parseThree False

declClassP :: GenParser Char st Frag
declClassP = do
  try (string "DeclClass") <|> try (string "Class")
  (name, deflTxt, superClass) <- nameDeflClass
  let supClassVal = if superClass == "" then Nothing else Just superClass
  return $ ClassDeclFrag $ ClassDecl name deflTxt supClassVal

declObjectP :: GenParser Char st Frag
declObjectP = do
  try (string "DeclObject") <|> try (string "Object")
  (name, deflTxt, instOf) <- nameDeflClass
  return $ ObjectDeclFrag $ ObjectDecl name deflTxt instOf

declRelationP :: GenParser Char st Frag
declRelationP = do
  try (string "DeclRelation")
  card <- braced idParser
  let cardVal = if card == "" then Nothing else Just card
  (name, deflTxt, srcCl) <- nameDeflOther
  spaces
  tgtCl <- braced idParser
  return $ RelationDeclFrag $ RelationDecl cardVal name deflTxt srcCl tgtCl

declBaseRelationP :: GenParser Char st Frag
declBaseRelationP = do
  try (string "DeclRel") <|> try (string "Relation")
  card <- braced idParser
  let cardVal = if card == "" then Nothing else Just card
  (name, deflTxt, sup) <- nameDeflOther
  let supRel = if sup == "" then Nothing else Just sup
  return $ BaseRelationDeclFrag $ BaseRelationDecl cardVal name deflTxt supRel

declRelTypeP :: GenParser Char st Frag
declRelTypeP = do
  try (string "RelType")
  (name, src, tgt) <- nameSrcTgt
  return $ RelationTypeDeclFrag $ RelationTypeDecl name src tgt

objRelationP :: GenParser Char st Frag
objRelationP = do
  try (string "Relate")
  (name, src, tgt) <- nameSrcTgt
  return $ ObjectLinkFrag $ ObjectLink src tgt name

idParser :: GenParser Char st String
idParser = many (noneOf "{}[]")
