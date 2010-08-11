{- |
Module      :  $Header$
Copyright   :  (c) DFKI GmbH, Uni Bremen 2004-2009
License     :  GPLv2 or higher

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
   deriving Show

parseMMiSSOntologyFile :: SourceName -> IO(WithError MMiSSOntology)
parseMMiSSOntologyFile s =
 do peFs <- parseFromFile ontoDoc s
    return $ case peFs of
      Right fs -> generateOntology (emptyMMiSSOntology "Test" AutoInsert) fs
      Left err -> hasError (show err)

-- | main function that collects fragments
ontoDoc :: GenParser Char st [Frag]
ontoDoc = do
  skip
  fs <- many (frag <?> "Fragment")
  eof
  return $ catMaybes fs

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
    in weither (const weOnto) (flip generateOntology fs) weOnto

-- | parse fragments
frag :: GenParser Char st (Maybe Frag)
frag = do
  char '\\'
  f <- fmap Just ontologyElement <|> (anyChar >> return Nothing)
  skip
  return f

skip :: GenParser Char st String
skip = many $ comment <|> noneOf "\\%"

comment :: GenParser Char st Char
comment = char '%' >> manyTill anyChar newline >> return '%'

braced :: GenParser Char st a -> GenParser Char st a
braced p = do
   b <- between (char '{') (char '}') p
   spaces
   return b

-- | maybe empty
value :: GenParser Char st String
value = fmap concat $ many
  $ many1 (noneOf "{}\\")
  <|> fmap (\ v -> '{' : v ++ "}") (braced value)
  <|> liftM2 (\ c1 c2 -> [c1, c2]) (char '\\') anyChar

ontologyElement :: GenParser Char st Frag
ontologyElement = declClassP <|> declObjectP <|> relationNameP
  <|> declRelationP <|> declBaseRelationP <|> declRelTypeP <|> objRelationP

nameDefl :: GenParser Char st (String, String)
nameDefl = do
  s1 <- braced idParser
  s2 <- braced value
  return (s1, s2)

cardP :: GenParser Char st (Maybe String)
cardP = do
  s <- braced idParser
  return $ if null s then Nothing else Just s

nameDeflOpt :: GenParser Char st (String, String, Maybe String)
nameDeflOpt = do
  (s1, s2) <- nameDefl
  s3 <- option "" $ braced idParser
  return (s1, s2, if null s3 then Nothing else Just s3)

nameSrcTgt :: GenParser Char st (String, String, String)
nameSrcTgt = do
  s1 <- braced idParser
  s2 <- braced idParser
  s3 <- braced idParser
  return (s1, s2, s3)

keyWord :: String -> GenParser Char st ()
keyWord s = do
  try (string s >> notFollowedBy alphaNum)
  spaces

declClassP :: GenParser Char st Frag
declClassP = do
  keyWord "DeclClass" <|> keyWord "Class"
  (name, deflTxt, supClassVal) <- nameDeflOpt
  return $ ClassDeclFrag $ ClassDecl name deflTxt supClassVal

declObjectP :: GenParser Char st Frag
declObjectP = do
  keyWord "DeclObject" <|> keyWord "Object"
  (name, deflTxt) <- nameDefl
  instOf <- braced idParser
  return $ ObjectDeclFrag $ ObjectDecl name deflTxt instOf

declRelationP :: GenParser Char st Frag
declRelationP = do
  keyWord "DeclRelation"
  cardVal <- cardP
  name <- braced idParser
  (deflTxt, srcCl, tgtCl) <- nameSrcTgt
  return $ RelationDeclFrag $ RelationDecl cardVal name deflTxt srcCl tgtCl

declBaseRelationP :: GenParser Char st Frag
declBaseRelationP = do
  keyWord "DeclRel" <|> keyWord "Relation"
  optional $ between (char '[') (char ']') idParser
  cardVal <- cardP
  (name, deflTxt, supRel) <- nameDeflOpt
  return $ BaseRelationDeclFrag $ BaseRelationDecl cardVal name deflTxt supRel

relationNameP :: GenParser Char st Frag
relationNameP = do
  keyWord "RelationName"
  name <- braced idParser
  deflTxt <- braced idParser
  return $ BaseRelationDeclFrag $ BaseRelationDecl Nothing name deflTxt Nothing

declRelTypeP :: GenParser Char st Frag
declRelTypeP = do
  keyWord "RelType"
  (name, src, tgt) <- nameSrcTgt
  return $ RelationTypeDeclFrag $ RelationTypeDecl name src tgt

objRelationP :: GenParser Char st Frag
objRelationP = do
  keyWord "Relate"
  (name, src, tgt) <- nameSrcTgt
  return $ ObjectLinkFrag $ ObjectLink src tgt name

idParser :: GenParser Char st String
idParser = many (noneOf "{}[]")
