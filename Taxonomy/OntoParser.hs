{-# OPTIONS_GHC -w #-}
{-- OntoParser stellt eine Funktion zum Parsen von mmisslatex-Ontologiebefehlen
    in LaTeX-Files (oder anderen Textfiles) zur Verfügung.
--}

module Taxonomy.OntoParser (

  parseMMiSSOntologyFile  -- SourceName -> IO(WithError (MMiSSOntology, [String]))
  {-- Main function that takes a filename as argument and parses that file
      for mmisslatex ontology commands. If it succeeds gives back the whole ontology structure
      along with a list of warnings (if class, object or relation declarations are missing).
  --}

)

where

import Data.Maybe

import Taxonomy.MMiSSOntology
import Text.ParserCombinators.Parsec

type Other = String

data ClassDecl = ClassDecl {
  className :: String,
  classText :: String,
  super :: Maybe String
} deriving(Show)

data ObjectDecl = ObjectDecl {
  objName :: String,
  objectText :: String,
  instanceOf :: String
} deriving(Show)

data RelationDecl = RelationDecl {
  multiplicities :: Maybe String,
  relName :: String,
  relationText :: String,
  source :: String,
  target :: String
} deriving(Show)

data BaseRelationDecl = BaseRelationDecl {
  baseMultiplicities :: Maybe String,
  baseRelName :: String,
  baseRelationText :: String,
  superRel :: Maybe String
} deriving(Show)

data RelationTypeDecl = RelationTypeDecl {
  nameOfRel :: String,
  nameOfSource :: String,
  nameOfTarget :: String
} deriving(Show)

data ObjectLink = ObjectLink {
  sourceObj :: String,
  targetObj :: String,
  linkRelation :: String
} deriving(Show)

data Frag =
   ClassDeclFrag ClassDecl
 | ObjectDeclFrag ObjectDecl
 | RelationDeclFrag RelationDecl
 | BaseRelationDeclFrag BaseRelationDecl
 | RelationTypeDeclFrag RelationTypeDecl
 | ObjectLinkFrag ObjectLink
 | OtherFrag Other deriving(Show)


parseMMiSSOntologyFile :: SourceName -> IO(WithError MMiSSOntology)
parseMMiSSOntologyFile s =
 do peFs <- parseFromFile (ontoDoc [] []) s
    case peFs of
      Right fs -> return (generateOntology (emptyMMiSSOntology "Test" AutoInsert) fs)
      Left err -> return (hasError (show err))

{-- ontoDoc ist die Hauptparser-Funktion. Jedes erkannte Fragment wird direkt verarbeitet und in
    Ontologie-Datenstruktur aufgenommen. Relationen werden so beim Parsen aufgesammelt und dem
    Parser für Objekt-Links zur Verfügung gestellt.
--}

ontoDoc :: [String] -> [Frag] -> GenParser Char st [Frag]
ontoDoc rels fs =
  do eof
     return(fs)
  <|> do f <- (frag rels) <?> "Fragment"
         ontoDoc rels (fs ++ [f])


generateOntology :: MMiSSOntology -> [Frag] -> WithError (MMiSSOntology)

generateOntology onto [] = hasValue(onto)

generateOntology onto (f:fs) =
  let weOnto = case f of
                ClassDeclFrag (ClassDecl name defaultText super) ->
                  insertClass onto name defaultText (maybeToList super) Nothing

                ObjectDeclFrag (ObjectDecl name defaultText instanceOf) ->
                  insertObject onto name defaultText instanceOf

                RelationDeclFrag (RelationDecl cardValue name defaultText sourceClass targetClass) ->
                  let weOnto = insertBaseRelation onto name defaultText Nothing cardValue
                  in weither (const weOnto)
                      ( \ o -> insertRelationType o name sourceClass targetClass)
                      weOnto

                BaseRelationDeclFrag (BaseRelationDecl cardValue name defaultText superRel) ->
                  insertBaseRelation onto name defaultText superRel cardValue

                RelationTypeDeclFrag (RelationTypeDecl name source target) ->
                  insertRelationType onto name source target

                ObjectLinkFrag (ObjectLink source target name) ->
                  insertLink onto source target name

                otherwise -> hasValue(onto)

  in weither (const weOnto) (flip generateOntology fs) weOnto

-- frag ist der eigentliche Parser für Fragmente. Als ersten Parameter bekommt er eine Liste der
-- bisher beim Parsen aufgesammelten Relationsnamen übergeben, damit der Link-Parser (aufgerufen vom
-- ontologyElement-Parser) die Makros, die einem Relationsnamen entsprechen als Links erkennen kann.

frag :: [String] -> GenParser Char st Frag
frag rels =
       comment
       <|> do backslash
              (ontologyElement rels) <|> escapedChar <|> return(OtherFrag "\\")
       <|> do eof
              return(OtherFrag "")
       <|> other

backslash :: GenParser Char st Char
backslash = char '\\'

escapedChar :: GenParser Char st Frag
escapedChar = do c <- anyChar
                 return (OtherFrag [c])

other :: GenParser Char st Frag
other = -- do str <- manyTill anyChar (try(oneOf "\\%\n"))
         do  str <- (many1 (noneOf "\\%"))
             return(OtherFrag str)

comment :: GenParser Char st Frag
comment = do char '%'
             s <- manyTill anyChar (try newline)
             return (OtherFrag "")

value :: String -> GenParser Char st String
value rightClosure =
  try(do s1 <- try(many (noneOf ("{}\\" ++ rightClosure)))
         s2 <- try(between (char '{') (char '}') (try(value rightClosure)))
         s3 <- option "" (value rightClosure)
         return (s1 ++ "{" ++ s2 ++ "}" ++ s3))
  <|> try(do s1 <- try(many (noneOf ("{}\\" ++ rightClosure)))
             s2 <- try(string "{}")
             s3 <- option "" (value rightClosure)
             return (s1 ++ "{}" ++ s3))
  <|> try(do s1 <- try(many (noneOf ("{}\\" ++ rightClosure)))
             s2 <- char '\\'
             s3 <- anyChar
             s4 <- option "" (value rightClosure)
             return (s1 ++ [s2] ++ [s3] ++ s4))
  <|> try(do s1 <- try(many1 (noneOf ("{}\\" ++ rightClosure)))
             return s1)


ontologyElement :: [String] -> GenParser Char st Frag
ontologyElement rels = declClassP <|> declObjectP <|> declRelationP
                       <|> declBaseRelationP <|> declRelTypeP
                       <|> objRelationP


declClassP :: GenParser Char st Frag

declClassP =
  do try (string "DeclClass") <|> (try (string "Class"))
     name <- try(between (char '{') (char '}') idParser)
     spaces
     defaultText <- (try (between (char '{') (char '}') (value "")))
     spaces
     superClass <- try(between (char '{') (char '}') idParser)
     superClassValue <- if (superClass == "")
                          then return(Nothing)
                          else return(Just(superClass))
     return(ClassDeclFrag (ClassDecl name defaultText superClassValue))

declObjectP =
  do try (string "DeclObject") <|> (try (string "Object"))
     name <- try(between (char '{') (char '}') idParser)
     spaces
     defaultText <- (try (between (char '{') (char '}') (value "")))
     spaces
     instanceOf <- try(between (char '{') (char '}') idParser)
     return(ObjectDeclFrag (ObjectDecl name defaultText instanceOf))

declRelationP =
  do try (string "DeclRelation")
     card <- option "" (try(between (char '{') (char '}') idParser))
     cardValue <- if (card == "")
                    then return(Nothing)
                    else return(Just(card))
     name <- try(between (char '{') (char '}') idParser)
     spaces
     defaultText <- try(between (char '{') (char '}') idParser)
     spaces
     sourceClass <- try(between (char '{') (char '}') idParser)
     spaces
     targetClass <- try(between (char '{') (char '}') idParser)
     return(RelationDeclFrag (RelationDecl cardValue name defaultText sourceClass targetClass))

declBaseRelationP =
  do try (string "DeclRel") <|> (try (string "Relation"))
     card <- choice ((try(string "{}")):(try(between (char '{') (char '}') idParser)):[])
     cardValue <- if (card == "{}")
                    then return(Nothing)
                    else return(Just(card))
     name <- try(between (char '{') (char '}') idParser)
     spaces
     defaultText <- try(between (char '{') (char '}') idParser)
     spaces
     super <- choice ((try(string "{}")):(try(between (char '{') (char '}') idParser)):[])
     superRel <- if (super == "{}")
                    then return(Nothing)
                    else return(Just(super))
     return(BaseRelationDeclFrag (BaseRelationDecl cardValue name defaultText superRel))

declRelTypeP =
  do try (string "RelType")
     name <- try(between (char '{') (char '}') idParser)
     spaces
     source <- try(between (char '{') (char '}') idParser)
     spaces
     target <- try(between (char '{') (char '}') idParser)
     return(RelationTypeDeclFrag (RelationTypeDecl name source target))

objRelationP =
  do try (string "Relate")
     name <- try(between (char '{') (char '}') idParser)
     spaces
     source <- try(between (char '{') (char '}') idParser)
     spaces
     target <- try(between (char '{') (char '}') idParser)
     return(ObjectLinkFrag (ObjectLink source target name))

{--
objLinkP :: [String] -> GenParser Char st Frag
objLinkP rels =
  try(
   do possibleRel <- try (many1 (noneOf "{\\\n"))
      if (possibleRel `elem` rels)
        then do sourceClass <- try(between (char '{') (char '}') idParser)
                spaces
                targetClass <- try(between (char '{') (char '}') idParser)
                return(ObjectLinkFrag (ObjectLink sourceClass targetClass possibleRel))
        else fail ""
  )
--}

idParser :: GenParser Char st String
idParser = many (noneOf "{}[]")
