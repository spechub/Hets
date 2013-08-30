{- |
Module      :  $Header$
Description :  QVT-Relational syntax parser
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}

{-
Relations Textual Syntax Grammar

<transformation> ::= 'transformation' <identifier>
                     '(' <modelDecl> ',' <modelDecl> ')'
                     '{' <keyDecl>* ( <relation> )* '}'
<modelDecl> ::= <modelId> ':' <metaModelId>
<modelId> ::= <identifier>
<metaModelId> ::= <identifier>
<keyDecl> ::= 'key' <classId> '{' <keyProperty> (, <keyProperty>)* '}' ';'
<classId> ::= <pathNameCS>
<keyProperty> ::= <identifier>
                | 'opposite' '(' <classId> '.' <identifier> ')'
<relation> ::= ['top'] 'relation' <identifier>
               '{'
               <varDeclaration>*
               (<domain> | <primitiveTypeDomain>)+
               [<when>] [<where>]
               '}'
<varDeclaration> ::= <identifier> (, <identifier>)* ':' <TypeCS> ';'
<domain> ::= 'domain' <modelId> <template> ';'

<primitiveTypeDomain> ::= 'primitive' 'domain' <identifier> ':' <TypeCS> ';'
<template> ::= <objectTemplate> ['{' <OclExpressionCS> '}']

<objectTemplate> ::= [<identifier>] ':' <pathNameCS>
                     '{' [<propertyTemplateList>] '}'
<propertyTemplateList> ::= <propertyTemplate> (',' <propertyTemplate>)*
<propertyTemplate> ::= <identifier> '=' <OclExpressionCS>
                     | 'opposite' '(' <classId> '.' <identifier> ')' '='
                       <OclExpressionCS>
<assignmentExp> ::= <identifier> '=' <OclExpressionCS> ';'
<when> ::= 'when' '{' (<OclExpressionCS> ';')* '}'
<where> ::= 'where' '{' (<OclExpressionCS> ';')* '}'
-}

module QVTR.Parser where

import QVTR.As
import CSMOF.As

import Text.ParserCombinators.Parsec

import Common.Lexer (parseToken)
import Common.Parsec


parseQVTR :: String -> Metamodel -> Metamodel -> Transformation
parseQVTR _ sMetamodel tMetamodel = 
  Transformation { transfName = ""
                 , sourceMetamodel = ("", metamodelName sMetamodel, sMetamodel) --(String,String,QVTR.Metamodel)
                 , targetMetamodel = ("", metamodelName tMetamodel, tMetamodel) --(String,String,QVTR.Metamodel)
                 , keys = [] --[Key]
                 , relations = [] --[Relation]
                 }


-- Read metamodel name for parsing xmi file
getMetamodelName :: String -> FilePath -> Side -> String
getMetamodelName input fname side = 
  let 
    p = case side of
          Source -> pFile --ToDo
          Target -> pFile --ToDo
  in 
    case runParser p () fname input of  -- Either ParseError String
      Left err -> ""
      Right name -> name


data Side = Source | Target


-- | a line comment starts with --
lineComment :: CharParser st String
lineComment = tryString "--" <++> many (noneOf "\n")

skip :: CharParser st ()
skip = skipMany $ forget space
  <|> forget (nestedComment "/*" "*/" <|> lineComment)

pChar :: CharParser st Char
pChar = alphaNum <|> oneOf "_'"

pKeyS :: String -> CharParser st String
pKeyS s = try (string s << notFollowedBy pChar) << skip

pKey :: String -> CharParser st ()
pKey = forget . pKeyS


pFile :: CharParser st String
pFile = do
  pKey "transformation"
  skipMany1 newline
  eof
  return $ "HOLA"
