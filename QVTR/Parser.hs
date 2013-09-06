{- |
Module      :  $Header$
Description :  QVT-Relational syntax parser
Copyright   :  (c) Daniel Calegari Universidad de la Republica, Uruguay 2013
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  dcalegar@fing.edu.uy
Stability   :  provisional
Portability :  portable
-}


module QVTR.Parser where


import qualified QVTR.As as QVTR
import qualified CSMOF.As as CSMOF

import Text.ParserCombinators.Parsec

import Common.Parsec


-- Parse a QVTR model transformation
-- <transformation> ::= <header> 
--                      '{' <keyDecl>* <relation>* '}'

pTransformation :: CharParser st QVTR.Transformation
pTransformation = do
  skip
  (name,souMeta,tarMeta) <- pTransfHeader
  skip
  char '{'
  skip
  keys <- many (try pKeyDecl)
  skip
  relations <- many (try pRelation)
  skip
  char '}'
  skip
  eof
  return (QVTR.Transformation 
            name 
            souMeta
            tarMeta
            keys
            relations
         )


-- Parse a transformation header without source and target CSMOF.Metamodel (just names)
-- <header> ::= 'transformation' <identifier>
--              '(' <modelDecl> ',' <modelDecl> ')'
-- <modelDecl> ::= <modelId> ':' <metaModelId>
-- <modelId> ::= <identifier>
-- <metaModelId> ::= <identifier>

pTransfHeader :: CharParser st (String, (String,String,CSMOF.Metamodel),(String,String,CSMOF.Metamodel))
pTransfHeader = do
  pKey "transformation"
  skip
  name <- pIdentifier
  skip
  list <- pBetParent $ pCommaSep $ pColonSep $ (skip >> pIdentifier << skip)
  return (  name,
            (head $ head list, head $ tail $ head list, emptyMetamodel),
            (head $ head $ tail list, head $ tail $ head $ tail list, emptyMetamodel)
         )


emptyMetamodel :: CSMOF.Metamodel
emptyMetamodel = CSMOF.Metamodel "" [] []


-- Parse keys of the transfromation
-- <keyDecl> ::= 'key' <classId> '{' <keyProperty> (, <keyProperty>)* '}' ';'
pKeyDecl :: CharParser st QVTR.Key
pKeyDecl = do
  skip
  pKey "key"
  skip
  classId <- pClassId
  skip
  list <- pBetBraces $ pCommaSep $ pKeyProperty
  skip
  char ';'
  return (QVTR.Key (fst classId) (snd classId) list) -- ToDo


-- <classId> ::= <identifier> '::' <identifier>
pClassId :: CharParser st (String,String)
pClassId = do
  met <- pIdentifier
  char ':'
  char ':'
  typ <- pIdentifier
  return ((met,typ))


-- <keyProperty> ::= <identifier>
--                 | 'opposite' '(' <identifier> '.' <identifier> ')'
pKeyProperty :: CharParser st QVTR.PropKey
pKeyProperty = do
    pKey "opposite"
    skip
    oppo <- pBetParent $ pFullName
    return (QVTR.OppositeProp (fst oppo) (snd oppo))
  <|>
    do
    skip
    ident <- pIdentifier
    return (QVTR.SimpleProp ident)


-- <identifier> '.' <identifier>
pFullName :: CharParser st (String,String)
pFullName = do
  cla <- pIdentifier
  char '.'
  typ <- pIdentifier
  return ((cla,typ))


-- Parse transformation rules
-- <relation> ::= ['top'] 'relation' <identifier>
--                '{'
--                <varDeclaration>*
--                <primitiveTypeDomain>*
--                <domain> <domain>
--                [<when>] [<where>]
--                '}'

pRelation :: CharParser st QVTR.Relation
pRelation = do
  skip
  top <- pIsTop
  skip
  iden <- pIdentifier
  skip
  char '{'
  skip
  varSet <- many (try pVarDeclaration)
  skip
  primDom <- many (try pPrimitiveTypeDomain)
  skip
  sourceDom <- pDomain
  skip
  targetDom <- pDomain
  skip
  whenCon <- option Nothing pWhen
  skip
  whereCon <- option Nothing pWhere
  skip
  char '}'
  return ( QVTR.Relation top iden (concat varSet) 
                     primDom sourceDom targetDom whenCon whereCon )

-- Parse if a relation is top or not
pIsTop :: CharParser st Bool
pIsTop = do 
  skip
  pKey "top" 
  skip
  pKey "relation" 
  return (True)
  <|>
  do skip
     pKey "relation"
     return (False)


-- Parse var declaration
-- <varDeclaration> ::= <identifier> (, <identifier>)* ':' <TypeCS> ';'

pVarDeclaration :: CharParser st [QVTR.RelVar]
pVarDeclaration = do
  skip
  vars <- pCommaSep pIdentifier
  skip
  char ':'
  skip
  typ <- pTypeCS
  skip
  char ';'
  return ( map (\nam -> (QVTR.RelVar typ nam)) vars )


-- <TypeCS> ::= <identifier> '::' <identifier>
--            | <identifier>

pTypeCS :: CharParser st String
pTypeCS =
  try (do typ <- pIdentifier
          skip
          notFollowedBy (char ':')
          return (typ)
         )
  <|>
  do
    _ <- pIdentifier
    char ':'
    char ':'
    typ <- pIdentifier
    return (typ)


-- Parse primitive domain
-- <primitiveTypeDomain> ::= 'primitive' 'domain' <identifier> ':' <TypeCS> ';'

pPrimitiveTypeDomain :: CharParser st QVTR.PrimitiveDomain
pPrimitiveTypeDomain = do
  skip
  pKey "primitive" 
  skip
  pKey "domain" 
  skip
  nam <- pIdentifier
  skip
  char ':'
  skip
  typ <- pTypeCS
  skip
  char ';'
  return ( QVTR.PrimitiveDomain nam typ ) 


-- <domain> ::= 'domain' <modelId> <template> ';'

pDomain :: CharParser st QVTR.Domain
pDomain = do
  skip
  (pKey "checkonly" <|> pKey "enforce")
  skip
  pKey "domain" 
  skip
  modelId <- pIdentifier
  skip
  tem <- pTemplate
  skip
  char ';'
  return ( QVTR.Domain modelId tem )


-- <template> ::= <objectTemplate>
-- <objectTemplate> ::= <identifier> ':' <pathNameCS>
--                     '{' [<propertyTemplateList>] '}'

pTemplate :: CharParser st QVTR.ObjectTemplate
pTemplate = do
  skip
  ide <- pIdentifier
  skip
  char ':'
  skip
  typ <- pClassId
  skip
  char '{'
  skip
  tempList <- option [] pPropertyTemplateList
  skip
  char '}'
  return ( QVTR.ObjectTemplate ide (fst typ) (snd typ) tempList )


-- <propertyTemplateList> ::= <propertyTemplate> (',' <propertyTemplate>)*

pPropertyTemplateList :: CharParser st [QVTR.PropertyTemplate]
pPropertyTemplateList = do
  tempList <- try $ pCommaSep pPropertyTemplate
  return ( tempList )


-- <propertyTemplate> ::= <identifier> '=' <OclExpressionCS>
--                     | <identifier> '=' <objectTemplate>

pPropertyTemplate :: CharParser st QVTR.PropertyTemplate
pPropertyTemplate = do
  skip
  ident <- pIdentifier
  skip
  pEqual
  skip
  (do t <- try pTemplate 
      return ( QVTR.PropertyTemplate ident Nothing (Just t) ) 
   <|> 
   do e <- try pOCLExpression
      return ( QVTR.PropertyTemplate ident (Just e) Nothing ))


-- <when> ::= 'when' '{' (<RelInvocation> ';')* (<OclExpressionCS> ';')* '}'
pWhen :: CharParser st (Maybe QVTR.WhenWhere)
pWhen = do
  skip
  pKey "when" 
  skip
  char '{'
  skip
  relInvok <- many (try pRelInvocation)
  skip
  oclExpre <- try $ pSemiSep pOCLExpression
  skip
  char '}'
  return ( Just (QVTR.WhenWhere relInvok oclExpre) )


-- <where> ::= 'where' '{' (<RelInvocation> ';')* (<OclExpressionCS> ';')* '}'
pWhere :: CharParser st (Maybe QVTR.WhenWhere)
pWhere = do
  skip
  pKey "where" 
  skip
  char '{'
  skip
  relInvok <- many (try pRelInvocation)
  skip
  oclExpre <- try $ pSemiSep pOCLExpression
  skip
  char '}'
  return ( Just (QVTR.WhenWhere relInvok oclExpre) )


-- <RelInvocation> ::= <identifier> '(' (<identifier> ',')* ')' ';'
pRelInvocation :: CharParser st QVTR.RelInvok
pRelInvocation = do
  skip
  nam <- pIdentifier
  skip
  char '('
  skip
  params <- pCommaSep pIdentifier
  skip
  char ')'
  skip
  char ';'
  return ( QVTR.RelInvok nam params )


-- Auxiliary definitions

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

pColon :: CharParser st ()
pColon = pSym ":"

pSymS :: String -> CharParser st String
pSymS s = tryString s << skip

pSym :: String -> CharParser st ()
pSym = forget . pSymS

pComma :: CharParser st ()
pComma = pSym ","

pEqual :: CharParser st ()
pEqual = pSym "="

pBetParent :: CharParser st a -> CharParser st a
pBetParent = between (char '(') (char ')')

pBetBraces :: CharParser st a -> CharParser st a
pBetBraces = between (char '{') (char '}')

pCommaSep :: CharParser st a -> CharParser st [a]
pCommaSep p  = p `sepBy` (char ',')

pSemiSep :: CharParser st a -> CharParser st [a]
pSemiSep p  = p `sepBy` (char ';')

pColonSep :: CharParser st a -> CharParser st [a]
pColonSep p  = p `sepBy` (char ':')

pIdentifier :: CharParser st String
pIdentifier = do
  skip
  c <- letter
  rest <- many (alphaNum <|> oneOf "_")
  return (c : rest)




-- FAKE OCL PARSER
-- <OclExpressionCS> ::= <Expre>
--                     | 'if' <Expre> 'then' <OclExpressionCS> 'else' <OclExpressionCS> 'endif'
--
-- <Expre> ::= '(' <Expre> ')'
--           | <String> 
--           | <identifier> 
--           | <Const>
--           | <Expre> <Duop> <Expre>
--           | <Unop> <Expre>
--
-- <Const> ::= 'true' | 'false'
-- <Unop>  ::= 'not'
-- <Duop>  ::= 'and' | 'or' | '='
--
-- <String> ::= ''' <text> ''' 
--            | <String> '+' <String>

pOCLExpression :: CharParser st QVTR.OCL
pOCLExpression = do
  skip
  (    do (b,le,re) <- try pOCLIf
          return ( QVTR.IFExpre b le re )
   <|> do r <- pOCLExpre
          return (QVTR.OCLExpre r))


pOCLExpre :: CharParser st QVTR.EXPRE
pOCLExpre = do
  skip
  (    do ex <- try $ pBetParent pOCLExpre
          return ( QVTR.Paren ex )
   <|> do s <- try pOCLSTRING
          return ( QVTR.StringExp s )
   <|> do v <- pIdentifier
          return ( QVTR.VarExp v )
   <|> do pOCLConst
   <|> do le <- pOCLExpre
          skip
          op <- pDuop
          skip
          re <- pOCLExpre
          (if op == "="
           then return ( QVTR.Equal le re )
           else if op == "and"
                then return ( QVTR.BoolExp (QVTR.AndB le re) )
                else return ( QVTR.BoolExp (QVTR.OrB le re)))
   <|> do pKey "not" 
          skip
          e <- try pOCLExpre
          return ( QVTR.BoolExp (QVTR.NotB e)) )


pDuop :: CharParser st String
pDuop = do
  skip
  (    do pKey "and" 
          return ( "and" )
   <|> do pKey "or" 
          return ( "or" )
   <|> do pKey "=" 
          return ( "=" ) )


pOCLConst :: CharParser st QVTR.EXPRE
pOCLConst = do
  skip
  (    do pKey "true" 
          return ( QVTR.BoolExp (QVTR.BExp True) )
   <|> do pKey "false" 
          return ( QVTR.BoolExp (QVTR.BExp False) ) )


pOCLIf :: CharParser st (QVTR.EXPRE,QVTR.OCL,QVTR.OCL)
pOCLIf = do
  skip
  pKey "if" 
  skip
  b <- pOCLExpre
  skip
  pKey "then" 
  skip
  e1 <- pOCLExpression
  skip
  pKey "else" 
  skip
  e2 <- pOCLExpression
  skip
  pKey "endif" 
  return ( (b,e1,e2) )


pOCLSTRING :: CharParser st QVTR.STRING
pOCLSTRING = do
  skip
  (     do (ls,rs) <- try pStringConcat
           return ( QVTR.ConcatExp ls rs )
    <|> do res <- pOCLSingleSTRING 
           return ( QVTR.Str res ))


pStringConcat :: CharParser st (QVTR.STRING,QVTR.STRING)
pStringConcat = do
  skip
  ls <- pOCLSingleSTRING
  skip
  char '+'
  skip
  rs <- pOCLSingleSTRING
  return ( (QVTR.Str ls, QVTR.Str rs) )


pOCLSingleSTRING :: CharParser st String
pOCLSingleSTRING = do
  skip
  char '\''
  skip
  res <- (many (noneOf "\'")) << (oneOf "\'")
  return ( res )


--  skip
--  res <- (many (noneOf ",;{}")) << (oneOf ",;")
--  return ( QVTR.StringExp (QVTR.Str res) )

