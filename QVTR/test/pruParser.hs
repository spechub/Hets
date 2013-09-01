import System.IO
import System.FilePath (replaceBaseName, replaceExtension, takeBaseName)

import qualified QVTR.As as QVTR
import QVTR.Print
import qualified CSMOF.As as CSMOF

import Text.ParserCombinators.Parsec

import Common.Parsec

import CSMOF.Parser

import Text.XML.Light


-- From the QVTR folder run: ghc -i.. -o main pruParser.hs

main :: IO ()
main = do  
    handle <- openFile "uml2rdbms.qvt" ReadMode  
    input <- hGetContents handle 
    case runParser pTransformation () "uml2rdbms.qvt" input of  -- Either ParseError String
      Left err -> print err
      Right trans -> let (_,sMet,_) = QVTR.sourceMetamodel trans
                         (_,tMet,_) = QVTR.targetMetamodel trans
                     in
                       do
                         sourceMetam <- parseXmiMetamodel (replaceName "uml2rdbms.qvt" sMet)
                         targetMetam <- parseXmiMetamodel (replaceName "uml2rdbms.qvt" tMet)
                         print (createTransfWithMeta trans sourceMetam targetMetam)



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
    met <- pIdentifier
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
  id <- pIdentifier
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
  return ( QVTR.ObjectTemplate id (fst typ) (snd typ) tempList )


-- <propertyTemplateList> ::= <propertyTemplate> (',' <propertyTemplate>)*

pPropertyTemplateList :: CharParser st [QVTR.PropertyTemplate]
pPropertyTemplateList = do
  tempList <- many (try pPropertyTemplate)
  return ( tempList )


-- <propertyTemplate> ::= <identifier> '=' <OclExpressionCS> ';'
--                     | <identifier> '=' <objectTemplate>

pPropertyTemplate :: CharParser st QVTR.PropertyTemplate
pPropertyTemplate = do
  skip
  ident <- pIdentifier
  skip
  pEqual
  skip
  (do t <- try pTemplate 
      oneOf ",;"
      return ( QVTR.PropertyTemplate ident Nothing (Just t) ) 
   <|> 
   do e <- pOCLExpression
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
  oclExpre <- many (try pOCLExpression)
  skip
  char '}'
  return ( Just (QVTR.When relInvok oclExpre) )


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
  oclExpre <- many (try pOCLExpression)
  skip
  char '}'
  return ( Just (QVTR.Where relInvok oclExpre) )


-- <RelInvocation> ::= <identifier> '(' (<identifier> ',')* ')' ';'
pRelInvocation :: CharParser st QVTR.RelInvok
pRelInvocation = do
  skip
  name <- pIdentifier
  skip
  char '('
  skip
  params <- pCommaSep pIdentifier
  skip
  char ')'
  skip
  char ';'
  return ( QVTR.RelInvok name params )


pOCLExpression :: CharParser st String
pOCLExpression = do
  skip
  res <- (many (noneOf ",;{}")) << (oneOf ",;")
  return (res)


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

pColonSep :: CharParser st a -> CharParser st [a]
pColonSep p  = p `sepBy` (char ':')

pIdentifier :: CharParser st String
pIdentifier = do
  skip
  c <- letter
  rest <- many (alphaNum <|> oneOf "_")
  return (c : rest)



---------------------------------------------------

replaceName :: FilePath -> String -> String
replaceName fp na = replaceBaseName (replaceExtension fp "xmi") na


parseXmiMetamodel :: FilePath -> IO CSMOF.Metamodel
parseXmiMetamodel fp = 
  do
    handle <- openFile fp ReadMode  
    contents <- hGetContents handle 
    case parseXMLDoc contents of
      Nothing -> return (CSMOF.Metamodel { CSMOF.metamodelName = takeBaseName fp
                           , CSMOF.element = []
                           , CSMOF.model = []
                           })
      Just el -> return (parseCSMOF el)


createTransfWithMeta :: QVTR.Transformation -> CSMOF.Metamodel -> CSMOF.Metamodel -> QVTR.Transformation
createTransfWithMeta trans souMeta tarMeta =
  let (sVar,sMet,_) = QVTR.sourceMetamodel trans
      (tVar,tMet,_) = QVTR.targetMetamodel trans
  in
    QVTR.Transformation (QVTR.transfName trans) (sVar,sMet,souMeta) (tVar,tMet,tarMeta) (QVTR.keys trans) (QVTR.relations trans)

