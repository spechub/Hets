-- |
-- the XPath Parser
--


module Text.XML.HXT.XPath.XPathParser
    ( parseNumber
    , parseStr
    , parseXPath
    , nodeTest, nameTest, predicate, tokenParser, symbol, symbolParser, number
    )
where

import Text.XML.HXT.XPath.XPathKeywords
import Text.XML.HXT.XPath.XPathDataTypes hiding (choice)
import Text.XML.HXT.DOM.XmlTree
    ( QName )

import Text.XML.HXT.Parser.XmlParser
    ( separator
    , systemLiteral
    , skipS0
    , ncName
    , qName
    )


import Text.XML.HXT.DOM.XmlTreeTypes
    ( mkName
    , mkNsName
    )

import Text.ParserCombinators.Parsec

-- ------------------------------------------------------------
-- parse functions which are used in the XPathFct module

-- |
-- parsing a number, parseNumber is used in "XPathFct"
-- by the number function
--
--    - returns : the parsed number as 'XPNumber' float
--                or 'XPVNumber' 'NaN' in case of error
parseNumber :: String -> XPathValue
parseNumber s
    = case (parse parseNumber' "" s) of
        Left _ -> XPVNumber NaN
        Right x  -> if (read x :: Float) == 0
                      then (XPVNumber Pos0)
                      else XPVNumber (Float (read x))

parseNumber' :: Parser String
parseNumber'
    = do
      skipS0
      m <- option "" (string "-")
      n <- number
      skipS0
      eof
      return (m ++ n)


-- |
-- parsing a string, parseStr is used in "XPathFct"
-- by the string function
--
--    - returns : the parsed string as 'XPVString'
parseStr :: String -> XPathValue
parseStr s
    = case (parse parseStr' "" s) of
        Left _ -> error "function: xnormalizeSpace"
        Right x  -> XPVString x

parseStr' :: Parser String
parseStr'
    = do
      skipS0
      m <- sepBy (many1 $ noneOf "\t\n\r ") skipS0
      skipS0
      eof
      return (foldr1 (\ x y -> x ++ " " ++ y) m)


-- ------------------------------------------------------------


-- |
-- the main entry point:
--	parsing a XPath expression
parseXPath :: Parser Expr
parseXPath 
    = do
      skipS0
      xPathExpr <- expr
      skipS0
      eof
      return xPathExpr


-- some useful token and symbol parser
lpar, rpar, lbra, rbra, slash, dslash	:: Parser ()

lpar   = tokenParser (symbol "(")
rpar   = tokenParser (symbol ")")
lbra   = tokenParser (symbol "[")
rbra   = tokenParser (symbol "]")
slash  = tokenParser (symbol "/")
dslash = tokenParser (symbol "//")


tokenParser :: Parser String -> Parser ()
tokenParser p
    = try ( do
            skipS0
            p
            skipS0
           )


symbolParser :: (String, a) -> Parser a
symbolParser (s,a)
    = do
      tokenParser (symbol s)
      return a


symbol :: String -> Parser String
symbol s = try (string s)



--  operation parser
orOp, andOp, eqOp, relOp, addOp, multiOp, unionOp :: Parser Op

orOp  = symbolParser ("or", Or)
andOp =	symbolParser ("and", And)

eqOp
    = symbolParser ("=", Eq)
      <|> 
      symbolParser ("!=", NEq)

relOp
    = choice [ symbolParser ("<=", LessEq)
             , symbolParser (">=", GreaterEq)
             , symbolParser ("<", Less)
             , symbolParser (">", Greater)
             ]

addOp
    = symbolParser ("+", Plus)
      <|> 
      symbolParser ("-", Minus)


multiOp
    = choice [ symbolParser ("*", Mult)
             , symbolParser ("mod", Mod)
             , symbolParser ("div", Div)
             ]


unionOp	= symbolParser ("|", Union)

-- ------------------------------------------------------------

mkExprNode :: Expr -> [(Op, Expr)] -> Expr
mkExprNode e1 [] = e1
mkExprNode e1 l@((op, _): _) = GenExpr op (e1:(map snd l))

exprRest :: Parser Op -> Parser Expr -> Parser (Op, Expr)
exprRest parserOp parserExpr
    = do
      op <- parserOp
      e2 <- parserExpr
      return (op, e2)


-- ------------------------------------------------------------

-- abbreviation of "//"
descOrSelfStep :: XStep 
descOrSelfStep = (Step DescendantOrSelf (TypeTest XPNode) [])

-- ------------------------------------------------------------
-- Location Paths (2)


-- [1] LocationPath 
locPath :: Parser LocationPath
locPath
    = absLocPath
      <|> 
      relLocPath'


-- [2] AbsoluteLocationPath
absLocPath :: Parser LocationPath
absLocPath
    = do -- [10]
      dslash
      s <- relLocPath
      return (LocPath Abs ([descOrSelfStep] ++ s))
      <|> 
      do
      slash
      s <- option [] relLocPath
      return (LocPath Abs s)
      <?> "absLocPath"


-- [3] RelativeLocationPath
relLocPath' :: Parser LocationPath
relLocPath'
    = do
      rel <- relLocPath
      return (LocPath Rel rel)

relLocPath :: Parser [XStep]
relLocPath
    = do
      s1 <- step
      s2 <- many step'
      return ([s1] ++ (concat s2))
      <?> "relLocPath"


-- Location Steps (2.1)
--
-- [4] Step
step' :: Parser [XStep]
step'
    = do -- [11]
      dslash
      s <- step
      return [descOrSelfStep,s]
      <|>
      do
      slash
      s <- step
      return [s]
      <?> "step'"

step :: Parser XStep
step
    = abbrStep
      <|>
      do
      as <- axisSpecifier'
      nt <- nodeTest
      pr <- many predicate
      return (Step as nt pr)
      <?> "step"


-- [5] AxisSpecifier
axisSpecifier' :: Parser AxisSpec
axisSpecifier'
    = do  -- [13]
      tokenParser (symbol "@")
      return Attribute
      <|>
      do
      as <- option Child ( try ( do -- child-axis is default-axis
                                 a <- axisSpecifier
                                 tokenParser (symbol "::")
                                 return a
                               )
                          )
      return as
      <?> "axisSpecifier'"


-- Axes (2.2)
--
-- [6] AxisName
axisSpecifier :: Parser AxisSpec
axisSpecifier
    = choice [ symbolParser (a_ancestor_or_self, AncestorOrSelf)
             , symbolParser (a_ancestor, Ancestor)
             , symbolParser (a_attribute, Attribute)
             , symbolParser (a_child, Child)
             , symbolParser (a_descendant_or_self, DescendantOrSelf)
             , symbolParser (a_descendant, Descendant)
             , symbolParser (a_following_sibling, FollowingSibling)
             , symbolParser (a_following, Following)
             , symbolParser (a_namespace, Namespace)
             , symbolParser (a_parent, Parent)
             , symbolParser (a_preceding_sibling, PrecedingSibling)
             , symbolParser (a_preceding, Preceding)
             , symbolParser (a_self, Self)
             ]
      <?> "axisSpecifier"


-- Node Tests (2.3)
--
-- [7] NodeTest
nodeTest :: Parser NodeTest
nodeTest
    = do
      nt <- try nodeType'
      return (TypeTest nt)
      <|>
      do
      processInst <- pI
      return (PI processInst)
      <|>
      do
      nt <- nameTest
      return (NameTest nt)
      <?> "nodeTest"

pI :: Parser String
pI
    = do
      tokenParser (symbol n_processing_instruction)
      li <- between lpar rpar literal
      return li
      <?> "Processing-Instruction"


-- Predicates (2.4)
--
-- [8] Predicate
-- [9] PredicateExpr
predicate :: Parser Expr
predicate
    = do
      ex <- between lbra rbra expr
      return ex


-- Abbreviated Syntax (2.5)
--
-- [10] AbbreviatedAbsoluteLocationPath: q.v. [2]
-- [11] AbbreviatedRelativeLocationPath: q.v. [4]

-- [12] AbbreviatedStep
abbrStep :: Parser XStep
abbrStep
    = do
      tokenParser (symbol "..")
      return (Step Parent (TypeTest XPNode) [])
      <|>
      do
      tokenParser (symbol ".")
      return (Step Self (TypeTest XPNode) [])
      <?> "abbrStep"

-- [13] AbbreviatedAxisSpecifier: q.v. [5]


-- ------------------------------------------------------------
-- Expressions (3)


-- Basics (3.1)
--
-- [14] Expr
expr :: Parser Expr
expr = orExpr


-- [15] PrimaryExpr
primaryExpr :: Parser Expr
primaryExpr
    = do
      vr <- variableReference
      return (VarExpr vr)
      <|>
      do
      ex <- between lpar rpar expr
      return ex
      <|>
      do
      li <- literal
      return (LiteralExpr li)
      <|> 
      do
      num <- number
      return (NumberExpr (Float $ read num))
      <|>
      do
      fc <- functionCall
      return (fc)
      <?> "primaryExpr"


-- Function Calls (3.2)
--
-- [16] FunctionCall
-- [17] Argument
functionCall :: Parser Expr
functionCall
    = do
      fn <- functionName
      arg <- between lpar rpar ( sepBy expr (separator ',') )
      return (FctExpr fn arg)
      <?> "functionCall"


-- Node-sets (3.3)
--
-- [18] UnionExpr
unionExpr :: Parser Expr
unionExpr
    = do
      e1 <- pathExpr
      eRest <- many (exprRest unionOp pathExpr)
      return (mkExprNode e1 eRest)


-- [19] PathExpr
pathExpr :: Parser Expr
pathExpr
    = do
      fe <- try filterExpr
      path <- do
              dslash
              LocPath t1 t2 <- relLocPath'
              return (PathExpr (Just fe) (Just (LocPath t1 ([descOrSelfStep] ++ t2))))
              <|>
              do
              slash
              relPath <- relLocPath'
              return (PathExpr (Just fe) (Just relPath))
              <|>
              return fe
      return path
      <|>
      do
      lp <- locPath
      return (PathExpr Nothing (Just lp))
      <?> "pathExpr"


-- [20] FilterExpr
filterExpr :: Parser Expr
filterExpr
    = do
      prim <- primaryExpr
      predicates <- many predicate
      if length predicates > 0
        then return (FilterExpr (prim : predicates))
        else return prim
      <?> "filterExpr"


-- Booleans (3.4)
--
-- [21] OrExpr
orExpr :: Parser Expr
orExpr
    = do
      e1 <- andExpr
      eRest <- many (exprRest orOp andExpr)
      return (mkExprNode e1 eRest)
      <?> "orExpr"


-- [22] AndExpr
andExpr :: Parser Expr
andExpr
    = do
      e1 <- equalityExpr
      eRest <- many (exprRest andOp equalityExpr)
      return (mkExprNode e1 eRest)
      <?> "andExpr"


-- [23] EqualityExpr
equalityExpr :: Parser Expr
equalityExpr
    = do
      e1 <- relationalExpr
      eRest <- many (exprRest eqOp relationalExpr)
      return (mkExprNode e1 eRest)
      <?> "equalityExpr"


-- [24] RelationalExpr
relationalExpr :: Parser Expr
relationalExpr
    = do
      e1 <- additiveExpr
      eRest <- many (exprRest relOp additiveExpr)
      return (mkExprNode e1 eRest)
      <?> "relationalExpr"


-- Numbers (3.5)
--
-- [25] AdditiveExpr
additiveExpr :: Parser Expr
additiveExpr
    = do
      e1 <- multiplicativeExpr
      eRest <- many (exprRest addOp multiplicativeExpr)
      return (mkExprNode e1 eRest)
      <?> "additiveExpr"


-- [26] MultiplicativeExpr
multiplicativeExpr :: Parser Expr
multiplicativeExpr
    = do
      e1 <- unaryExpr
      eRest <- many (exprRest multiOp unaryExpr)
      return (mkExprNode e1 eRest)
      <?> "multiplicativeExpr"


-- [27] UnaryExpr
unaryExpr :: Parser Expr
unaryExpr
    = do
      tokenParser (symbol "-")
      u <- unaryExpr
      return (GenExpr Unary [u])
      <|>
      do
      u <- unionExpr
      return u
      <?> "unaryExpr"


-- Lexical Structure (3.7)
--
-- [29] Literal
-- systemLiteral from XmlParser is used
literal :: Parser String
literal = systemLiteral


-- [30] Number
number :: Parser String
number
    = do
      tokenParser (symbol ".")
      d <- many1 digit
      return ("0." ++ d)
      <|>
      do
      d <- many1 digit
      d1 <- option "" ( do
                        tokenParser (symbol ".")
                        d2 <- option "0" (many1 digit)
                        return ("." ++ d2)
                      )
      return (d ++ d1)
      <?> "number"


-- [35] FunctionName
-- no nodetype name is allowed as a function name
functionName :: Parser String
functionName
    = try ( do
            (fn1, fn2) <- qName
            let fn = (fn1 ++ fn2) in
              if fn == "processing-instruction" || fn == "comment"
                 || fn == "text" || fn == "node"
                   then fail ("function name: " ++ fn ++ "not allowed")
                   else return fn
          )
      <?> "functionName"


-- [36] VariableReference
variableReference :: Parser (String, String)
variableReference
    = do
      tokenParser (symbol "$")
      name <- qName      	
      return name
      <?> "variableReference"


-- [37] NameTest
nameTest :: Parser QName
nameTest
    = do
      tokenParser (symbol "*")
      return (mkName "*")
      <|> try ( do
                pre <- ncName
                symbol ":*"
                return (mkNsName (pre ++ ":*") "")                
              )
      <|>
      do
      (pre,local) <- qName      	      
      return (mkNsName (pre ++ ":" ++ local) "")
      <?> "nameTest"	

	
-- [38] NodeType
nodeType' :: Parser XPathNode
nodeType' 
    = do
      nt <- nodeType
      lpar
      rpar
      return nt
      <?> "nodeType'"
	
nodeType :: Parser XPathNode
nodeType 
    = choice [ symbolParser (n_comment, XPCommentNode)
             , symbolParser (n_text, XPTextNode)
             , symbolParser (n_processing_instruction, XPPINode)
             , symbolParser (n_node, XPNode)
             ]
      <?> "nodeType"
