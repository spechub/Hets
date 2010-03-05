{- |
Module      :  $Header$
Description :  XPath utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

XPath utilities independent of xml package.
references:
<http://www.w3.org/TR/xpath/>
<http://www.galiel.net/el/study/XPath_Overview.html>
<http://www.fh-wedel.de/~si/HXmlToolbox/hxpath/diplomarbeit.pdf>
<http://hackage.haskell.org/package/hxt-xpath>
(modules XPathParser, XPathDataTypes)
<http://hackage.haskell.org/package/hxt-8.5.0>
(modules Text.XML.HXT.DOM.Unicode, Text.XML.HXT.Parser.XmlCharParser)
<http://www.w3.org/TR/REC-xml/#NT-Name>

'ncName' from 'OWL.Parse' allows `+' in names. Unicode is not
fully supported. A qualified name is an ncName or two ncNames
separated by a colon (different from OWL uris).
-}

module Common.XPath where

import Text.ParserCombinators.Parsec
import Common.Parsec
import Data.Char
import Data.List

-- * data types and pretty printing (via show)

-- | axis specifier
data Axis
  = Ancestor Bool -- ^ or self?
  | Attribute
  | Child
  | Descendant Bool -- ^ or self?
  | Following Bool -- ^ sibling?
  | Namespace
  | Parent
  | Preceding Bool -- ^ sibling?
  | Self deriving Show

-- | all possible values
allAxis :: [Axis]
allAxis = let bl = [True, False] in
  [ Attribute
  , Child
  , Namespace
  , Parent
  , Self ]
  ++ [ Ancestor b | b <- bl ]
  ++ [ Descendant b | b <- bl ]
  ++ [ Following b | b <- bl ]
  ++ [ Preceding b | b <- bl ]

-- | utility to show (constant) constructors as lower case strings
lowerShow :: Show a => a -> String
lowerShow = map toLower . show

-- | proper string representation (do not use show)
showAxis :: Axis -> String
showAxis a =
  let s = takeWhile isAlpha $ lowerShow a
      orSelf b = if b then s ++ "-or-self" else s
      sibl b = if b then s ++ "-sibling" else s
  in case a of
  Ancestor c -> orSelf c
  Descendant c -> orSelf c
  Following c -> sibl c
  Preceding c -> sibl c
  _ -> s

data NodeTest
  = NameTest String -- ^ optional prefix and local part (possibly *)
  | PI String -- ^ processing-instruction node type with optional literal
  | Node
  | Comment
  | Text
    deriving Show

-- | all node types without processing-instruction
nodeTypes :: [NodeTest]
nodeTypes = [Node, Comment, Text]

-- | the processing-instruction string
pIS :: String
pIS = "processing-instruction"

-- | put parens arount a string
paren :: String -> String
paren = ('(' :) . (++ ")")

-- | proper string representation (do not use show)
showNodeTest :: NodeTest -> String
showNodeTest t = case t of
  NameTest q -> q
  PI s -> pIS ++ paren s
  _ -> lowerShow t ++ paren ""

-- | the stuff of a path between the slashes
data Step = Step Axis NodeTest [Expr] -- ^ with predicate list

-- | string representation considering abbreviations
showStep :: Step -> String
showStep (Step a n ps) =
  let t = showNodeTest n in
  case (a, n) of
     (Attribute, _) -> '@' : t
     (Child, _) -> t
     (Self, Node) -> "."
     (Parent, Node) -> ".."
     _ -> showAxis a ++ "::" ++ t
  ++ concatMap showPred ps

instance Show Step where
  show = showStep

-- | test for @descendant-or-self::node()@ step
isDescOrSelfNode :: Step -> Bool
isDescOrSelfNode (Step a n _) = case (a, n) of
  (Descendant True, Node) -> True
  _ -> False

-- | only absolute paths may be empty
data Path = Path Bool [Step] -- ^ absolute?

-- | show a path abbreviating @\/descendant-or-self::node()\/@
showSteps :: Bool -> [Step] -> String
showSteps abso sts = let h = if abso then "/" else "" in case sts of
  [] -> h
  s : r -> let f = h ++ showStep s in case r of
    [] -> f
    _ -> if abso && isDescOrSelfNode s then "//" ++ showSteps False r
         else f ++ showSteps True r

instance Show Path where
  show (Path abso sts) = showSteps abso sts

-- | indicator for primary expressions
data PrimKind
  = Var -- ^ leading dollar
  | Literal -- ^ single or double quotes
  | Number -- ^ digits possibly with decimal point

-- | expressions where function calls, unary and infix expressions are generic
data Expr
  = GenExpr Bool String [Expr] -- ^ infix?, op or fct, and arguments
  | PathExpr (Maybe Expr) Path -- ^ optional filter and path
  | FilterExpr Expr [Expr] -- ^ primary expression with predicates
  | PrimExpr PrimKind String

instance Show Expr where
  show = showExpr

-- | put square brackets around an expression
showPred :: Expr -> String
showPred e = '[' : showExpr e ++ "]"

-- | show expression with minimal parens
showExpr :: Expr -> String
showExpr e = case e of
  GenExpr infx op args ->
    if infx then
        showInfixExpr op args
    else op ++ paren (intercalate "," $ map showExpr args)
  PathExpr m p -> case m of
      Nothing -> ""
      Just f -> showExpr f
    ++ show p
  FilterExpr pe ps ->
    (if isPrimExpr pe then id else paren) (showExpr pe)
    ++ concatMap showPred ps
  PrimExpr _ s -> s

{- | show arguments with minimal parens interspersed with the infix operator.
Also treat the unary minus where the argument list is a singleton.
Alphanumeric operators are shown with spaces, which looks bad for @mod@ and
@div@ in conjunction with additive, relational, or equality operators.  The
unary minus gets a leading blank if the preceding character is a
'ncNameChar'. -}
showInfixExpr :: String -> [Expr] -> String
showInfixExpr op args = case args of
  [] -> op -- cannot happen
  [arg] -> -- unary minus
    let s = showExpr arg
    in op ++ case arg of
       GenExpr True aOp _ -> case aOp of
         "|" -> s
         _ -> paren s
       _ -> s
  arg : rargs ->
    let mi = findIndex (elem op) inOps
        f = parenExpr False mi arg
        padOp = if any isAlpha op then ' ' : op ++ " " else
          if elem op addOps && not (null f) && ncNameChar (last f)
             then ' ' : op else op
    in f ++ concatMap ((padOp ++) .  parenExpr True mi) rargs

{- | put parens around arguments that have a lower precedence or
     equal precendence if they are a right argument. -}
parenExpr :: Bool -> Maybe Int -> Expr -> String
parenExpr rst mi e =
  let s = showExpr e
  in case e of
  GenExpr True op (_ : _ : _) ->
    let mj = findIndex (elem op) inOps
        putPar = case (mi, mj) of
           (Just i, Just j) -> i > j || rst && i == j
           _ -> True
    in if putPar then paren s else s
  _ -> s

-- | test if expression is primary
isPrimExpr :: Expr -> Bool
isPrimExpr e = case e of
  PrimExpr _ _ -> True
  GenExpr False _ _ -> True
  _ -> False

-- * infix operators

-- | unequal (@!=@) and equal (@=@)
eqOps :: [String]
eqOps = ["!=", "="]

-- | the four other comparisons
relOps :: [String]
relOps = ["<=", ">=", "<", ">"]

-- | @+@ and @-@, where @-@ is allowed within names and as unary operator
addOps :: [String]
addOps = ["+", "-"]

-- | @*@, div and mod, where @*@ is also used as wildcard for node names
multOps :: [String]
multOps = ["*", "div", "mod"]

{- | all infix operators. Lowest precedence for @or@ followed by @and@,
highest is union(@|@).  Only these three operators may get more than two
arguments. -}
inOps :: [[String]]
inOps =
  [ ["or"]
  , ["and"]
  , eqOps
  , relOps
  , addOps
  , multOps
  , ["|"]]

-- * parsers

-- | skip trailing spaces
skips :: Parser a -> Parser a
skips = (<< spaces)

-- | parse keyword and skip spaces
symbol :: String -> Parser String
symbol = skips . tryString

-- | skip left paren
lpar :: Parser ()
lpar = forget (symbol "(")

-- | skip right paren
rpar :: Parser ()
rpar = forget (symbol ")")

-- | non-abbreviated axis parser
axis :: Parser Axis
axis = choice (map (\ a -> symbol (showAxis a) >> return a) allAxis)
  <?> "axis"

-- | the axis specifier parser
abbrAxis :: Parser Axis
abbrAxis =
  (symbol "@" >> return Attribute)
  <|> try (axis << symbol "::")
  <|> return Child
  <?> "abbrAxis"

-- | starting name character (no unicode)
ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | name character (without @+@) including centered dot (and no other unicode)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".-_\183"

-- | non-colon xml names (non-skipping)
ncName :: Parser String
ncName = satisfy ncNameStart <:> many (satisfy ncNameChar) <?> "ncName"

-- | literal string within single or double quotes (skipping)
literal :: Parser String
literal = skips $
  char '"' <:> many (satisfy (/= '"')) <++> string "\""
  <|> char '\'' <:> many (satisfy (/= '\'')) <++> string "'"

-- | ncName or wild-card (@*@) (skipping)
localName :: Parser String
localName = symbol "*" <|> skips ncName <?> "localName"

-- | the node test parser
nodeTest :: Parser NodeTest
nodeTest = fmap PI (symbol pIS >> lpar >> literal << rpar)
  <|> choice (map (\ t -> symbol (lowerShow t)
                   >> lpar >> rpar >> return t) nodeTypes)
  <|> do
    p <- try (ncName <++> string ":")
    l <- localName
    return $ NameTest $ p ++ l
  <|> do
    l <- localName
    return $ NameTest l
  <?> "nodeTest"

-- | parent or self abbreviated steps
abbrStep :: Parser Step
abbrStep =
  (symbol ".." >> return (Step Parent Node []))
  <|> (symbol "." >> return (Step Self Node []))
  <?> "abbrStep"

-- | the predicate (expression in square brackets) parser
predicate :: Parser Expr
predicate = symbol "[" >> expr << symbol "]" <?> "predicate"

-- | the step (stuff between slashes) parser
step :: Parser Step
step = abbrStep <|> do
  a <- abbrAxis
  t <- nodeTest
  ps <- many predicate
  return (Step a t ps)
  <?> "step"

-- | the implicit @descendant-or-self::node()@ step constant
descOrSelfStep :: Step
descOrSelfStep = Step (Descendant True) Node []

-- | a double or single slash
doubleSlash :: Parser Bool
doubleSlash = (symbol "//" >> return True) <|> (symbol "/" >> return False)

{- | a step starting with a single or double slash,
     the latter yielding two steps. -}
slashStep :: Parser [Step]
slashStep = do
  b <- doubleSlash
  s <- step
  return (if b then [descOrSelfStep, s] else [s])
  <?> "slashStep"

-- | parse the steps of a relative path
relPath :: Parser [Step]
relPath = do
  s <- step
  sl <- many slashStep
  return (s : concat sl)
  <?> "relPath"

-- | a (possibly empty) absolute or (non-empty) relative path
path :: Parser Path
path = do
    m <- optionMaybe doubleSlash
    s <- (case m of
      Just False -> optionL
      _ -> id) relPath
    return (case m of
      Nothing -> Path False s
      Just b -> Path True $ if b then descOrSelfStep : s else s)
    <?> "path"

-- | at least one digit and at most one decimal point (skipping)
number :: Parser String
number = skips $ many1 digit <++> optionL (char '.' <:> many digit)
  <|> try (char '.' <:> many1 digit)

-- | a qualified name (prefixed or unprefixed)
qualName :: Parser String
qualName = skips $ ncName <++> optionL (char ':' <:> ncName)

-- | parse a primary expression (including 'fct' or 'expr' in parens)
primExpr :: Parser Expr
primExpr = fmap (PrimExpr Var) (char '$' <:> qualName)
  <|> (lpar >> expr << rpar)
  <|> fmap (PrimExpr Literal) literal
  <|> fmap (PrimExpr Number) number
  <|> fct

-- | parse a function call by checking the qname and the left paren
fct :: Parser Expr
fct = do
  q <- try $ do
    n <- qualName
    if elem n $ pIS : map lowerShow nodeTypes
      then fail $ n ++ " not allowed as function name"
      else lpar >> return n
  args <- sepBy expr (symbol ",")
  rpar
  return $ GenExpr False q args

-- | parse a filter expresssion as primary expression followed by predicates
filterExpr :: Parser Expr
filterExpr = do
  e <- primExpr
  ps <- many predicate
  return $ if null ps then e else FilterExpr e ps

{- | a path expression is either a filter expression followed by a (non-empty)
     absoulte path or an ordinary 'path'. -}
pathExpr :: Parser Expr
pathExpr = do
    f <- filterExpr
    s <- optionL $ do
      b <- doubleSlash
      r <- relPath
      return $ if b then descOrSelfStep : r else r
    return $ if null s then f else PathExpr (Just f) $ Path True s
  <|> fmap (PathExpr Nothing) path

-- | parse multiple argument expressions separated by an infix symbol
singleInfixExpr :: Parser Expr -> String -> Parser Expr
singleInfixExpr p s = do
  l <- sepBy1 p $ symbol s
  return $ case l of
    [e] -> e
    _ -> GenExpr True s l

-- | 'pathExpr' are arguments of union expression
unionExpr :: Parser Expr
unionExpr = singleInfixExpr pathExpr "|"

-- | 'unionExpr' can be prefixed by the unary minus
unaryExpr :: Parser Expr
unaryExpr = do
    symbol "-"
    e <- unaryExpr
    return $ GenExpr True "-" [e]
  <|> unionExpr

{- | parse as many arguments separated by any infix symbol as possible
     but construct left-associative binary application trees. -}
leftAssocExpr :: Parser Expr -> [String] -> Parser Expr
leftAssocExpr p ops =
  chainl1 p $ do
    op <- choice $ map symbol ops
    return $ \ a b -> GenExpr True op [a, b]

-- * all final infix parsers using 'leftAssocExpr' or 'singleInfixExpr'

multExpr :: Parser Expr
multExpr = leftAssocExpr unaryExpr multOps

addExpr :: Parser Expr
addExpr = leftAssocExpr multExpr addOps

relExpr :: Parser Expr
relExpr = leftAssocExpr addExpr relOps

eqExpr :: Parser Expr
eqExpr = leftAssocExpr relExpr eqOps

andExpr :: Parser Expr
andExpr = singleInfixExpr eqExpr "and"

-- | the top-level expressions interspersed by @or@.
expr :: Parser Expr
expr = singleInfixExpr andExpr "or"

-- * checking sanity of paths

data PrincipalNodeType
  = TAttribute
  | TNamespace
  | TElement deriving Eq

principalNodeType :: Axis -> PrincipalNodeType
principalNodeType a = case a of
  Attribute -> TAttribute
  Namespace -> TNamespace
  _ -> TElement

-- | may this step have further steps
isElementNode :: Step -> Bool
isElementNode (Step a t _) =
  principalNodeType a == TElement && case t of
  Node -> True
  NameTest _ -> True
  _ -> False

isLegalPath :: [Step] -> Bool
isLegalPath l = case l of
  [] -> True
  [_] -> True
  s : r -> isElementNode s && isLegalPath r

finalStep :: Path -> Maybe Step
finalStep (Path _ l) = case l of
  [] -> Nothing
  _ -> Just $ last l

finalPrincipalNodeType :: Path -> PrincipalNodeType
finalPrincipalNodeType p = case finalStep p of
  Nothing -> TElement
  Just (Step a _ _) -> principalNodeType a

data BasicType
  = NodeSet
  | Boolean
  | Numeral
  | String
  | Object

coreFcts :: [(String, (BasicType, [BasicType]))]
coreFcts =
  [ ("last", (Numeral, []))
  , ("position", (Numeral, []))
  , ("count", (Numeral, [NodeSet]))
  , ("id", (NodeSet, [Object]))
  , ("local-name", (String, [NodeSet]))
  , ("namespace-uri", (String, [NodeSet]))
  , ("name", (String, [NodeSet]))
  , ("string", (String, [Object]))
  , ("concat", (String, [String, String]))
  , ("substring-before", (String, [String, String]))
  , ("substring-after", (String, [String, String]))
  , ("substring", (String, [String, Numeral, Numeral]))
  , ("starts-with", (Boolean, [String, String]))
  , ("contains", (Boolean, [String, String]))
  , ("string-length", (Numeral, [String]))
  , ("normalize-space", (String, [String]))
  , ("translate", (String, [String, String, String]))
  , ("boolean", (Boolean, [Object]))
  , ("not", (Boolean, [Boolean]))
  , ("true", (Boolean, []))
  , ("false", (Boolean, []))
  , ("lang", (Boolean, [String]))
  , ("number", (Numeral, [Object]))
  , ("sum", (Numeral, [NodeSet]))
  , ("floor", (Numeral, [Numeral]))
  , ("ceiling", (Numeral, [Numeral]))
  , ("round", (Numeral, [Numeral]))
  ]

basicType :: Expr -> BasicType
basicType e = case e of
  GenExpr infx op _ ->
    if infx then case op of
       "|" -> NodeSet
       _ | elem op $ ["or", "and"] ++ eqOps ++ relOps -> Boolean
         | elem op $ addOps ++ multOps -> Numeral
       _ -> Object
    else case lookup op coreFcts of
           Just (t, _) -> t
           Nothing -> Object
  PrimExpr k _ -> case k of
    Number -> Numeral
    Literal -> String
    Var -> Object
  _ -> NodeSet

isPathExpr :: Expr -> Bool
isPathExpr e = case e of
  GenExpr True "|" args -> all isPathExpr args
  GenExpr False "id" [_] -> True
  PrimExpr Var _ -> True
  PathExpr m (Path _ s) -> isLegalPath s && maybe True isPathExpr m
  FilterExpr p _ -> isPathExpr p
  _ -> False

-- | parse string and perform sanity check
maybePath :: String -> Maybe Expr
maybePath s = case parse (expr << eof) "" s of
  Right e | isPathExpr e -> Just e
  _ -> Nothing
