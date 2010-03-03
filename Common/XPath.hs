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
import Common.Lexer
import Data.Char
import Data.List

data Axis
  = Ancestor Bool -- or self?
  | Attribute
  | Child
  | Descendant Bool -- or self?
  | Following Bool -- sibling?
  | Namespace
  | Parent
  | Preceding Bool -- sibling?
  | Self deriving (Eq, Ord, Show)

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

lowerShow :: Show a => a -> String
lowerShow = map toLower . show

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
  = NameTest String String -- prefix and local part (possibly *)
  | PINode String
  | Node
  | Comment
  | Text
    deriving Show

nodeTypes :: [NodeTest]
nodeTypes = [Node, Comment, Text]

pIS :: String
pIS = "processing-instruction"

paren :: String -> String
paren = ('(' :) . (++ ")")

showNodeTest :: NodeTest -> String
showNodeTest t = case t of
  NameTest p l -> (if null p then "" else p ++ ":") ++ l
  PINode s -> pIS ++ paren s
  _ -> lowerShow t ++ paren ""

data Step = Step Axis NodeTest [Expr]

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

isDescOrSelfNode :: Step -> Bool
isDescOrSelfNode (Step a n _) = case (a, n) of
  (Descendant True, Node) -> True
  _ -> False

data Path = Path Bool [Step] -- absolute? or relative

showSteps :: Bool -> [Step] -> String
showSteps abso sts = let h = if abso then "/" else "" in case sts of
  [] -> h
  s : r -> let f = h ++ showStep s in case r of
    [] -> f
    _ -> if abso && isDescOrSelfNode s then "//" ++ showSteps False r
         else f ++ showSteps True r

showPath :: Path -> String
showPath (Path abso sts) = showSteps abso sts

data PrimKind
  = Var -- leading dollar
  | Literal -- single or double quotes
  | Number -- digits possible with decimal point

data Expr
  = GenExpr Bool String [Expr] -- infix
  | PathExpr (Maybe Expr) Path
  | FilterExpr Expr [Expr]
  | PrimExpr PrimKind String

showPred :: Expr -> String
showPred e = '[' : showExpr e ++ "]"

showExpr :: Expr -> String
showExpr e = case e of
  GenExpr infx op args ->
    if infx then
        showInfixExpr op args
    else op ++ paren (intercalate "," $ map showExpr args)
  PathExpr m p -> case m of
      Nothing -> ""
      Just f -> showExpr f
    ++ showPath p
  FilterExpr pe ps ->
    (if isPrimExpr pe then id else paren) (showExpr e)
    ++ concatMap showPred ps
  PrimExpr _ s -> s

isPrimExpr :: Expr -> Bool
isPrimExpr e = case e of
  PrimExpr _ _ -> True
  GenExpr False _ _ -> True
  _ -> False

eqOps :: [String]
eqOps = ["!=", "="]

relOps :: [String]
relOps = ["<=", ">=", "<", ">"]

addOps :: [String]
addOps = ["+", "-"]

multOps :: [String]
multOps = ["*", "div", "mod"]

inOps :: [[String]]
inOps =
  [ ["or"]
  , ["and"]
  , eqOps
  , relOps
  , addOps
  , multOps
  , ["|"]]

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

tryStr :: String -> Parser String
tryStr = try . string

skips :: Parser a -> Parser a
skips = (<< spaces)

symbol :: String -> Parser String
symbol = skips . tryStr

lpar :: Parser ()
lpar = forget (symbol "(")

rpar :: Parser ()
rpar = forget (symbol ")")

axis :: Parser Axis
axis = choice (map (\ a -> tryStr (showAxis a) >> return a) allAxis)
  <?> "axis"

abbrAxis :: Parser Axis
abbrAxis =
  (char '@' >> return Attribute)
  <|> try (axis << tryStr "::")
  <|> return Child
  <?> "abbrAxis"

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | name character (without '+')
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".-_\183"

ncName :: Parser String
ncName = satisfy ncNameStart <:> many (satisfy ncNameChar) <?> "ncName"

literal :: Parser String
literal = skips $
  char '"' <:> many (satisfy (/= '"')) <++> string "\""
  <|> char '\'' <:> many (satisfy (/= '\'')) <++> string "'"

localName :: Parser String
localName = symbol "*" <|> skips ncName <?> "localName"

nodeTest :: Parser NodeTest
nodeTest = fmap PINode (symbol pIS >> lpar >> literal << rpar)
  <|> choice (map (\ t -> symbol (lowerShow t)
                   >> lpar >> rpar >> return t) nodeTypes)
  <|> do
    p <- try (ncName << char ':')
    l <- localName
    return $ NameTest p l
  <|> do
    l <- localName
    return $ NameTest "" l
  <?> "nodeTest"

abbrStep :: Parser Step
abbrStep =
  (tryStr ".." >> return (Step Parent Node []))
  <|> (char '.' >> return (Step Self Node []))
  <?> "abbrStep"

predicate :: Parser Expr
predicate = symbol "[" >> expr << symbol "]" <?> "predicate"

step :: Parser Step
step = abbrStep <|> do
  a <- abbrAxis
  t <- nodeTest
  ps <- many predicate
  return (Step a t ps)
  <?> "step"

descOrSelfStep :: Step
descOrSelfStep = Step (Descendant True) Node []

doubleSlash :: Parser Bool
doubleSlash = (tryStr "//" >> return True) <|> (char '/' >> return False)

slashStep :: Parser [Step]
slashStep = do
  b <- doubleSlash
  s <- step
  return (if b then [descOrSelfStep, s] else [s])
  <?> "slashStep"

relPath :: Parser [Step]
relPath = do
  s <- step
  sl <- many slashStep
  return (s : concat sl)
  <?> "relPath"

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

number :: Parser String
number = skips $ many1 digit <++> optionL (char '.' <:> many digit)
  <|> char '.' <:> many1 digit

primExpr :: Parser Expr
primExpr = fmap (PrimExpr Var) (skips $ char '$' <:> ncName)
  <|> (lpar >> expr << rpar)
  <|> fmap (PrimExpr Literal) literal
  <|> fmap (PrimExpr Number) number
  <|> fct

fct :: Parser Expr
fct = do
  q <- try $ do
    n <- skips $ ncName <++> optionL (char ':' <:> ncName)
    if elem n $ pIS : map lowerShow nodeTypes
      then fail $ n ++ " not allowed as function name"
      else lpar >> return n
  args <- sepBy expr (symbol ",")
  rpar
  return $ GenExpr False q args

filterExpr :: Parser Expr
filterExpr = do
  e <- primExpr
  ps <- many predicate
  return $ if null ps then e else FilterExpr e ps

pathExpr :: Parser Expr
pathExpr = do
    f <- filterExpr
    s <- optionL $ do
      b <- doubleSlash
      r <- relPath
      return $ if b then descOrSelfStep : r else r
    return $ if null s then f else PathExpr (Just f) $ Path True s
  <|> fmap (PathExpr Nothing) path

singleInfixExpr :: Parser Expr -> String -> Parser Expr
singleInfixExpr p s = do
  l <- sepBy1 p $ symbol s
  return $ case l of
    [e] -> e
    _ -> GenExpr True s l

unionExpr :: Parser Expr
unionExpr = singleInfixExpr pathExpr "|"

unaryExpr :: Parser Expr
unaryExpr = do
    symbol "-"
    e <- unaryExpr
    return $ GenExpr True "-" [e]
  <|> unionExpr

leftAssocExpr :: Parser Expr -> [String] -> Parser Expr
leftAssocExpr p ops =
  chainl1 p $ do
    op <- choice $ map symbol ops
    return $ \ a b -> GenExpr True op [a, b]

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

expr :: Parser Expr
expr = singleInfixExpr andExpr "or"
