{- |
Module      :  $Header$
Description :  XPath utilities
Copyright   :  (c) Christian Maeder, DFKI GmbH 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

XPath utilities independent of xml package
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

showAxis :: Axis -> String
showAxis a =
  let s = map toLower . takeWhile isAlpha $ show a
      orSelf b = if b then s ++ "-or-self" else s
      sibl b = if b then s ++ "-sibling" else s
  in case a of
  Ancestor c -> orSelf c
  Descendant c -> orSelf c
  Following c -> sibl c
  Preceding c -> sibl c
  _ -> s

data NodeTest
  = NameTest String -- possibly containing colon
  | PrefixTest String
  | PINode String
  | NodeTest
  | CommentNode
  | TextNode

pIS :: String
pIS = "processing-instruction"

nodeS :: String
nodeS = "node"

commentS :: String
commentS = "comment"

textS :: String
textS = "text"

paren :: String -> String
paren = ('(' :) . (++ ")")

showNodeTest :: NodeTest -> String
showNodeTest t = let
  b = (++ paren "")
  in case t of
  NameTest s -> if null s then "*" else s
  PrefixTest p -> p ++ ":*"
  PINode s -> pIS ++ paren s
  NodeTest -> b nodeS
  CommentNode -> b commentS
  TextNode -> b textS

data Step = Step Axis NodeTest [Expr]

showStep :: Step -> String
showStep (Step a n ps) =
  showAxis a ++ "::" ++ showNodeTest n ++ concatMap showPred ps

data Path = Path Bool [Step] -- absolute? or relative

showPath :: Path -> String
showPath (Path abso sts) =
  if abso then concatMap (('/' :) . showStep) sts
     else intercalate "/" $ map showStep sts

data PrimKind
  = Var -- leading dollar
  | Literal -- single or double quotes
  | Number -- digits possible with decimal point

data Expr
  = GenExpr Bool String [Expr] -- infix
  | PathExpr Path
  | FilterExpr Expr [Expr] [Step]
  | PrimExpr PrimKind String

showPred :: Expr -> String
showPred e = '[' : showExpr e ++ "]"

showExpr :: Expr -> String
showExpr e = case e of
  GenExpr infx op args ->
    if infx then
        showInfixExpr op args
    else op ++ paren (intercalate "," $ map showExpr args)
  PathExpr p -> showPath p
  FilterExpr pe ps sts ->
    (if isPrimExpr pe then id else paren) (showExpr e)
    ++ concatMap showPred ps
    ++ showPath (Path True sts)
  PrimExpr _ s -> s

isPrimExpr :: Expr -> Bool
isPrimExpr e = case e of
  PrimExpr _ _ -> True
  GenExpr False _ _ -> True
  _ -> False

inOps :: [[String]]
inOps =
  [ ["or"]
  , ["and"]
  , ["!=", "="]
  , ["<=", ">=", "<", ">"]
  , ["+", "-"]
  , ["*", "div", "mod"]
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
        padOp = if op == "|" then op else ' ' : op ++ " "
    in parenExpr False mi arg
       ++ concatMap ((padOp ++) .  parenExpr True mi) rargs

parenExpr :: Bool -> Maybe Int -> Expr -> String
parenExpr rst mi e =
  let s = showExpr e
  in case e of
  GenExpr True op _ ->
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

lpar, rpar, lbra, rbra, slash, dslash :: Parser ()

lpar   = forget (symbol "(")
rpar   = forget (symbol ")")
lbra   = forget (symbol "[")
rbra   = forget (symbol "]")
slash  = forget (symbol "/")
dslash = forget (symbol "//")

axis :: Parser Axis
axis = choice $ map (\ a -> symbol (showAxis a) >> return a) allAxis

abbrAxis :: Parser Axis
abbrAxis =
  (symbol "@" >> return Attribute)
  <|> try (axis << symbol "::")
  <|> return Child

ncNameStart :: Char -> Bool
ncNameStart c = isAlpha c || c == '_'

-- | rfc3987 plus '+' from scheme (scheme does not allow the dots)
ncNameChar :: Char -> Bool
ncNameChar c = isAlphaNum c || elem c ".+-_\183"

ncName :: Parser String
ncName = satisfy ncNameStart <:> many (satisfy ncNameChar)

literal :: Parser String
literal =
  char '"' <:> many (satisfy (/= '"')) <++> string "\""
  <|> char '\'' <:> many (satisfy (/= '\'')) <++> string "'"

nodeTest :: Parser NodeTest
nodeTest = fmap PINode (symbol pIS >> lpar >> literal << rpar)
  <|> choice (map (\ t -> symbol (takeWhile isAlpha $ showNodeTest t)
                          >> lpar >> rpar >> return t)
              [NodeTest, CommentNode, TextNode])
  <|> (symbol "*" >> return (NameTest ""))
  <|> do
    n <- ncName
    (symbol ":*" >> return (PrefixTest n))
      <|> fmap (NameTest . (n ++)) (option "" $ char ':' <:> ncName)
