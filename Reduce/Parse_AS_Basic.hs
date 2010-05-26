{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for reduce computer algebra system
-}

module Reduce.Parse_AS_Basic
    where

import qualified Common.AnnoState as AnnoState
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Common.Parsec

import Reduce.AS_BASIC_Reduce
import Reduce.Keywords
import Text.ParserCombinators.Parsec

-- the basic lexer, test using e.g. runParser identifier 0 "" "asda2_3"

-- ---------------------------------------------------------------------------
-- ------------------------- Parser for Expressions --------------------------
-- ---------------------------------------------------------------------------

{- | parsing of identifiers. an identifier is a letter followed by
     letters, numbers, or _, but not a keyword -}
identifier :: CharParser st Id.Token
identifier =
  lexemeParser (Lexer.pToken $ reserved allKeywords Lexer.scanAnyWords)

prefixidentifier :: CharParser st Id.Token
prefixidentifier = lexemeParser (Lexer.pToken Lexer.scanAnyWords)

-- | parser for numbers (both integers and floats) without signs
number :: CharParser st Id.Token
number = Lexer.pToken Lexer.scanFloat

-- | parses a possibly signed number
signednumber :: CharParser st EXPRESSION
signednumber =
    do
      nr <- number
      return $ if isFloating nr
        then Double (read (tokStr nr)) (tokPos nr)
        else Int (read (tokStr nr)) (tokPos nr)
    <|>
    do
      Lexer.keySign (string "-")
      nr <- number
      return $ if isFloating nr
        then Double (-1 * read (tokStr nr)) (tokPos nr)
        else Int (-1 * read (tokStr nr)) (tokPos nr)

expression :: CharParser st EXPRESSION
expression = do
  exp1 <- factor
  exps <- many
    $ pair (lexemeParser (Lexer.keySign $ string "+" <|> string "-")) factor
  if null exps then return exp1
     else return $ foldr (\ a b -> Op (fst a) [b, snd a] nullRange) exp1 exps
  <|>
  listexp

-- | parse a product of basic expressions
factor :: CharParser st EXPRESSION
factor = do
  exp1 <- expexp
  exps <- many
    $ pair (lexemeParser (Lexer.keySign $ string "*" <|> string "/")) factor
  if null exps then return exp1
     else return $ foldr (\ a b -> Op (fst a) [b, snd a] nullRange) exp1 exps

-- | parse a sequence of exponentiations
expexp :: CharParser st EXPRESSION
expexp = do
  exp1 <- expatom
  exps <- many
    $ pair (lexemeParser (Lexer.keySign $ tryString "**" <|> string "^")) expexp
  if null exps then return exp1
    else return $ foldr (\ a b -> Op (fst a) [b, snd a] nullRange) exp1 exps


-- | parse a basic expression
expatom :: CharParser st EXPRESSION
expatom = signednumber
  <|>
  do
    ident <- identifier
    return (Var ident)
  <|>
  do
    oParenT
    expr <- expression
    cParenT
    return expr
  <|>
  do 
    ident <- prefixidentifier
    oParenT
    exps <- Lexer.separatedBy expression (Lexer.keySign (string ","))
    cParenT
    return (Op (tokStr ident) (fst exps) nullRange)

-- | parses a list expression
listexp :: CharParser st EXPRESSION
listexp = do
  (Lexer.keySign (string "{"))
  elems <- Lexer.separatedBy formulaorexpression (Lexer.keySign (string ","))
  (Lexer.keySign (string "}"))
  return (List (fst elems) nullRange)


-----------------------------------------------------------------------------
---------------------------- parser for formulas ----------------------------
-----------------------------------------------------------------------------

parseVarList :: CharParser st EXPRESSION
parseVarList = do
  Lexer.keySign (string "{")
  elems <- Lexer.separatedBy identifier (Lexer.keySign (string ","))
  Lexer.keySign (string "}")
  return (List (map Var $ fst elems) nullRange)

parseVar :: CharParser st EXPRESSION
parseVar = do
  ident <- identifier
  return (Var ident)


existsFormula :: CharParser st EXPRESSION
existsFormula = do
      Lexer.keySign (string "ex")
      oParenT
      vars <- ( parseVar <|> parseVarList)
      Lexer.keySign (string ",")
      expr <- formulaorexpression
      cParenT
      return (Op "ex" [vars, expr] nullRange)

forallFormula :: CharParser st EXPRESSION
forallFormula = do
      Lexer.keySign (string "all")
      oParenT
      vars <- parseVar <|> parseVarList
      Lexer.keySign (string ",")
      expr <- formulaorexpression
      cParenT
      return (Op "all" [vars, expr] nullRange)


-- | parser for atoms
truefalseFormula :: CharParser st EXPRESSION
truefalseFormula =
    do
      lexemeParser (Lexer.keyWord (tryString "true"))
      return (Op "True" [] nullRange)
    <|>
    do
      lexemeParser (Lexer.keyWord (tryString "false"))
      return (Op "False" [] nullRange)
    <|>
    existsFormula
    <|>
    forallFormula

-- | parser for predicates
predFormula :: CharParser st EXPRESSION
predFormula =
    do
      exp1 <- expression
      op <- lexemeParser (Lexer.keySign $ tryString "<=" <|> tryString ">=")
        <|> lexemeParser (single (oneOf "=<>"))
      exp2 <- expression
      return (Op op [exp1, exp2] nullRange)

atomicFormula :: CharParser st EXPRESSION
atomicFormula = truefalseFormula <|> predFormula <|> parenFormula

-- | parser for formulas
aFormula :: CharParser st EXPRESSION
aFormula = try negFormula <|> impOrFormula

-- | parser for symbols followed by whitechars
lexemeParser :: CharParser st a -> CharParser st a
lexemeParser = (<< skip)

negFormula :: CharParser st EXPRESSION
negFormula = do
  lexemeParser (Lexer.keyWord (tryString "not"))
  f <- atomicFormula
  return (Op "Not" [f] nullRange)

-- | parses a formula within brackets
parenFormula :: CharParser st EXPRESSION
parenFormula = do
  lexemeParser oParenT
  f <- aFormula
  lexemeParser cParenT
  return f

-- | parser for implications and ors (same precedence)
impOrFormula :: CharParser st EXPRESSION
impOrFormula = do
  f1 <- andFormula
  opfs <- many $ pair (lexemeParser $ Lexer.keyWord
                      $ tryString "or" <|> tryString "impl") impOrFormula
  if null opfs then return f1
   else return $ foldr (\ (a1, a2) b -> Op (case a1 of
                                   "or" -> "or"
                                   "impl" -> "impl"
                                   _ -> error "impl or or expected")
                                    [b, a2] nullRange
                                 ) f1 opfs

-- | a parser for and sequence of and formulas
andFormula :: CharParser st EXPRESSION
andFormula = do
  f1 <- atomicFormula
  opfs <- many $ pair (lexemeParser $ keyWord $ tryString "and") atomicFormula
  if null opfs then return f1
   else return $ foldr (\ a b -> (Op "and" [b, snd a] nullRange)) f1 opfs

-- ---------------------------------------------------------------------------
-- -------------------------- Parser for Commands ----------------------------
-- ---------------------------------------------------------------------------

formulaorexpression :: CharParser st EXPRESSION
formulaorexpression = try aFormula <|> expression

-- | parser for commands
command :: CharParser st CMD
command = do
  cmd <- lexemeParser $ Lexer.keyWord $ choice $ map tryString
    ["solve", "simplify", "divide", "int", "rlqe", "factorize"]
  oParenT
  arg1 <- formulaorexpression
  args <- many $ pair (lexemeParser $ string ",") formulaorexpression
  cParenT
  return (Cmd cmd (arg1 : map snd args))
  <|>
  do
    ident <- identifier
    op <- tryString ":="
    exp <- expression
    return (Cmd ":=" [(Var ident),exp])
  <|>
  repeatExpr

repeatExpr :: CharParser st CMD
repeatExpr = do
  cmd <- (lexemeParser (tryString "repeat"))
  statements <- Lexer.separatedBy command (lexemeParser (Lexer.keySign (string ";")))
  skip
  until <- tryString "until"
  skip
  convergence <- tryString "convergence"
  oParenT
  accuracy <- expression
  lexemeParser $ tryString ","
  var <- expression
  cParenT
  return (Repeat accuracy var (fst statements))

-----------------------------------------------------------------------------
--------------------------- parser spec entries. ----------------------------
-----------------------------------------------------------------------------

-- | parser for operator declarations: example: operator a,b,c
opItem :: CharParser st OP_ITEM
opItem = do
  Lexer.keySign (lexemeParser (tryString "operator"))
  var1 <- identifier
  vars <- many $ pair (lexemeParser $ string ",") identifier
  return (Op_item (var1 : map snd vars) nullRange)


-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  fmap Basic_spec (AnnoState.annosParser parseBasicItems)
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AnnoState.AParser st BASIC_ITEMS
parseBasicItems = parseOpDecl <|> parseAxItems

-- | parser for predicate declarations
parseOpDecl :: AnnoState.AParser st BASIC_ITEMS
parseOpDecl = fmap Op_decl opItem

-- | parser for Axiom_item
parseAxItems :: AnnoState.AParser st BASIC_ITEMS
parseAxItems = do
  AnnoState.dotT
  cmd <- (AnnoState.allAnnoParser command)
  return $ Axiom_item cmd


-- ---------------------------------------------------------------------------
-- ---------------------- parser for symbol maps etc. ------------------------
-- ---------------------------------------------------------------------------

-- | parsing a prop symbol
symb :: GenParser Char st SYMB
symb = fmap Symb_id identifier


-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = do
  s <- symb
  do f <- pToken $ toKey mapsTo
     t <- symb
     return (Symb_map s t $ tokPos f)
    <|> return (Symb s)

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([SYMB], [Token])
symbs = do
       s <- symb
       do c <- commaT `followedWith` symb
          (is, ps) <- symbs
          return (s : is, c : ps)
         <|> return ([s], [])

-- | parse a list of symbol mappings
symbMapItems :: GenParser Char st SYMB_MAP_ITEMS
symbMapItems = do
  (is, ps) <- symbMaps
  return (Symb_map_items is $ catRange ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps = do
  s <- symbMap
  do c <- commaT `followedWith` symb
     (is, ps) <- symbMaps
     return (s : is, c : ps)
    <|> return ([s], [])

parseResult :: String -> Maybe EXPRESSION
parseResult inp = case runParser formulaorexpression "" "" inp of
               Left _ -> Nothing
               Right s -> Just s
