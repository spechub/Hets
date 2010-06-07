{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for CSL
-}

module CSL.Parse_AS_Basic ( parseBasicSpec
                          , parseSymbItems
                          , parseSymbMapItems
                          , parseResult
                          , expression
                          , command
                          , aFormula
                          , parseBasicItems
                          , parseOpDecl
                          , parseAxItems
                          , basicSpec
                          , signednumber
                          , oneOfKeys
                          , extparam
                          )
    where

import qualified Common.AnnoState as AnnoState
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Common.Parsec

import CSL.AS_BASIC_CSL
import CSL.Keywords
import Text.ParserCombinators.Parsec

-- the basic lexer, test using e.g. runParser identifier 0 "" "asda2_3"


-- ---------------------------------------------------------------------------

-- * Interface to the syntax class

-- ---------------------------------------------------------------------------

parseBasicSpec :: Maybe (AnnoState.AParser st BASIC_SPEC)
parseBasicSpec = Just basicSpec
parseSymbItems :: Maybe (GenParser Char st SYMB_ITEMS)
parseSymbItems = Just symbItems
parseSymbMapItems :: Maybe (GenParser Char st SYMB_MAP_ITEMS)
parseSymbMapItems = Just symbMapItems


-- ---------------------------------------------------------------------------

-- * Parser utils

-- ---------------------------------------------------------------------------

pComma :: CharParser st String
pComma = lexemeParser $ Lexer.keySign $ string ","

lstring :: String -> CharParser st String
lstring = lexemeParser . string

-- | parser for symbols followed by whitechars
lexemeParser :: CharParser st a -> CharParser st a
lexemeParser = (<< skip)

-- ---------------------------------------------------------------------------

-- * Parser for Expressions

-- ---------------------------------------------------------------------------

mkOp :: String -> [EXPRESSION] -> EXPRESSION
mkOp s el = Op s [] el nullRange

{- | parsing of identifiers. an identifier is a letter followed by
     letters, numbers, or _, but not a keyword -}
identifier :: CharParser st Id.Token
identifier =
  lexemeParser $ Lexer.pToken $ reserved allKeywords Lexer.scanAnyWords

prefixidentifier :: CharParser st Id.Token
prefixidentifier =
    lexemeParser $ Lexer.pToken $ Lexer.scanAnySigns <|> Lexer.scanAnyWords

-- | parser for numbers (both integers and floats) without signs
number :: CharParser st Id.Token
number = Lexer.pToken Lexer.scanFloat

-- | parses a possibly signed number
signednumber :: CharParser st EXPRESSION
signednumber = do
    (sign, nr) <- pair (option "" $ Lexer.keySign (string "-")) number
    return $ if isFloating nr
             then Double (read (sign ++ tokStr nr)) (tokPos nr)
             else Int (read (sign ++ tokStr nr)) (tokPos nr)

oneOfKeys :: [String] -> CharParser st String
oneOfKeys l = lexemeParser $ Lexer.keySign $ choice $ map tryString l

expression :: CharParser st EXPRESSION
expression = do
  exp1 <- factor
  exps <- many
    $ pair (oneOfKeys ["+", "-"]) factor
  if null exps then return exp1
     else return $ foldr (\ a b -> mkOp (fst a) [b, snd a]) exp1 exps
  <|>
  listexp

-- | parse a product of basic expressions
factor :: CharParser st EXPRESSION
factor = do
  exp1 <- expexp
  exps <- many
    $ pair (oneOfKeys ["*", "/"]) factor
  if null exps then return exp1
     else return $ foldr (\ a b -> mkOp (fst a) [b, snd a]) exp1 exps

-- | parse a sequence of exponentiations
expexp :: CharParser st EXPRESSION
expexp = do
  exp1 <- expatom
  exps <- many
    $ pair (oneOfKeys ["**", "^"]) expexp
  if null exps then return exp1
    else return $ foldr (\ a b -> mkOp (fst a) [b, snd a]) exp1 exps

-- | parse a basic expression
expatom :: CharParser st EXPRESSION
expatom = signednumber <|> (oParenT >> expression << cParenT) <|> expsymbol

expsymbol :: CharParser st EXPRESSION
expsymbol = 
    do 
      ident <- prefixidentifier  -- EXTENDED
      ep <- option ([],[])
            $ oBracketT >> Lexer.separatedBy extparam pComma << cBracketT
      exps <- option ([],[])
              $ oParenT >> Lexer.separatedBy formulaorexpression pComma
                    << cParenT
      return $ Op (tokStr ident) (fst ep) (fst exps) nullRange


-- | parses a list expression
listexp :: CharParser st EXPRESSION
listexp = do
  (Lexer.keySign (string "{"))
  elems <- Lexer.separatedBy formulaorexpression pComma
  (Lexer.keySign (string "}"))
  return (List (fst elems) nullRange)

-- ---------------------------------------------------------------------------

-- ** parser for extended parameter, e.g., [I=0,...]

-- ---------------------------------------------------------------------------

extparam :: CharParser st EXTPARAM
extparam = do
  i <- identifier
  pair (oneOfKeys ["=", "<=", ">=", "!=", "<", ">"]) expression >--> EP i

-- ---------------------------------------------------------------------------

-- * parser for formulas

-- ---------------------------------------------------------------------------

parseVarList :: CharParser st EXPRESSION
parseVarList = do
  Lexer.keySign (string "{")
  elems <- Lexer.separatedBy parseVar pComma
  Lexer.keySign (string "}")
  return (List (fst elems) nullRange)

parseVar :: CharParser st EXPRESSION
parseVar = do
  ident <- identifier
  return (Var ident)



quantFormula :: String -> CharParser st EXPRESSION
quantFormula q = do
  Lexer.keySign (string q)
  oParenT
  vars <- ( parseVar <|> parseVarList)
  pComma
  expr <- formulaorexpression
  cParenT
  return (mkOp q [vars, expr])


-- | parser for atoms
truefalseFormula :: CharParser st EXPRESSION
truefalseFormula =
    do
      lexemeParser (Lexer.keyWord (tryString "true"))
      return (mkOp "True" [])
    <|>
    do
      lexemeParser (Lexer.keyWord (tryString "false"))
      return (mkOp "False" [])
    <|> quantFormula "ex" <|> quantFormula "all"

-- | parser for predicates
predFormula :: CharParser st EXPRESSION
predFormula = do
  exp1 <- expression
  mExp2 <- optionMaybe
           $ pair (oneOfKeys ["<=", ">=", "!="]
                   <|> lexemeParser (single $ oneOf "=<>")) expression
  case mExp2 of
    Just (op, exp2) -> return $ mkOp op [exp1, exp2]
    _ -> return $ exp1

atomicFormula :: CharParser st EXPRESSION
atomicFormula = truefalseFormula <|> predFormula <|> parenFormula

-- | parser for formulas
aFormula :: CharParser st EXPRESSION
aFormula = try negFormula <|> impOrFormula

negFormula :: CharParser st EXPRESSION
negFormula = do
  lexemeParser (Lexer.keyWord (tryString "not"))
  f <- atomicFormula
  return (mkOp "Not" [f])

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
   else return $ foldr (\ (a1, a2) b -> mkOp (case a1 of
                                   "or" -> "or"
                                   "impl" -> "impl"
                                   _ -> error "impl or or expected")
                                    [b, a2]
                                 ) f1 opfs

-- | a parser for and sequence of and formulas
andFormula :: CharParser st EXPRESSION
andFormula = do
  f1 <- atomicFormula
  opfs <- many $ pair (lexemeParser $ keyWord $ tryString "and") atomicFormula
  if null opfs then return f1
   else return $ foldr (\ a b -> (mkOp "and" [b, snd a])) f1 opfs

-- ---------------------------------------------------------------------------

-- * Parser for Commands

-- ---------------------------------------------------------------------------

formulaorexpression :: CharParser st EXPRESSION
formulaorexpression = try aFormula <|> expression

-- | parser for commands
command :: CharParser st CMD
command = reduceCommand <|> try assignment <|> repeatExpr <|> constraint

reduceCommand :: CharParser st CMD
reduceCommand = do
  cmd <- lexemeParser $ Lexer.keyWord $ choice $ map tryString
         ["solve", "simplify", "divide", "int", "rlqe", "factorize"]
  oParenT
  arg1 <- formulaorexpression
  args <- many $ pComma >> formulaorexpression
  cParenT
  return $ Cmd cmd $ arg1 : args

assignment :: CharParser st CMD
assignment = do
  ident <- expsymbol
  lexemeParser $ tryString ":="
  exp' <- expression
  return $ Cmd ":=" [ident, exp']

constraint :: CharParser st CMD
constraint = do
  exp' <- try aFormula
  case exp' of
    Op _ _ _ _ ->
        return $ Cmd "constraint" [exp']
    _ -> fail "Malformed constraint"


repeatExpr :: CharParser st CMD
repeatExpr = do
  lexemeParser $ string "repeat"
  statements <- Lexer.separatedBy command $ lstring ";"
  lstring "until"
  cstr <- aFormula
  return $ Repeat cstr $ fst statements

-- ---------------------------------------------------------------------------

-- * parser spec entries

-- ---------------------------------------------------------------------------

-- | parser for operator declarations: example: operator a,b,c
opItem :: CharParser st OP_ITEM
opItem = do
  Lexer.keySign (lexemeParser (tryString "operator"))
  var1 <- identifier
  vars <- many $ pair pComma identifier
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

-- * parser for symbol maps etc.

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
