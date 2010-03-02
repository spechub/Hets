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
import qualified Common.AS_Annotation as Annotation
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Control.Monad

import Reduce.AS_BASIC_Reduce
import Reduce.Keywords
import Text.ParserCombinators.Parsec

-- the basic lexer, test using e.g. runParser identifier 0 "" "asda2_3"

-----------------------------------------------------------------------------
--------------------------- Parser for Expressions --------------------------
-----------------------------------------------------------------------------

-- | parsing of identifiers. an identifier is a letter followed by letters/numbers/_, but not a keyword
identifier :: CharParser st Id.Token
identifier = Lexer.pToken $ Lexer.reserved allKeywords Lexer.scanAnyWords

-- | parser for numbers (both integers and floats) without signs
number :: CharParser st Id.Token
number = Lexer.pToken Lexer.scanFloat

expression :: CharParser st EXPRESSION
expression = do
  exp1 <- factor
  exps <- many $ liftM2 (,) (Lexer.keySign (string "+" <|> string "-")) factor
  if null exps then return exp1  
     else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps
  <|>
  listexp

-- | parse a product of basic expressions
factor :: CharParser st EXPRESSION
factor = do
  exp1 <- expexp 
  exps <- many $ liftM2 (,) (Lexer.keySign (string "*" <|> string "/")) factor
  if null exps then return exp1  
     else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps

-- | parse a sequence of exponentiations
expexp :: CharParser st EXPRESSION
expexp = do
  exp1 <- expatom 
  exps <- many $ liftM2 (,) (Lexer.keySign (string "**" <|> string "^")) expexp
  if null exps then return exp1  
    else return $ foldr (\ a b -> (Op (fst a) [b,(snd a)] nullRange)) exp1 exps
  
         
-- | parse a basic expression
expatom :: CharParser st EXPRESSION
expatom = do
  nr <- number
  if (isFloating nr) then return (Double (read (tokStr nr)) (tokPos nr))
     else return (Int (read (tokStr nr)) (tokPos nr))
  <|> 
  do
    id <- identifier
    return (Var id)
  <|>
  do
    oParenT
    exp <- expression
    cParenT
    return exp

-- | parses a list expression
listexp :: CharParser st EXPRESSION
listexp = do
  (Lexer.keySign (string "{"))
  elems <- Lexer.separatedBy expression  (Lexer.keySign (string ","))
  (Lexer.keySign (string "}"))
  return (List (fst elems) nullRange)



-----------------------------------------------------------------------------
---------------------------- parser for formulas ----------------------------
-----------------------------------------------------------------------------

-- | parser for atoms
truefalseFormula :: CharParser st EXPRESSION
truefalseFormula = 
    do 
      (lexemeParser (Lexer.keySign (string "true")))
      return (Op "True" [] nullRange)
    <|> 
    do
      (lexemeParser (Lexer.keySign (string "false")))
      return (Op "False" [] nullRange)

-- | parser for predicates
predFormula :: CharParser st EXPRESSION
predFormula =
    do
      exp1 <- expression
      op <- (Lexer.keySign (try (string "<=") <|> try (string ">=") <|> try (string "=") <|> try (string "<") <|> try (string ">")))
      exp2 <- expression
      return (Op op [exp1,exp2] nullRange)
 
atomicFormula :: CharParser st EXPRESSION
atomicFormula = truefalseFormula <|> predFormula <|> parenFormula

-- | parser for formulas
aFormula :: CharParser st EXPRESSION
aFormula = (try negFormula) <|> impOrFormula

-- | parser for symbols followed by whitechars
lexemeParser :: CharParser st a -> CharParser st a
lexemeParser p1 = do
  res <- p1
  skip
  return res

negFormula :: CharParser st EXPRESSION
negFormula = do
  (lexemeParser (Lexer.keySign (string "not")))
  f <- atomicFormula
  return (Op "Not" [f] nullRange)

-- | parses a formula within brackets
parenFormula :: CharParser st EXPRESSION
parenFormula = do
  oParenT
  f <- aFormula
  cParenT
  return f

-- | parser for implications and ors (same precedence)
impOrFormula :: CharParser st EXPRESSION
impOrFormula = do
  f1 <- andFormula
  opfs <- many $ liftM2 (,) (lexemeParser (Lexer.keySign (string "or" <|> string "impl"))) impOrFormula
  if null opfs then return f1 
   else return $ foldr (\ a b -> case (fst a) of 
                                   "or" -> (Op "Or" [b,(snd a)] nullRange)
                                   "impl" -> (Op "Impl" [b,(snd a)] nullRange)
                                 ) f1 opfs


-- | a parser for and sequence of and formulas
andFormula :: CharParser st EXPRESSION
andFormula = do
  f1 <- atomicFormula
  opfs <- many $ liftM2 (,) (lexemeParser (Lexer.keySign (string "and"))) atomicFormula
  if null opfs then return f1 
   else return $ foldr (\ a b -> (Op "And" [b,(snd a)] nullRange)) f1 opfs

-----------------------------------------------------------------------------
---------------------------- Parser for Commands ----------------------------
-----------------------------------------------------------------------------

formulaorexpression :: CharParser st EXPRESSION
formulaorexpression = ((try aFormula) <|> expression)

-- | parser for commands
command :: CharParser st CMD
command = do
  cmd <- (lexemeParser (Lexer.keySign (try (string "solve")) <|> string "simplify" <|> string "remainder" <|> string "gcd" <|> string "int" <|> string "qelim"))
  oParenT
  arg1 <- formulaorexpression
  args <- many $ liftM2 (,) (lexemeParser (Lexer.keySign (string ","))) formulaorexpression
  cParenT
  return (Cmd cmd (arg1 : (map snd args))) 


-----------------------------------------------------------------------------
--------------------------- parser spec entries. ----------------------------
-----------------------------------------------------------------------------

-- | parser for operator declarations: example: operator a,b,c
opItem :: CharParser st OP_ITEM
opItem = do 
  Lexer.keySign (lexemeParser (string "operator"))
  var1 <- identifier
  vars <- many $ liftM2 (,) (lexemeParser (Lexer.keySign (string ","))) identifier
  return (Op_item  (var1:(map snd vars)) nullRange)
  

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



-----------------------------------------------------------------------------
------------------------ parser for symbol maps etc. ------------------------
-----------------------------------------------------------------------------

-- | parsing a prop symbol
symb :: GenParser Char st SYMB
symb = fmap Symb_id identifier


-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = do
  s <- symb
  do  f <- pToken $ toKey mapsTo
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
       do   c <- commaT `followedWith` symb
            (is, ps) <- symbs
            return (s:is, c:ps)
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
  do  c <- commaT `followedWith` symb
      (is, ps) <- symbMaps
      return (s:is, c:ps)
    <|> return ([s], [])
