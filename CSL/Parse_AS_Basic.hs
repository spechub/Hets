{-# LANGUAGE TypeSynonymInstances #-}
{- |
Module      :  ./CSL/Parse_AS_Basic.hs
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  non-portable

Parser for abstract syntax for CSL
-}

module CSL.Parse_AS_Basic where

import qualified Common.AnnoState as AnnoState
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Common.Parsec
import Common.AS_Annotation as AS_Anno
import Common.GlobalAnnotations (PrefixMap)

import CSL.AS_BASIC_CSL
import CSL.ASUtils
import CSL.Print_AS ()
import CSL.Keywords
import CSL.TreePO

import Numeric
import Data.Char

import qualified Data.Set as Set

import Text.ParserCombinators.Parsec as Parsec
import Text.ParserCombinators.Parsec.Error
import Control.Monad
import qualified Control.Monad.Fail as Fail

-- TODO: extract range information for the basic term and command types

-- ---------------------------------------------------------------------------

-- * Interface to the syntax class

-- ---------------------------------------------------------------------------

parseBasicSpec :: Maybe (PrefixMap -> AnnoState.AParser st BASIC_SPEC)
parseBasicSpec = Just (const basicSpec)

parseSymbItems :: Maybe (GenParser Char st SYMB_ITEMS)
parseSymbItems = Just symbItems

parseSymbMapItems :: Maybe (GenParser Char st SYMB_MAP_ITEMS)
parseSymbMapItems = Just symbMapItems


-- ---------------------------------------------------------------------------

-- * Parser utils

-- ---------------------------------------------------------------------------


addToPosition :: SourcePos -- ^ original position
              -> SourcePos -- ^ relative position
              -> SourcePos -- ^ new position
addToPosition sp1 sp2
    | Parsec.sourceLine sp2 == 1 =
        setSourceColumn sp1 $
                        Parsec.sourceColumn sp1 + Parsec.sourceColumn sp2 - 1
    | otherwise =
        setSourceColumn (setSourceLine sp1
                        $ Parsec.sourceLine sp1 + Parsec.sourceLine sp2 - 1)
                            $ Parsec.sourceColumn sp2

posInputParser :: a -> GenParser tok st (a, SourcePos, [tok], st)
posInputParser x = do
  pos <- getPosition
  inp <- getInput
  st <- getState
  return (x, pos, inp, st)


{- Tests for subparser
let p1 = getState >>= many1 . string
runParser (string "h" >> runSubParser p1 "\n" "sourcename" >>= posInputParser) () "k" "h\n\nghurra"
-}
runSubParser :: GenParser tok st a -> st -> SourceName
             -> GenParser tok st' (Either ParseError (st, a))
runSubParser sp st sn = do
  -- save the current state
  pos <- getPosition
  inp <- getInput
  case runParser (sp >>= posInputParser) st sn inp of
    Left err -> return $ Left err
    Right (x, pos', inp', st') -> do
      setPosition $ addToPosition pos pos'
      setInput inp'
      return $ Right (st', x)


instance OperatorState (AnnoState.AnnoState st) where
    lookupOperator _ = lookupOperator ()
    lookupBinder _ = lookupBinder ()

data OpVarState a = OpVarState a (Set.Set String)

instance OperatorState a => OperatorState (OpVarState a) where
    lookupOperator (OpVarState x _) = lookupOperator x
    lookupBinder (OpVarState x _) = lookupBinder x
    addVar (OpVarState st s) x = OpVarState st $ Set.insert x s
    isVar (OpVarState _ s) x = Set.member x s


-- call opvar-state-subparser on given state
runWithVars :: OperatorState a => [String] -> CharParser (OpVarState a) res
            -> CharParser a res
runWithVars l p = do
  st <- getState
  res <- runSubParser p (OpVarState st $ Set.fromList l) ""
  case res of
    Left err -> parseError $ unlines $ map messageString $ errorMessages err
    Right (_, x) -> return x

-- TEST: for subparser...


parseError :: String -> CharParser st a
parseError s = do
  p <- getPosition
  return $ error
             $ concat [ "Parse error at line: ", show (Parsec.sourceLine p)
                      , " col: ", show (Parsec.sourceColumn p), "\n", s]

pComma :: CharParser st String
pComma = lexemeParser $ string ","

pSemi :: CharParser st String
pSemi = lexemeParser $ string ";"

lstring :: String -> CharParser st String
lstring = lexemeParser . string

-- | parser for symbols followed by whitechars
lexemeParser :: CharParser st a -> CharParser st a
lexemeParser = (<< skip)

getOpName :: String -> [OPNAME] -> OPNAME
getOpName s l = f l
    where f (x : xs) = if s == show x then x else f xs
          f [] = error $ "getOpName: no op found for " ++ s ++ " in " ++ show l

mkFromOps :: [OPNAME] -> String -> [EXPRESSION] -> EXPRESSION
mkFromOps l s = mkPredefOp (getOpName s l)

-- ---------------------------------------------------------------------------

-- * Parser for Expressions

-- ---------------------------------------------------------------------------


{- | parsing of identifiers. an identifier is a letter followed by
     letters, numbers, or _, but not a keyword -}
identifier :: CharParser st Id.Token
identifier =
  lexemeParser $ Lexer.pToken $ reserved allKeywords Lexer.scanAnyWords

prefixidentifier :: CharParser st Id.Token
prefixidentifier =
    lexemeParser $ Lexer.pToken $ Lexer.scanAnySigns <|> Lexer.scanAnyWords

-- | parses a possibly signed number to an EXPRESSION
signednumberExp :: CharParser st EXPRESSION
signednumberExp =
    let f (eN, rg) = either (flip Int rg) (flip Rat rg . readRat) eN
    in signednumber >-> f

-- | parses a possibly signed number (both integers and floats)
signednumber :: CharParser st (Either APInt String, Range)
signednumber =
    let f c x = return (c $ tokStr x, tokPos x)
        g x | isFloating x = f Right x
            | otherwise = f (Left . read) x
    in Lexer.pToken Lexer.scanFloatExt >>= g

readRat :: String -> APFloat
readRat s = case readFloat fls of
              [(r, "")] -> withSgn r
              _ -> error $ "readRat: cannot read float " ++ s
    where withSgn x = if sgn then - x else x
          (sgn, fls) = case dropWhile isSpace s of
                         '-' : s' -> (True, s')
                         _ -> (False, s)

readDbl :: String -> Double
readDbl = read

{- | The version in Common.Lexer is not compatible with floating point numbers
which may start with ".". This one does it.
This version is still not compatible with -! -}
keySignNumCompat :: CharParser st a -> CharParser st a
keySignNumCompat = try . (<< notFollowedBy (oneOf signNumCompatChars))

signNumCompatChars :: String
signNumCompatChars = "!#$&*+-/:<=>?@\\^|~" ++
    "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

oneOfKeys :: [String] -> CharParser st String
oneOfKeys l = lexemeParser $ keySignNumCompat $ choice $ map tryString l

plusmin :: OperatorState st => CharParser st EXPRESSION
plusmin = do
  let ops = [OP_plus, OP_minus]
  exp1 <- factor
  exps <- many $ pair (oneOfKeys $ map show ops) factor
  return $ if null exps then exp1
           else foldl (\ a b -> mkFromOps ops (fst b) [a, snd b]) exp1 exps

-- | parse a product of basic expressions
factor :: OperatorState st => CharParser st EXPRESSION
factor = do
  let ops = [OP_mult, OP_div]
  exp1 <- expexp
  exps <- many $ pair (oneOfKeys $ map show ops) expexp
  return $ if null exps then exp1
     else foldl (\ a b -> mkFromOps ops (fst b) [a, snd b]) exp1 exps

-- | parse a sequence of exponentiations
expexp :: OperatorState st => CharParser st EXPRESSION
expexp = do
  exp1 <- expatom
  exps <- many $ pair (oneOfKeys ["**", "^"]) expatom
  return $ if null exps then exp1
    else foldl (\ a b -> mkPredefOp OP_pow [a, snd b]) exp1 exps

-- | parse a basic expression
expatom :: OperatorState st => CharParser st EXPRESSION
expatom = try signednumberExp <|> (oParenT >> plusmin << cParenT)
          <|> listexp <|> intervalexp <|> expsymbol

expsymbol :: OperatorState st => CharParser st EXPRESSION
expsymbol = do
  ident <- prefixidentifier  -- EXTENDED
  ep <- option ([], [])
        $ oBracketT >> Lexer.separatedBy extparam pComma << cBracketT
  exps <- option ([], [])
          $ oParenT >> Lexer.separatedBy formulaorexpression pComma << cParenT
  st <- getState
  case mkAndAnalyzeOp' True st (tokStr ident) (fst ep) (fst exps)
           $ getRange ident of
    Left s -> parseError $ "expsymbol at op " ++ tokStr ident
              ++ show (fst exps) ++ ": " ++ s
    Right e -> return e

opdecl :: OperatorState st => CharParser st OpDecl
opdecl = do
  ident <- prefixidentifier  -- EXTENDED
  ep <- option ([], [])
        $ oBracketT >> Lexer.separatedBy extparam pComma << cBracketT
  args <- option ([], [])
          $ oParenT >> Lexer.separatedBy prefixidentifier pComma << cParenT
  let vdl = map (flip VarDecl Nothing) $ fst args
  return $ OpDecl (SimpleConstant $ tokStr ident) (fst ep) vdl $ tokPos ident

-- | parses a list expression
listexp :: OperatorState st => CharParser st EXPRESSION
listexp = do
  keySignNumCompat $ string "{"
  elems <- Lexer.separatedBy formulaorexpression pComma
  keySignNumCompat $ string "}"
  return (List (fst elems) nullRange)

intervalexp :: CharParser st EXPRESSION
intervalexp = do
  nums <- lstring "[" >> Lexer.separatedBy signednumber pComma << lstring "]"
  let getFloat = either fromInteger readDbl
  case fst nums of
    [(x, rg1), (y, rg2)] -> return $ Interval (getFloat x) (getFloat y) $ Range
                            $ joinRanges $ map rangeToList [rg1, rg2]
    _ -> parseError
         "intervalexp: Parse error: interval with other than two arguments"

-- ---------------------------------------------------------------------------

-- ** parser for extended parameter, e.g., [I=0,...]

-- ---------------------------------------------------------------------------

extparam :: CharParser st EXTPARAM
extparam = do
  i <- identifier
  liftM2 (EP i) (oneOfKeys ["=", "<=", ">=", "!=", "<", ">", "-|"])
    $ option 0 $ signednumber
          >-> either id (error "extparam: floats not supported") . fst

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


quantFormula :: OperatorState st => OPNAME -> CharParser st EXPRESSION
 -- TODO: static analysis requires probably a better representation of quantifiers
quantFormula q = do
  Lexer.keySign (string $ show q)
  oParenT
  vars <- parseVar <|> parseVarList
  pComma
  expr <- formulaorexpression
  cParenT
  return (mkPredefOp q [vars, expr])


-- | parser for atoms
truefalseFormula :: OperatorState st => CharParser st EXPRESSION
truefalseFormula =
    do
      lexemeParser (Lexer.keyWord (tryString $ show OP_true))
      return (mkPredefOp OP_true [])
    <|>
    do
      lexemeParser (Lexer.keyWord (tryString $ show OP_false))
      return (mkPredefOp OP_false [])
    <|> quantFormula OP_ex <|> quantFormula OP_all

-- | parser for predicates
predFormula :: OperatorState st => CharParser st EXPRESSION
predFormula = do
  let ops = [ OP_leq, OP_geq, OP_neq, OP_eq, OP_lt, OP_gt ]
  exp1 <- plusmin
  mExp2 <- optionMaybe
           $ pair (oneOfKeys (map show $ take 3 ops) -- the first 3 print as 2-chars
                   <|> lexemeParser (single $ oneOf "=<>")) plusmin
  case mExp2 of
    Just (op, exp2) -> return $ mkFromOps ops op [exp1, exp2]
    _ -> return exp1

atomicFormula :: OperatorState st => CharParser st EXPRESSION
atomicFormula = truefalseFormula <|> predFormula <|> parenFormula

-- | parser for formulas
aFormula :: OperatorState st => CharParser st EXPRESSION
aFormula = try negFormula <|> impOrFormula

negFormula :: OperatorState st => CharParser st EXPRESSION
negFormula = do
  lexemeParser (Lexer.keyWord (tryString $ show OP_not))
  f <- atomicFormula
  return (mkPredefOp OP_not [f])

-- | parses a formula within brackets
parenFormula :: OperatorState st => CharParser st EXPRESSION
parenFormula = do
  lexemeParser oParenT
  f <- aFormula
  lexemeParser cParenT
  return f

-- | parser for implications and ors (same precedence)
impOrFormula :: OperatorState st => CharParser st EXPRESSION
impOrFormula = do
  let ops = [ OP_or, OP_impl ]
  f1 <- andFormula
  opfs <- many $ pair (lexemeParser $ Lexer.keyWord
                      $ tryString (show OP_or) <|> tryString (show OP_impl))
          andFormula
  return $ if null opfs then f1
   else foldl (\ a (op, b) -> mkFromOps ops op [a, b]) f1 opfs

-- | a parser for and sequence of and formulas
andFormula :: OperatorState st => CharParser st EXPRESSION
andFormula = do
  f1 <- atomicFormula
  opfs <- many $ pair (lexemeParser $ keyWord $ tryString $ show OP_and)
          atomicFormula
  return $ if null opfs then f1
   else foldl (\ b a -> (mkPredefOp OP_and [b, snd a])) f1 opfs

-- ---------------------------------------------------------------------------

-- * Parser for Commands

-- ---------------------------------------------------------------------------


formulaorexpression :: OperatorState st => CharParser st EXPRESSION
formulaorexpression = try aFormula <|> plusmin

-- | parser for commands
command :: CharParser (AnnoState.AnnoState st) CMD
command = reduceCommand <|> try assignment <|> repeatExpr <|> caseExpr
          <|> sequenceExpr <|> constraint

reduceCommand :: OperatorState st => CharParser st CMD
reduceCommand = do
  cmd <- lexemeParser $ Lexer.keyWord $ choice $ map tryString
         ["solve", "simplify", "divide", "int", "rlqe", "factorize", "print"]
  oParenT
  arg1 <- formulaorexpression
  args <- many $ pComma >> formulaorexpression
  cParenT
  return $ Cmd cmd $ arg1 : args

assignment :: OperatorState st => CharParser st CMD
assignment = do
  ident@(OpDecl _ _ vdl _) <- opdecl
  lexemeParser $ choice [tryString ":=", tryString "="]
  exp' <- runWithVars (map varDeclName vdl) plusmin
  return $ Ass ident exp'

constraint :: OperatorState st => CharParser st CMD
constraint = do
  exp' <- try aFormula
  case exp' of
    Op {} ->
        return $ Cmd "constraint" [exp']
    _ -> Fail.fail "Malformed constraint"


sequenceExpr :: CharParser (AnnoState.AnnoState st) CMD
sequenceExpr = do
  lstring "sequence"
  statements <- many1 (AnnoState.dotT >> AnnoState.allAnnoParser command)
  lstring "end"
  return $ Sequence $ map AS_Anno.item statements

repeatExpr :: CharParser (AnnoState.AnnoState st) CMD
repeatExpr = do
  lstring "repeat"
  statements <- many1 (AnnoState.dotT >> AnnoState.allAnnoParser command)
  lstring "until"
  cstr <- aFormula
  return $ Repeat cstr $ map AS_Anno.item statements

singleCase :: CharParser (AnnoState.AnnoState st) (EXPRESSION, [CMD])
singleCase =
    let p1 = lstring "else" >> return (mkPredefOp OP_true [])
    in do
      lstring "case"
      cond <- choice [try p1, aFormula]
      lstring ":"
      statements <- many1 (AnnoState.dotT >> AnnoState.allAnnoParser command)
      return (cond, map AS_Anno.item statements)


caseExpr :: CharParser (AnnoState.AnnoState st) CMD
caseExpr = many1 singleCase >-> Cond << lstring "end"

-- ---------------------------------------------------------------------------

-- * parser spec entries

-- ---------------------------------------------------------------------------


-- | parser for operator declarations: example: operator a,b,c
opItem :: CharParser st OP_ITEM
opItem = do
  Lexer.keySign (lexemeParser (tryString "operator"))
  vars <- sepBy1 identifier pComma
  return $ Op_item vars nullRange


-- | Parser for variable declarations: example: vars x,y in {1,2}; z in [-1,1]
varItems :: CharParser st [VAR_ITEM]
varItems = oneOfKeys ["vars", "var"] >> sepBy1 varItem pSemi

-- | Parser for a variable declaration: example: vars x,y in {1,2}
varItem :: CharParser st VAR_ITEM
varItem = do
  vars <- sepBy1 identifier pComma
  oneOfKeys ["in"]
  dom <- parseDomain
  return $ Var_item vars dom nullRange


{- | Parser for extended parameter declarations:
example: I in [1,2]; -}
epDecl :: CharParser st (Id.Token, EPDomain)
epDecl = do
  epId <- identifier
  oneOfKeys ["in"]
  parseEPDomain >-> (,) epId

{- | Parser for extended parameter default values and domain variable
declarations: example: I = 1; n=2 -}
epNumValAss :: CharParser st (Id.Token, APInt)
epNumValAss = do
  epId <- identifier
  oneOfKeys ["="]
  getSignedNumber >-> (,) epId . read


parseDomain :: CharParser st Domain
parseDomain = do
  lp <- lexemeParser $ oneOf "{[]"
  gcl <- sepBy1 (signednumber >-> either GCI (GCR . readRat) . fst) pComma
  rp <- lexemeParser $ oneOf "[]}"
  let f o c = case gcl of
                [lb, rb] -> return $ IntVal (lb, o) (rb, c)
                _ -> parseError "parseDomain: incorrect interval-list"
  case [lp, rp] of
    "{}" -> return $ Set $ Set.fromList gcl
    "[]" -> f True True
    "[[" -> f True False
    "][" -> f False False
    "]]" -> f False True
    _ -> parseError "parseDomain: malformed domain parens"

parseEPVal :: CharParser st EPVal
parseEPVal = do
  mId <- optionMaybe identifier
  case mId of
    Just n -> return $ EPConstRef n
    _ -> getSignedNumber >-> EPVal . read

parseEPDomain :: CharParser st EPDomain
parseEPDomain = do
  lexemeParser $ string "["
  l <- parseEPVal
  pComma
  r <- parseEPVal
  lexemeParser $ string "]"
  return $ ClosedInterval l r


-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  AnnoState.annosParser parseBasicItems >-> Basic_spec
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AnnoState.AParser st BASIC_ITEM
parseBasicItems = parseOpDecl <|> parseVarDecl <|> parseEPDefValOrDomDecl
                  <|> parseEPDecl <|> parseAxItems

-- | parser for operator declarations
parseOpDecl :: AnnoState.AParser st BASIC_ITEM
parseOpDecl = opItem >-> Op_decl

-- | parser for variable declarations
parseVarDecl :: AnnoState.AParser st BASIC_ITEM
parseVarDecl = varItems >-> Var_decls

{- | parser for extended parameter declarations, one of:
default value for an extended parameter (I=2)
a domain variable declaration (n=10) -}
parseEPDefValOrDomDecl :: AnnoState.AParser st BASIC_ITEM
parseEPDefValOrDomDecl = do
  lstring "set"
  mDef <- optionMaybe $ try $ lexemeParser $ string "default"
  case mDef of
    Nothing -> sepBy1 epNumValAss pSemi >-> EP_domdecl
    _ -> sepBy1 epNumValAss pSemi >-> EP_defval

-- | parser for extended parameter declarations
parseEPDecl :: AnnoState.AParser st BASIC_ITEM
parseEPDecl = oneOfKeys ["eps", "ep"] >> sepBy1 epDecl pSemi >-> EP_decl

-- | parser for Axiom_item
parseAxItems :: AnnoState.AParser st BASIC_ITEM
parseAxItems = do
  AnnoState.dotT
  cmd <- AnnoState.allAnnoParser command
  return $ Axiom_item cmd


-- ---------------------------------------------------------------------------

-- * parser for symbol maps etc.

-- ---------------------------------------------------------------------------

-- | parsing a prop symbol
symb :: GenParser Char st SYMB
symb = identifier >-> Symb_id


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

parseCommand :: String -> Maybe CMD
parseCommand inp =
    case runParser command (AnnoState.emptyAnnos ()) "" inp of
      Left _ -> Nothing
      Right s -> Just s

parseExpression :: OperatorState a => a -> String -> Maybe EXPRESSION
parseExpression st inp =
    case runParser formulaorexpression st "" inp of
      Left _ -> Nothing
      Right s -> Just s
