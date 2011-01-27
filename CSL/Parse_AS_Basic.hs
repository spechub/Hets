{- |
Module      :  $Header$
Description :  Parser for basic specs
Copyright   :  (c) Dominik Dietrich, DFKI Bremen 2010
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  dominik.dietrich@dfki.de
Stability   :  experimental
Portability :  portable

Parser for abstract syntax for CSL
-}

module CSL.Parse_AS_Basic where

import qualified Common.AnnoState as AnnoState
import Common.Id as Id
import Common.Keywords as Keywords
import Common.Lexer as Lexer
import Common.Parsec
import Common.AS_Annotation as AS_Anno

import CSL.AS_BASIC_CSL
import CSL.Keywords
import Text.ParserCombinators.Parsec as Parsec
import Control.Monad
import Data.Maybe

-- TODO: extract range information for the basic term and command types

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
    where f (x:xs) = if s == show x then x else f xs
          f [] = error $ "getOpName: no op found for " ++ s ++ " in " ++ show l

mkFromOps :: [OPNAME] -> String -> [EXPRESSION] -> EXPRESSION
mkFromOps l s exps = mkPredefOp (getOpName s l) exps

-- | Lookup the string in the predefined operator map
mkAndAnalyzeOp :: String -> [EXTPARAM] -> [EXPRESSION] -> Range -> EXPRESSION
mkAndAnalyzeOp s eps exps rg =
    let err msg = "At operator " ++ s ++ "\n" ++ msg
        -- an error-message producing function
        g msg | not $ null eps = Just $ err msg
                                 ++ "* No extended parameters allowed\n"
              | null msg = Nothing
              | otherwise = Just $ err msg
        opOrErr mOp x = case x of
                          Just msg -> error msg
                          _ -> OpId $ opname $ fromJust mOp
        op = case lookupOpInfoForStatAna s (length exps) of
               Left False -> OpUser $ SimpleConstant s
               -- if registered it must be registered with the given arity or
               -- as flex-op, otherwise we don't accept it
               Left True -> opOrErr Nothing $ g "* Wrong arity\n"
               Right opinfo -> opOrErr (Just opinfo) $ g ""
    in Op op eps exps rg

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
    let f (eN, rg) = either (flip Int rg) (flip Double rg) eN
    in signednumber >-> f

-- | parses a possibly signed number (both integers and floats) 
signednumber :: CharParser st (Either APInt APFloat, Range)
signednumber = 
    let f c x = return (c $ read $ tokStr x, tokPos x)
        g x | isFloating x = f Right x
            | otherwise  = f Left x
    in Lexer.pToken Lexer.scanFloatExt >>= g

-- | The version in Common.Lexer is not compatible with floating point numbers
-- which may start with ".". This one does it.
keySignNumCompat :: CharParser st a -> CharParser st a
keySignNumCompat = try . (<< notFollowedBy (oneOf signNumCompatChars))

signNumCompatChars :: String
signNumCompatChars = "!#$&*+-/:<=>?@\\^|~" ++
    "\161\162\163\167\169\172\176\177\178\179\181\182\183\185\191\215\247"

oneOfKeys :: [String] -> CharParser st String
oneOfKeys l = lexemeParser $ keySignNumCompat $ choice $ map tryString l

plusmin :: CharParser st EXPRESSION
plusmin = do
  let ops = [OP_plus, OP_minus]
  exp1 <- factor
  exps <- many $ pair (oneOfKeys $ map show ops) factor
  return $ if null exps then  exp1
           else foldl (\ a b -> mkFromOps ops (fst b) [a, snd b]) exp1 exps

-- | parse a product of basic expressions
factor :: CharParser st EXPRESSION
factor = do
  let ops = [OP_mult, OP_div]
  exp1 <- expexp
  exps <- many $ pair (oneOfKeys $ map show ops) expexp
  if null exps then return exp1
     else return $ foldl (\ a b -> mkFromOps ops (fst b) [a, snd b]) exp1 exps

-- | parse a sequence of exponentiations
expexp :: CharParser st EXPRESSION
expexp = do
  exp1 <- expatom
  exps <- many $ pair (oneOfKeys ["**", "^"]) expatom
  if null exps then return exp1
    else return $ foldl (\ a b -> mkPredefOp OP_pow [a, snd b]) exp1 exps

-- | parse a basic expression
expatom :: CharParser st EXPRESSION
expatom = try signednumberExp <|> (oParenT >> plusmin << cParenT)
          <|> listexp <|> intervalexp <|> expsymbol

expsymbol :: CharParser st EXPRESSION
expsymbol =
    do
      ident <- prefixidentifier  -- EXTENDED
      ep <- option ([],[])
            $ oBracketT >> Lexer.separatedBy extparam pComma << cBracketT
      exps <- option ([],[])
              $ oParenT >> Lexer.separatedBy formulaorexpression pComma
                    << cParenT
      return $ mkAndAnalyzeOp (tokStr ident) (fst ep) (fst exps) nullRange


-- | parses a list expression
listexp :: CharParser st EXPRESSION
listexp = do
  Lexer.keySign $ string "{"
  elems <- Lexer.separatedBy formulaorexpression pComma
  Lexer.keySign $ string "}"
  return (List (fst elems) nullRange)

intervalexp :: CharParser st EXPRESSION
intervalexp = do
  nums <- lstring "[" >> Lexer.separatedBy signednumber pComma << lstring "]"
  let getFloat = either fromInteger id
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



quantFormula :: OPNAME -> CharParser st EXPRESSION
 -- TODO: static analysis requires probably a better representation of quantifiers
quantFormula q = do
  Lexer.keySign (string $ show q)
  oParenT
  vars <- ( parseVar <|> parseVarList)
  pComma
  expr <- formulaorexpression
  cParenT
  return (mkPredefOp q [vars, expr])


-- | parser for atoms
truefalseFormula :: CharParser st EXPRESSION
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
predFormula :: CharParser st EXPRESSION
predFormula = do
  let ops = [ OP_leq, OP_geq, OP_neq, OP_eq, OP_lt, OP_gt ]
  exp1 <- plusmin
  mExp2 <- optionMaybe
           $ pair (oneOfKeys (map show $ take 3 ops) -- the first 3 print as 2-chars
                   <|> lexemeParser (single $ oneOf "=<>")) plusmin
  case mExp2 of
    Just (op, exp2) -> return $ mkFromOps ops op [exp1, exp2]
    _ -> return $ exp1

atomicFormula :: CharParser st EXPRESSION
atomicFormula = truefalseFormula <|> predFormula <|> parenFormula

-- | parser for formulas
aFormula :: CharParser st EXPRESSION
aFormula = try negFormula <|> impOrFormula

negFormula :: CharParser st EXPRESSION
negFormula = do
  lexemeParser (Lexer.keyWord (tryString $ show OP_not))
  f <- atomicFormula
  return (mkPredefOp OP_not [f])

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
  let ops = [ OP_or, OP_impl ]
  f1 <- andFormula
  opfs <- many $ pair (lexemeParser $ Lexer.keyWord
                      $ tryString (show OP_or) <|> tryString (show OP_impl))
          andFormula
  if null opfs then return f1
   else return $ foldl (\ a (op, b) -> mkFromOps ops op [a, b]) f1 opfs

-- | a parser for and sequence of and formulas
andFormula :: CharParser st EXPRESSION
andFormula = do
  f1 <- atomicFormula
  opfs <- many $ pair (lexemeParser $ keyWord $ tryString $ show OP_and)
          atomicFormula
  if null opfs then return f1
   else return $ foldl (\ b a -> (mkPredefOp OP_and [b, snd a])) f1 opfs

-- ---------------------------------------------------------------------------

-- * Parser for Commands

-- ---------------------------------------------------------------------------

formulaorexpression :: CharParser st EXPRESSION
formulaorexpression = try aFormula <|> plusmin

-- | parser for commands
command :: CharParser (AnnoState.AnnoState st) CMD
command = reduceCommand <|> try assignment <|> repeatExpr <|> caseExpr
          <|> sequenceExpr <|> constraint

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
  exp' <- plusmin
  return $ Ass ident exp'

constraint :: CharParser st CMD
constraint = do
  exp' <- try aFormula
  case exp' of
    Op _ _ _ _ ->
        return $ Cmd "constraint" [exp']
    _ -> fail "Malformed constraint"


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
singleCase = do
  lstring "case"
  cond <- aFormula
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


parseDomain :: CharParser st Domain
parseDomain = do
  lp <- lexemeParser $ oneOf "{[]"
  gcl <- sepBy1 (signednumber >-> either GCI GCR . fst) pComma
  rp <- lexemeParser $ oneOf "[]}"
  let f o c = case gcl of
                [lb, rb] -> return $ IntVal (lb, o) (rb, c)
                _ -> parseError "parseDomain: incorrect interval-list"
  case [lp, rp] of
    "{}" -> return $ Set gcl
    "[]" -> f True True
    "[[" -> f True False
    "][" -> f False False
    "]]" -> f False True
    _ -> parseError "parseDomain: malformed domain parens"


-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec =
  AnnoState.annosParser parseBasicItems >-> Basic_spec
  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- | Parser for basic items
parseBasicItems :: AnnoState.AParser st BASIC_ITEM
parseBasicItems = parseOpDecl <|> parseVarDecl <|> parseAxItems

-- | parser for predicate declarations
parseOpDecl :: AnnoState.AParser st BASIC_ITEM
parseOpDecl = opItem >-> Op_decl

-- | parser for predicate declarations
parseVarDecl :: AnnoState.AParser st BASIC_ITEM
parseVarDecl = varItems >-> Var_decls

-- | parser for Axiom_item
parseAxItems :: AnnoState.AParser st BASIC_ITEM
parseAxItems = do
  AnnoState.dotT
  cmd <- (AnnoState.allAnnoParser command)
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

parseExpression :: String -> Maybe EXPRESSION
parseExpression inp =
    case runParser formulaorexpression "" "" inp of
      Left _ -> Nothing
      Right s -> Just s

