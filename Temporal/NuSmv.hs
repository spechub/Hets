{- |
Module      :  ./Temporal/NuSmv.hs
Copyright   :  (c) Klaus Hartke, Uni Bremen 2008
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  experimental
Portability :  portable

-}

module NuSmv (basicExpr, program) where

import Control.Monad (liftM, liftM2)
import Data.Char (toLower)
import Data.List (intercalate, intersperse)
import Text.ParserCombinators.Parsec hiding (State, token)


(<<) :: (Monad m) => m a -> m b -> m a
(<<) a b = do x <- a
              b
              return x


-- ----------------------------------------------------------------------------


checkWith :: (Show a) => GenParser tok st a -> (a -> Bool) -> GenParser tok st a
checkWith p f = do x <- p
                   if f x then return x
                          else unexpected (show x)


reserved :: [String] -> CharParser st String -> CharParser st String
reserved l p = try $ checkWith p (`notElem` l)


-- ----------------------------------------------------------------------------


ws :: Parser ()
ws = many (oneOf " \t\r\n") >> return ()


token :: String -> Parser ()
token x = string x >> ws


keyword :: String -> Parser ()
keyword x = try (string x >> notFollowedBy alphaNum) >> ws


identifier :: Parser String
identifier = liftM2 (:) idFirstChar (many idConsecutiveChar) <?> "identifier"
  where
    idFirstChar = letter
               <|> char '_'

    idConsecutiveChar = idFirstChar
                     <|> digit
                     <|> char '$'
                     <|> char '#'
                     <|> char '\\'
                     <|> char '-'


integer :: Parser Int
integer = liftM read (liftM2 (++) (option "" (string "-")) (many1 digit))
          <?> "integer number"


-- ----------------------------------------------------------------------------


keywords :: [String]
keywords = [ "MODULE", "DEFINE", "CONSTANTS", "VAR", "IVAR", "INIT", "TRANS",
              "INVAR", "SPEC", "CTLSPEC", "LTLSPEC", "PSLSPEC", "COMPUTE",
              "INVARSPEC", "FAIRNESS", "JUSTICE", "COMPASSION", "ISA", "ASSIGN",
              "CONSTRAINT", "SIMPWFF", "CTLWFF", "LTLWFF", "PSLWFF", "COMPWFF",
              "IN", "MIN", "MAX", "process", "array", "of", "boolean",
              "integer", "real", "word", "word1", "bool", "EX", "AX", "EF",
              "AF", "EG", "AG", "E", "F", "O", "G", "H", "X", "Y", "Z", "A",
              "U", "S", "V", "T", "BU", "EBF", "ABF", "EBG", "ABG", "case",
              "esac", "mod", "next", "init", "union", "in", "xor", "xnor",
              "self", "TRUE", "FALSE" ]


{- ----------------------------------------------------------------------------
Basic Expressions of NuSMV
---------------------------------------------------------------------------- -}


data Expr = Bool Bool                        -- Boolean Constant
          | Int Int                          -- Integer Constant
          | Var [String]                     {- Symbol Constant,
                                              Variable Identifier,
                                              or Define Identifier -}
          | Word Int Int                     -- Word Constant
          | Range Int Int                    -- Range Constant
          | Not Expr                         -- Logical/Bitwise NOT
          | And Expr Expr                    -- Logical/Bitwise AND
          | Or Expr Expr                    -- Logical/Bitwise OR
          | Xor Expr Expr                    -- Logical/Bitwise XOR
          | Xnor Expr Expr                   -- Logical/Bitwise NOT XOR
          | Impl Expr Expr                   -- Logical/Bitwise Implication
          | Equiv Expr Expr                  -- Logical/Bitwise Equivalence
          | Eq Expr Expr                     -- Equality
          | Neq Expr Expr                    -- Inequality
          | Lt Expr Expr                     -- Less Than
          | Gt Expr Expr                     -- Greater Than
          | Leq Expr Expr                    -- Less Than Or Equal
          | Geq Expr Expr                    -- Greater Than Or Equal
          | Neg Expr                         -- Integer Unary Minus
          | Add Expr Expr                    -- Integer Addition
          | Sub Expr Expr                    -- Integer Subtraction
          | Mult Expr Expr                   -- Integer Multiplication
          | Div Expr Expr                    -- Integer Division
          | Mod Expr Expr                    -- Integer Remainder
          | Bsr Expr Expr                    -- Bit Shift Right
          | Bsl Expr Expr                    -- Bit Shift Left
          | Concat Expr Expr                 -- Word Concatenation
          | Select Expr (Int, Int)           -- Word Bits Selection
          | ToWord Expr                      -- Boolean to Word[1] convertion
          | ToBool Expr                      -- Word[1] to Boolean convertion
          | Union Expr Expr                  -- Union of Set Expressions
          | Set [Expr]                       -- Set Expression
          | In Expr Expr                     -- Inclusion Expression
          | Case [(Expr, Expr)]              -- Case Expression
          | Next Expr                        -- Next Expression


instance Show Expr where
  show expr = showBasicExpr expr True


showBasicExpr (Bool True) outer = "TRUE"
showBasicExpr (Bool False) outer = "FALSE"
showBasicExpr (Int value) outer = show value
showBasicExpr (Var ids) outer = intercalate "." ids
showBasicExpr (Word width value) outer = concat [ "0d", show width, "_",
                                                  show value ]
showBasicExpr (Range from to) outer = concat [ show from, "..", show to ]
showBasicExpr (Not expr) outer = '!' : showBasicExpr expr False
showBasicExpr (And exprA exprB) True = concat [ showBasicExpr exprA False,
                                              " & ", showBasicExpr exprB False ]
showBasicExpr (Or exprA exprB) True = concat [ showBasicExpr exprA False, " | ",
                                               showBasicExpr exprB False ]
showBasicExpr (Xor exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " xor ",
                                                showBasicExpr exprB False ]
showBasicExpr (Xnor exprA exprB) True = concat [ showBasicExpr exprA False,
                                                 " xnor ",
                                                 showBasicExpr exprB False ]
showBasicExpr (Impl exprA exprB) True = concat [ showBasicExpr exprA False,
                                                 " -> ",
                                                 showBasicExpr exprB False ]
showBasicExpr (Equiv exprA exprB) True = concat [ showBasicExpr exprA False,
                                                  " <-> ",
                                                  showBasicExpr exprB False ]
showBasicExpr (Eq exprA exprB) True = concat [ showBasicExpr exprA False,
                                               " = ",
                                               showBasicExpr exprB False ]
showBasicExpr (Neq exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " != ",
                                                showBasicExpr exprB False ]
showBasicExpr (Lt exprA exprB) True = concat [ showBasicExpr exprA False, " < ",
                                               showBasicExpr exprB False ]
showBasicExpr (Gt exprA exprB) True = concat [ showBasicExpr exprA False, " > ",
                                               showBasicExpr exprB False ]
showBasicExpr (Leq exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " <= ",
                                                showBasicExpr exprB False ]
showBasicExpr (Geq exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " >= ",
                                                showBasicExpr exprB False ]
showBasicExpr (Neg expr) outer = '-' : showBasicExpr expr False
showBasicExpr (Add exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " + ",
                                                showBasicExpr exprB False ]
showBasicExpr (Sub exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " - ",
                                                showBasicExpr exprB False ]
showBasicExpr (Mult exprA exprB) True = concat [ showBasicExpr exprA False,
                                                 " * ",
                                                 showBasicExpr exprB False ]
showBasicExpr (Div exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " / ",
                                                showBasicExpr exprB False ]
showBasicExpr (Mod exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " mod ",
                                                showBasicExpr exprB False ]
showBasicExpr (Bsr exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " >> ",
                                                showBasicExpr exprB False ]
showBasicExpr (Bsl exprA exprB) True = concat [ showBasicExpr exprA False,
                                                " << ",
                                                showBasicExpr exprB False ]
showBasicExpr (Concat exprA exprB) True = concat [ showBasicExpr exprA False,
                                                   " :: ",
                                                   showBasicExpr exprB False ]
showBasicExpr (Select expr (from, to)) outer = concat
 [ showBasicExpr expr False, "[", show from, ", ", show to, "]" ]
showBasicExpr (ToWord expr) outer = concat [ "word1(", showBasicExpr expr True,
                                             ")" ]
showBasicExpr (ToBool expr) outer = concat [ "bool(", showBasicExpr expr True,
                                             ")" ]
showBasicExpr (Union exprA exprB) True = concat [ showBasicExpr exprA False,
                                                  " union ",
                                                  showBasicExpr exprB False ]
showBasicExpr (Set exprs) outer = '{' : intercalate ", "
  (map (`showBasicExpr` False) exprs) ++ "}"
showBasicExpr (In exprA exprB) True = concat [ showBasicExpr exprA False,
                                               " in ",
                                               showBasicExpr exprB False ]
showBasicExpr (Case cases) outer = concat [ "case ",
 intercalate "\n" (map (\ (exprA, exprB) ->
  concat [showBasicExpr exprA False, " : ",
 showBasicExpr exprB False, ";"]) cases), " esac" ]
showBasicExpr (Next expr) outer = concat [ "next(",
                                           showBasicExpr expr True, ")" ]
showBasicExpr expr False = concat [ "(", showBasicExpr expr True, ")" ]


{- ----------------------------------------------------------------------------
Parser for Basic Expressions
---------------------------------------------------------------------------- -}


basicExpr :: Parser Expr
basicExpr = implExpr
  where
    implExpr = chainr1 equivExpr (token "->" >> return Impl)

    equivExpr = chainl1 orExpr (token "<->" >> return Equiv)

    orExpr = chainl1 andExpr ((token "|" >> return Or) <|>
                               (keyword "xor" >> return Xor) <|>
                               (keyword "xnor" >> return Xnor))

    andExpr = chainl1 eqExpr (token "&" >> return And)

    eqExpr = chainl1 inExpr ((token "=" >> return Eq) <|>
                              (token "!=" >> return Neq) <|>
                              try (token "<=" >> return Leq) <|>
                              try (token ">=" >> return Geq) <|>
                              (token "<" >> return Lt) <|>
                              (token ">" >> return Gt))

    inExpr = chainl1 unionExpr (keyword "in" >> return In)

    unionExpr = chainl1 shiftExpr (keyword "union" >> return Union)

    shiftExpr = chainl1 modExpr (try (token ">>" >> return Bsr) <|>
                                 try (token "<<" >> return Bsl))

    modExpr = chainl1 addSubExpr (keyword "mod" >> return Mod)

    addSubExpr = chainl1 multDivExpr ((token "+" >> return Add) <|>
                                       (token "-" >> return Sub))

    multDivExpr = chainl1 negateExpr ((token "*" >> return Mult) <|>
                                       (token "/" >> return Div))

    negateExpr = (token "-" >> liftM Neg negateExpr) <|>
                  concatExpr

    concatExpr = chainl1 selectExpr (try (token "::") >> return Concat)

    selectExpr =  do expr <- notExpr
                     option expr (do token "[" <?> "selector"
                                     bits <- sepBy1 bit (token "[")
                                     return (foldl Select expr bits))

    notExpr = (token "!" >> liftM Not notExpr) <|>
               primaryExpr

    primaryExpr = parenthesizedExpr <|>
                   liftM Set (between (token "{") (token "}")
                              (sepBy1 implExpr (char ',' >> ws))) <|>
                   (do expr <- constantExpr << ws
                       case expr of
                         Var ["word1"] -> liftM ToWord parenthesizedExpr
                         Var ["bool"] -> liftM ToBool parenthesizedExpr
                         Var ["case"] -> caseExpr
                         Var ["next"] -> liftM Next parenthesizedExpr
                         _ -> return expr)

    parenthesizedExpr = between (token "(") (token ")") implExpr

    caseExpr = liftM Case (manyTill (do lhs <- implExpr
                                        token ":"
                                        rhs <- implExpr
                                        token ";"
                                        return (lhs, rhs)) (token "esac"))

    bit =  do value1 <- integer << ws
              token ":"
              value2 <- integer << ws
              token "]"
              return (value1, value2)


{- ----------------------------------------------------------------------------
Parser for Constant Expressions
---------------------------------------------------------------------------- -}


constantExpr :: Parser Expr
constantExpr = (constantA <?> "integer constant") <|>
                (constantB <?> "boolean constant") <|>
                (constantE <?> "symbolic constant") <|>
                (constantF <?> "variable identifier") <|>
                (constantG <?> "define identifier")
  where
    constantA =  do char '-'
                    value <- many1 digit
                    range (negate (read value))

    constantB =  do char '0'
                    constantC <|> constantD

    constantC =  do base <- oneOf "bBoOdDhH"
                    width <- many digit
                    char '_'
                    value <- case toLower base of
                               'b' -> many1 (oneOf "01_")
                               'o' -> many1 (octDigit <|> char '_')
                               'd' -> many1 (digit <|> char '_')
                               'h' -> many1 (hexDigit <|> char '_')

                    let width' = case width of
                                   "" -> case toLower base of
                                           'b' -> 1 * length value
                                           'o' -> 3 * length value
                                           'd' -> error $ "Cannot calculate " ++
                                                   "width of decimal integers"
                                           'h' -> 4 * length value
                                   _ -> read width

                    let value' = case toLower base of
                                   'b' -> error "Cannot decode binary integer"
                                   'o' -> read ("0o" ++ filter (/= '_') value)
                                   'd' -> read (filter (/= '_') value)
                                   'h' -> read ("0x" ++ filter (/= '_') value)

                    return (Word width' value')

    constantD =  do value <- many digit
                    case value of
                      "" -> return (Bool False)
                      _ -> range (read ('0' : value))

    constantE =  do char '1'
                    value <- many digit
                    case value of
                      "" -> return (Bool True)
                      _ -> range (read ('1' : value))

    constantF =  do value <- many1 digit
                    range (read value)

    constantG =  do value <- sepBy1 identifier (char '.')
                    case value of
                      ["FALSE"] -> return (Bool False)
                      ["TRUE"] -> return (Bool True)
                      _ -> return (Var value)

    range x = (string ".." >> liftM (Range x) integer)
              <|> return (Int x)


{- ----------------------------------------------------------------------------
Complex Identifiers
---------------------------------------------------------------------------- -}


data ComplexId = Id String
               | ComplexId ComplexId String
               | IndexedId ComplexId Int
               | Self


instance Show ComplexId where
  show (Id s) = s
  show (ComplexId id s) = show id ++ "." ++ s
  show (IndexedId id i) = show id ++ "[" ++ show i ++ "]"
  show (Self) = "self"


complexId :: Parser ComplexId
complexId =  do id <- reserved keywords identifier << ws
                return (Id id) -- TODO: really complex identifiers


{- ----------------------------------------------------------------------------
NuSMV Programs
---------------------------------------------------------------------------- -}


data Program = Program [Module]


data Module = Module String [String] [Element]


data Element = VarDecl [(String, Type)]
             | IVarDecl [(String, Type)]
             | DefineDecl [(String, Expr)]
             | ConstDecl [String]
             | Init Expr
             | Invar Expr
             | Trans Expr
             | Assign [(AssignLhs, AssignRhs)]
             | Fairness Expr
             | Justice Expr
             | Compassion Expr Expr


data Type = BoolType
          | WordType Int
          | EnumType [EnumValue]
          | RangeType Int Int
          | ArrayType Int Int Type


data EnumValue = Symbol String
               | Number Int


data AssignLhs = CurrentValue ComplexId
               | InitialValue ComplexId
               | NextValue ComplexId


type AssignRhs = Expr


instance Show Program where
  show = showProgram


showProgram (Program mods) = concatMap showModule mods


instance Show Module where
  show = showModule


showModule (Module name params elements) = concat [ "MODULE ",
 name, showParams params, "\n", concatMap showElement elements ]
  where
    showParams [] = ""
    showParams params = concat [ "(", intercalate ", " params, ")" ]


instance Show Element where
  show = showElement


showElement (VarDecl vars) = concat [ "VAR", concatMap showVar vars, "\n" ]
  where
    showVar (id, ty) = concat [ " ", id, " : ", showType ty, ";" ]

showElement (IVarDecl vars) = concat [ "IVAR", concatMap showVar vars, "\n" ]
  where
    showVar (id, ty) = concat [ " ", id, " : ", showType ty, ";" ]

showElement (DefineDecl defs) = concat [ "DEFINE",
 concatMap showDefine defs, "\n" ]
  where
    showDefine (id, expr) = concat [ " ", id, " := ",
     showBasicExpr expr True, ";" ]

showElement (ConstDecl consts) = concat [ "CONSTANTS ",
 intercalate ", " consts, ";\n" ]
showElement (Init expr) = concat [ "INIT ", showBasicExpr expr True, ";\n" ]
showElement (Invar expr) = concat [ "INVAR ", showBasicExpr expr True, ";\n" ]
showElement (Trans expr) = concat [ "TRANS ", showBasicExpr expr True, ";\n" ]

showElement (Assign assigns) = concat [ "ASSIGN", concatMap showAssign assigns, "\n" ]
  where
    showAssign (lhs, rhs) = concat [ " ", show lhs, " := ", show rhs, ";" ]

showElement (Fairness expr) = concat [ "FAIRNESS ", showBasicExpr expr True, ";\n" ]
showElement (Justice expr) = concat [ "JUSTICE ", showBasicExpr expr True, ";\n" ]
showElement (Compassion exprA exprB) = concat [ "COMPASSION(",
  showBasicExpr exprA True, ", ", showBasicExpr exprB True, ");\n" ]


instance Show Type where
  show = showType


showType BoolType = "boolean"
showType (WordType width) = concat [ "word[", show width, "]" ]
showType (EnumType values) = concat [ "{",
 intercalate "," (map showValue values), " }" ]
  where
    showValue (Symbol symbol) = ' ' : symbol
    showValue (Number number) = ' ' : show number
showType (RangeType from to) = concat [ show from, "..", show to ]
showType (ArrayType from to ty) = concat [ "array ",
 show from, "..", show to, " of ", showType ty ]


instance Show AssignLhs where
  show (CurrentValue id) = show id
  show (InitialValue id) = "init(" ++ show id ++ ")"
  show (NextValue id) = "next(" ++ show id ++ ")"


{- ----------------------------------------------------------------------------
Parser for Programs
---------------------------------------------------------------------------- -}


program :: Parser Program
program = liftM Program (many modul)


modul :: Parser Module
modul =  do keyword "MODULE"
            name <- reserved keywords identifier << ws
            params <- option [] (between (token "(") (token ")") parameters)
            elements <- many element
            return (Module name params elements)
  where
    parameters = sepBy1 (reserved keywords identifier << ws) (token ",")


element :: Parser Element
element = varDecl
       <|> ivarDecl
       <|> constDecl
       <|> defineDecl
       <|> initConstraint
       <|> invarConstraint
       <|> transConstraint
       <|> assign
       <|> fairness
       <|> justice
       <|> compassion
  where
    varDecl =  do keyword "VAR"
                  vars <- many1 (do id <- reserved keywords identifier << ws
                                    token ":"
                                    ty <- typeSpec
                                    token ";"
                                    return (id, ty))
                  return (VarDecl vars)

    ivarDecl =  do keyword "IVAR"
                   vars <- many1 (do id <- reserved keywords identifier << ws
                                     token ":"
                                     ty <- typeSpec
                                     token ";"
                                     return (id, ty))
                   return (IVarDecl vars)

    defineDecl =  do keyword "DEFINE"
                     defs <- many1 (do id <- reserved keywords identifier << ws
                                       token ":="
                                       expr <- basicExpr
                                       token ";"
                                       return (id, expr))
                     return (DefineDecl defs)

    constDecl =  do keyword "CONSTANTS"
                    consts <- sepBy1 (reserved keywords identifier << ws)
                                     (token ",")
                    token ";"
                    return (ConstDecl consts)

    initConstraint =  do keyword "INIT"
                         expr <- basicExpr
                         optional (token ";")
                         return (Init expr)

    invarConstraint =  do keyword "INVAR"
                          expr <- basicExpr
                          optional (token ";")
                          return (Invar expr)

    transConstraint =  do keyword "TRANS"
                          expr <- basicExpr
                          optional (token ";")
                          return (Trans expr)

    assign =  do keyword "ASSIGN"
                 assigns <- many1 (do lhs <- assignLhs
                                      token ":="
                                      rhs <- basicExpr
                                      token ";"
                                      return (lhs, rhs))
                 return (Assign assigns)
      where
        assignLhs =  do keyword "init"
                        token "("
                        id <- complexId
                        token ")"
                        return (InitialValue id)
                 <|> do keyword "next"
                        token "("
                        id <- complexId
                        token ")"
                        return (NextValue id)
                 <|> do id <- complexId
                        return (CurrentValue id)

    fairness =  do keyword "FAIRNESS"
                   expr <- basicExpr
                   optional (token ";")
                   return (Fairness expr)

    justice =  do keyword "JUSTICE"
                  expr <- basicExpr
                  optional (token ";")
                  return (Justice expr)

    compassion =  do keyword "COMPASSION"
                     token "("
                     exprA <- basicExpr
                     token ","
                     exprB <- basicExpr
                     token ")"
                     optional (token ";")
                     return (Compassion exprA exprB)


typeSpec :: Parser Type
typeSpec = boolSpec
        <|> wordSpec
        <|> enumSpec
        <|> rangeSpec
        <|> arraySpec
  where
    boolSpec =  do keyword "boolean"
                   return BoolType

    wordSpec =  do keyword "word"
                   token "["
                   width <- integer
                   token "]"
                   return (WordType width)

    enumSpec =  do token "{"
                   values <- sepBy1 (liftM Symbol identifier <|>
                                     liftM Number integer) (ws >> token ",")
                   token "}"
                   return (EnumType values)

    rangeSpec =  do from <- integer
                    token ".."
                    to <- integer
                    return (RangeType from to)

    arraySpec =  do keyword "array"
                    from <- integer
                    token ".."
                    to <- integer
                    keyword "of"
                    ty <- typeSpec
                    return (ArrayType from to ty)


-- ----------------------------------------------------------------------------
