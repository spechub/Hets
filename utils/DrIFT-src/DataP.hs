{-
Adaptation and extension of a parser for data definitions given in
appendix of G. Huttons's paper - Monadic Parser Combinators.
-}

module DataP (Statement(..),Data(..),Type(..),Body(..),
               Name,Var,Class,Constructor,
               datadecl,newtypedecl)
where

import ParseLib2
import Data.Char


data Statement = DataStmt | NewTypeStmt deriving (Eq,Show)
data Data = D {        name :: Name,            -- type name
                       constraints :: [(Class,Var)],
                       vars :: [Var],           -- Parameters
                       body :: [Body],
                       derives :: [Class],              -- derived classes
                       statement :: Statement}
          | Directive
          | TypeName Name
               deriving (Eq,Show)
data Body = Body { constructor :: Constructor,
                   labels :: [Name],
                   types :: [Type]} deriving (Eq,Show)
type Name = String
type Var = String
type Class = String
type Constructor = String
----------------------------------------------------------------------------

extContext :: Parser [()]
extContext = do
   symbol "forall"
   many1 variable
   char '.'
   junk
   constructorP
   many variable
   symbol "=>"
   return []

datadecl :: Parser Data
datadecl = do
    symbol "data"
    cons <- opt constraint
    x <- constructorP
    xs <- many variable
    symbol "="
    opt extContext
    b <- (infixdecl +++ conrecdecl) `sepby1` symbol "|"
    d <- opt deriveP
    return $ D x cons xs b d DataStmt

newtypedecl :: Parser Data
newtypedecl = do
       symbol "newtype"
       cons <- opt constraint
       x <- constructorP
       xs <- many variable
       symbol "="
       b <- conrecdecl
       d <- opt deriveP
       return $ D x cons xs [b] d NewTypeStmt

---------------------------------------------------------------------------

isSign :: Char -> Bool
isSign x = not (isAlpha x || isSpace x || elem x "\"|[](){}")

constructorP :: Parser String
constructorP = token $
       do {x <- upper;xs <- many alphanum;return (x:xs)} +++ do
               char '('
               junk
               char ':'
               y <- many1 $ sat isSign
               junk
               char ')'
               return ("(:" ++ y ++ ")")


infixconstr :: Parser String
infixconstr = token $ do
       x <- char ':'
       y <- many1 $ sat isSign
       return (x:y)


variable :: Parser String
variable = identifier [ "data","deriving","newtype", "type", "forall",
                       "instance", "class", "module", "import",
                       "infixl", "infix","infixr", "default"]

conrecdecl :: Parser Body
conrecdecl = do
       x <- constructorP
       (ls,ts) <- record +++ fmap (\a -> ([],a)) (many type2)
       return $ Body x ls ts

infixdecl :: Parser Body
infixdecl = do
       t1 <- type2
       x <- infixconstr
       ts <- many1 type2
       return $ Body ("(" ++ x ++ ")") [] (t1:ts)

record :: Parser ([String], [Type])
record = do
       symbol "{"
       (ls,ts) <- fmap unzip $ rectype `sepby1` symbol ","
       symbol "}"
       return (ls,ts)

constraint :: Parser [(String, String)]
constraint = do{x <- constrs; symbol "=>"; return x}
       where
       constrs = fmap (\x -> [x]) one +++
                 bracket (symbol "(") (one `sepby` symbol ",") (symbol ")")
       one = do{c <- constructorP; v <- variable; return (c,v)}

deriveP :: Parser [String]
deriveP = do{symbol "deriving"; one +++ more}
       where
       one = fmap (\x -> [x]) constructorP -- well, it has the same form
       more = bracket  (symbol "(")
                       (constructorP `sepby` symbol ",")
                       (symbol ")")
---------------------------------------------------------------------------
data Type      = Arrow Type Type -- fn
               | LApply Type [Type] -- proper application
               | Var String      -- variable
               | Con String      -- constructor
               | Tuple [Type]    -- tuple
               | List Type       -- list
                       deriving (Eq,Show)
type0 :: Parser Type
type0 = type1 `chainr1` fmap (const Arrow) (symbol "->")

type1 :: Parser Type
type1 = (do c <- con
            as <- many1 type2
            return (LApply c as)) +++
        type2

type2 :: Parser Type
type2 = (char '!') +++ return '!' >> var +++ con +++ list +++ tuple

var :: Parser Type
var = fmap Var variable

con :: Parser Type
con = fmap Con constructorP

list :: Parser Type
list = fmap List $ bracket (symbol "[")
                       type0
                       (symbol "]")

tuple :: Parser Type
tuple = fmap f $ bracket (symbol "(")
                       (type0 `sepby` symbol ",")
                       (symbol ")")
       where f [t] = t
             f ts = Tuple ts

--record entry
rectype :: Parser (String,Type)
rectype = do
       s <- variable
       symbol "::"
       opt $ symbol "!"
       t <- type0
       return (s,t)
