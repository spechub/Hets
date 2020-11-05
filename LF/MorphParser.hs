module LF.MorphParser where

import LF.Sign
import LF.Morphism

import Common.Lexer
import Common.Parsec
import Common.AnnoParser (commentLine)

import Text.ParserCombinators.Parsec

import System.Directory
import System.IO.Unsafe

import qualified Data.HashMap.Lazy as Map
import Data.Maybe (fromMaybe)


readMorphism :: FilePath -> Morphism
readMorphism file =
     let mor = unsafePerformIO $ readMorph file
     in fromMaybe (error $ "readMorphism : Could not read the " ++
                           "morphism from " ++ show file) mor

readMorph :: FilePath -> IO (Maybe Morphism)
readMorph file = do
  e <- doesFileExist file
  if e then do
       content <- readFile file
       case runParser (parseMorphism << eof) () file content of
               Right m -> return $ Just m
               Left err -> error $ show err
       else return Nothing


parseMorphism :: CharParser st Morphism
parseMorphism = do
     skips $ manyTill anyChar (string "=")
     pkeyword "Morphism"
     skipChar '{'
     mb <- parseWithEq "morphBase"
     skipChar ','
     mm <- parseWithEq "morphModule"
     skipChar ','
     mn <- parseWithEq "morphName"
     skipChar ','
     pkeyword "source"
     skipChar '='
     s <- parseSignature
     skipChar ','
     pkeyword "target"
     skipChar '='
     t <- parseSignature
     skipChar ','
     pkeyword "morphType"
     skipChar '='
     mt <- parseMorphType
     skipChar ','
     pkeyword "symMap"
     skipChar '='
     sm <- parseMap
     skipChar '}'
     return $ Morphism mb mm mn s t mt sm

-- | plain string parser with skip
pkeyword :: String -> CharParser st ()
pkeyword s = keywordNotFollowedBy s (alphaNum <|> char '/') >> return ()

keywordNotFollowedBy :: String -> CharParser st Char -> CharParser st String
keywordNotFollowedBy s c = skips $ try $ string s << notFollowedBy c

skips :: CharParser st a -> CharParser st a
skips = (<< skipMany
        (forget space <|> forget commentLine <|> nestCommentOut <?> ""))

qString :: CharParser st String
qString = skips endsWithQuot

parensP :: CharParser st a -> CharParser st a
parensP p = between (skipChar '(') (skipChar ')') p
     <|> p

bracesP :: CharParser st a -> CharParser st a
bracesP = between (skipChar '{') (skipChar '}')

bracketsP :: CharParser st a -> CharParser st a
bracketsP = between (skipChar '[') (skipChar ']')

endsWithQuot :: CharParser st String
endsWithQuot = do
     skipChar '"'
     manyTill anyChar (string "\"")

commaP :: CharParser st ()
commaP = skipChar ',' >> return ()

sepByComma :: CharParser st a -> CharParser st [a]
sepByComma p = sepBy1 p commaP

skipChar :: Char -> CharParser st ()
skipChar = forget . skips . char

parseWithEq :: String -> CharParser st String
parseWithEq s = do
    pkeyword s
    skipChar '='
    qString

parseSym :: CharParser st Symbol
parseSym = do
    pkeyword "Symbol"
    skipChar '{'
    sb <- parseWithEq "symBase"
    skipChar ','
    sm <- parseWithEq "symModule"
    skipChar ','
    sn <- parseWithEq "symName"
    skipChar '}'
    return $ Symbol sb sm sn

parse1Context :: CharParser st CONTEXT
parse1Context = do
    skipChar '('
    v <- qString
    skipChar ','
    e <- parseExp
    option () $ skipChar ')'
    return [(v, e)]

parseExp :: CharParser st EXP
parseExp = (pkeyword "Type" >> return Type)
   <|> do
    pkeyword "Var"
    fmap Var qString
   <|> do
    pkeyword "Const"
    fmap Const parseSym
   <|> do
    pkeyword "Appl"
    ex <- parensP parseExp
    exl <- bracketsP $ option [] $ sepByComma parseExp
    return $ Appl ex exl
   <|> do
    pkeyword "Func"
    exl <- bracketsP $ option [] $ sepByComma parseExp
    ex <- parensP parseExp
    return $ Func exl ex
   <|> do
    ty <- choice $ map (\ ty -> pkeyword ty >> return ty)
               ["Pi", "Lamb"]
    c <- bracketsP $ option [] $ sepByComma parse1Context
    e <- parensP parseExp
    return $ (case ty of
        "Pi" -> Pi
        "Lamb" -> Lamb
        _ -> error "Pi or Lamb expected.\n") (concat c) e

parseDef :: CharParser st DEF
parseDef = do
    pkeyword "Def"
    skipChar '{'
    pkeyword "getSym"
    skipChar '='
    sym <- parseSym
    skipChar ','
    pkeyword "getType"
    skipChar '='
    tp <- parseExp
    skipChar ','
    pkeyword "getValue"
    skipChar '='
    val <- (pkeyword "Nothing" >> return Nothing)
             <|> do pkeyword "Just"
                    e <- parensP parseExp
                    return $ Just e
    skipChar '}'
    return $ Def sym tp val

parseSignature :: CharParser st Sign
parseSignature = do
    pkeyword "Sign"
    skipChar '{'
    sb <- parseWithEq "sigBase"
    skipChar ','
    sm <- parseWithEq "sigModule"
    skipChar ','
    pkeyword "getDefs"
    skipChar '='
    sd <- bracketsP $ option [] $ sepByComma parseDef
    skipChar '}'
    return $ Sign sb sm sd

parseMorphType :: CharParser st MorphType
parseMorphType =
     choice $ map (\ t -> pkeyword (show t) >> return t)
          [Definitional, Postulated, Unknown ]

parse1Map :: CharParser st (Symbol, EXP)
parse1Map = do
    skipChar '('
    s <- parseSym
    skipChar ','
    e <- parseExp
    skipChar ')'
    return (s, e)

parseMap :: CharParser st (Map.HashMap Symbol EXP)
parseMap = do
     pkeyword "fromList"
     fmap Map.fromList $ bracketsP $ option [] $ sepByComma parse1Map
