{- |
Module      :  $Header$
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  provisional
Portability :  portable

Parsing lists of lists being MILO (MId-Level Ontology) .kif files
-}

module CASL.Kif where

import Text.ParserCombinators.Parsec
import qualified Text.PrettyPrint.HughesPJ as Doc
import Data.Char

data StringKind = Quoted | Token 

data ListOfList = Literal StringKind String | List [ListOfList]

-- | skip white spaces and comments for the lexer

dq :: Char
dq = '"'

scanString :: CharParser st String
scanString = do 
  o <- char dq
  s <- many $ fmap (: []) (satisfy (/= dq)) <|> (try (string "\\\""))
  c <- char dq
  return $ o : concat s ++ [c]

isTokenChar :: Char -> Bool
isTokenChar c = isPrint c && not (elem c "()\";" || isSpace c)

scanLiteral :: CharParser st String
scanLiteral =  many1 (satisfy isTokenChar)

eolOrEof :: GenParser Char st ()
eolOrEof = (oneOf "\n\r" >> return ()) <|> eof

commentOut :: CharParser st ()
commentOut = char ';' >> manyTill anyChar eolOrEof >> return ()

skip :: CharParser st [()]
skip = many ((satisfy isSpace >> return ()) <|> commentOut)

lexem :: CharParser st a -> CharParser st a
lexem p = do 
  r <- p 
  skip
  return r

nestedList :: CharParser st ListOfList
nestedList = do
    lexem $ char '('
    l <- many nestedList
    lexem $ char ')'
    return $ List l
 <|> fmap (Literal Token) (lexem scanLiteral)
 <|> fmap (Literal Quoted) (lexem scanString)

kifProg :: CharParser st [ListOfList]
kifProg = do
  skip
  l <- many1 nestedList
  eof
  return l

ppListOfList :: ListOfList -> Doc.Doc
ppListOfList e = case e of
    Literal _ s -> Doc.text s 
    List l -> Doc.parens $ Doc.fsep $ map ppListOfList l

kifParse :: String -> IO ()
kifParse s = do 
  e <- parseFromFile kifProg s 
  case e of 
    Left err -> putStrLn $ show err
    Right l -> putStrLn $ show $ Doc.vcat $ map ppListOfList l
 
