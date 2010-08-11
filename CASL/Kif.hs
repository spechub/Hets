{- |
Module      :  $Header$
Description :  Parsing lists of lists with SUMO .kif files
Copyright   :  (c) T.Mossakowski, C.Maeder and Uni Bremen 2006
License     :  GPLv2 or higher

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsing lists of lists with SUMO (suggested upper merged ontology) .kif files
-}

module CASL.Kif where

import Common.Parsec
import Text.ParserCombinators.Parsec
import qualified Text.PrettyPrint.HughesPJ as Doc
import Data.Char

data StringKind = Quoted | KToken | QWord | AtWord deriving Show

data ListOfList = Literal StringKind String | List [ListOfList]
     deriving Show

-- | skip white spaces and comments for the lexer

dq :: Char
dq = '"'

scanString :: CharParser st String
scanString = enclosedBy
  (flat $ many $ fmap (: []) (satisfy (/= dq)) <|> tryString "\\\"")
  $ char dq

isKTokenChar :: Char -> Bool
isKTokenChar c = isPrint c && not (elem c "()\";" || isSpace c)

scanLiteral :: CharParser st ListOfList
scanLiteral = do
  s@(c : _) <- many1 (satisfy isKTokenChar)
  return $ Literal (if c == '?' then QWord else
                        if c == '@' then AtWord else KToken) s

eolOrEof :: GenParser Char st ()
eolOrEof = (oneOf "\n\r" >> return ()) <|> eof

commentOut :: CharParser st ()
commentOut = char ';' >> manyTill anyChar eolOrEof >> return ()

skip :: CharParser st [()]
skip = many ((satisfy isSpace >> return ()) <|> commentOut)

lexem :: CharParser st a -> CharParser st a
lexem = (<< skip)

nestedList :: CharParser st ListOfList
nestedList = do
    lexem $ char '('
    l <- many nestedList
    lexem $ char ')'
    return $ List l
 <|> fmap (Literal Quoted) (lexem scanString)
 <|> lexem scanLiteral

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
    Left err -> print err
    Right l -> print $ Doc.vcat $ map ppListOfList l
