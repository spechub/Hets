{- |
Module      :  ./Common/AnnoParser.hs
Description :  parsers for annotations and annoted items
Copyright   :  (c) Klaus Luettich, Christian Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsers for annotations and annoted items

   Follows Chap. II:5 of the CASL Reference Manual.

   uses Lexer, Keywords and Token rather than CaslLanguage

   semantic annotations now end immediately after the keyword!
-}

module Common.AnnoParser
    ( annotationL
    , annotations
    , fromPos
    , parseAnno
    , parseAnnoId
    , commentLine
    , newlineOrEof
    ) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos as Pos

import Common.Parsec
import Common.Lexer
import Common.Token
import Common.Id as Id
import Common.IRI as IRI
import Common.Keywords
import Common.AS_Annotation
import Common.Utils (trimRight)
import qualified Control.Monad.Fail as Fail

import qualified Data.Map as Map
import Data.List

comment :: GenParser Char st Annotation
comment = commentLine <|> commentGroup

parseAnnoId :: GenParser Char st Id
parseAnnoId = let keys = ([], []) in mixId keys keys

charOrEof :: Char -> GenParser Char st ()
charOrEof c = forget (char c) <|> eof

newlineOrEof :: GenParser Char st ()
newlineOrEof = lookAhead $ charOrEof '\n'

mkLineAnno :: String -> Annote_text
mkLineAnno s = let r = unwords $ words s in Line_anno $
  [' ' | not (null r) && isPrefixOf " " s] ++ r

commentLine :: GenParser Char st Annotation
commentLine = do
    p <- getPos
    tryString percents
    line <- manyTill anyChar newlineOrEof
    q <- getPos
    return $ Unparsed_anno Comment_start (mkLineAnno line) (Range [p, dec q])

dec :: Pos -> Pos
dec p = Id.incSourceColumn p (-1)

mylines :: String -> [String]
mylines s = let strip = unwords . words in
  case lines s ++ ["" | isSuffixOf "\n" s] of
  [] -> []
  [x] -> let x0 = strip x in
         [if null x0 then x0
          else [' ' | head x == ' '] ++ x0 ++ [' ' | last x == ' ']]
  (x : r) ->
     let x0 = strip x
         e = last r
         e0 = strip e
         needsBlank = not (null x0) && head x == ' '
         addBlank y = [' ' | not (null y) && needsBlank] ++ y
     in addBlank x0 : map (addBlank . strip) (init r)
        ++ [if null e then e
            else if null e0 then [' ' | needsBlank]
            else addBlank e0 ++ [' ' | last e == ' ']]

commentGroup :: GenParser Char st Annotation
commentGroup = do
    p <- getPos
    textLines <- plainBlock "%{" "}%"
    q <- getPos
    return $ Unparsed_anno Comment_start
               (Group_anno $ mylines textLines) (Range [p, dec q])

annote :: GenParser Char st Annotation
annote = annoLabel <|> do
    p <- getPos
    i <- try annoIdent
    anno <- annoteGroup p i <|> annoteLine p i
    case parseAnno anno p of
      Left err -> do
        setPosition (errorPos err)
        Fail.fail (tail (showErrorMessages "or" "unknown parse error"
                    "expecting" "unexpected" "end of input"
                    (errorMessages err)))
      Right pa -> return pa

annoLabel :: GenParser Char st Annotation
annoLabel = do
    p <- getPos
    labelLines <- plainBlock "%(" ")%"
    q <- getPos
    return $ Label (mylines labelLines) $ Range [p, dec q]

annoIdent :: GenParser Char st Annote_word
annoIdent = fmap Annote_word $ string percentS >>
    (scanAnyWords <|>
     Fail.fail "wrong comment or annotation starting with a single %")

annoteGroup :: Pos -> Annote_word -> GenParser Char st Annotation
annoteGroup p s =
  let aP = do
        annoteLines <- plainBlock "(" ")%"
        q <- getPos
        return $ Unparsed_anno s (Group_anno $ mylines annoteLines)
                  $ Range [p, dec q]
  in case s of
        Annote_word w -> case lookup w $ swapTable semantic_anno_table of
          Just sa -> return $ Semantic_anno sa
            $ Range [p, Id.incSourceColumn p $ length (show sa) - 3]
          Nothing -> aP
        _ -> aP

annoteLine :: Pos -> Annote_word -> GenParser Char st Annotation
annoteLine p s = do
        line <- manyTill anyChar newlineOrEof
        q <- getPos
        return $ Unparsed_anno s (mkLineAnno line) $ Range [p, dec q]

annotationL :: GenParser Char st Annotation
annotationL = comment <|> annote <?> "\"%\""

annotations :: GenParser Char st [Annotation]
annotations = many (annotationL << skip)

{- ---------------------------------------
parser for the contents of annotations
--------------------------------------- -}

commaIds :: GenParser Char st [Id]
commaIds = commaSep1 parseAnnoId

parseAnno :: Annotation -> Pos -> Either ParseError Annotation
parseAnno anno sp = case anno of
    Unparsed_anno (Annote_word kw) txt qs -> let
          nsp = Id.incSourceColumn sp (length kw + 1)
          inp = annoArg txt
          mkAssoc dir p = do
                        res <- p
                        return (Assoc_anno dir res qs)
          in Map.findWithDefault (Right anno) kw $ Map.map ( \ p ->
                              parseInternal p nsp inp) $ Map.fromList
             [ (left_assocS, mkAssoc ALeft commaIds)
             , (right_assocS, mkAssoc ARight commaIds)
             , (precS , precAnno qs)
             , (displayS , displayAnno qs)
             , (numberS , numberAnno qs)
             , (stringS , stringAnno qs)
             , (listS , listAnno qs)
             , (floatingS, floatingAnno qs)
             , (prefixS, prefixAnno qs)]
    _ -> Right anno

fromPos :: Pos -> SourcePos
fromPos p = Pos.newPos (Id.sourceName p) (Id.sourceLine p) (Id.sourceColumn p)

parseInternal :: GenParser Char () a -> Pos -> String -> Either ParseError a
parseInternal p sp = parse
  (do
    setPosition $ fromPos sp
    spaces
    res <- p
    eof
    return res) (Id.sourceName sp)

checkForPlaces :: [Token] -> GenParser Char st [Token]
checkForPlaces ts =
    do let ps = filter isPlace ts
       if null ps then nextListToks $ topMix3 ([], [])
          -- topMix3 starts with square brackets
          else if isSingle ps then return []
               else unexpected "multiple places"

nextListToks :: GenParser Char st [Token] -> GenParser Char st [Token]
nextListToks f =
    do ts <- f
       cs <- checkForPlaces ts
       return (ts ++ cs)

caslListBrackets :: GenParser Char st Id
caslListBrackets =
    do l <- nextListToks $ afterPlace ([], [])
       (c, p) <- option ([], nullRange) $ comps ([], [])
       return $ Id l c p

precAnno, numberAnno, stringAnno, listAnno, floatingAnno
    :: Range -> GenParser Char st Annotation
precAnno ps = do
    leftIds <- braces commaIds
    sign <- (tryString "<>" <|> string "<") << spaces
    rightIds <- braces commaIds
    return $ Prec_anno
               (if sign == "<" then Lower else BothDirections)
               leftIds
               rightIds
               ps

numberAnno ps = do
    n <- parseAnnoId
    return $ Number_anno n ps

listAnno ps = do
    bs <- caslListBrackets
    commaT
    ni <- parseAnnoId
    commaT
    ci <- parseAnnoId
    return $ List_anno bs ni ci ps

stringAnno ps = literal2idsAnno ps String_anno

floatingAnno ps = literal2idsAnno ps Float_anno

prefixAnno :: Range -> GenParser Char st Annotation
prefixAnno ps = do
    prefixes <- many $ do
        p <- (string colonS >> return "") <|>
             (IRI.ncname << string colonS)
        spaces
        i <- angles IRI.iriParser
        spaces
        return (p, i)
    return $ Prefix_anno prefixes ps

literal2idsAnno :: Range -> (Id -> Id -> Range -> Annotation)
                -> GenParser Char st Annotation
literal2idsAnno ps con = do
    i1 <- parseAnnoId
    commaT
    i2 <- parseAnnoId
    return $ con i1 i2 ps

displayAnno :: Range -> GenParser Char st Annotation
displayAnno ps = do
    ident <- parseAnnoId
    tls <- many $ foldl1 (<|>) $ map dispSymb display_format_table
    return (Display_anno ident tls ps)

dispSymb :: (Display_format, String)
          -> GenParser Char st (Display_format, String)
dispSymb (dfSymb, symb) = do
  tryString (percentS ++ symb) << spaces
  str <- manyTill anyChar $ lookAhead $ charOrEof '%'
  return (dfSymb, trimRight str)
