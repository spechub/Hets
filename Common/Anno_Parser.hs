{- |
Module      :  $Header$
Description :  parsers for annotations and annoted items
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Parsers for annotations and annoted items

   Follows Chap. II:5 of the CASL Reference Manual.

   uses Lexer, Keywords and Token rather than CaslLanguage
-}

module Common.Anno_Parser
    ( annotationL
    , annotations
    , fromPos
    , parse_anno
    , some_id
    ) where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos as Pos

import Common.Lexer
import Common.Token
import Common.Id as Id
import Common.Keywords
import Common.AS_Annotation
import qualified Data.Map as Map

comment :: GenParser Char st Annotation
comment = commentLine <|> commentGroup

some_id :: GenParser Char st Id
some_id = mixId keys keys where keys = ([], [])

charOrEof :: Char -> GenParser Char st ()
charOrEof c = (char c >> return ()) <|> eof

newlineOrEof :: GenParser Char st ()
newlineOrEof = lookAhead $ charOrEof '\n'

mkLineAnno :: String -> Annote_text
mkLineAnno s = let r = unwords $ words s in Line_anno $
  (if not (null r) && take 1 s == " " then " " else "") ++ r

commentLine :: GenParser Char st Annotation
commentLine = do
    p <- getPos
    try $ string percents
    line <- manyTill anyChar newlineOrEof
    q <- getPos
    return $ Unparsed_anno Comment_start (mkLineAnno line) (Range [p, q])

dec :: Pos -> Pos
dec p = Id.incSourceColumn p (-2)

mylines :: String -> [String]
mylines s = let strip = unwords . words in case lines s ++
    if drop (length s - 1) s == "\n" then [""] else [] of
  [] -> []
  [x] -> let x0 = strip x in
         [if null x0 then x0
          else (if head x == ' ' then " " else "")  ++ x0
                   ++ if last x == ' ' then " " else ""]
  (x : r) ->
     let x0 = strip x
         e = last r
         e0 = strip e
         needsBlank = not (null x0) && head x == ' '
         addBlank y = (if not (null y) && needsBlank
                       then " " else "") ++ y
     in addBlank x0 : map (addBlank . strip) (init r)
        ++ [if null e then e
            else if null e0 then if needsBlank then " " else ""
            else addBlank e0 ++ if last e == ' ' then " " else ""]

commentGroup :: GenParser Char st Annotation
commentGroup = do
    p <- getPos
    text_lines <- plainBlock "%{" "}%"
    q <- getPos
    return $ Unparsed_anno Comment_start
               (Group_anno $ mylines text_lines) (Range [p, dec q])

annote :: GenParser Char st Annotation
annote = anno_label <|> do
    p <- getPos
    i <- try anno_ident
    anno <- annote_group p i <|> annote_line p i
    case parse_anno anno p of
      Left  err -> do
        setPosition (errorPos err)
        fail (tail (showErrorMessages "or" "unknown parse error"
                    "expecting" "unexpected" "end of input"
                    (errorMessages err)))
      Right pa -> return pa

anno_label :: GenParser Char st Annotation
anno_label = do
    p <- getPos
    label_lines <- plainBlock "%(" ")%"
    q <- getPos
    return $ Label (mylines label_lines) $ Range [p, dec q]

anno_ident :: GenParser Char st Annote_word
anno_ident = fmap Annote_word $ string percentS >>
    (scanAnyWords <|>
     fail "wrong comment or annotation starting with a single %")

annote_group :: Pos -> Annote_word -> GenParser Char st Annotation
annote_group p s = do
    annote_lines <- plainBlock "(" ")%"
    q <- getPos
    return $ Unparsed_anno s (Group_anno $ mylines annote_lines)
               $ Range [p, dec q]

annote_line :: Pos -> Annote_word -> GenParser Char st Annotation
annote_line p s = do
    line <- manyTill anyChar newlineOrEof
    q <- getPos
    return $ Unparsed_anno s (mkLineAnno line) $ Range [p, q]

annotationL :: GenParser Char st Annotation
annotationL = comment <|> annote <?> "\"%\""

annotations :: GenParser Char st [Annotation]
annotations = many (annotationL << skip)

-----------------------------------------
-- parser for the contents of annotations
-----------------------------------------

commaIds :: GenParser Char st [Id]
commaIds = commaSep1 some_id

annoArg :: Annote_text -> String
annoArg txt = case txt of
  Line_anno str -> str
  Group_anno ls -> unlines ls

parse_anno :: Annotation -> Pos -> Either ParseError Annotation
parse_anno anno sp =
    case anno of
    Unparsed_anno (Annote_word kw) txt qs ->
        case lookup kw $ swapTable semantic_anno_table of
        Just sa -> semantic_anno sa txt sp
        _  -> let nsp = Id.incSourceColumn sp (length kw + 1)
                  inp = annoArg txt
                  mkAssoc dir p = do
                        res <- p
                        return (Assoc_anno dir res qs) in
             Map.findWithDefault (Right anno) kw $ Map.map ( \ p ->
                              parse_internal p nsp inp) $ Map.fromList
             [ (left_assocS, mkAssoc ALeft commaIds)
             , (right_assocS, mkAssoc ARight commaIds)
             , (precS    , prec_anno qs)
             , (displayS , display_anno qs)
             , (numberS  , number_anno qs)
             , (stringS  , string_anno qs)
             , (listS    , list_anno qs)
             , (floatingS, floating_anno qs) ]
    _ -> Right anno

fromPos :: Pos -> SourcePos
fromPos p = Pos.newPos (Id.sourceName p) (Id.sourceLine p) (Id.sourceColumn p)

parse_internal :: GenParser Char () a -> Pos -> [Char]
               -> Either ParseError a
parse_internal p sp inp = parse (do setPosition $ fromPos sp
                                    skip
                                    res <- p
                                    eof
                                    return res
                                )
                                (Id.sourceName sp)
                                inp

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

prec_anno, number_anno, string_anno, list_anno, floating_anno
    :: Range -> GenParser Char st Annotation
prec_anno ps = do
    left_ids <- braces commaIds
    sign <- (try (string "<>") <|> (string "<")) << skip
    right_ids <- braces commaIds
    return $ Prec_anno
               (if sign == "<" then Lower else BothDirections)
               left_ids
               right_ids
               ps

number_anno ps = do
    n <- some_id
    return $ Number_anno n ps

list_anno ps = do
    bs <- caslListBrackets
    commaT
    ni <- some_id
    commaT
    ci <- some_id
    return $ List_anno bs ni ci ps

string_anno ps  = literal_2ids_anno ps String_anno

floating_anno ps = literal_2ids_anno ps Float_anno

literal_2ids_anno :: Range -> (Id -> Id -> Range -> Annotation)
                -> GenParser Char st Annotation
literal_2ids_anno ps con = do
    i1 <- some_id
    commaT
    i2 <- some_id
    return $ con i1 i2 ps

display_anno :: Range -> GenParser Char st Annotation
display_anno ps = do
    ident <- some_id
    tls <- many $ foldl1 (<|>) $ map disp_symb display_format_table
    return (Display_anno ident tls ps)
    where  disp_symb (df_symb, symb) =
               do (try $ string $ percentS ++ symb) << skip
                  str <- manyTill anyChar $ lookAhead $ charOrEof '%'
                  return (df_symb, reverse $ dropWhile (`elem` whiteChars)
                         $ reverse str)

semantic_anno :: Semantic_anno -> Annote_text -> Pos
              -> Either ParseError Annotation
semantic_anno sa text sp =
  if all (`elem` whiteChars) $ annoArg text
  then Right $ Semantic_anno sa (Range [sp])
  else Left $ newErrorMessage
           (UnExpect ("garbage after %"
                      ++ lookupSemanticAnno sa)) $ fromPos sp
