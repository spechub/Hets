
{- |
Module      :  $Header$
Copyright   :  (c) Klaus Lüttich, Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

   This file implements parsers for annotations and annoted items.
   Follows Chap. II:5 of the CASL Reference Manual.

   uses Lexer, Keywords and Token rather than CaslLanguage 
-}

module Common.Anno_Parser where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Error
import Text.ParserCombinators.Parsec.Pos as Pos

import Common.Lexer
import Common.Token
import Common.Id as Id
import Common.AS_Annotation

comment :: GenParser Char st Annotation
comment = commentLine <|> commentGroup

some_id :: GenParser Char st Id
some_id = mixId keys keys where keys = ([], [])

charOrEof :: Char -> GenParser Char st ()
charOrEof c = (char c >> return ()) <|> eof
newlineOrEof :: GenParser Char st ()
newlineOrEof = charOrEof '\n'

commentLine :: GenParser Char st Annotation
commentLine = do try $ string "%%"
                 line <- manyTill anyChar newlineOrEof
                 return $ Unparsed_anno Comment_start (Line_anno line) []

commentGroup :: GenParser Char st Annotation 
commentGroup = do try $ string "%{"
                  text_lines <- manyTill anyChar $ try $ string "}%"
                  sp <- getPos
                  return $ Unparsed_anno Comment_start 
                           (Group_anno $ lines text_lines) 
                           [Id.incSourceColumn sp (-2)]

annote :: GenParser Char st Annotation
annote = anno_label <|> 
         do start_source_pos <- getPos
            i <- try anno_ident
            anno <- ((annote_group i) <|> (annote_line i))
            end_pos <- getPos
            case (parse_anno (add_pos end_pos anno) start_source_pos) of
                Left  err -> do setPosition (errorPos err)
                                fail (tail (showErrorMessages "or" 
                                            "unknown parse error" 
                                            "expecting" "unexpected" 
                                            "end of input"
                                            (errorMessages err)))
                Right pa -> return pa
    where add_pos sp a =
              up_pos_l (\l -> l++[conv sp a]) a
          conv sp a = case a of
                      Unparsed_anno _ (Group_anno _) _ -> 
                          Id.incSourceColumn sp (-2)
                      _ -> sp

anno_label :: GenParser Char st Annotation
anno_label = 
    do try $ string "%("
       label_lines <- manyTill anyChar $ try $ string ")%"
       sp <- getPos
       return (Label (lines label_lines) [Id.incSourceColumn sp (-2)])

anno_ident :: GenParser Char st Annote_word
anno_ident = fmap Annote_word $ string "%" >> casl_words

annote_group :: Annote_word -> GenParser Char st Annotation
annote_group s = do char '(' -- ) 
                    annote_lines <- manyTill anyChar $ try $ string ")%"
                    return $ Unparsed_anno s
                            (Group_anno $ lines annote_lines) []

annote_line :: Annote_word -> GenParser Char st Annotation
annote_line s = 
    do line <- manyTill anyChar newlineOrEof
       return $ Unparsed_anno s (Line_anno line) []

annotationL :: GenParser Char st Annotation
annotationL = do start_source_pos <- getPos
                 anno <- (comment <|> annote) <?> "\"%\""
                 return (add_pos anno start_source_pos)
    where add_pos an p = up_pos_l (\l -> p:l) an

annotations :: GenParser Char st [Annotation]
annotations = many (annotationL << skip) 

-----------------------------------------
-- parser for the contents of annotations
-----------------------------------------

commaIds :: GenParser Char st [Id]
commaIds = commaSep1 some_id 

parse_anno :: Annotation -> Pos -> Either ParseError Annotation
parse_anno anno sp = 
    case anno of
    Unparsed_anno (Annote_word kw) as _ ->
        case lookup kw $ swapTable semantic_anno_table of
        Just sa -> semantic_anno sa as sp 
        _  -> let nsp = Id.incSourceColumn sp (length kw + 1)
                  inp = case as of Line_anno str -> str 
                                   Group_anno ls -> unlines ls
                  mkAssoc dir p = do res <- p
                                     return (Assoc_anno dir res []) in
                  case kw of
             "prec"    -> parse_internal prec_anno    nsp inp
             "display" -> parse_internal display_anno nsp inp
             "left_assoc" -> parse_internal (mkAssoc ALeft commaIds) nsp inp
             "right_assoc" -> parse_internal (mkAssoc ARight commaIds) nsp inp
             "number"   -> parse_internal number_anno   nsp inp
             "string"   -> parse_internal string_anno   nsp inp
             "list"     -> parse_internal list_anno     nsp inp
             "floating" -> parse_internal floating_anno nsp inp
             _ -> Right anno
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
       (c, p) <- option ([], []) $ comps ([], [])
       return $ Id l c p

prec_anno, number_anno, string_anno, list_anno, floating_anno 
    :: GenParser Char st Annotation
prec_anno = do left_ids <- braces commaIds
               sign <- (try (string "<>") <|> (string "<")) << skip
               right_ids <- braces commaIds
               return $ Prec_anno 
                          (if sign == "<" then Lower else BothDirections)
                          left_ids
                          right_ids
                          [] 

number_anno   = 
    do n <- some_id
       return $ Number_anno n []

list_anno     = do 
    bs <- caslListBrackets 
    p <- commaT
    ni <- some_id 
    q <- commaT
    ci <- some_id
    return $ List_anno bs ni ci (toPos p [] q)

string_anno   = literal_2ids_anno String_anno

floating_anno = literal_2ids_anno Float_anno

literal_2ids_anno :: (Id -> Id -> [Pos] -> Annotation) 
                -> GenParser Char st Annotation
literal_2ids_anno con = 
    do i1 <- some_id
       p <- commaT
       i2 <- some_id
       return $ con i1 i2 [tokPos p]

display_anno :: GenParser Char st Annotation
display_anno = do ident <- some_id
                  tls <- many $ foldl1 (<|>) $ map disp_symb 
                         display_format_table
                  return (Display_anno ident tls [])
    where  disp_symb (df_symb, symb) = 
               do (try $ string $ "%"++symb) << skip
                  str <- manyTill anyChar $ lookAhead $ charOrEof '%'
                  return (df_symb, reverse $ dropWhile (`elem` whiteChars)
                         $ reverse str)

semantic_anno :: Semantic_anno -> Annote_text -> Pos 
              -> Either ParseError Annotation
semantic_anno sa text sp =
    let err = Left $ newErrorMessage 
              (UnExpect ("garbage after %" 
                         ++ lookupSemanticAnno sa))
              $ fromPos sp
        in case text of
                     Line_anno str ->      
                         if all (`elem` whiteChars) str then 
                            Right $ Semantic_anno sa []
                         else err
                     _ -> err

