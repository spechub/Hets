
{- HetCATS/Anno_Parser.hs
   Authors: Klaus L�ttich, Christian Maeder
   Year:   2002/2003

   This file implements parsers for annotations and annoted items.

   used Lexer, Keywords and Token rather than CaslLanguage 
-}

module Anno_Parser where
import Parsec
import ParsecError
import ParsecPos
import ParsecPerm

import Lexer
import Token

import Id
import AS_Annotation


comment, commentLine, commentGroup :: GenParser Char st Annotation
comment = commentLine <|> commentGroup

commentLine = do try (string "%%")
		 line <- manyTill�anyChar�(newline <|> (eof >> return '\n'))  
		 return (Comment_line line [])
		 
commentGroup = do try (string "%{")
		  text_lines <- manyTill anyChar (try (string "}%"))
		  sp <- getPosition
		  return (Comment_group (lines text_lines) [conv sp])
    where conv sp = (\(l,c) -> (l,c-2)) (convToPos sp)

annote, label :: GenParser Char st Annotation
annote = Anno_Parser.label <|> 
	 do start_source_pos <- getPosition
	    ide <- anno_ident
	    anno <- ((annote_group ide) <|> (annote_line ide))
	    end_pos <- getPosition
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
	  conv sp a = (\(l,c) -> case a of
			   Annote_group _ _ _ -> (l,c-2)
			   Annote_line  _ _ _ -> (l,c)
			   _ -> error "nothing to be done for other Annos"
		   ) (convToPos sp)

label = do try(string "%(")
	   label_lines <- manyTill anyChar (string ")%")
	   sp <- getPosition
	   return (Label (lines label_lines) [conv sp])
    where conv sp = (\(l,c) -> (l,c-2)) (convToPos sp)

anno_ident :: GenParser Char st String
anno_ident = string "%" >> scanAnyWords

annote_group, annote_line :: String -> GenParser Char st Annotation
annote_group ide = 
    do char '(' -- ) 
       annote_lines <- manyTill anyChar (string ")%")
       return (Annote_group ide (lines annote_lines) [])

annote_line ide = 
                 do anno <- do char ' '
			       line <- manyTill anyChar 
			                               (newline <|>
							(eof >> return '\n'))
			       return (Annote_line ide line [])
			       -- AnnoteWord (%implies ...)
			    <|> do newline
				   return (Annote_line ide "" [])
		    return(anno)

annotationL, annotation :: GenParser Char st Annotation
annotationL = do start_source_pos <- getPosition
		 anno <- (comment <|> annote)
		 return (add_pos anno (convToPos start_source_pos))
    where add_pos an p = up_pos_l (\l -> p:l) an

annotation = do a <- annotationL  
		skip -- cause all parsers above are not lexeme
		return a

annotations :: GenParser Char st [Annotation]
annotations = many annotation

-----------------------------------------
-- parser for the contents of annotations
-----------------------------------------

parse_anno :: Annotation -> SourcePos -> Either ParseError Annotation
parse_anno anno sp = case anno of
 		     Annote_line kw as pos ->  			 
		        case kw of
			 "def"     -> semantic_anno Definitional kw as sp pos
			 "implies" -> semantic_anno Implies      kw as sp pos
			 "cons"    -> semantic_anno Conservative kw as sp pos
			 "mono"    -> semantic_anno Monomorph    kw as sp pos
			 _         -> parse_anno (Annote_group kw [as] pos) sp 
		     Annote_group kw as _ -> 
			 case kw of
			  "prec"    -> parse_internal prec_anno    nsp inp
			  "display" -> parse_internal display_anno nsp inp
			  "left_assoc" -> parse_internal 
                                                   (lassoc assoc_anno) 
			                           nsp inp
			  "right_assoc" -> parse_internal 
			                           (rassoc assoc_anno) 
			                           nsp inp
			  "number"   -> parse_internal number_anno   nsp inp
			  "string"   -> parse_internal string_anno   nsp inp
			  "list"     -> parse_internal list_anno     nsp inp
			  "floating" -> parse_internal floating_anno nsp inp
			  _ -> Right anno
			  {- a strict implementation:
			     _ -> Left(newErrorMessage 
					    (UnExpect ("kind of annotation or this kind is not allowed as group: " ++ kw))
					    sp) -}
			 where nsp = updatePosString sp (kw ++ "(")
			       inp = unlines as
			       lassoc p = do res <- p
					     return (Lassoc_anno res [])     
			       rassoc p = do res <- p
					     return (Rassoc_anno res [])
			       assoc_anno = (sepBy1 parseId commaT)


		     _ -> Right anno

parse_internal :: GenParser Char () a -> SourcePos -> [Char] 
	       -> Either ParseError a
parse_internal p sp inp = parse (do setPosition sp
				    skip
				    res <- p
				    return res
				)
			        (sourceName sp)
			        inp 

prec_anno, number_anno, string_anno, list_anno, floating_anno 
    :: GenParser Char st Annotation
prec_anno = do left_ids <- oBraceT >> sepBy1 parseId commaT << cBraceT
	       sign <- (try (string "<>") <|> (string "<")) << skip
	       right_ids <- oBraceT >> (sepBy1 parseId commaT) << cBraceT
	       return ( Prec_anno (sign == "<")
				  left_ids
				  right_ids
			          []
		      )

number_anno   = literal_anno f 1 "number"
    where f [x] = Number_anno x
	  f _   = error "wrong_number of ids"
string_anno   = literal_anno f 2 "string"
    where f [x1,x2] = String_anno x1 x2
	  f _       = error "wrong_number of ids"
floating_anno = literal_anno f 2 "floating"
    where f [x1,x2] = Float_anno x1 x2
	  f _       = error "wrong_number of ids"
list_anno     = literal_anno f 3 "list"
    where f [x1,x2,x3] = List_anno x1 x2 x3
	  f _          = error "wrong_number of ids"

literal_anno :: ([Id] -> [a] -> b) -> Int -> [Char] -> GenParser Char st b
literal_anno con nums conStr = 
    do ids <- sepBy1 parseId commaT
       if length ids == nums then return $ con ids $ []
	else unexpected $ "Annotation \"" ++ conStr ++ 
		          "\" malformed: wrong number of ids, " ++ 
		          show nums ++ " id(s) expected!" 


display_anno :: GenParser Char st Annotation
display_anno = do ident <- parseId
		  tls <- permute ( mklst <$?> (disp_symb "HTML")
				         <|?> (disp_symb "LATEX")
				         <|?> (disp_symb "RTF") )
		  return (Display_anno ident tls [])
    where mklst a b c = [a,b,c] 
	  disp_symb sym = ((ready_symb,""),
				 do { symb <- (try (string 
							   ready_symb))
				              << skip
				    ; str <- manyTill anyChar 
				      ((fmap 
					(\_->())
					(lookAhead (string "%")))
				       <|>
				       eof)
				    ; return (symb, reverse $
					      dropWhile (`elem` whiteChars)
					      $ reverse str)
				    }
				) where ready_symb = "%"++sym

semantic_anno :: (a -> b) -> [Char] -> [Char] -> SourcePos -> a 
	      -> Either ParseError b
semantic_anno anno kw as sp pos = 
    if (`elem` whiteChars) `all` as then 
       Right (anno pos)
    else 
       Left (newErrorMessage (Expect("only whitespaces after %" ++ kw)) sp)

