
{- HetCATS/Anno_Parser.hs
   Author: Klaus Lüttich
   Year:   2002

   This file implements parsers for annotations and annoted items.

   todo:
     - parsing contents of annotations
     - annoted parser
 
-}

module Anno_Parser where
import Parsec
import qualified ParsecToken as P
import ParsecError
import ParsecPos
import ParsecPerm

import Utils

import CaslLanguage
import Id
import AS_Annotation

import P_user_state
import Logic

comment = commentLine <|> commentGroup

commentLine = do try (string "%%")
		 line <- manyTill anyChar (newline <|> (eof >> return '\n'))  
		 return (Comment_line line [])
		 
commentGroup = do try (string "%{")
		  text_lines <- manyTill anyChar (try (string "}%"))
		  sp <- getPosition
		  return (Comment_group (lines text_lines) [c sp])
    where c sp = (\(l,c) -> (l,c-2)) (convToPos sp)

annote = Anno_Parser.label <|> 
	 do start_source_pos <- getPosition
	    id <- anno_ident
	    anno <- ((annote_group id) <|> (annote_line id))
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
	      up_pos_l (\l -> l++[c sp a]) a
	  c sp a = (\(l,c) -> case a of
			   Annote_group _ _ _ -> (l,c-2)
			   Annote_line  _ _ _ -> (l,c)
			   _ -> error "nothing to be done for other Annos"
		   ) (convToPos sp)
label = do try(string "%(")
	   label_lines <- manyTill anyChar (string ")%")
	   sp <- getPosition
	   return (Label (lines label_lines) [c sp])
    where c sp = (\(l,c) -> (l,c-2)) (convToPos sp)

anno_ident = string "%" >> casl_words

annote_group id = do char '(' -- ) 
		     annote_lines <- manyTill anyChar (string ")%")
		     return (Annote_group id (lines annote_lines) [])

annote_line id = do anno <- do char ' '
			       annote_line <- manyTill anyChar 
			                               (newline <|>
							(eof >> return '\n'))
			       return (Annote_line id annote_line [])
			       -- AnnoteWord (%implies ...)
			    <|> do newline
				   return (Annote_line id "" [])
		    return(anno)

annotationL = do start_source_pos <- getPosition
		 anno <- (comment <|> annote)
		 return (add_pos anno (convToPos start_source_pos))
    where add_pos an p = up_pos_l (\l -> p:l) an

annotation = do a <- annotationL  
		whiteSpace -- cause all parsers above are not lexeme
		return a

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
		     Annote_group kw as pos -> 
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
			       assoc_anno = (sepBy1 casl_id comma)


		     _ -> Right anno

parse_internal p sp inp = parse (do setPosition sp
				    whiteSpace
				    res <- p
				    return res
				)
			        (sourceName sp)
			        inp 

prec_anno = do left_ids <- braces (sepBy1 casl_id comma)
	       sign <- (try (symbol "<>") <|> (symbol "<"))
	       right_ids <- braces (sepBy1 casl_id comma)
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

literal_anno con count conStr = 
    do ids <- sepBy1 casl_id comma
       if length ids == count then return $ con ids $ []
	else unexpected $ "Annotation \"" ++ conStr ++ 
		          "\" malformed: wrong number of ids, " ++ 
		          show count ++ " id(s) expected!" 


display_anno = do ident <- casl_id
		  tls <- permute ( mklst <$?> (disp_symb ident "HTML")
				         <|?> (disp_symb ident "LATEX")
				         <|?> (disp_symb ident "RTF") )
		  return (Display_anno ident tls [])
    where mklst a b c = [a,b,c] 
	  disp_symb ident sym = ((ready_symb,""),
				 do { symb <- lexeme (try (string 
							   ready_symb))
				    ; str <- manyTill anyChar 
				      ((fmap 
					(\_->())
					(lookAhead (string "%")))
				       <|>
				       eof)
				    ; return (symb,chomp str)
				    }
				) where ready_symb = "%"++sym


semantic_anno anno kw as sp pos = 
    if (`elem` " \t") `all` as then 
       Right (anno pos)
    else 
       Left (newErrorMessage (Expect("only whitespaces after %" ++ kw)) sp)

