module Anno_Parser where
import Parsec
import qualified ParsecToken as P
import ParsecError
import ParsecPos
import ParsecPerm

import CaslLanguage
import Id
import AS_Annotation

import P_user_state
import Logic

comment = commentLine <|> commentGroup

commentLine = do { try (string "%%")
		 ; line <- manyTill anyChar (lookAhead newline)  
		 ; return (Comment_line line [])
		 }

commentGroup = do { try (string "%{")
		  ; text_lines <- manyTill (anyChar) 
		    (try (string "}%"))
		  ; return (Comment_group (lines text_lines) [])
		  }

annote = Anno_Parser.label <|> 
	 do start_source_pos <- getPosition
	    id <- anno_ident
	    ((annote_group id) <|> (annote_line id))
	    {-case (parse_anno anno start_source_pos) of
	      Left  err -> do { setPosition (errorPos err)
			      ; fail (tail (showErrorMessages "or" 
					    "unknown parse error" 
					    "expecting" "unexpected" 
					    "end of input"
					    (errorMessages err)))
			      } 
	      Right pa -> return pa
	    -}
{-    where switch_logic pa = 		  
	      case pa of 
	      (Logic_anno (logic,sub_logic)) -> -- updateUserState 
	                               (if sub_logic == "" then 
					(update_logic logic)
					else 
					(update_sublogic (logic,sub_logic))
				       )
	                                >> (return pa)
	      otherwise -> return pa
-}

label = do { try(string "%(")
	   ; label_lines <- manyTill anyChar (string ")%")
	   ; return (Label (lines label_lines) [])
	   }

anno_ident = do { string "%"
		; ident <- casl_words
		; return ident 
		}

annote_group id = do { char '(' -- ) 
		     ; annote_lines 
		       <- manyTill (anyChar) (string ")%")
		     ; return (Annote_group id (lines annote_lines) [])
		     }

annote_line id = do { anno <- (do { char ' '
				  ; annote_line 
				    <- manyTill anyChar (lookAhead newline)
				  ; return (Annote_line id annote_line [])
				  } 
			       -- AnnoteWord (%implies ...)
			       <|> do { newline
				      ; return (Annote_line id "" [])
				      })
		    ; return(anno)
		    }

annotations = many (do start_source_pos <- getPosition
		       anno <- (comment <|> annote)
	 	       end_source_pos <- getPosition
		       whiteSpace -- cause all parsers above are not lexeme
		       return (add_pos anno (convToPos start_source_pos))
		    )
    where add_pos an p = an
-----------------------------------------
-- parser for the contents of annotations
-----------------------------------------
{-
parse_anno :: Annotation -> SourcePos -> Either ParseError Annotation
parse_anno anno sp = case anno of
		     Annote_line kw as pos ->  			 
		       (case kw of
			"def"     -> semantic_anno Definitional kw as sp
			"implies" -> semantic_anno Implies      kw as sp 
			"cons"    -> semantic_anno Conservative kw as sp
			otherwise -> parse_anno (Annote_group kw [as] pos) sp
		       )
		     Annote_group kw as pos -> 
			 (case kw of
			  "prec"    -> parse_internal prec_anno    nsp inp
			  "display" -> parse_internal display_anno nsp inp
--			  "logic"   -> parse_internal logic_anno   nsp inp
			  "left_assoc" -> parse_internal 
                                          (lassoc assoc_anno) 
			                  nsp inp
			  "right_assoc" -> parse_internal 
			                   (rassoc assoc_anno) 
			                   nsp inp
			  otherwise -> Left(newErrorMessage 
					    (UnExpect ("kind of annotation or this kind is not allowed as group: " ++ kw))
					    sp)
			 )
			 where nsp = updatePosString sp (kw ++ "(")
			       inp = unlines as
			       lassoc p = do { res <- p
					     ; return (Lassoc_anno res)
					     }
			       rassoc p = do { res <- p
					     ; return (Rassoc_anno res)
					     }
			       assoc_anno = (sepBy1 casl_id comma)


		     otherwise -> Right anno

parse_internal p sp inp = parse (do { setPosition sp
				    ; whiteSpace
				    ; res <- p
				    ; return res
				    })
			  (sourceName sp)
			  inp 

prec_anno = do { left_ids <- braces (sepBy1 casl_id comma)
	       ; sign <- (try (symbol "<>") <|> (symbol "<"))
	       ; right_ids <- braces (sepBy1 casl_id comma)
	       ; return ( Prec_anno ( (sign == "<")
				    , left_ids
				    , right_ids))
	       }


display_anno = do { ident <- casl_id
		  ; tls <- permute ( mklst <$?> (disp_symb ident "HTML")
				           <|?> (disp_symb ident "LATEX")
				           <|?> (disp_symb ident "RTF") )
		  ; return (Display_anno (ident,tls))
		  }
    where mklst a b c = [a,b,c] 
	  disp_symb ident sym = ((ready_symb,show ident),
				 do { symb <- lexeme (try (string 
							   ready_symb))
				    ; str <- manyTill anyChar 
				      ((fmap 
					(\_->())
					(lookAhead (string "%")))
				       <|>
				       eof)
				    ; return (symb,str)
				    }
				) where ready_symb = "%"++sym

{-logic_anno = do { logic <- lexeme casl_words
		; sub_logic <- option "" (lexeme casl_words)
		; eof <?> 
		  "one logic name followed by an optional sublogic name"
		; return (Logic_anno (logic,sub_logic))
		}
-}

semantic_anno anno kw as sp = 
    if (`elem` " \t") `all` as then 
       Right anno
    else 
       Left (newErrorMessage (Expect("only whitespaces after %" ++ kw)) sp)
-}