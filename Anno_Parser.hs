module Anno_Parser where
import Parsec
import qualified ParsecToken as P
import ParsecError
import ParsecPos
import ParsecPerm

import CaslLanguage 
import Id
import AS_Annotation

comment = commentLine <|> commentGroup

commentLine = do { try(string("%%"))
		 ; line <- manyTill anyChar (lookAhead newline)  
		 ; return (Comment_line line)
		 }

commentGroup = do { try(string("%{"))
		  ; text_lines <- manyTill (anyChar) 
		    (try(string("}%")))
		  ; return (Comment_group(lines(text_lines)))
		  }

annote = Anno_Parser.label <|> 
	 do { start_source_pos <- getPosition
	    ; id <- anno_ident
	    ; anno <- ((annote_group id) <|> (annote_line id))
	    ; parsed_anno <- return(parse_anno anno start_source_pos)
	    ; case parsed_anno of
	      Left  err -> do { let 
				sp = errorPos err
				nsp = setSourceColumn sp ((sourceColumn sp)-1)
				in
				setPosition nsp
			      {- ; inp <- getInput
			      ; setInput ("%"++inp)
			      ; char '%' -}
			      ; fail (tail (showErrorMessages "or" 
					    "unknown parse error" 
					    "expecting" "unexpected" 
					    "end of input"
					    (errorMessages err)))
			      } 
	      -- simple error handling 
	      Right pa -> return pa
	    }

label = do { try(string "%(")
	   ; label_lines <- manyTill anyChar (string ")%")
	   ; return (Label (lines label_lines))
	   }

anno_ident = do { string "%"
		; ident <- casl_words
		; return ident 
		}

annote_group id = do { char '(' -- ) 
		     ; annote_lines 
		       <- manyTill (anyChar) (string ")%")
		     ; return (Annote_group (id,(lines annote_lines)))
		     }

annote_line id = do { anno <- (do { char ' '
				  ; annote_line 
				    <- manyTill anyChar (lookAhead newline)
				  ; return (Annote_line(id,
							annote_line))
				  } 
			       -- AnnoteWord (%implies ...)
			       <|> do { newline
				      ; return (Annote_line(id,""))
				      })
		    ; return(anno)
		    }

annotation = many (do { start_source_pos <- getPosition
		      ; anno <- (comment <|> annote)
	 	      ; end_source_pos <- getPosition
		      ; whiteSpace -- cause all parser above are not lexeme
		      ; return (Pos_anno((convToPos(start_source_pos),
					  convToPos(end_source_pos)),
					 anno))
		      })

-----------------------------------------
-- parser for the contents of annotations
-----------------------------------------

parse_anno :: Annotation -> SourcePos -> Either ParseError Annotation
parse_anno anno sp = case anno of
		     Annote_line(kw,as) ->  			 
		       (case kw of
			"def"     -> semantic_anno Definitional kw as sp
			"implies" -> semantic_anno Implies      kw as sp 
			"cons"    -> semantic_anno Conservative kw as sp
			otherwise -> parse_anno (Annote_group(kw,[as])) sp
		       )
		     Annote_group(kw,as) -> 
			 (case kw of
			  "prec"    -> parse_internal prec_anno    nsp inp
			  "display" -> parse_internal display_anno nsp inp
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
			   
semantic_anno anno kw as sp = 
    if all (`elem` " \t") as then 
       Right anno
    else 
       Left (newErrorMessage (Expect("only whitespaces after " ++ kw)) sp)
