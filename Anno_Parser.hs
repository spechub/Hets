module Anno_Parser where
import Parsec
import qualified ParsecToken as P
import CaslLanguage 
import AS_Annotation

------ helper functions ------ 

convToPos (sp) = (sourceLine(sp),sourceColumn(sp))

------------------------------

comment = commentLine <|> commentGroup

commentLine = lexeme (do { try(string("%%"))
			 ; line <- manyTill anyChar (try (newline))  
			 ; return (Comment_line line)
			 })

commentGroup = lexeme (do { try(string("%{"))
			  ; text_lines <- manyTill (anyChar) 
			    (try(symbol("}%")))
			  ; return (Comment_group(lines(text_lines)))
			  })

annote = label <|> annote_line <|> annote_group

label = lexeme ( do { try(string("%("))
		    ; label_lines <- manyTill 
		      (anyChar) 
		      (try(symbol(")%")))
		    ; return (Label(lines(label_lines)))
		    })

anno_ident = do { try(string("%"))
		; ident <- casl_words
		; return ident 
		}

annote_group =  lexeme ( do { ident <- try anno_ident 
			    ; try(char('(')) 
			    ; annote_lines 
			      <- manyTill (anyChar) (try(symbol(")%")))
			    ; return (Annote_group(ident,lines(annote_lines)))
			    })

annote_line = lexeme ( do { start_source_pos <- try getPosition 
			  ; ident <- try anno_ident
			             -- AnnoteLine
			  ; anno <- (do { try(char(' '))
					; annote_line 
					  <- manyTill anyChar (try newline)
					; return (Annote_line(ident,
							      annote_line))
					} 
				     -- AnnoteWord (%implies ...)
				     <|> do { try newline
					    ; return (Annote_line(ident,""))
					    })
			  ; end_source_pos <- getPosition
			  ; test <- return(2+2) --parse_anno(anno,start_source_pos)
			  ; return (Pos_anno((convToPos(start_source_pos),
					      convToPos(end_source_pos)),
					     anno))
			  })

annotation = many (comment <|> annote)
