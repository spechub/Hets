module CaslLanguage where
import Parsec
import qualified ParsecToken as P
import ParsecLanguage (emptyDef)

import Id
------ helper functions ------ 

convToPos (sp) = (sourceLine(sp),sourceColumn(sp))

------------------------------

casl_letter = ['a'..'z'] ++ ['A'..'Z'] ++
	      [toEnum(192) .. toEnum(207)] ++
              [toEnum(209) .. toEnum(214)] ++
	      [toEnum(216) .. toEnum(221)] ++
	      [toEnum(223) .. toEnum(239)] ++ -- icelandic eth
	      [toEnum(241) .. toEnum(246)] ++
	      [toEnum(248) .. toEnum(253)] ++ -- icelandic thorn
	      [toEnum(255)] 

casl_no_bracket_sign = "+-*/|\\&=`<>!?:$@#^~¡¿×÷£©±¶§¹²³¢°¬µ.·"

casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm def else end " ++
    "exists false fit forall free from generated get given " ++
    "hide idem if in lambda library local not op ops pred preds " ++
    "result reveal sort sorts spec then to true type types " ++
    "unit units var vars version view when with within . ·"

casl_reserved_ops = 
    ": :? ::= = => <=> . · | |-> \\/ /\\ ¬"

caslDef = ( emptyDef {P.nestedComments = True
		     ,P.commentStart   = "%["
		     ,P.commentEnd     = "]%"
		     ,P.identStart     = oneOf casl_letter
		     ,P.identLetter    = (try infix_underscore
					  <|>
					  oneOf(casl_letter ++ "'") 
					  <|> 
					  digit)
		     ,P.reservedNames  = words casl_reserved_words
		     ,P.opStart = oneOf casl_no_bracket_sign
		     ,P.opLetter = oneOf casl_no_bracket_sign
		     ,P.reservedOpNames = words casl_reserved_ops
		     })

infix_underscore = do { uc <- try (char '_')
		      ; notFollowedBy (oneOf(" _\n" ++ 
					     casl_no_bracket_sign)
				      )
		      ; return uc
		      }

casl_lexer = P.makeTokenParser caslDef

whiteSpace    = P.whiteSpace casl_lexer
lexeme        = P.lexeme casl_lexer

symbol        = P.symbol casl_lexer
natural       = P.natural casl_lexer

parens        = P.parens casl_lexer
braces        = P.braces casl_lexer
squares       = P.squares casl_lexer

semi          = P.semi casl_lexer
comma         = P.comma casl_lexer
colon         = P.colon casl_lexer

identifier    = P.identifier casl_lexer
operator      = P.operator casl_lexer 

reserved      = P.reserved casl_lexer
reservedOp    = P.reservedOp casl_lexer

charLiteral   = P.charLiteral casl_lexer
stringLiteral = P.stringLiteral casl_lexer


-- parses an Identifier without consuming following whitespaces
casl_words = do { c  <- (P.identStart caslDef)
		; cs <- many(P.identLetter caslDef)
		; return (c:cs)
		}

dot_words = try (do { dot  <- char '.'
		; word <- casl_words
		; return (dot:word)
		})
	    <?> "dot word"

-- parsers for reserved words and ops with two different signs, bat
-- the same meaning
reserved_dot = (reserved "·") <|> (reserved ".")

reserved_not = (reservedOp "¬") <|> (reserved "not")

reserved_op = (reserved "ops") <|> (reserved "op")

reserved_sort = (reserved "sorts") <|> (reserved "sort")

reserved_pred = (reserved "preds") <|> (reserved "pred")

-- parsers returning Ids according Id.hs
simple_id = do { sp <- getPosition
	       ; id <- identifier
	       ; return (Id [Token id (convToPos sp)] [] [])
	       }

casl_id = comp_id
 
token_id = do { tok <- try CaslLanguage.token
	      ; return (Id [tok] [] [])
	      }

token = do { sp  <- getPosition 
	   ; tok <-  choice [identifier,
			     lexeme dot_words,
			     operator, 
			     fmap (\x -> show x) (charLiteral),
			     fmap (:"") (digit)]
	   ; return (Token tok (convToPos sp))
	   }

place = (do { sp  <- getPosition
	    ; try (symbol Id.place)
	    ; return (Token Id.place (convToPos sp))
	    }
	 ) <?> "place"

place_token = do { pla <- try CaslLanguage.place
		 ; option ([pla]) (do { tok <- try CaslLanguage.token
				      ; return [pla,tok]
				      })
		 }


mixfix_id accum = do { ts <- (try (fmap (:[]) CaslLanguage.place) 
			      <|>
			      try (fmap (:[]) CaslLanguage.token) 
			      <|>
			      special_between (symbol "{") (symbol "}") 
			      (mkTokLst (mixfix_id []))
			      <|>
			      try (special_between (symbol "[") (symbol "]") 
				   (mkTokLst (mixfix_id [])))
			      <|>
			      bracket_pair "{" "}"
			      <|>
			      bracket_pair "[" "]"
			      <?> "mixfix id"
			     )
		     ; sqs <- option [] (lookAhead (fmap (:[]) (symbol "[")))
		     ; fts <- option [] (lookAhead 
					 (fmap (:[]) (CaslLanguage.token)))
		     ; Id ats _ _ <- 
		       let 
		       accum_ts = (accum ++ ts)
		       is_last_op = (case (last accum_ts) of 
				     t@(Token s _) -> not
				                       ((last s) `elem` "[{}]"
							||
							isPlace (t)) )
		       in
		       if sqs == [] then
		       (if is_last_op then
			(if fts == [] then
			 option (Id accum_ts [] []) (mixfix_id accum_ts)
			 else
			 unexpected "token follows token" 
			)
			else -- not is_last_op
			option (Id accum_ts [] []) (mixfix_id accum_ts)
		       )
		       else -- sqs \= []
		       (if isPlace (last accum_ts) then
			option (Id accum_ts [] []) (mixfix_id accum_ts)
			else
			return (Id accum_ts [] [])
		       )
		     ; return (Id ats [] [])
		     }
    where mkTokLst p = fmap (\(Id ts cs pos) -> ts) p
	  bracket_pair open close = do { o_sp <- getPosition
				       ; o <- try (symbol open)
				       ; c_sp <- getPosition
				       ; c <- try (symbol close)
				       ; return [Token o (convToPos o_sp),
						 Token c (convToPos c_sp)]
				       }		

special_between start end p = do { st_sp <- getPosition
				 ; st <- start
				 ; res <- special_manyTill p end
				 ; return ([Token st (convToPos st_sp)] ++
					   res) -- res also contains end
				 }

special_manyTill p end = scan
    where scan  = do{ sp <- getPosition
		    ; e <- end
		    ; return [Token e (convToPos sp)] }
		  <|>
		  do{ x <- p
		    ; xs <- scan
		    ; return (x ++ xs) }


comp_id = do { Id ts _ _  <- test_mixfix_id (mixfix_id [])
             ; Id ts cs pos <- option (Id ts [] []) 
                                   (do { cs <- squares (sepBy1 comp_id comma)
				       ; return (Id ts cs [])
				       })
	     ; option (Id ts cs pos) 
	              (do { ps <- many CaslLanguage.place
			  ; return (Id (ts++ps) cs [])
			  })
             }
    where test_mixfix_id p = do { id@(Id ts _ _) <- p
				; if (case ts of [] -> False
				                 [a] -> not (isPlace a)
				                 otherwise -> True) 
				  then
				  return id
				  else
				  fail "only one place is not a legal mixfix id "
				}