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

casl_no_bracket_sign = "+-*/|\\&=,`<>!?:$@#^~¡¿×÷£©±¶§¹²³¢º¬µ.·"

casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm def else end " ++
    "exists false fit forall free from generated get given " ++
    "hide idem if in lambda library local not op ops pred preds " ++
    "result reveal sort sorts spec then to true type types " ++
    "unit units var vars version view ehen with within . ·"

casl_reserved_ops = 
    ": :? ::= = => <=> . · | |-> \\/ /\\ ¬"

caslDef = ( emptyDef {P.nestedComments = False
		     ,P.commentStart   = "%["
		     ,P.commentEnd     = "]%"
		     ,P.identStart     = oneOf(casl_letter)
		     ,P.identLetter    = (try infix_underscore
					  <|>
					  oneOf(casl_letter ++ "'") 
					  <|> 
					  digit)
		     ,P.reservedNames  = words(casl_reserved_words)
		     ,P.opStart = oneOf(casl_no_bracket_sign)
		     ,P.opLetter = oneOf(casl_no_bracket_sign)
		     ,P.reservedOpNames = words(casl_reserved_ops)
		     })

infix_underscore = do { uc <- try (char '_')
		      ; notFollowedBy (oneOf(" _\n" ++ 
					     casl_no_bracket_sign)
				      )
		      ; return uc
		      }

casl_lexer = P.makeTokenParser (caslDef)

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

-- parsers returning Ids according Id.hs
simple_id = do { sp <- getPosition
	       ; id <- identifier
	       ; return (Id([Token(id,convToPos sp)],[]))
	       }

casl_id = comp_id -- <|> token_id
 
token_id = do { tok <- try CaslLanguage.token
	      ; return (Id([tok],[]))
	      }

token = do { sp  <- getPosition 
	   ; tok <-  choice [identifier,lexeme dot_words,operator, 
			     fmap (\x -> show x) (digit <|> charLiteral)]
	   ; return (Token(tok,convToPos sp))
	   }

place = (do { sp  <- getPosition
	    ; try (symbol Id.place)
	    ; return (Token(Id.place,convToPos sp))
	    }
	 ) <?> "place"

mixfix_id = do { ids <- many1 (try CaslLanguage.token <|> 
			      try CaslLanguage.place)
	       ; return (Id(ids,[]))
	       }

comp_id = do { mid <- mixfix_id
             ; ts <- return (case mid of Id(t,_)-> t)
             ; option (Id(ts, [])) 
               (do {cs <- squares (sepBy1 comp_id comma);
                    return (Id(ts, cs))
                   })
             }
