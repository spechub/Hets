module CaslLanguage where
import Parsec
import qualified ParsecToken as P
import ParsecLanguage (emptyDef)

casl_letter = ['a'..'z'] ++ ['A'..'Z'] ++
	      [toEnum(192) .. toEnum(207)] ++
              [toEnum(209) .. toEnum(214)] ++
	      [toEnum(216) .. toEnum(221)] ++
	      [toEnum(223) .. toEnum(239)] ++ -- icelandic eth
	      [toEnum(241) .. toEnum(246)] ++
	      [toEnum(248) .. toEnum(253)] ++ -- icelandic thorn
	      [toEnum(255)] 

casl_no_bracket_sign = "+-*/|\\&=,`<>!?:$@#^~¡¿×÷£©±¶§¹²³¢º¬µ."

casl_reserved_words = 
    "and arch as assoc axiom axioms closed comm def else end " ++
    "exists false fit forall free from generated get given " ++
    "hide idem if in lambda library local not op ops pred preds " ++
    "result reveal sort sorts spec then to true type types " ++
    "unit units var vars version view ehen with within . "

casl_reserved_ops = 
    ": :? ::= = => <=> . · | |-> \\/ /\\ ¬"

caslDef = ( emptyDef {P.nestedComments = False
		     ,P.commentStart   = "%["
		     ,P.commentEnd     = "]%"
		     ,P.identStart     = oneOf(casl_letter)
		     ,P.identLetter    = (oneOf(casl_letter++"'") 
					  <|> 
					  digit <|> infix_underscore)
		     ,P.reservedNames  = words(casl_reserved_words)
		     ,P.opStart = oneOf(casl_no_bracket_sign)
		     ,P.opLetter = oneOf(casl_no_bracket_sign)
		     ,P.reservedOpNames = words(casl_reserved_ops)
		     })

infix_underscore = try (do { uc <- char('_')
			   ; notFollowedBy (oneOf(" _\n" ++ 
						  casl_no_bracket_sign ))
			     <|>
			     notFollowedBy (fmap (\() -> ' ') eof)
			   ; return uc
			   })

casl_lexer = P.makeTokenParser (caslDef)

whiteSpace= P.whiteSpace casl_lexer
lexeme    = P.lexeme casl_lexer
symbol    = P.symbol casl_lexer
natural   = P.natural casl_lexer
parens    = P.parens casl_lexer
semi      = P.semi casl_lexer
identifier= P.identifier casl_lexer
reserved  = P.reserved casl_lexer
reservedOp= P.reservedOp casl_lexer

-- parses an Identifier without consuming following whitespaces
casl_words = do { c  <- (P.identStart(caslDef))
		; cs <- many(P.identLetter(caslDef))
		; return (c:cs)
		}

dot_words = do { dot  <- char '.'
	       ; word <- casl_words
	       ; return (dot:word)
	       }


