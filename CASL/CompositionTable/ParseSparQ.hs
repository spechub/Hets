{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  fmossa@tzi.de
Stability   :  provisional
Portability :  portable

Parses CompositionTables in SparQ(Lisp)-Format using Parsec <http://www.cs.uu.nl/~daan/parsec.html>

-}

module CASL.CompositionTable.ParseSparQ where

import Data.Char (digitToInt, isDigit)
import Common.Id -- (Token(..), place)
import Common.Token
import Text.ParserCombinators.Parsec
import qualified Text.ParserCombinators.Parsec.Pos as Pos
import CASL.CompositionTable.CompositionTable
import Common.AnnoState
import Common.Lexer
import Debug.Trace

parse_ p inp = runParser p (emptyAnnos ()) "" inp

parseFile p f = do s <- readFile f
		   putStrLn (show (parse_ p s))

parseFile_ :: GenParser Char (AnnoState ()) a -> String ->IO (Either ParseError a)
parseFile_ p f = do s <- readFile f
		    return (parse_ p s)
		     

parseSparQTableFromFile :: String -> IO (Either ParseError Table)

parseSparQTableFromFile filename =    do ret <- (parseFile_ parseSparQTable filename)
					 return ret


-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)

parseSparQTable :: CharParser st Table
parseSparQTable = do skipMany skippable
		     calculusName <- parseCalculusName
		     skipMany skippable 
		     identityRelation <- parseCalculusProperties
		     skipMany skippable
		     ct <- parseConversetable
		     try( do skipMany skippable
			     s <- parseReflectionOperations
			     skipMany skippable) 
		      <|> skipMany skippable	     
		     br <- parseBaseRelations
		     skipMany skippable
		     compt <- parseCompTable
		     return (Table (Table_Attrs calculusName (Baserel identityRelation) br) compt
				   ct (Reflectiontable []) (Models []))



parseCalculusProperties :: CharParser st String
parseCalculusProperties = do many (try (parseArity) <|> 
				   try (parseBasisEntity) <|>
				   try(parseQualifier) <|> 
				   try (parseParametric))	  
			     id <- parseIdentityRelation
			     many (try (parseArity) <|> 
				   try (parseBasisEntity) <|>
				   try(parseQualifier))	  
			     many skippable
			     return id	


parseParametric :: CharParser st String
parseParametric = do many skippable
		     string ":parametric?"
		     many space
		     param <- word
		     return param 

parseArity :: CharParser st String
parseArity = do many skippable
		string ":arity"
		many space
		string ":"
		arity <- word
		return arity

parseBasisEntity :: CharParser st String          
parseBasisEntity = do many skippable
		      string ":basis-entity"
		      many space
		      string ":"
		      entity <- word
		      return entity

parseIdentityRelation :: CharParser st String
parseIdentityRelation = do many skippable
			   string ":identity-relation"
			   many space
			   id <- parseRelationId
			   return (baserelBaserel id)

parseQualifier :: CharParser st String
parseQualifier = do many skippable
		    string ":qualifier"
		    many space
		    parseQualifierBrace


parseQualifierBrace :: CharParser st String
parseQualifierBrace = do string "(" <|> string "#'("
			 many (many1 (noneOf "()") <|> 
				      try (parseQualifierBrace))

			 string ")"
			 return ""

skippable :: CharParser st String
skippable = many1 space <|> parseAnnotation

parseAnnotation :: CharParser st String
parseAnnotation = 
		  try (do string ";;#|"
			  many (many1 (noneOf ";")
					  <|> try (string ";" << 
					       notFollowedBy (char
					       ';')))
			  string ";;|#")	
	           <|>

		    do many space
		       string ";" 
		       many (string ";")
		       {-many (parseChar <|> oneOf "\r\t\v\f
		       \160")-}
		       many (noneOf "\n") 
		       string "\n"
			  
	          	  
		     		     

parseCalculusName :: CharParser st String
parseCalculusName = do many skippable
		       string "(def-calculus"
		       many space
		       s <- parseQuotedStrings
		       space
		       return s

parseQuotedStrings :: CharParser st String
parseQuotedStrings = do char '"'
			words <- many1 (noneOf "\"")
		        char '"'
			return words     

word :: CharParser st String
word = many1 (letter <|> char '_' <|> char '.' <|> char '-' <|> digit)

quotedWord :: CharParser st String
quotedWord = do char '"'
		word <- word
		char '"'
		return word  

bracedWord :: CharParser st String
bracedWord = do char '('
		word <- word
		char ')'
		return word
parseBaseRelations :: CharParser st [Baserel]
parseBaseRelations = do many skippable
			string ":base-relations"
			many skippable
			oParenT
			baserels <- many1 parseRelationId
			cParenT
			return baserels

parseCompTable :: CharParser st Compositiontable
parseCompTable = do many skippable 
		    string ":composition-operation"
		    many skippable
		    oParenT	
		    cmptabentries <- parseComptabentryList
		    cParenT
		    return (Compositiontable cmptabentries)		    

parseComptabentryList :: CharParser st [Cmptabentry]
parseComptabentryList = do entries <- many1 parseComptabentry
			   return entries			   

parseComptabentry :: CharParser st Cmptabentry
parseComptabentry = do many skippable
		       oParenT
		       rel1 <- parseRelationId
		       rel2 <- parseRelationId
		       results <- parseComptabentryResults
		       cParenT			
		       return (Cmptabentry (Cmptabentry_Attrs rel1 rel2) (results))
   
parseComptabentryResults :: CharParser st [Baserel]
parseComptabentryResults = try ( do oParenT
				    results <- many1 parseRelationId
				    cParenT
				    return results)
			 <|>
			    try (do string "NIL"
				    return []) 
			 
			 <|>
			    do result <- parseRelationId
			       return [result]
			 <|> 
			     do oParenT
				many space
				cParenT
				return []
			       

parseConversetable :: CharParser st Conversetable
parseConversetable = try( do entry1 <- parseInverse
			     entry3 <- parseShortcut
			     entry2 <- parseHoming		
			     return (Conversetable_Ternary entry1 entry3
				    entry2))
		     <|> do entry <- parseConverse
			    return (Conversetable entry)

parseConverse :: CharParser st [Contabentry]
parseConverse =  do many skippable
		    string ":converse-operation"
		    many skippable
		    oParenT
		    invrels <- many1 parseContabentry
		    cParenT
		    return invrels

parseContabentry:: CharParser st Contabentry
parseContabentry = do many skippable
		      oParenT
		      id1 <- parseRelationId
		      id2 <- parseRelationId
		      cParenT
		      return (Contabentry id1 id2)
	

parseContabentryList :: String -> CharParser st [Contabentry_Ternary]
parseContabentryList s = do many skippable
			    string s
			    many skippable
			    oParenT
			    invrels <- many1 parseContabentryTernary
			    cParenT
			    return invrels

parseContabentryTernary :: CharParser st Contabentry_Ternary
parseContabentryTernary = do many skippable
			     oParenT
			     id1 <- parseRelationId
			     ids <- (many1 parseRelationId) <|> 
				    parseBracedRelationIds 

			     cParenT
			     return (Contabentry_Ternary id1 ids) 
				    
parseBracedRelationIds :: CharParser st [Baserel]
parseBracedRelationIds = do many skippable
			    oParenT
                            ids <- many1 parseRelationId
                            cParenT 
                            return ids	 
				  
parseReflectionOperations :: CharParser st String
parseReflectionOperations =  do many skippable
			        string ":reflection-operation"
			        many skippable
			        oParenT
			        invrels <- many1 parseContabentry
			        cParenT
			        return ""

parseInverse :: CharParser st [Contabentry_Ternary]
parseInverse = parseContabentryList ":inverse-operation"
	  

parseHoming :: CharParser st [Contabentry_Ternary]
parseHoming = parseContabentryList ":homing-operation"


parseShortcut :: CharParser st [Contabentry_Ternary]
parseShortcut = parseContabentryList ":shortcut-operation"

parseRelationId :: CharParser st Baserel
parseRelationId = do chars <- many1 (noneOf "() \r\v\f\t\160\n")
		     skip
		     return (Baserel chars)
parseChar :: CharParser st Char
parseChar = do s <- letter
	       return s
	    <|>
	    do n <- digit
	       return n
	    <|>
	    do u <- char '_'
	       return u 
	    <|>
	    do k <- char '-'
	       return k
	    <|>
	    do l <- char '\''
	       return l
	        
