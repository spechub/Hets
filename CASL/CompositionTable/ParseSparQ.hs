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

-- * positions from "Text.ParserCombinators.Parsec.Pos" starting at (1,1)

parseSparQTable :: CharParser st Table
parseSparQTable = do skip
		     ct <- parseConversetable
		     skip
		     br <- parseBaseRelations
		     skip
		     compt <- parseCompTable
		     return (Table (Table_Attrs "test" "test" br) compt
				   ct (Models []))

parseBaseRelations :: CharParser st [Baserel]
parseBaseRelations = do skip
			string ":base-relations"
			skip
			oParenT
			baserels <- many1 parseRelationId
			cParenT
			return baserels

parseCompTable :: CharParser st Compositiontable
parseCompTable = do skip 
		    string ":composition-operation"
		    skip
		    oParenT	
		    cmptabentries <- parseComptabentryList
		    cParenT
		    return (Compositiontable cmptabentries)		    

parseComptabentryList :: CharParser st [Cmptabentry]
parseComptabentryList = do entries <- many1 parseComptabentry
			   return entries			   

parseComptabentry :: CharParser st Cmptabentry
parseComptabentry = do oParenT
		       rel1 <- parseRelationId
		       rel2 <- parseRelationId
		       results <- parseComptabentryResults
		       cParenT			
		       return (Cmptabentry (Cmptabentry_Attrs rel1 rel2) (results))
   
parseComptabentryResults :: CharParser st [Baserel]
parseComptabentryResults = do oParenT
			      results <- many1 parseRelationId
			      cParenT
			      return results
			 <|>
			    do string "NIL"
			       return [] 
			       

parseConversetable :: CharParser st Conversetable
parseConversetable = do entry1 <- parseInverse
			entry3 <- parseShortcut
			entry2 <- parseHoming		
			return (Conversetable_Ternary entry1 entry3 entry2)

parseContabentryList :: String -> CharParser st [Contabentry_Ternary]
parseContabentryList s = do skip
			    string s
			    skip
			    oParenT
			    invrels <- many1 parseContabentryTernary
			    cParenT
			    return invrels

parseContabentryTernary :: CharParser st Contabentry_Ternary
parseContabentryTernary = do oParenT
			     id1 <- parseRelationId
			     ids <- many1 parseRelationId
			     cParenT
			     return (Contabentry_Ternary id1 ids) 
				    
				    

parseInverse :: CharParser st [Contabentry_Ternary]
parseInverse = parseContabentryList ":inverse-operation"
	  

parseHoming :: CharParser st [Contabentry_Ternary]
parseHoming = parseContabentryList ":homing-operation"


parseShortcut :: CharParser st [Contabentry_Ternary]
parseShortcut = parseContabentryList ":shortcut-operation"

parseRelationId :: CharParser st Baserel
parseRelationId = do chars <- many1 parseChar
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
	        
