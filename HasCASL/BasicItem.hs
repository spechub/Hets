module BasicItem where

import Id
import Lexer
import LocalEnv
import Parsec

{-
isSigStartKeyword s = s `elem` (words "sort sorts op ops pred preds type types var vars axiom axioms forall free generated .") 

getDot = oneOf ".\183"
-}

skipChar c = skip (char c)
semi = skipChar ';' >> ann
optSemi = option [] semi

pluralKeyword s = skip (do { w <- string s;
			     option (w) (char 's' >> return (w++"s"))
			   })

sortId = mixId
varId = mixId
opId = mixId
comma = skipChar ','
equal = skipChar '='

data SortItem = AllLess [Id] (Maybe Id) 
	      | AllEqual [Id] 
	      | SubType Id -- Term
		deriving (Show)

sortDecl s1 = do { comma;
		   s <- sepBy sortId comma;
		   option (AllLess (s1:s) Nothing) (subSortDecl (s1:s));
		 }

subSortDecl l = do { skipChar '<';
		     s <- sortId;
		     return (AllLess l (Just s))
		   }

isoDecl s1 = do { equal;
                  subSortDefn s1
		  <|>
		  do { s <- sepBy sortId equal;
		       return (AllEqual (s1:s))
		     }
		}

subSortDefn s = do { t <- between (try (skipChar '{')) (skipChar '}') 
		     (return ""); -- parse single var decl and term
		     return (SubType s)
		   }

sortItem = do { s1 <- sortId;
		sortDecl s1
		<|>
		subSortDecl [s1]
		<|>
                isoDecl s1
	      } 		

sortItems = do { pluralKeyword "sort";
		 s <- sepBy1 sortItem semi;
		 optSemi;
		 return s 
	       }

opItem = do { o1 <- opId;
	      opDecl o1
	      <|>
	      opDefn o1
	    }

opDecl = return 
opDefn = return

opItems = do { pluralKeyword "op";
	       s <- sepBy1 opItem semi;
	       optSemi;
	       return s;
	     }
		   
sigItems = sortItems -- <|> opItems


basicItem = sigItems 


basicSpec = do { ann;
--		 setState(empty);
		 many1 basicItem;
	       }




















