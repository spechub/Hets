module BasicItem where

import Id
import Lexer
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
comma = skipChar ','
sortEq = skipChar '='

type SortId = Id

data SortItem = AllLess [SortId] (Maybe SortId) 
	      | AllEqual [SortId] 
	      | SubType SortId -- Term
		deriving (Show)

commaSortList s1 = do { comma;
			s <- sepBy sortId comma;
			option (AllLess (s1:s) Nothing) (superSort (s1:s));
		      }

superSort l = do { skipChar '<';
		   s <- sortId;
		   return (AllLess l (Just s))
		 }

equalSort s1 = do { sortEq;
		    s <- sepBy sortId sortEq;
		    return (AllEqual (s1:s))
		  }

sortItem = do { s1 <- sortId;
		commaSortList s1
		<|>
		superSort [s1]
		<|>
                equalSort s1;
	      } 		

parseSortItems = do { pluralKeyword "sort";
		      s <- sepBy1 sortItem semi;
		      optSemi;
		      return s 
		    }
		   
parseSigItems = parseSortItems


parseBasicItem = parseSigItems 


parseBasicSpec = do { ann;
		      many1 parseBasicItem;
		   }




















