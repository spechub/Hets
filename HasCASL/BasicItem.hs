module BasicItem where

import Id
import Lexer
import Type
import Term
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

isoDecl sig s1 = do { equal;
                  subSortDefn sig s1
{-		  <|>
		  do { s <- sepBy sortId equal;
		       return (AllEqual (s1:s))
		     }
-}		}

subSortDefn sig s = do { t <- between (try (skipChar '{')) (skipChar '}') 
			         (return ""); -- parse single var decl and term
			 let si = SortItem (Decl (Symb s Sort)
					            (Token("", nullPos)))
			             (SortRels [] []) Nothing
			 in
			 return (sig { sorts = si:(sorts sig) })
		   }

sortItem sig = do { s1 <- sortId;
--		    sortDecl sig s1
--		    <|>
--		    subSortDecl sig [s1]
--		    <|>
                    isoDecl sig s1
		  } 		

sortItemsAux sig = do { sig2 <- sortItem sig;
			option (sig2) 
		          (semi >> option (sig2) 
			        (sortItemsAux sig2))
		      }

sortItems sig = do { pluralKeyword "sort";
		     sortItemsAux sig
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

basicItems sig = do { sig2 <- basicItem sig;
		      option (sig2) (basicItems sig2)
		    }

basicSpec sig = do { ann;
		     basicItems sig
		   }



















