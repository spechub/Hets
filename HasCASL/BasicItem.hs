module BasicItem where

import Id
import Lexer
import LocalEnv
import Maybe
import Parsec
import Token
import Type
import Term


{-
isSigStartKeyword s = s `elem` (words "sort sorts op ops pred preds type types var vars axiom axioms forall free generated .") 

getDot = oneOf ".\183"
-}

mapf :: (Functor f) => f a -> (a -> b) -> f b
mapf = flip fmap

semi = bind (\ x y -> (Just x, y)) (skipChar ';') ann 
optSemi = option (Nothing, []) semi

pluralKeyword s = makeToken (string s <++> option "" (string "s"))

sortId = parseId
varId = parseId
opId = parseId
comma = skipChar ','
equal = skipChar '='


data ParsedSortItems = AllLess [(Token, Id)] (Maybe (Token, Id)) 
		     | AllEqual [(Token, Id)] 
		     | SubType (Token, Id) -- Term
		       deriving (Show)

{-
commaSortDecl s1 = do { comma;
		   s <- sepBy sortId comma;
		   option (AllLess (s1:s) Nothing) (subSortDecl (s1:s));
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
-}

subSortDecl l = do { t <- skipChar '<';
		     s <- sortId;
		     return (AllLess l (Just (t, s)))
		   }

sortItem key = do { s1 <- sortId;
		    subSortDecl [(key, s1)]
{-		    <|>
		    commaSortDecl key s1
		    <|>
                    isoDecl key s1
-}
		  } 		

toSymb x = Symb x Sort
mkItem subs supers (key, id) = 
    SortItem (Decl (toSymb id) key []) (SortRels subs supers) Nothing []

asSortItems :: ParsedSortItems -> [SortItem]
asSortItems (AllLess l m) = 
    let p = maybeToList m
        f = map (asType . snd)
	super = f p
	sis = map (mkItem [] super) l 
	subs = f l
	supers = map (mkItem subs []) p
    in sis ++ supers 

sortItemsAux sig key = do { si <- sortItem key;
			    (m, an) <- optSemi;
			    let sig2 = sig in -- addSig sig si an in 
                            case m of Nothing -> return sig2
                                      Just key -> option sig2 
			                          (try (sortItemsAux sig2 key))
			  }

sortItems sig = do { key <- pluralKeyword "sort" 
		   ; sortItemsAux sig key
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

basicItem :: Env -> Parser Env
basicItems sig = do { sig2 <- basicItem sig;
		      option (sig2) (basicItems sig2)
		    }

basicSpec sig = do { ann;
		     basicItems sig
		   }



















