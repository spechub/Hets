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

semi = fmap Just (skipChar ';')
optSemi = bind (\ x y -> (x, y)) (option Nothing semi) ann

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


commaSortDecl :: [(Token, Id)] -> Parser ParsedSortItems
commaSortDecl l = do { c <- comma
		     ; s <- sortId
		     ; let l2 = (c, s) : l in
		       commaSortDecl l2
		       <|> subSortDecl l2
		       <|> return (AllLess l2 Nothing)
		     }
equalSortDecl :: Token -> [(Token, Id)] -> Parser [(Token, Id)]
equalSortDecl e l = do { s2 <- sortId
		       ; let l2 = (e, s2):l in
			 option l2 (do { e2 <- equal
				       ; equalSortDecl e2 l2
				       })
		       } 

isoDecl :: Token -> Id -> Parser ParsedSortItems
isoDecl key s1 = do { e <- equal
                    ;  subSortDefn key s1
		      <|>
		      (do { l <- equalSortDecl e [(key, s1)]
			  ; return (AllEqual l)
			  })
		    }

subSortDefn :: Token -> Id -> Parser ParsedSortItems
subSortDefn key s = do { t <- between (try (skipChar '{')) (skipChar '}') 
			 (return "") -- parse single var decl and term
		       ; return (SubType (key, s))
		       }
subSortDecl :: [(Token, Id)] -> Parser ParsedSortItems
subSortDecl l = do { t <- skipChar '<'
		   ; s <- sortId
		   ; return (AllLess l (Just (t, s)))
		   }

sortItem :: Token -> Parser ParsedSortItems
sortItem key = do { s1 <- sortId
		  ; subSortDecl [(key, s1)]
		    <|>
		    commaSortDecl [(key, s1)]
		    <|>
                    isoDecl key s1
		    <|> 
		    return (AllLess [(key, s1)] Nothing)
		  } 		

toSymb x = Symb x Sort
mkItem :: [Type] -> [Type] -> (Token, Id) -> SortItem
mkItem subs supers (key, id) = 
    SortItem (Decl (toSymb id) key []) (SortRels subs supers) Nothing []

asSortItems :: ParsedSortItems -> [SortItem]
asSortItems (AllLess l m) = 
    let p = maybeToList m
        f = map (asType . snd)
	super = f p
	sis = map (mkItem [] super) l 
	subs = reverse (f l)
	supers = map (mkItem subs []) p
    in supers ++ sis 

asSortItems (AllEqual l) =
    let  types = reverse (map (asType . snd) l)
         sorts = map (mkItem types types) l 
    in   sorts -- maybe delete self

asSortItems (SubType p) =
    [mkItem [] [] p]

sortItemsAux sig key = do { si <- sortItem key;
			    (m, an) <- optSemi;
			    let (l:li) = asSortItems si
                                li2 = (l {sortAn = an}) : li
			        sig2 = sig {sorts = li2 ++ sorts sig}
			    in 
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



















