
{- HetCATS/HasCASL/ParseItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL basic Items
-}

module ParseItem where

import Id
import Keywords
import Lexer
import HToken
import As
import Parsec
import AS_Annotation
import Anno_Parser(annotationL)
import ParseTerm

-----------------------------------------------------------------------------
-- annotations
-----------------------------------------------------------------------------

-- annotations on one line
lineAnnos :: GenParser Char st [Annotation]
lineAnnos = do { p <- getPosition
	       ; do { a <- annotationL  
		    ; skip
		    ; q <- getPosition
		    ; if sourceLine q == sourceLine p then
		      do { l <- lineAnnos
			 ; return (a:l)
			 }
		      else return [a]
		    }
		 <|> return []
	       }

-- optional semicolon followed by annotations on the same line
optSemi :: GenParser Char st (Maybe Token, [Annotation])
optSemi = bind (,) (option Nothing (fmap Just semiT)) lineAnnos

annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

itemList keyword parser constr =
    do { p <- pluralKeyword keyword
       ; (vs, ts, ans) <- itemAux (annoParser parser)
       ; let r = zipWith appendAnno vs ans 
	 in return (constr r (map tokPos (p:ts)))
       }

appendAnno (Annoted x p l r) y =  Annoted x p l (r++y)

itemAux :: GenParser Char st a 
	-> GenParser Char st ([a], [Token], [[Annotation]])
itemAux itemParser = 
    do { a <- itemParser
       ; (m, an) <- optSemi
       ; case m of { Nothing -> return ([a], [], [an])
                   ; Just t -> do { tryItemEnd startKeyword
				  ; return ([a], [t], [an])
				  }
	                        <|> 
	                        do { (as, ts, ans) <- itemAux itemParser
				   ; return (a:as, t:ts, an:ans)
				   }
		   }
       }

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

nullKind = Kind [] (Universe nullPos) []

commaTypeDecl :: TypePattern -> GenParser Char st TypeItem
commaTypeDecl s = do { c <- commaT 
		     ; (is, cs) <- typePattern `separatedBy` commaT
		     ; let l = s : is 
		           p = tokPos c : map tokPos cs
		       in
		       subTypeDecl (l, p)
		       <|> kindedTypeDecl (l, p)
		       <|> return (TypeDecl l nullKind p)
		     }

kindedTypeDecl (l, p) = 
    do { t <- colonT
       ; s <- kind
       ; let d = TypeDecl l s (p++[tokPos t]) in 
	 if length l > 1 then return d
	 else pseudoTypeDef (head l) s [tokPos t]
          <|> return d
       }

isoDecl :: TypePattern -> GenParser Char st TypeItem
isoDecl s = do { e <- equalT
               ; subTypeDefn (s, tokPos e)
		 <|>
		 (do { (l, p) <- typePattern `separatedBy` equalT
		     ; return (IsoDecl (s:l) (tokPos e : map tokPos p))
		     })
	       }

subTypeDefn :: (TypePattern, Pos) -> GenParser Char st TypeItem
subTypeDefn (s, e) = do { a <- annos
			; o <- oBraceT
			; v <- var
			; c <- colonT
			; t <- parseType
			; d <- dotT -- or bar
			; f <- fmap TermFormula term
			; p <- cBraceT
			; return (SubtypeDefn s v t (Annoted f [] a []) 
				  (e:tokPos o:tokPos c:tokPos d:[tokPos p]))
			}


subTypeDecl :: ([TypePattern], [Pos]) -> GenParser Char st TypeItem
subTypeDecl (l, p) = 
    do { t <- lessT
       ; s <- parseType
       ; return (SubtypeDecl l s (p++[tokPos t]))
       }

sortItem :: GenParser Char st TypeItem
sortItem = do { s <- typePattern;
		    subTypeDecl ([s],[])
		    <|>
		    kindedTypeDecl ([s],[])
		    <|>
		    commaTypeDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (TypeDecl [s] nullKind [])
		  } 		

sortItems = itemList sortS sortItem (TypeItems Plain)

typeItem :: GenParser Char st TypeItem
typeItem = do { s <- typePattern;
		    subTypeDecl ([s],[])
		    <|>
		    dataDef s nullKind []
		    <|> 
		    pseudoTypeDef s nullKind []
		    <|>
		    kindedTypeDecl ([s],[])
		    <|>
		    commaTypeDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (TypeDecl [s] nullKind [])
		  } 		

typeItems = itemList typeS typeItem (TypeItems Plain)

-----------------------------------------------------------------------------
-- pseudotype
-----------------------------------------------------------------------------

pseudoTypeDef t k l = 
    do c <- asKey assignS
       p <- pseudoType
       return (AliasType t k p (l++[tokPos c]))
			
typeArgSeq =    
    do (ts, ps) <- typeArgs `separatedBy` semiT 
       return [TypeArgs (concat ts) (map tokPos ps)]

typeArgParen = 
    do o <- oParenT
       (ts, ps) <- typeArgs `separatedBy` semiT       
       c <- cParenT	   
       return (TypeArgs (concat ts) (map tokPos (o:ps++[c])))

pseudoType = do l <- asKey lamS
		ts <- many1 typeArgParen <|> typeArgSeq
		d <- dotT
		t <- pseudoType
                return (PseudoType ts t (map tokPos [l,d]))
	     <|> fmap SimplePseudoType parseType	       

-----------------------------------------------------------------------------
-- datatype
-----------------------------------------------------------------------------

dataDef t k l =
    do c <- asKey defnS
       a <- annos
       (Annoted v _ _ b:as, ps) <- aAlternative `separatedBy` asKey barS
       return (Datatype (DatatypeDecl t k (Annoted v [] a b:as) 
                        Nothing (map tokPos (l++c:ps))))

aAlternative = do { a <- alternative
                  ; an <- annos
                  ; return (Annoted a [] [] an)
                  }

alternative = do { s <- pluralKeyword sortS <|> pluralKeyword typeS
                 ; (ts, cs) <- parseType `separatedBy` commaT
                 ; return (Subtype ts (map tokPos (s:cs)))
                 }
              <|> 
              do { i <- uninstOpName
                 ; cs <- many tupleComponent
		 ; do { q <- quMarkT
		      ; return (Constructor i cs Partial [tokPos q])
		      }
		   <|> return (Constructor i cs Total [])
		 }


tupleComponent = 
    do o <- oParenT
       do (cs, ps) <- component `separatedBy` semiT 
	  c <- cParenT
	  return (NestedComponents (concat cs) (toPos o ps c))
        <|> 
        do (cs, ps) <- tupleComponent `separatedBy` commaT
	   c <- cParenT
	   return (NestedComponents cs (toPos o ps c))
		      

component = do { (is, cs) <- uninstOpName `separatedBy` commaT
               ; if length is == 1 then
                 compType is cs 
                 <|> return [NoSelector (mkType(head is))]
                 else compType is cs
               }
         where mkType (Id is cs ps) = 
		   let ts = map TypeToken is
		       t = if length ts == 1 then head ts
			   else MixfixType ts
		       in if null cs then t
  		       else let qs = map mkType cs
				q = BracketType Squares qs ps
				in MixfixType (q:ts)

compType is cs = do { c <- colonT 
                    ; t <- parseType
		    ; return (makeComps is (cs++[c]) Total t)
		    }
                 <|> 
		 do { c <- qColonT 
                    ; t <- parseType
		    ; return (makeComps is (cs++[c]) Partial t)
		    }     
    where makeComps [a] [b] k t = [Selector a k t Other (tokPos b)] 
	  makeComps (a:r) (b:s) k t = 
	      (Selector a k t Comma (tokPos b)):makeComps r s k t 
	  makeComps _ _ _ _ = error "makeComps: empty selector list"

-----------------------------------------------------------------------------
-- classDecl
-----------------------------------------------------------------------------

pparseDownSet = 
	     do c <- className
		e <- equalT     
	        o <- oBraceT
		i <- typeVar
		d <- dotT
                j <- asKey (tokStr i)
		l <- lessT
                t <- parseType
		p <- cBraceT
		return (DownsetDefn c i t (map tokPos [e,o,d,j,l,p])) 



