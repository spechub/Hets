
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
		           p = c : cs
		       in
		       subTypeDecl (l, p)
		       <|> kindedTypeDecl (l, p)
		       <|> return (TypeDecl l nullKind (map tokPos p))
		     }

kindedTypeDecl (l, p) = 
    do { t <- colonT
       ; s <- kind
       ; let d = TypeDecl l s (map tokPos (p++[t])) in 
	 if length l > 1 then return d
	 else pseudoTypeDef (head l) s [t]
	  <|> dataDef (head l) s [t] 
          <|> return d
       }

isoDecl :: TypePattern -> GenParser Char st TypeItem
isoDecl s = do { e <- equalT
               ; subTypeDefn (s, e)
		 <|>
		 (do { (l, p) <- typePattern `separatedBy` equalT
		     ; return (IsoDecl (s:l) (map tokPos (e:p)))
		     })
	       }

subTypeDefn :: (TypePattern, Token) -> GenParser Char st TypeItem
subTypeDefn (s, e) = do { a <- annos
			; o <- oBraceT
			; v <- var
			; c <- colonT
			; t <- parseType
			; d <- dotT -- or bar
			; f <- fmap TermFormula term
			; p <- cBraceT
			; return (SubtypeDefn s v t (Annoted f [] a []) 
				  (toPos e [o,c,d] p))
			}


subTypeDecl :: ([TypePattern], [Token]) -> GenParser Char st TypeItem
subTypeDecl (l, p) = 
    do { t <- lessT
       ; s <- parseType
       ; return (SubtypeDecl l s (map tokPos (p++[t])))
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

typeItems = do p <- pluralKeyword typeS
	       do    q <- pluralKeyword instanceS
		     typeItemList [p,q] Instance
	         <|> typeItemList [p] Plain

typeItemList ps k = 
    do { (vs, ts, ans) <- itemAux (annoParser typeItem)
       ; let r = zipWith appendAnno vs ans 
	 in return (TypeItems k r (map tokPos (ps++ts)))
       }

-----------------------------------------------------------------------------
-- pseudotype
-----------------------------------------------------------------------------

pseudoTypeDef t k l = 
    do c <- asKey assignS
       p <- pseudoType
       return (AliasType t k p (map tokPos (l++[c])))
			
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
       (Annoted v _ _ b:as, ps) <- aAlternative `separatedBy` barT
       let aa = Annoted v [] a b:as 
	   qs = map tokPos (l++c:ps)
	 in do d <- asKey derivingS
	       cl <- parseClass
	       return (Datatype (DatatypeDecl t k aa (Just cl)
		       (qs ++ [tokPos d])))
	    <|> return (Datatype (DatatypeDecl t k aa Nothing qs))

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


dataItem = do t <- typePattern
	      do   c <- colonT
		   k <- kind
		   Datatype d <- dataDef t k [c]
		   return d
		<|> do Datatype d <- dataDef t nullKind []
		       return d

dataItems = itemList typeS dataItem FreeDatatype

-----------------------------------------------------------------------------
-- classItem
-----------------------------------------------------------------------------

classDecl :: GenParser Char st ClassDecl
classDecl = do   (is, cs) <- className `separatedBy` commaT
		 if length is == 1 then 
		    subClassDecl (is, cs)
		    <|>
		    return (ClassDecl is (map tokPos cs))
		   else 
                    isoClassDecl (head is)
		    <|>
		    subClassDecl (is, cs)
		    <|>
		    return (ClassDecl is (map tokPos cs))

subClassDecl (l, p) = 
    do { t <- lessT
       ; s <- parseClass
       ; return (SubclassDecl l s (map tokPos (p++[t])))
       }

isoClassDecl s = 
    do { e <- equalT
       ;     do o <- oBraceT
		i <- typeVar
		d <- dotT
                j <- asKey (tokStr i)
		l <- lessT
                t <- parseType
		p <- cBraceT
		return (DownsetDefn s i t (map tokPos [e,o,d,j,l,p])) 
	     <|> 
	     do c <- parseClass
	        return (ClassDefn s c [tokPos e])
       }

classItem = do c <- classDecl
	       do { o <- oBraceT 
                  ; a <- annos
                  ; i:is <- many1 basicItems
                  ; p <- cBraceT
                  ; return (ClassItem c ((Annoted i [] a [])  
                                         : map (\x -> Annoted x [] [] []) is)
                                   (map tokPos [o, p])) 
		  }
                  <|> 
		  return (ClassItem c [] [])

classItems = do p <- pluralKeyword classS
	        do   q <- pluralKeyword instanceS
		     classItemList [p,q] Instance
	         <|> classItemList [p] Plain

classItemList ps k = 
    do { (vs, ts, ans) <- itemAux (annoParser classItem)
       ; let r = zipWith appendAnno vs ans 
	 in return (ClassItems k r (map tokPos (ps++ts)))
       }

-----------------------------------------------------------------------------
-- opItem
-----------------------------------------------------------------------------

opName = do i@(Id is cs ps) <- uninstOpName
	    if isPlace $ last is then return (OpName i [])
	      else 
	        do ts <- many typeVarDeclSeq
		   u <- many placeT
		   return (OpName (Id (is++u) cs ps) ts)

typeVarDeclSeq = 
    do o <- oBracketT
       (ts, cs) <- typeVarDecls `separatedBy` semiT
       c <- cBracketT
       return (TypeVarDecls (concat ts) (toPos o cs c))

opItem = do (os, ps) <- opName `separatedBy` commaT
	    if length os == 1 then
		    opDeclOrDefn (head os)
		    else opDecl os ps

opDecl os ps = do c <- colonT
		  t <- typeScheme
		  do   d <- commaT
		       (as, cs) <- opAttr `separatedBy` commaT
		       return (OpDecl os t as (map tokPos (ps++[c,d]++cs))) 
		    <|> return (OpDecl os t [] (map tokPos (ps++[c])))

opAttr = do a <- asKey assocS
	    return (BinOpAttr Assoc (tokPos a))
	 <|>
	 do a <- asKey commS
	    return (BinOpAttr Comm (tokPos a))
	 <|>
	 do a <- asKey idemS
	    return (BinOpAttr Idem (tokPos a))
	 <|>
	 do a <- asKey unitS
	    t <- term
	    return (UnitOpAttr t (tokPos a))

quColon = do c <- colonT
	     return (Total, c)
	  <|> 
	  do c <- qColonT
	     return (Partial, c) 

opDeclOrDefn o = 
    do c <- colonT
       t <- typeScheme
       do   d <- commaT
	    (as, cs) <- opAttr `separatedBy` commaT
	    return (OpDecl [o] t as (map tokPos ([c,d]++cs))) 
	 <|> do e <- equalT
		f <- term 
		return (OpDefn o [] t Total f (toPos c [] e))  
         <|> return (OpDecl [o] t [] (map tokPos [c]))
    <|> 
    do ps <- many1 (bracketParser patterns oParenT cParenT semiT 
		      (BracketPattern Parens)) 
       do    (p, c) <- quColon
	     t <- parseType 
	     e <- equalT
	     f <- term 
	     return (OpDefn o ps (SimpleTypeScheme t) p f (toPos c [] e))
    <|> 
    do c <- qColonT 
       t <- parseType 
       e <- equalT
       f <- term 
       return (OpDefn o [] (SimpleTypeScheme t) Partial f (toPos c [] e))

opItems = itemList opS opItem OpItems

-----------------------------------------------------------------------------
-- predItem
-----------------------------------------------------------------------------

predItem = do (os, ps) <- opName `separatedBy` commaT
	      if length os == 1 then 
		 predDecl os ps
		 <|> 
		 predDefn (head os)
		 else predDecl os ps 

predDecl os ps = do c <- colonT
		    t <- typeScheme
		    return (PredDecl os t (map tokPos (ps++[c])))

predDefn o = do ps <- many (bracketParser patterns oParenT cParenT semiT 
		      (BracketPattern Parens)) 
		e <- asKey equivS
		f <- term
		return (PredDefn o ps (TermFormula f) [tokPos e]) 

predItems = itemList predS predItem PredItems

-----------------------------------------------------------------------------
-- sigItem
-----------------------------------------------------------------------------

sigItems = sortItems <|> opItems <|> predItems <|> typeItems


-----------------------------------------------------------------------------
-- generated sigItems
-----------------------------------------------------------------------------

generatedItems = do { g <- asKey generatedS
                    ; do { FreeDatatype ds ps <- dataItems
                         ; return (GenItems [Annoted (TypeItems Plain
				   (map (\d -> Annoted
							(Datatype (item d)) 
					 [] (l_annos d) (r_annos d)) ds) ps) 
					 [] [] []] 
				   [tokPos g])
                         }
                      <|> 
                      do { o <- oBraceT
                         ; a <- annos
                         ; i:is <- many1 sigItems
                         ; c <- cBraceT
                         ; return (GenItems ((Annoted i [] a [])  
                                            : map (\x -> Annoted x [] [] []) is)
                                   (toPos g [o] c)) 
                         }
                    }


-----------------------------------------------------------------------------
-- basicItem
-----------------------------------------------------------------------------

freeDatatype =   do { f <- asKey freeS
                    ; FreeDatatype ds ps <- dataItems
                    ; return (FreeDatatype ds (tokPos f : ps))
                    }

progItems = do p <- pluralKeyword programS
	       d <- dotT
	       (es, ps) <- annotedProgEq `separatedBy` dotT
	       return (ProgItems es (map tokPos (p:d:ps))) 

annotedProgEq = bind appendAnno (annoParser (patternTermPair True True equalS))
		lineAnnos

basicItems = fmap SigItems sigItems
	     <|> classItems
	     <|> progItems
	     <|> generatedItems
             <|> freeDatatype
	     <|> genVarItem
             <|> forallItem
             <|> dotFormulae
             <|> axiomItems

axiomItems =     do { a <- pluralKeyword axiomS
                    ; (fs, ps, ans) <- itemAux (fmap TermFormula term)
                    ; return (AxiomItems (zipWith 
                                           (\ x y -> Annoted x [] [] y) 
                                           fs ans) (map tokPos (a:ps)))
                    }

forallItem =     do { f <- asKey forallS 
                    ; (vs, ps) <- genVarDecls `separatedBy` semiT 
                    ; AxiomItems fs ds <- dotFormulae
                    ; return (LocalVarAxioms (concat vs) fs 
			      (map tokPos (f:ps) ++ ds))
                    }


genVarItem = do { v <- pluralKeyword varS
                ; (vs, ps) <- genVarItems
                ; return (GenVarItems vs (map tokPos (v:ps)))
                }


dotFormulae = do { d <- dotT
                 ; (fs, ds) <- aFormula `separatedBy` dotT
                 ; let ps = map tokPos (d:ds) in 
                   if null (r_annos(last fs)) then  
                   do { (m, an) <- optSemi
                      ; case m of 
                        { Nothing -> return (AxiomItems fs ps)
                        ; Just t -> return (AxiomItems 
                               (init fs ++ [appendAnno (last fs) an])
                               (ps ++ [tokPos t]))
                        }
                      }
                   else return (AxiomItems fs ps)
                 }

genVarItems = 
           do { vs <- genVarDecls
              ; do { s <- semiT
                   ; do { tryItemEnd startKeyword
                        ; return (vs, [s])
                        }
                     <|> 
                     do { (ws, ts) <- genVarItems
                        ; return (vs++ws, s:ts)
                        }
                   }
                <|>
                return (vs, [])
              }

aFormula = bind appendAnno (annoParser (fmap TermFormula term)) lineAnnos

basicSpec = (oBraceT >> cBraceT >> return (BasicSpec []))
            <|> 
            fmap BasicSpec (many1 aBasicItems)

aBasicItems = bind (\ x y -> Annoted y [] x []) annos basicItems
