
{- HetCATS/HasCASL/ParseItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parser for HasCASL basic Items
-}

module HasCASL.ParseItem where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import Common.Token
import HasCASL.HToken
import HasCASL.As
import Common.Lib.Parsec
import qualified Common.Lib.Set as Set
import Common.AS_Annotation
import HasCASL.ParseTerm

hasCaslStartKeywords :: [String]
hasCaslStartKeywords = dotS:cDot: hascasl_reserved_words

hasCaslItemList :: String -> AParser b
		-> ([Annoted b] -> [Pos] -> a) -> AParser a
hasCaslItemList = auxItemList hasCaslStartKeywords

hasCaslItemAux :: AParser a 
	       -> AParser ([a], [Token], [[Annotation]])
hasCaslItemAux = itemAux hasCaslStartKeywords

-- ------------------------------------------------------------------------
-- sortItem
-- ------------------------------------------------------------------------

commaTypeDecl :: TypePattern -> AParser TypeItem
commaTypeDecl s = do c <- anComma 
		     (is, cs) <- typePattern `separatedBy` anComma
		     let l = s : is 
		         p = c : cs
		     subTypeDecl (l, p)
		       <|> kindedTypeDecl (l, p)
		       <|> return (TypeDecl l star (map tokPos p))

kindedTypeDecl :: ([TypePattern], [Token]) -> AParser TypeItem
kindedTypeDecl (l, p) = 
    do t <- colT
       s <- kind
       let d = TypeDecl l s (map tokPos (p++[t]))
       if length l > 1 then return d
	  else pseudoTypeDef (head l) (Just s) [t]
		   <|> dataDef (head l) s [t] 
		   <|> return d

isoDecl :: TypePattern -> AParser TypeItem
isoDecl s = do e <- equalT
               subTypeDefn (s, e)
	         <|> do (l, p) <- typePattern `separatedBy` equalT
			return (IsoDecl (s:l) (map tokPos (e:p)))

vars :: AParser Vars
vars = fmap Var var 
       <|> do o <- oParenT
	      (vs, ps) <- vars `separatedBy` anComma
	      c <- cParenT
	      return (VarTuple vs $ toPos o ps c)

subTypeDefn :: (TypePattern, Token) -> AParser TypeItem
subTypeDefn (s, e) = do a <- annos
			o <- oBraceT
			v <- vars
			c <- colT
			t <- parseType
			d <- dotT -- or bar
			f <- fmap TermFormula term
			p <- cBraceT
			return (SubtypeDefn s v t (Annoted f [] a []) 
				  (toPos e [o,c,d] p))

subTypeDecl :: ([TypePattern], [Token]) -> AParser TypeItem
subTypeDecl (l, p) = 
    do t <- lessT
       s <- parseType
       return (SubtypeDecl l s (map tokPos (p++[t])))

sortItem :: AParser TypeItem
sortItem = do s <- typePattern
	      subTypeDecl ([s],[])
		    <|>
		    kindedTypeDecl ([s],[])
		    <|>
		    commaTypeDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (TypeDecl [s] star [])

sortItems :: AParser SigItems
sortItems = hasCaslItemList sortS sortItem (TypeItems Plain)

typeItem :: AParser TypeItem
typeItem = do s <- typePattern;
	      subTypeDecl ([s],[])
		    <|>
		    dataDef s star []
		    <|> 
		    pseudoTypeDef s Nothing []
		    <|>
		    kindedTypeDecl ([s],[])
		    <|>
		    commaTypeDecl s
		    <|>
                    isoDecl s
		    <|> 
		    return (TypeDecl [s] star [])

typeItemList :: [Token] -> Instance -> AParser SigItems
typeItemList ps k = 
    do (vs, ts, ans) <- hasCaslItemAux (annoParser typeItem)
       let r = zipWith appendAnno vs ans 
       return (TypeItems k r (map tokPos (ps++ts)))

typeItems :: AParser SigItems
typeItems = do p <- pluralKeyword typeS
	       do    q <- pluralKeyword instanceS
		     typeItemList [p, q] Instance
	         <|> typeItemList [p] Plain

-----------------------------------------------------------------------------
-- pseudotype
-----------------------------------------------------------------------------
typeArgParen :: AParser TypeArg
typeArgParen = 
    do o <- oParenT
       TypeArg i k s ps <- singleTypeArg
       p <- cParenT
       return $ TypeArg i k s (tokPos o: ps ++ [tokPos p])


pseudoType :: AParser TypeScheme
pseudoType = do l <- asKey lamS
		ts <- many1 typeArgParen <|> single singleTypeArg
		d <- dotT
		t <- pseudoType
		let qs = map tokPos [l,d]
		case t of 
		       TypeScheme ts1 gt ps -> 
			   return $ TypeScheme (ts1++ts) gt (ps++qs)
	     <|> do st <- parseType
		    return $ simpleTypeScheme st

pseudoTypeDef :: TypePattern -> Maybe Kind -> [Token] -> AParser TypeItem
pseudoTypeDef t k l = 
    do c <- asKey assignS
       p <- pseudoType
       return (AliasType t k p (map tokPos (l++[c])))
			
-----------------------------------------------------------------------------
-- datatype
-----------------------------------------------------------------------------

component :: AParser [Components]
component = do (is, cs) <- uninstOpId `separatedBy` anComma
               if length is == 1 then
                 compType is cs 
                 <|> return [NoSelector (idToType(head is))]
                 else compType is cs

idToType :: Id -> Type
idToType (Id is cs ps) = 
    let ts = map TypeToken is
	t = if length ts == 1 then head ts
	    else MixfixType ts
	in if null cs then t
  	   else let qs = map idToType cs
		    q = BracketType Squares qs ps
		    in MixfixType (q:ts)

tupleComponent :: AParser Components
tupleComponent = 
    do o <- oParenT
       do (cs, ps) <- component `separatedBy` anSemi 
	  c <- cParenT
	  return (NestedComponents (concat cs) (toPos o ps c))
        <|> 
        do (cs, ps) <- tupleComponent `separatedBy` anComma
	   c <- cParenT
	   return (NestedComponents cs (toPos o ps c))


altComponent :: AParser Components
altComponent = 
    tupleComponent
    <|> do i <- hconsId
	   return (NoSelector $ idToType i)
		      
compType :: [UninstOpId] -> [Token] -> AParser [Components]
compType is cs = do c <- colT 
                    t <- parseType
		    return (makeComps is (cs++[c]) Total t)
                 <|> 
		 do c <- qColonT 
                    t <- parseType
		    return (makeComps is (cs++[c]) Partial t)
    where makeComps [a] [b] k t = [Selector a k t Other (tokPos b)] 
	  makeComps (a:r) (b:s) k t = 
	      (Selector a k t Comma (tokPos b)):makeComps r s k t 
	  makeComps _ _ _ _ = error "makeComps: empty selector list"

alternative :: AParser Alternative
alternative = do s <- pluralKeyword sortS <|> pluralKeyword typeS
                 (ts, cs) <- parseType `separatedBy` anComma
                 return (Subtype ts (map tokPos (s:cs)))
              <|> 
              do i <- hconsId
                 cs <- many altComponent
		 do q <- quMarkT
		    return (Constructor i cs Partial [tokPos q])
		   <|> return (Constructor i cs Total [])

dataDef :: TypePattern -> Kind -> [Token] -> AParser TypeItem
dataDef t k l =
    do c <- asKey defnS
       a <- annos
       (Annoted v _ _ b:as, ps) <- aAlternative `separatedBy` barT
       let aa = Annoted v [] a b:as 
	   qs = map tokPos (l++c:ps)
       do d <- asKey derivingS
	  cl <- parseClass
	  return (Datatype (DatatypeDecl t k aa (Just cl)
			    (qs ++ [tokPos d])))
	 <|> return (Datatype (DatatypeDecl t k aa Nothing qs))
    where aAlternative = bind (\ a an -> Annoted a [] [] an)  
			 alternative annos

dataItem :: AParser DatatypeDecl
dataItem = do t <- typePattern
	      do   c <- colT
		   k <- kind
		   Datatype d <- dataDef t k [c]
		   return d
		<|> do Datatype d <- dataDef t star []
		       return d

dataItems :: AParser BasicItem
dataItems = hasCaslItemList typeS dataItem FreeDatatype

-----------------------------------------------------------------------------
-- classItem
-----------------------------------------------------------------------------

subClassDecl :: [ClassId] -> Kind -> [Token] -> AParser ClassDecl
subClassDecl l k p = 
    do t <- lessT
       s <- parseClass
       return (SubclassDecl l k s (map tokPos (p++[t])))

isoClassDecl :: ClassId -> Kind -> [Token] -> AParser ClassDecl
isoClassDecl s k ps = 
    do e <- equalT
       do o <- oBraceT
	  if null ps && (case k of ExtClass (Intersection cs _) InVar _ -> 
			                                    Set.isEmpty cs
			           _ -> False)
	     then do i <- pToken scanWords
		     d <- dotT
		     j <- asKey (tokStr i)
		     l <- lessT
		     t <- parseType
		     p <- cBraceT
		     return (DownsetDefn s i t (map tokPos [e,o,d,j,l,p])) 
	     else unexpected "kind annotation"
	 <|> do c <- parseClass
	        return (ClassDefn s k c $ map tokPos (ps ++[e]))

classDecl :: AParser ClassDecl
classDecl = do   (is, cs) <- classId `separatedBy` anComma
		 (ps, k) <- option ([], star) $ bind  (,) (single colT) kind 
		 if length is == 1 then 
		    subClassDecl is k (cs++ps)
		    <|>
                    isoClassDecl (head is) k ps
		    <|>
		    return (ClassDecl is k $ map tokPos (cs++ps))
		   else 
		    subClassDecl is k (cs++ps)
		    <|>
		    return (ClassDecl is k $ map tokPos (cs++ps))

classItem :: AParser ClassItem
classItem = do c <- classDecl
	       do o <- oBraceT 
                  is <- annosParser basicItems
                  p <- cBraceT
                  return (ClassItem c is $ toPos o [] p) 
                 <|> 
		  return (ClassItem c [] [])

classItemList :: [Token] -> Instance -> AParser BasicItem
classItemList ps k = 
    do (vs, ts, ans) <- hasCaslItemAux (annoParser classItem)
       let r = zipWith appendAnno vs ans 
       return (ClassItems k r (map tokPos (ps++ts)))

classItems :: AParser BasicItem
classItems = do p <- pluralKeyword classS
	        do   q <- pluralKeyword instanceS
		     classItemList [p, q] Instance
	         <|> classItemList [p] Plain

-----------------------------------------------------------------------------
-- opItem
-----------------------------------------------------------------------------

typeVarDeclSeq :: AParser ([TypeArg], [Pos])
typeVarDeclSeq = 
    do o <- oBracketT
       (ts, cs) <- typeVarDecls `separatedBy` anSemi
       c <- cBracketT
       return (concat ts, toPos o cs c)

opId :: AParser OpId
opId = do i@(Id is cs ps) <- uninstOpId
	  if isPlace $ last is then return (OpId i [] [])
	      else 
	        do (ts, qs) <- option ([], [])
			       typeVarDeclSeq
		   u <- many placeT
		   return (OpId (Id (is++u) cs ps) ts qs)

opAttr :: AParser OpAttr
opAttr = do a <- asKey assocS
	    return (BinOpAttr Assoc [tokPos a])
	 <|>
	 do a <- asKey commS
	    return (BinOpAttr Comm [tokPos a])
	 <|>
	 do a <- asKey idemS
	    return (BinOpAttr Idem [tokPos a])
	 <|>
	 do a <- asKey unitS
	    t <- term
	    return (UnitOpAttr t [tokPos a])

opDecl :: [OpId] -> [Token] -> AParser OpItem
opDecl os ps = do c <- colT
		  t <- typeScheme
		  do   d <- anComma
		       (as, cs) <- opAttr `separatedBy` anComma
		       return (OpDecl os t as (map tokPos (ps++[c,d]++cs))) 
		    <|> return (OpDecl os t [] (map tokPos (ps++[c])))

opDeclOrDefn :: OpId -> AParser OpItem
opDeclOrDefn o = 
    do c <- colT
       t <- typeScheme
       do   d <- anComma
	    (as, cs) <- opAttr `separatedBy` anComma
	    return (OpDecl [o] t as (map tokPos ([c,d]++cs))) 
	 <|> do e <- equalT
		f <- term 
		return (OpDefn o [] t Total f (toPos c [] e))  
         <|> return (OpDecl [o] t [] (map tokPos [c]))
    <|> 
    do ps <- many1 (bracketParser patterns oParenT cParenT anSemi 
		      (BracketPattern Parens)) 
       do    (p, c) <- quColon
	     t <- parseType 
	     e <- equalT
	     f <- term 
	     return (OpDefn o ps (simpleTypeScheme t) p f (toPos c [] e))
    <|> 
    do c <- qColonT 
       t <- parseType 
       e <- equalT
       f <- term 
       return (OpDefn o [] (simpleTypeScheme t) Partial f (toPos c [] e))

opItem :: AParser OpItem
opItem = do (os, ps) <- opId `separatedBy` anComma
	    if length os == 1 then
		    opDeclOrDefn (head os)
		    else opDecl os ps

opItems :: AParser SigItems
opItems = hasCaslItemList opS opItem OpItems

-----------------------------------------------------------------------------
-- predItem
-----------------------------------------------------------------------------

predDecl :: [OpId] -> [Token] -> AParser PredItem
predDecl os ps = do c <- colT
		    t <- typeScheme
		    return (PredDecl os t (map tokPos (ps++[c])))

predDefn :: OpId -> AParser PredItem
predDefn o = do ps <- many (bracketParser patterns oParenT cParenT anSemi 
		      (BracketPattern Parens)) 
		e <- asKey equivS
		f <- term
		return (PredDefn o ps (TermFormula f) [tokPos e]) 

predItem :: AParser PredItem
predItem = do (os, ps) <- opId `separatedBy` anComma
	      if length os == 1 then 
		 predDecl os ps
		 <|> 
		 predDefn (head os)
		 else predDecl os ps 

predItems :: AParser SigItems
predItems = hasCaslItemList predS predItem PredItems

-----------------------------------------------------------------------------
-- sigItem
-----------------------------------------------------------------------------

sigItems :: AParser SigItems
sigItems = sortItems <|> opItems <|> predItems <|> typeItems

-----------------------------------------------------------------------------
-- generated sigItems
-----------------------------------------------------------------------------

generatedItems :: AParser BasicItem
generatedItems = do g <- asKey generatedS
                    do FreeDatatype ds ps <- dataItems
                       return (GenItems [Annoted (TypeItems Plain
				   (map (\d -> Annoted
							(Datatype (item d)) 
					 [] (l_annos d) (r_annos d)) ds) ps) 
					 [] [] []] 
				   [tokPos g])
                      <|> 
                      do o <- oBraceT
                         is <- annosParser sigItems
                         c <- cBraceT
                         return (GenItems is
                                   (toPos g [o] c)) 

-----------------------------------------------------------------------------
-- generic var decls (after "vars")
-----------------------------------------------------------------------------

genVarItems :: AParser ([GenVarDecl], [Token])
genVarItems = 
           do vs <- genVarDecls
              do s <- try (addAnnos >> Common.Lexer.semiT << addLineAnnos)
                 do tryItemEnd hasCaslStartKeywords
                    return (vs, [s])
                   <|> 
                     do (ws, ts) <- genVarItems
                        return (vs++ws, s:ts)
                <|>
                return (vs, [])

-----------------------------------------------------------------------------
-- basicItem
-----------------------------------------------------------------------------

freeDatatype, progItems, axiomItems, forallItem, genVarItem, dotFormulae, 
  basicItems :: AParser BasicItem

freeDatatype =   do f <- asKey freeS
                    FreeDatatype ds ps <- dataItems
                    return (FreeDatatype ds (tokPos f : ps))

progItems = hasCaslItemList programS (patternTermPair (NoToken equalS) 
				      WithIn equalS) ProgItems

axiomItems =     do a <- pluralKeyword axiomS
                    (fs, ps, ans) <- hasCaslItemAux (fmap TermFormula term)
                    return (AxiomItems [] (zipWith 
                                           (\ x y -> Annoted x [] [] y) 
                                           fs ans) (map tokPos (a:ps)))

forallItem =     do f <- forallT
                    (vs, ps) <- genVarDecls `separatedBy` anSemi 
		    a <- annos
		    AxiomItems _ ((Annoted ft qs as rs):fs) ds <- dotFormulae
		    let aft = Annoted ft qs (a++as) rs
		    return (AxiomItems (concat vs) (aft:fs) 
			    (map tokPos (f:ps) ++ ds))

genVarItem = do v <- pluralKeyword varS
                (vs, ps) <- genVarItems
                return (GenVarItems vs (map tokPos (v:ps)))

dotFormulae = do d <- dotT
                 (fs, ds) <- aFormula `separatedBy` dotT
                 let ps = map tokPos (d:ds)
                 if null (r_annos(last fs)) then  
                   do (m, an) <- optSemi
                      case m of 
                        Nothing -> return (AxiomItems [] fs ps)
                        Just t -> return (AxiomItems []
                               (init fs ++ [appendAnno (last fs) an])
                               (ps ++ [tokPos t]))
                   else return (AxiomItems [] fs ps)
    where aFormula = bind appendAnno 
		     (annoParser (fmap TermFormula term)) lineAnnos

basicItems = fmap SigItems sigItems
	     <|> classItems
	     <|> progItems
	     <|> generatedItems
             <|> freeDatatype
	     <|> genVarItem
             <|> forallItem
             <|> dotFormulae
             <|> axiomItems

basicSpec :: AParser BasicSpec
basicSpec = (fmap BasicSpec $ annosParser basicItems)
            <|> (oBraceT >> cBraceT >> return (BasicSpec []))

