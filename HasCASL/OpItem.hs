module OpItem (opItems) where

import ItemAux
import Lexer
import LocalEnv
import Parsec
import ParseTerm
import ParseType
import Term
import Token
import Type

opId = parseId

opItem ast key = do { o1 <- opId
		    ; ol <- single (oneOpItem (key, o1))
		            <|> commaOpItem (key, o1)
		    ; return ((map AnOpItem ol) ++ ast)
		    }

mkOpItem a t (k, o) = OpItem (Decl (Symb o t) k []) a Nothing []

commaOpItem o = 
    do { l <- comma >>= separatedBy (const opId) comma
       ; t <- partialColon >>= parsePartialType
       ; a <- option [] attrs
       ; return (map (mkOpItem a t) (o:l)) 
       }

declHead = (oParen >>= varDecls) << cParen

oneOpItem o = 
  do { d <- option [] declHead
     ; c <- partialColon
     ; t <- (if null d then parsePartialType else funType) c
     ; let ty = if null d then t else 
                   let args = map (symbType . symb) d
                       arg = crossProduct args
                   in (if isColon c then totalFun else partialFun)(arg, t)
           op = mkOpItem [] ty o
       in option op (parseAttrs op <|> parseOpDefn d op)
     }

parseAttr :: Parser OpAttr
parseAttr =  
        fmap (const AssocOpAttr) (toKey assocStr) 
        <|>
        fmap (const CommOpAttr) (toKey commStr) 
        <|> 
        fmap (const IdemOpAttr) (toKey idemStr) 
        <|>
	(toKey unitStr >> fmap UnitOpAttr parseTerm)

attrs = comma >> parseAttr `sepBy1` comma

parseAttrs op = do { l <- attrs
		   ; return (op {opAttrs = l})
		   }

parseOpDefn decls op = do { t <- equal >> parseTerm
			  ; let t' = Binding ArgDecl decls t
			    in  return (op {opDefn = Just (Definition t')})
			  }

opItems ast = do { key <- pluralKeyword opStr;
		 ; itemAux opItem ast key
		 } <|> predItems ast

predItem ast key =  do { o1 <- opId
		       ; ol <- single (onePredItem (key, o1))
		               <|> commaPredItem (key, o1)
		       ; return ((map AnOpItem ol) ++ ast)
		       }

commaPredItem o = 
    do { l <- comma >>= separatedBy (const opId) comma
       ; t <- predType
       ; return (map (mkOpItem [] t) (o:l)) 
       }

predType = fmap predicate (colon >>= productType) 

onePredItem o = 
  do { d <- option [] declHead
     ; toKey equivStr
     ; t <- parseTerm
     ; let args = map (symbType . symb) d
           ty = predicate (crossProduct args)
           t' = if null d then t else 
                  Binding ArgDecl d t
           e = Just (Definition t')
           op = mkOpItem [] ty o
       in return (op {opDefn = e})
     }
   <|>
   do { ty <- predType
      ; return (mkOpItem [] ty o)
      }

predItems ast = do { key <- pluralKeyword predStr;
		   ; itemAux predItem ast key
		   }

