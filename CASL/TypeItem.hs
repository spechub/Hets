
{- HetCATS/CASL/TypeItem.hs
   $Id$
   Authors: Christian Maeder
   Year:    2002
   
   parse DATATYPE-DECL

   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.1 Basic Specifications with Subsorts
-}

module CASL.TypeItem where

import Common.AnnoState
import Common.Id
import Common.Keywords
import Common.Lexer
import CASL.AS_Basic_CASL
import Common.AS_Annotation
import Common.Lib.Parsec
import Common.Token
import CASL.Formula
import CASL.ItemList

-- ------------------------------------------------------------------------
-- datatypes
-- ------------------------------------------------------------------------

datatype :: AParser DATATYPE_DECL
datatype = do s <- sortId
	      addAnnos
	      e <- asKey defnS
	      addAnnos
	      a <- getAnnos
	      (Annoted v _ _ b:as, ps) <- aAlternative 
		`separatedBy` barT
	      return (Datatype_decl s (Annoted v [] a b:as) 
			(map tokPos (e:ps)))

aAlternative :: AParser (Annoted ALTERNATIVE)
aAlternative = do a <- alternative 
		  an <- annos
		  return (Annoted a [] [] an)

alternative :: AParser ALTERNATIVE
alternative = do s <- pluralKeyword sortS
		 (ts, cs) <- sortId `separatedBy` anComma
		 return (Subsorts ts (map tokPos (s:cs)))
              <|> 
              do i <- parseId
		 do o <- oParenT
		    (cs, ps) <- component `separatedBy` anSemi
		    c <- cParenT
		    let qs = toPos o ps c in
			do q <- quMarkT
			   return (Partial_construct i cs 
				     (qs++[tokPos q]))
			<|> return (Total_construct i cs qs)

		   <|> return (Total_construct i [] [])

isSortId :: Id -> Bool
isSortId (Id is _ _) = length is == 1 && not (null (tokStr (head is))) 
		       && head (tokStr (head is)) `elem` caslLetters

component :: AParser COMPONENTS
component = do (is, cs) <- parseId `separatedBy` anComma
	       if length is == 1 && isSortId (head is) then
		 compSort is cs 
		 <|> return (Sort (head is))
		 else compSort is cs

compSort :: [OP_NAME] -> [Token] -> AParser COMPONENTS
compSort is cs = do c <- colonST
		    (b, t, _) <- opSort
		    let p = map tokPos (cs++[c]) in 
		      return (if b then Partial_select is t p
			      else  Total_select is t p)

-- ------------------------------------------------------------------------
-- sigItems
-- ------------------------------------------------------------------------

typeItems :: AParser SIG_ITEMS
typeItems = itemList typeS datatype Datatype_items

