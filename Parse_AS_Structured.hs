
{- HetCATS/Parse_AS_Structured.hs
   $Id$
   Author: Christian Maeder
   Year:   2002

   Parsing the Structured part of hetrogenous specifications.
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.2 Structured Specifications
-}

module Parse_AS_Structured where

import Grothendieck
import LogicGraph

import AS_Structured
import AS_Annotation
import Anno_Parser
import Id(tokPos)
import Keywords
import Lexer
import Parsec

import Maybe(maybeToList)

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

-- simpleId as spec- and view-name 
simpleId = pToken (reserved casl_reserved_words scanAnyWords)

spec :: [AnyLogic] -> GenParser Char st SPEC
-- first logic is the current logic!

reSpec p = annoParser (simpleSpec p) >>= (renaming p <|> restriction p)

parseMaps :: [AnyLogic] -> GenParser Char st G_symb_map_items_list
parseMaps p@(Logic l:: _) = fmap G_symb_map_items_list 
			    (parse_symb_map_items_list l)

renaming p s = 
    do w <- asKey withS
       m <- parseMaps p
       return (Translation s (Renaming m [tokPos w]))

simpleSpec p = groupSpec p <|> fmap Basic_spec p

aSpec p = do a <- annos
	     s <- spec p
	     return (Annoted s [] a [])

groupSpec p = do o <- oBraceT
		 a <- aSpec p
		 c <- cBraceT
		 return (Group a (map tokPos [o, c])) 
	      <|>
	      do n <- simpleId
		 f <- fitArgs p
		 return (Spec_inst n f)

fitArgs :: GenParser Char st G_basic_spec -> GenParser Char st [Annoted FIT_ARG]
-- toDo
fitArgs p = return []

optEnd = option Nothing (fmap Just (asKey endS))

specDefn p = 
    do s <- asKey specS 
       n <- simpleId
       g <- generics p
       e <- asKey equalS
       a <- aSpec p
       o <- optEnd
       return (Spec_defn n g a (map tokPos ([s, e] ++ Maybe.maybeToList o)))
       
-- toDo
generics p = return (Genericity (Params []) (Imported []) [])



