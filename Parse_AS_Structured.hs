
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
import Logic

import AS_Structured
import AS_Annotation
import Anno_Parser
import Id(tokPos)
import Keywords
import Lexer
import Parsec
import Id

import Maybe(maybeToList)

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

-- simpleId as spec- and view-name 
simpleId = pToken (reserved casl_reserved_words scanAnyWords)



spec :: AnyLogic -> GenParser Char st SPEC
-- current logic
spec l = reSpec l 

reSpec :: AnyLogic -> GenParser Char st SPEC
reSpec l = annoParser (simpleSpec l) >>= (renaming l ) -- <|> restriction l

parseMaps :: AnyLogic -> GenParser Char st (G_symb_map_items_list, [Token])
parseMaps (Logic l) = do (cs, ps) <- parse_symb_map_items l `separatedBy` commaT
			 return (G_symb_map_items_list l cs, ps) 

renaming l s = 
    do w <- asKey withS
       (m, ps) <- parseMaps l
       return (Translation s (Renaming m (map tokPos (w:ps))))

simpleSpec :: AnyLogic -> GenParser Char st SPEC
simpleSpec l@(Logic i) = groupSpec l <|> fmap (Basic_spec . G_basic_spec i) 
			                 (parse_basic_spec i)

aSpec l = annoParser (spec l)

groupSpec l = do b <- oBraceT
		 a <- aSpec l
		 c <- cBraceT
		 return (Group a (map tokPos [b, c])) 
	      <|>
	      do n <- simpleId
		 f <- fitArgs l
		 return (Spec_inst n f)

fitArgs :: AnyLogic -> GenParser Char st [Annoted FIT_ARG]
-- toDo
fitArgs l = return []

optEnd = option Nothing (fmap Just (asKey endS))

specDefn l = 
    do s <- asKey specS 
       n <- simpleId
       g <- generics l
       e <- asKey equalS
       a <- aSpec l
       q <- optEnd
       return (Spec_defn n g a (map tokPos ([s, e] ++ Maybe.maybeToList q)))
       
-- toDo
generics l = return (Genericity (Params []) (Imported []) [])



