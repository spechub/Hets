
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
import List

import Maybe(maybeToList, fromJust)

------------------------------------------------------------------------
-- annotation adapter
------------------------------------------------------------------------

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

------------------------------------------------------------------------
-- simpleIds for spec- and view-name 
------------------------------------------------------------------------

logicS = "logic" -- new keyword

simpleId = pToken (reserved (logicS:casl_reserved_words) scanAnyWords)

------------------------------------------------------------------------
-- logic and encoding names
------------------------------------------------------------------------

-- exclude colon (because encoding must be recognized)
-- ecclude dot to recognize optional sublogic name

otherChars = "_`"
 
-- better list what is allowed rather than exclude what is forbidden
-- white spaces und non-printables should be not allowed!
encodingName = pToken(reserved (funS:casl_reserved_words) (many1 
		    (oneOf (otherChars ++ (signChars \\ ":.")) 
		     <|> scanLPD)))

-- keep these identical in order to
-- decide after seeing ".", ":" or "->" what was meant
logicName = do e <- encodingName
	       do string dotS
		  s <- encodingName
                  return (Logic_name e (Just s)) 
		 <|> return (Logic_name e Nothing)        

------------------------------------------------------------------------
-- parse Logic_code
------------------------------------------------------------------------

parseLogic :: GenParser Char st Logic_code
parseLogic = 
    do l <- asKey logicS
       do e <- logicName
          case e of 
		 Logic_name _ (Just _) -> parseOptLogTarget Nothing (Just e) [l]
		 Logic_name f Nothing -> 
		      do c <- asKey colonS
			 parseLogAfterColon (Just f) [l,c]
		      <|> parseOptLogTarget Nothing (Just e) [l]
         <|> do f <- asKey funS
		t <- logicName
		return (Logic_code Nothing Nothing (Just t) (map tokPos [l,f]))

-- auxiliary (given encoding e)
parseLogAfterColon e l =
    do s <- logicName
       parseOptLogTarget e (Just s) l
	 <|> return (Logic_code e (Just s) Nothing (map tokPos l))
    <|> parseOptLogTarget e Nothing l
    <|> return (Logic_code e Nothing Nothing (map tokPos l))

-- auxiliary (given encoding e or source s) 
parseOptLogTarget e s l =
    do f <- asKey funS
       do t <- logicName
	  return (Logic_code e s (Just t) (map tokPos (l++[f])))
        <|> return (Logic_code e s Nothing (map tokPos (l++[f])))


------------------------------------------------------------------------
-- find the proper logic list
------------------------------------------------------------------------

findLogic :: String -> [AnyLogic] -> ([AnyLogic],[AnyLogic])
findLogic s l = partition (\ (Logic x) -> language_name x == s) l

------------------------------------------------------------------------
-- parse G_mapping
------------------------------------------------------------------------

parseMapping :: [AnyLogic] -> GenParser Char st ([G_mapping], [Token])
parseMapping l@(Logic i : _) =
    do n <- parseLogic
       let s = case n of 
	       Logic_code _ _ (Just (Logic_name t _)) _ -> tokStr t
	       _ -> language_name i
	   (f, r) = findLogic s l in
		  if null f then fail ("unknown language " ++ s)
		  else do c <- commaT
			  (gs, ps) <- parseMapping (f++r)
			  return (G_logic_translation n : gs, c:ps)
		       <|> return ([G_logic_translation n], [])
    <|> do is <- parse_symb_map_items i
	   do c <- commaT 
  	      (g:gs, ps) <- parseMapping l
	      let gg = case g of 
		       G_symb_map (G_symb_map_items_list j js) -> 
			   G_symb_map (G_symb_map_items_list i 
				       (is: map (fromJust . coerce i j) js)) 
					  : gs
		       _ -> G_symb_map (G_symb_map_items_list i [is]) : g : gs
	        in return (gg, c : ps)
	     <|> return ([G_symb_map (G_symb_map_items_list i [is])], [])
	   

------------------------------------------------------------------------
-- specs
------------------------------------------------------------------------

spec :: [AnyLogic] -> GenParser Char st SPEC
-- current logic is first element
spec l = reSpec l 

reSpec :: [AnyLogic] -> GenParser Char st SPEC
reSpec l = annoParser (simpleSpec l) >>= (renaming l ) -- <|> restriction l

parseMaps :: [AnyLogic] -> GenParser Char st (G_symb_map_items_list, [Token])
parseMaps (Logic i : _) = 
    do (cs, ps) <- parse_symb_map_items i `separatedBy` commaT
       return (G_symb_map_items_list i cs, ps) 


-- parseMapping :: [AnyLogic] -> GenParser Char st (G_mapping, [Token])


renaming l s = 
    do w <- asKey withS
       (m, ps) <- parseMaps l
       return (Translation s (Renaming [G_symb_map m] (map tokPos (w:ps))))

simpleSpec :: [AnyLogic] -> GenParser Char st SPEC
simpleSpec l@(Logic i : _) = 
    groupSpec l <|> fmap (Basic_spec . G_basic_spec i) 
		  (case parse_basic_spec i of 
		   Nothing -> fail ("no parser for language " 
				    ++ language_name i)
		   Just p -> p
		  )

aSpec l = annoParser (spec l)

groupSpec l = do b <- oBraceT
		 a <- aSpec l
		 c <- cBraceT
		 return (Group a (map tokPos [b, c])) 
	      <|>
	      do n <- simpleId
		 f <- fitArgs l
		 return (Spec_inst n f)

fitArgs :: [AnyLogic] -> GenParser Char st [Annoted FIT_ARG]
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
