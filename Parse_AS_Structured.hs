
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
import Token
import Parsec
import Id
import List

import Maybe(maybeToList)

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
       do e <- logicName  -- try to parse encoding or logic source after "logic" 
          case e of 
		 Logic_name _ (Just _) -> parseOptLogTarget Nothing (Just e) [l]
		 Logic_name f Nothing -> 
		      do c <- asKey colonS
			 parseLogAfterColon (Just f) [l,c]
		      <|> parseOptLogTarget Nothing (Just e) [l]
         <|> do f <- asKey funS  -- parse at least a logic target after "logic"
		t <- logicName
		return (Logic_code Nothing Nothing (Just t) (map tokPos [l,f]))

-- parse optional logic source and target after a colon (given an encoding e)
parseLogAfterColon e l =
    do s <- logicName
       parseOptLogTarget e (Just s) l
	 <|> return (Logic_code e (Just s) Nothing (map tokPos l))
    <|> parseOptLogTarget e Nothing l
    <|> return (Logic_code e Nothing Nothing (map tokPos l))

-- parse an optional logic target (given encoding e or source s) 
parseOptLogTarget e s l =
    do f <- asKey funS
       do t <- logicName
	  return (Logic_code e s (Just t) (map tokPos (l++[f])))
        <|> return (Logic_code e s Nothing (map tokPos (l++[f])))

------------------------------------------------------------------------
-- for parsing "," not followed by "logic" within G_mapping
------------------------------------------------------------------------
-- ParsecCombinator.notFollowedBy only allows to check for a single "tok"
-- thus a single Char.

notFollowedWith :: GenParser tok st a -> GenParser tok st b 
		-> GenParser tok st a 

p1 `notFollowedWith` p2 = try ((p1 >> p2 >> pzero) <|> p1)

plainComma = commaT `notFollowedWith` asKey logicS

-- rearrange list to keep current logic as first element
-- does not consume anything! (may only fail)
switchLogic :: Logic_code -> [AnyLogic] -> GenParser Char st [AnyLogic]
switchLogic n l@(Logic i : _) =
       let s = case n of 
	       Logic_code _ _ (Just (Logic_name t _)) _ -> tokStr t
	       _ -> language_name i
	   (f, r) =  partition (\ (Logic x) -> language_name x == s) l
       in if null f then fail ("unknown language " ++ s)
	  else return (f++r)

------------------------------------------------------------------------
-- parse G_mapping (if you modify this, do so for G_hiding, too!)
------------------------------------------------------------------------

parseItemsMap :: [AnyLogic] -> GenParser Char st (G_symb_map_items_list, [Token])
parseItemsMap (Logic i : _) = 
    do (cs, ps) <- parse_symb_map_items i `separatedBy` plainComma
       return (G_symb_map_items_list i cs, ps) 

parseMapping :: [AnyLogic] -> GenParser Char st ([G_mapping], [Token])
parseMapping l =
    do n <- parseLogic
       l' <- switchLogic n l  
       do c <- commaT
	  (gs, ps) <- parseMapping l'
	  return (G_logic_translation n : gs, c:ps)
        <|> return ([G_logic_translation n], [])
    <|> do (m, ps) <- parseItemsMap l
	   do  c <- commaT 
  	       (gs, qs) <- parseMapping l
	       return (G_symb_map m : gs, ps ++ c : qs)
	     <|> return ([G_symb_map m], ps)

------------------------------------------------------------------------
-- parse G_hiding (copied from above, but code sharing would be better!) 
------------------------------------------------------------------------

parseItemsList :: [AnyLogic] -> GenParser Char st (G_symb_items_list, [Token])
parseItemsList (Logic i : _) = 
    do (cs, ps) <- parse_symb_items i `separatedBy` plainComma
       return (G_symb_items_list i cs, ps) 

parseHiding :: [AnyLogic] -> GenParser Char st ([G_hiding], [Token])
parseHiding l =
    do n <- parseLogic
       l' <- switchLogic n l 
       do c <- commaT
	  (gs, ps) <- parseHiding l'
	  return (G_logic_projection n : gs, c:ps)
        <|> return ([G_logic_projection n], [])
    <|> do (m, ps) <- parseItemsList l
	   do  c <- commaT 
  	       (gs, qs) <- parseHiding l
	       return (G_symb_list m : gs, ps ++ c : qs)
	     <|> return ([G_symb_list m], ps)

------------------------------------------------------------------------
-- specs
------------------------------------------------------------------------

spec :: [AnyLogic] -> GenParser Char st SPEC
-- current logic is first element
spec l = reSpec l 

reSpec :: [AnyLogic] -> GenParser Char st SPEC
reSpec l = annoParser (simpleSpec l) >>= 
	   (\ s -> renaming l s <|> restriction l s)

renaming l s = 
    do w <- asKey withS
       (m, ps) <- parseMapping l
       return (Translation s (Renaming m (map tokPos (w:ps))))

restriction l s = 
    do w <- asKey hideS
       (m, ps) <- parseHiding l
       return (Reduction s (Hidden m (map tokPos (w:ps))))

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
