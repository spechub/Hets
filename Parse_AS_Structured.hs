
-- parse (do x<-many (char 'a'); s <- getInput; return (x,s)) "" "aaab"


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

import Logic_CASL  -- we need the default logic

import AS_Structured
import AS_Library
import AS_Annotation
import Anno_Parser
import Id(tokPos)
import Keywords
import Lexer
import Token
import Parsec
import ParsecChar (digit)
import Id
import List

import Maybe(maybeToList)

import Print_AS_Structured  -- for test purposes
import Print_HetCASL

------------------------------------------------------------------------
-- annotation adapter
------------------------------------------------------------------------

-- skip to leading annotation and read many
annos :: GenParser Char st [Annotation]
annos = skip >> many (annotationL << skip)

annoParser parser = bind (\x y -> Annoted y [] x []) annos parser

annoParser2 parser = bind (\x (Annoted y pos l r) -> Annoted y pos (x++l) r) annos parser

emptyAnno :: a -> Annoted a
emptyAnno x = Annoted x [] [] []

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

parseLogic :: GenParser Char AnyLogic Logic_code
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
{-switchLogic :: Logic_code -> LogicGraph -> GenParser Char st LogicGraph
switchLogic n l@(Logic i : _) =
       let s = case n of 
	       Logic_code _ _ (Just (Logic_name t _)) _ -> tokStr t
	       _ -> language_name i
	   (f, r) =  partition (\ (Logic x) -> language_name x == s) l
       in if null f then fail ("unknown language " ++ s)
	  else return (f++r)
-}

------------------------------------------------------------------------
-- parse G_mapping (if you modify this, do so for G_hiding, too!)
------------------------------------------------------------------------

parseItemsMap :: GenParser Char AnyLogic (G_symb_map_items_list, [Token])
parseItemsMap = 
   do Logic id <- getState
      (cs, ps) <- do
         s <- getInput
         pos <- getPosition
         (cs,rest) <- case parse_symb_map_items id of 
             Nothing -> fail ("no symbol map parser for language " 
   				    ++ language_name id)
	     Just p -> return (p (sourceName pos) s)
         setInput rest
         return cs 
       `separatedBy` plainComma
      return (G_symb_map_items_list id cs, ps)


parseMapping :: LogicGraph -> GenParser Char AnyLogic ([G_mapping], [Token])
parseMapping l =
    do n <- parseLogic
       do c <- commaT
	  (gs, ps) <- parseMapping l
	  return (G_logic_translation n : gs, c:ps)
        <|> return ([G_logic_translation n], [])
    <|> do (m, ps) <- parseItemsMap
	   do  c <- commaT 
  	       (gs, qs) <- parseMapping l
	       return (G_symb_map m : gs, ps ++ c : qs)
	     <|> return ([G_symb_map m], ps)

------------------------------------------------------------------------
-- parse G_hiding (copied from above, but code sharing would be better!) 
------------------------------------------------------------------------

parseItemsList :: LogicGraph -> GenParser Char AnyLogic (G_symb_items_list, [Token])
parseItemsList l = 
   do Logic id <- getState
      (cs,ps) <- do
         s <- getInput
         pos <- getPosition
         (cs,rest) <- case parse_symb_items id of 
             Nothing -> fail ("no symbol item parser for language " 
	   			    ++ language_name id)
	     Just p -> return (p (sourceName pos) s)
         setInput rest
         return cs 
       `separatedBy` plainComma
      return (G_symb_items_list id cs, []) 


parseHiding :: LogicGraph -> GenParser Char AnyLogic ([G_hiding], [Token])
parseHiding l =
    do n <- parseLogic
       do c <- commaT
	  (gs, ps) <- parseHiding l
	  return (G_logic_projection n : gs, c:ps)
        <|> return ([G_logic_projection n], [])
    <|> do (m, ps) <- parseItemsList l
	   do  c <- commaT 
  	       (gs, qs) <- parseHiding l
	       return (G_symb_list m : gs, ps ++ c : qs)
	     <|> return ([G_symb_list m], ps)

parseRevealing :: LogicGraph -> GenParser Char AnyLogic (G_symb_map_items_list, [Token])
parseRevealing l = undefined

------------------------------------------------------------------------
-- specs
------------------------------------------------------------------------

spec :: LogicGraph -> GenParser Char AnyLogic (Annoted SPEC)
spec l = do (sps,ps) <- annoParser2 (specA l) `separatedBy` (asKey thenS)
            return (case sps of
                    [sp] -> sp
                    otherwise -> emptyAnno (Extension sps (map tokPos ps)))

specA :: LogicGraph -> GenParser Char AnyLogic (Annoted SPEC)
specA l = do (sps,ps) <- annoParser (specB l) `separatedBy` (asKey andS)
             return (case sps of
                     [sp] -> sp
                     otherwise -> emptyAnno (Union sps (map tokPos ps)))

specB :: LogicGraph -> GenParser Char AnyLogic SPEC
specB l = do p1 <- asKey localS
             sp1 <- aSpec l
             p2 <- asKey withinS
             sp2 <- annoParser (specB l)
             return (Local_spec sp1 sp2 (map tokPos [p1,p2]))
          <|> do sp <- specC l
                 return (item sp)

specC :: LogicGraph -> GenParser Char AnyLogic (Annoted SPEC)
specC l = do{sp <- annoParser (specD l)
             ; (do{  p <- asKey withS
                   ; (m, ps) <- parseMapping l
                   ; return (emptyAnno (Translation sp (Renaming m (map tokPos (p:ps)))))
                  })<|>( do
                {  p <- asKey hideS
                 ; (m, ps) <- parseHiding l
                 ; return (emptyAnno (Reduction sp (Hidden m (map tokPos (p:ps)))))
                })<|>( do 
                {  p <- asKey revealS
                 ; (m, ps) <- parseRevealing l
                 ; return (emptyAnno (Reduction sp (Revealed m (map tokPos (p:ps)))))
                })<|> return sp
             }
specD :: LogicGraph -> GenParser Char AnyLogic SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l = do (p,b) <- try (do p1 <- asKey freeS
                              p2 <- oBraceT
                              return (p1,p2))
             a <- aSpec l
             c <- cBraceT
	     return (Free_spec (emptyAnno (Group a (map tokPos [b, c]))) [tokPos p])
      <|> do (p,n) <- try (do p1 <- asKey freeS
                              p2 <- simpleId
                              return (p1,p2))       
             (f,ps) <- fitArgs l
             return (Free_spec (emptyAnno (Spec_inst n f)) [tokPos p])
      <|> do p <- asKey cofreeS
             sp <- groupSpec l
             return (Cofree_spec (emptyAnno sp) [tokPos p])
      <|> do p <- asKey closedS
             sp <- groupSpec l
             return (Closed_spec (emptyAnno sp) [tokPos p])
      <|> specE l
       
specE :: LogicGraph -> GenParser Char AnyLogic SPEC
specE l = groupSpec l
      <|> basicSpec l
      <|> logicSpec l


basicSpec :: LogicGraph -> GenParser Char AnyLogic SPEC
basicSpec l = do Logic id <- getState
                 s <- getInput
                 pos <- getPosition
		 (bspec,rest) <- case parse_basic_spec id of 
		   Nothing -> fail ("no parser for language " 
				    ++ language_name id)
		   Just p -> return (p (sourceName pos) s)
                 setInput rest
                 return (Basic_spec (G_basic_spec id bspec))


logicSpec :: LogicGraph -> GenParser Char AnyLogic SPEC
logicSpec l = undefined {-do
   log <- parseLogic
                        name <- many1 alphaNum;
                        setState (case lookup name logics of
                          Nothing -> error ("logic "++name++" unknown")
                          Just id -> id); 
                        spaces; return (\x->x) } )],
-}

aSpec l = annoParser2 (spec l)

groupSpec l = do b <- oBraceT
		 a <- aSpec l
		 c <- cBraceT
		 return (Group a (map tokPos [b, c])) 
	      <|>
	      do n <- simpleId
		 (f,ps) <- fitArgs l
		 return (Spec_inst n f)
            -- ??? What to do with ps? Spec_inst is not consistent here!

fitArgs :: LogicGraph -> GenParser Char AnyLogic ([Annoted FIT_ARG],[Pos])
fitArgs l = do fas <- many (fitArg l)
               let (fas1,ps) = unzip fas
               return (fas1,concat ps)

fitArg :: LogicGraph -> GenParser Char AnyLogic (Annoted FIT_ARG,[Pos])
fitArg l = do b <- oBracketT   
              fa <- annoParser (fittingArg l)
              c <- cBracketT
              return (fa,[tokPos b,tokPos c])

fittingArg :: LogicGraph -> GenParser Char AnyLogic FIT_ARG
fittingArg l = do sp <- aSpec l
                  Logic id <- getState
                  (symbit,ps) <- option (G_symb_map_items_list id [],[]) 
                                 (do s <- asKey fitS               
                                     (m, ps) <- parseItemsMap 
                                     return (m,[tokPos s]))
                  return (Fit_spec sp symbit ps)
            <|>
               do an <- annos
                  s <- asKey viewS
                  vn <- simpleId
                  (fa,ps) <- fitArgs l
                  return (Fit_view vn fa (tokPos s:ps) an)


optEnd = option Nothing (fmap Just (asKey endS))
       
generics l = do 
   (pa,ps1) <- params l
   (imp,ps2) <- option ([],[]) (imports l)
   return (Genericity (Params pa) (Imported imp) (ps1++ps2))

params :: LogicGraph -> GenParser Char AnyLogic ([Annoted SPEC],[Pos])
params l = do pas <- many (param l)
              let (pas1,ps) = unzip pas
              return (pas1,concat ps)

param :: LogicGraph -> GenParser Char AnyLogic (Annoted SPEC,[Pos])
param l = do b <- oBracketT   
             pa <- aSpec l
             c <- cBracketT
             return (pa,[tokPos b,tokPos c])

imports l = do s <- asKey givenS
               (sps,ps) <- annoParser (groupSpec l) `separatedBy` commaT
               return (sps,map tokPos (s:ps))

libItem l = -- spec defn
    do s <- asKey specS 
       n <- simpleId
       g <- generics l
       e <- asKey equalS
       a <- aSpec l
       q <- optEnd
       return (AS_Library.Spec_defn n g a (map tokPos ([s, e] ++ Maybe.maybeToList q)))
  <|> -- view defn
    do s1 <- asKey viewS
       vn <- simpleId
       g <- generics l
       s2 <- asKey ":"
       vt <- viewType l
       (symbMap,ps) <- option ([],[]) 
                        (do s <- asKey equalS               
                            (m, ps) <- parseMapping l
                            return (m,[s]))          
       q <- optEnd
       return (AS_Library.View_defn vn g vt symbMap 
                    (map tokPos ([s1,s2] ++ ps ++ Maybe.maybeToList q)))
  <|> -- download
    do s1 <- asKey fromS
       ln <- libName
       s2 <- asKey getS
       (il,ps) <- itemNameOrMap `separatedBy` commaT
       q <- optEnd
       return (Download_items ln il (map tokPos ([s1,s2]++ps++ Maybe.maybeToList q)))

viewType l = do sp1 <- annoParser (groupSpec l)
                s <- asKey toS
                sp2 <- annoParser (groupSpec l)
                return (View_type sp1 sp2 [tokPos s])

libName = do lid <- libId
             v <- option Nothing (fmap Just version)
             return (case v of
               Nothing -> Lib_id lid
               Just v1 -> Lib_version lid v1)

libId = do (path,ps) <- scanAnyWords `separatedBy` (asKey "/")
           return (Indirect_link (concat (intersperse "/" path)) [tokPos (head ps)])
           -- ??? URL need to be added

version = do s <- asKey versionS
             (ns,ps) <- many1 digit `separatedBy` (asKey ".")
             return (Version_number ns (map tokPos [s,head ps]))

itemNameOrMap = do i1 <- simpleId
                   i' <- option Nothing (do
                      s <- asKey "|->"
                      i <- simpleId
                      return (Just (i,s)))
                   return (case i' of
                      Nothing -> Item_name i1
                      Just (i2,s) -> Item_name_map i1 i2 [tokPos s])


library l = do s1 <- asKey libraryS
               ln <- libName
               an <- annos
               ls <- many (annoParser (libItem l))
               return (Lib_defn ln ls [tokPos s1] an)

-------------------------------------------------------------
-- Testing
-------------------------------------------------------------

parseSPEC fname =
  do input <- readFile fname
     case runParser (do x <- spec ([],[])
                        s1<-getInput
                        return (x,s1))
               (Logic CASL) fname input of
            Left err -> error (show err)
            Right x -> return x

parseLib fname =
  do input <- readFile fname
     case runParser (do x <- library ([],[])
                        s1<-getInput
                        return (x,s1))
               (Logic CASL) fname input of
            Left err -> error (show err)
            Right x -> return x

test fname = do
  (x,errs) <- parseLib fname
  putStrLn (show (printText0_eGA x))