{-| 
   
Module      :  $Header$
Copyright   :  (c) Till Mossakowski, Christian Maeder, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   Parsing the Structured part of hetrogenous specifications.
   Concerning the homogeneous syntax, this follows Sect II:3.1.3 
   of the CASL Reference Manual.

-}
{-
   http://www.cofi.info/Documents/CASL/Summary/
   from 25 March 2001

   C.2.2 Structured Specifications

   todo:
    fixing of details concerning annos
    logic translations and implicit coercions
    "and" should do union of involved logics

    arch specs
-}

module Syntax.Parse_AS_Structured where

import Logic.Grothendieck
import Logic.Logic

-- import CASL.Logic_CASL  -- we don't need the default logic

import Syntax.AS_Structured
import Common.AS_Annotation
import Common.AnnoState
import Common.Id(tokPos)
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Lib.Parsec
import Common.Id
import Data.List((\\))

-- import Syntax.Print_AS_Structured  -- for test purposes


------------------------------------------------------------------------
-- annotation adapter
------------------------------------------------------------------------

annoParser2 :: AParser (Annoted a) -> AParser (Annoted a)
annoParser2 parser = bind (\x (Annoted y pos l r) -> 
			   Annoted y pos (x++l) r) annos parser

emptyAnno :: a -> Annoted a
emptyAnno x = Annoted x [] [] []

------------------------------------------------------------------------
-- logic and encoding names
------------------------------------------------------------------------

-- exclude colon (because encoding must be recognized)
-- exclude dot to recognize optional sublogic name
-- include underscore and backquote
 
-- better list what is allowed rather than exclude what is forbidden
-- white spaces und non-printables should be not allowed!
encodingName :: AParser Token
encodingName = pToken(reserved (funS:casl_reserved_words) (many1 
		    (oneOf ("_`" ++ (signChars \\ ":.")) 
		     <|> scanLPD)))

-- keep these identical in order to
-- decide after seeing ".", ":" or "->" what was meant
logicName :: AParser Logic_name
logicName = do e <- encodingName
	       do string dotS
		  s <- encodingName
                  return (Logic_name e (Just s)) 
		 <|> return (Logic_name e Nothing)        

------------------------------------------------------------------------
-- parse Logic_code
------------------------------------------------------------------------

parseLogic :: AParser Logic_code
parseLogic = 
    do l <- asKey logicS
       do e <- logicName -- try to parse encoding or logic source after "logic"
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
parseLogAfterColon :: Maybe Token -> [Token] -> AParser Logic_code
parseLogAfterColon e l =
    do s <- logicName
       parseOptLogTarget e (Just s) l
	 <|> return (Logic_code e (Just s) Nothing (map tokPos l))
    <|> parseOptLogTarget e Nothing l
    <|> return (Logic_code e Nothing Nothing (map tokPos l))

-- parse an optional logic target (given encoding e or source s) 
parseOptLogTarget :: Maybe Token -> Maybe Logic_name -> [Token] 
		  -> AParser Logic_code
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
p1 `notFollowedWith` p2 = try $ do pp <- (try (p1 >> p2) >> return pzero)
                                         <|> return p1
				   pp 
-- see http://www.mail-archive.com/haskell@haskell.org/msg14388.html
-- by Andrew Pimlott

plainComma :: AParser Token
plainComma = anComma `notFollowedWith` asKey logicS

------------------------------------------------------------------------
-- parse G_mapping (if you modify this, do so for G_hiding, too!)
------------------------------------------------------------------------

parseItemsMap :: AnyLogic -> AParser (G_symb_map_items_list, [Token])
parseItemsMap (Logic lid) = 
   do (cs, ps) <- callParser (parse_symb_map_items lid) 
		  (language_name lid) "symbol maps" `separatedBy` plainComma 
      return (G_symb_map_items_list lid cs, ps)

parseMapping :: (AnyLogic, LogicGraph) -> AParser ([G_mapping], [Token])
parseMapping l =
    do n <- parseLogic
       do c <- anComma
	  (gs, ps) <- parseMapping l
	  return (G_logic_translation n : gs, c:ps)
        <|> return ([G_logic_translation n], [])
    <|> do (m, ps) <- parseItemsMap $ fst l
	   do  c <- anComma 
  	       (gs, qs) <- parseMapping l
	       return (G_symb_map m : gs, ps ++ c : qs)
	     <|> return ([G_symb_map m], ps)

------------------------------------------------------------------------
-- parse G_hiding (copied from above, but code sharing would be better!) 
------------------------------------------------------------------------

parseItemsList :: (AnyLogic, LogicGraph) 
	       -> AParser (G_symb_items_list, [Token])
parseItemsList (Logic lid, _) = 
   do (cs, _ps) <- callParser (parse_symb_items lid) 
		  (language_name lid) "symbols" `separatedBy` plainComma
      return (G_symb_items_list lid cs, []) 

parseHiding :: (AnyLogic, LogicGraph) -> AParser ([G_hiding], [Token])
parseHiding l =
    do n <- parseLogic
       do c <- anComma
	  (gs, ps) <- parseHiding l
	  return (G_logic_projection n : gs, c:ps)
        <|> return ([G_logic_projection n], [])
    <|> do (m, ps) <- parseItemsList l
	   do  c <- anComma 
  	       (gs, qs) <- parseHiding l
	       return (G_symb_list m : gs, ps ++ c : qs)
	     <|> return ([G_symb_list m], ps)

parseRevealing :: (AnyLogic, LogicGraph) 
	       -> AParser (G_symb_map_items_list, [Token])
parseRevealing _ = error "Parse_AS_Structured.hs:parseRevealing"

------------------------------------------------------------------------
-- specs
------------------------------------------------------------------------

spec :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC)
spec l = do (sps,ps) <- annoParser2 (specA l) `separatedBy` (asKey thenS)
            return (case sps of
                    [sp] -> sp
                    _ -> emptyAnno (Extension sps (map tokPos ps)))

specA :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC)
specA l = do (sps,ps) <- specB l `separatedBy` (asKey andS)
             return (case sps of
                     [sp] -> sp
                     _ -> emptyAnno (Union sps (map tokPos ps)))

specB :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC)
specB l = do p1 <- asKey localS
             sp1 <- aSpec l
             p2 <- asKey withinS
             sp2 <- specB l
             return (emptyAnno $ Local_spec sp1 sp2 (map tokPos [p1,p2]))
          <|> specC l

specC :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC)
specC l@(Logic lid, lG) = 
        let rest = annoParser (specD l) >>= translation_list l
        in case data_logic lid of
	  Nothing -> rest
	  Just (Logic dlid) -> do
                         p1 <- asKey "data"
			 sp1 <- groupSpec (Logic dlid, lG)
                         sp2 <- specD l
                         return (emptyAnno (Data (Logic dlid) 
                                                 (emptyAnno sp1) 
                                                 (emptyAnno sp2) 
                                                 [tokPos p1]))
		  <|> rest
          
translation_list :: (AnyLogic, LogicGraph) -> Annoted SPEC 
		 -> AParser (Annoted SPEC)
translation_list l sp =
     do sp' <- translation l sp
        translation_list l sp'
 <|> return sp

translation :: (AnyLogic, LogicGraph) -> Annoted SPEC 
	    -> AParser (Annoted SPEC)
translation l sp =
     do p <- asKey withS
        (m, ps) <- parseMapping l
        return (emptyAnno (Translation sp (Renaming m (map tokPos (p:ps)))))
 <|> do p <- asKey hideS
        (m, ps) <- parseHiding l
        return (emptyAnno (Reduction sp (Hidden m (map tokPos (p:ps)))))
 <|> do p <- asKey revealS
        (m, ps) <- parseItemsMap $ fst l
        return (emptyAnno (Reduction sp (Revealed m (map tokPos (p:ps)))))

groupSpecLookhead :: AParser Token
groupSpecLookhead = oBraceT <|> ((simpleId << annos) 
				 `followedWith`
				 (asKey withS <|> asKey hideS
				  <|> asKey revealS <|> asKey andS
				  <|> asKey thenS <|> cBraceT
				  <|> asKey fitS <|> asKey viewS
				  <|> asKey specS <|> asKey archS
				  <|> asKey unitS
				  <|> asKey withinS <|> asKey endS
				  <|> oBracketT <|> cBracketT
				  <|> (eof >> return (Token "" nullPos))))

specD :: (AnyLogic, LogicGraph) -> AParser SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l = do p <- asKey freeS `followedWith` groupSpecLookhead
             sp <- groupSpec l
	     return (Free_spec (emptyAnno sp) [tokPos p])
      <|> do p <- asKey cofreeS `followedWith` groupSpecLookhead
             sp <- groupSpec l
             return (Cofree_spec (emptyAnno sp) [tokPos p])
      <|> do p <- asKey closedS `followedWith` groupSpecLookhead
             sp <- groupSpec l
             return (Closed_spec (emptyAnno sp) [tokPos p])
      <|> specE l
       
specE :: (AnyLogic, LogicGraph) -> AParser SPEC
specE l = do lookAhead (try (oBraceT >> cBraceT)) 
                       -- avoid overlap with group spec
             basicSpec l        
      <|> logicSpec l
      <|> (lookAhead groupSpecLookhead >> groupSpec l)
      <|> basicSpec l


-- | call a logic specific parser if it exists
callParser :: Maybe (AParser a) -> String -> String -> AParser a
callParser p name itemType = do
    case p of 
	 Nothing -> fail ("no "++itemType++" parser for language " 
			    ++ name)
	 Just pa -> pa

basicSpec :: (AnyLogic, LogicGraph) -> AParser SPEC
basicSpec (Logic lid, _) = 
              do bspec <- callParser (parse_basic_spec lid) (language_name lid)
                            "basic specification"
                 return (Basic_spec (G_basic_spec lid bspec))


logicSpec :: (AnyLogic, LogicGraph) -> AParser SPEC
logicSpec (oldlog, lG) = do
   s1 <- asKey logicS
   lid <- logicName
   let Logic_name t _ = lid
   s2 <- asKey ":"
   newlog <- lookupLogicName lid lG
   logtrans <- coercelog newlog oldlog
   sp <- annoParser (specE (newlog, lG))
   let sp1 = Qualified_spec lid sp (map tokPos [s1,t,s2])
   return (logtrans sp1)

lookupLogicName :: Monad m => Logic_name -> LogicGraph -> m AnyLogic
lookupLogicName (Logic_name lid _sublog) lg = 
    lookupLogic "Parser: " (tokStr lid) lg

{- a code snippit to lookup the sublogic:
      case sublog of
        Nothing -> Logic lid
        Just s ->
         case find (\sub -> tokStr s `elem` sublogic_names lid sub) 
                   (all_sublogics lid) of
            Nothing -> error ("sublogic "++tokStr s++
                              " in logic "++tokStr log++" unknown")
            Just sub -> Logic lid  -- ??? can we throw away sublogic?
-}
coercelog :: Monad m => AnyLogic -> AnyLogic -> m (a -> a)
coercelog (Logic newlid) (Logic oldlid) =
  if newlang == oldlang then return id
   else fail ("Cannot coerce from "++newlang++" to "++oldlang)
  where newlang = language_name newlid
        oldlang = language_name oldlid
   -- \sp -> Translation (emptyAnno sp) 
   --		  (Renaming [G_logic_translation (Logic_code...)] [])

aSpec :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC)
aSpec l = annoParser2 (spec l)

groupSpec :: (AnyLogic, LogicGraph) -> AParser SPEC
groupSpec l = do b <- oBraceT
		 a <- aSpec l
		 c <- cBraceT
		 return (Group a (map tokPos [b, c])) 
	      <|>
	      do n <- simpleId
		 (f,ps) <- fitArgs l
		 return (Spec_inst n f ps)

fitArgs :: (AnyLogic, LogicGraph) -> AParser ([Annoted FIT_ARG],[Pos])
fitArgs l = do fas <- many (fitArg l)
               let (fas1,ps) = unzip fas
               return (fas1,concat ps)

fitArg :: (AnyLogic, LogicGraph) -> AParser (Annoted FIT_ARG,[Pos])
fitArg l = do b <- oBracketT   
              fa <- annoParser (fittingArg l)
              c <- cBracketT
              return (fa,[tokPos b,tokPos c])

fittingArg :: (AnyLogic, LogicGraph) -> AParser FIT_ARG
fittingArg l@(Logic lid, _) = 
               do (an,s) <- try (do an <- annos
                                    s <- asKey viewS
                                    return (an,s))
                  vn <- simpleId
                  (fa,ps) <- fitArgs l
                  return (Fit_view vn fa (tokPos s:ps) an)
            <|>
               do sp <- aSpec l
                  (symbit,ps) <- option (G_symb_map_items_list lid [],[])
                                 (do s <- asKey fitS               
                                     (m, qs) <- parseItemsMap $ fst l
                                     return (m, map tokPos (s : qs)))
                  return (Fit_spec sp symbit ps)


optEnd :: AParser (Maybe Token)
optEnd = option Nothing (fmap Just (asKey endS))
       
generics :: (AnyLogic, LogicGraph) -> AParser GENERICITY
generics l = do 
   (pa,ps1) <- params l
   (imp,ps2) <- option ([],[]) (imports l)
   return (Genericity (Params pa) (Imported imp) (ps1++ps2))

params :: (AnyLogic, LogicGraph) -> AParser ([Annoted SPEC],[Pos])
params l = do pas <- many (param l)
              let (pas1,ps) = unzip pas
              return (pas1,concat ps)

param :: (AnyLogic, LogicGraph) -> AParser (Annoted SPEC,[Pos])
param l = do b <- oBracketT   
             pa <- aSpec l
             c <- cBracketT
             return (pa,[tokPos b,tokPos c])

imports :: (AnyLogic, LogicGraph) -> AParser ([Annoted SPEC], [Pos])
imports l = do s <- asKey givenS
               (sps,ps) <- annoParser (groupSpec l) `separatedBy` anComma
               return (sps,map tokPos (s:ps))



