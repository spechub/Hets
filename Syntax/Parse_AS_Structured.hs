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
    logic translations and implicit coercions
    "and" should do union of involved logics

    arch specs
-}

module Syntax.Parse_AS_Structured where

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck

import Syntax.AS_Structured
import Common.AS_Annotation
import Common.AnnoState
import Common.Id(tokPos)
import Common.Keywords
import Common.Lexer
import Common.Token
import Text.ParserCombinators.Parsec
import Common.Id
import Data.List((\\))

-- import Syntax.Print_AS_Structured  -- for test purposes


------------------------------------------------------------------------
-- annotation adapter
------------------------------------------------------------------------

annoParser2 :: AParser st (Annoted a) -> AParser st (Annoted a)
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
encodingName :: AParser st Token
encodingName = pToken(reserved (funS:casl_reserved_words) (many1 
                    (oneOf ("_`" ++ (signChars \\ ":.")) 
                     <|> scanLPD)))

-- keep these identical in order to
-- decide after seeing ".", ":" or "->" what was meant
logicName :: AParser st Logic_name
logicName = do e <- encodingName
               do string dotS
                  s <- encodingName
                  return (Logic_name e (Just s)) 
                 <|> return (Logic_name e Nothing)        

------------------------------------------------------------------------
-- parse Logic_code
------------------------------------------------------------------------

parseLogic :: LogicGraph -> AParser AnyLogic Logic_code
parseLogic lG = do
   lc <- parseLogicAux
   case lc of
     Logic_code _ _ (Just l) _ -> do
         lookupAndSetLogicName l lG
         return lc
     Logic_code (Just c) _ _ _ -> do
         lookupAndSetComorphismName c lG
         return lc
     _ -> return lc

parseLogicAux :: AParser AnyLogic Logic_code
parseLogicAux = 
    do l <- asKey logicS
       do e <- logicName -- try to parse encoding or logic source after "logic"
          case e of 
              Logic_name _ (Just _) -> parseOptLogTarget Nothing (Just e) [l]
              Logic_name f Nothing -> 
                      do c <- colonT
                         parseLogAfterColon (Just f) [l,c]
                      <|> parseOptLogTarget Nothing (Just e) [l]
         <|> do f <- asKey funS  -- parse at least a logic target after "logic"
                t <- logicName
                return (Logic_code Nothing Nothing (Just t) (map tokPos [l,f]))

-- parse optional logic source and target after a colon (given an encoding e)
parseLogAfterColon :: Maybe Token -> [Token] 
                   -> AParser AnyLogic Logic_code
parseLogAfterColon e l =
    do s <- logicName
       parseOptLogTarget e (Just s) l
         <|> return (Logic_code e (Just s) Nothing (map tokPos l))
    <|> parseOptLogTarget e Nothing l
    <|> return (Logic_code e Nothing Nothing (map tokPos l))

-- parse an optional logic target (given encoding e or source s) 
parseOptLogTarget :: Maybe Token -> Maybe Logic_name -> [Token] 
                  -> AParser AnyLogic Logic_code
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

plainComma :: AParser st Token
plainComma = anComma `notFollowedWith` asKey logicS

------------------------------------------------------------------------
-- parse G_mapping 
------------------------------------------------------------------------

callSymParser :: Maybe (AParser st a) -> String -> String -> 
                 AParser st ([a], [Token])
callSymParser p name itemType = do
    case p of 
         Nothing -> fail ("no symbol"++itemType++" parser for language " 
                            ++ name)
         Just pa -> pa `separatedBy` plainComma

parseItemsMap :: AParser AnyLogic (G_symb_map_items_list, [Token])
parseItemsMap = 
   do (Logic lid) <- getUserState
      (cs, ps) <- callSymParser (parse_symb_map_items lid) 
                  (language_name lid) " maps" 
      return (G_symb_map_items_list lid cs, ps)

parseMapping :: LogicGraph 
                  -> AParser AnyLogic ([G_mapping], [Token])
parseMapping = parseMapOrHide G_logic_translation G_symb_map parseItemsMap

parseMapOrHide :: (Logic_code -> a) -> (t -> a) 
               -> AParser AnyLogic (t, [Token]) -> LogicGraph 
               -> AParser AnyLogic ([a], [Token])
parseMapOrHide constrLogic constrMap pa lG =
    do n <- parseLogic lG
       do c <- anComma
          (gs, ps) <- parseMapOrHide constrLogic constrMap pa lG
          return (constrLogic n : gs, c:ps)
        <|> return ([constrLogic n], [])
    <|> do (m, ps) <- pa
           do  c <- anComma 
               (gs, qs) <- parseMapOrHide constrLogic constrMap pa lG
               return (constrMap m : gs, ps ++ c : qs)
             <|> return ([constrMap m], ps)

------------------------------------------------------------------------
-- parse G_hiding 
------------------------------------------------------------------------

parseItemsList :: AParser AnyLogic (G_symb_items_list, [Token])
parseItemsList = 
   do Logic lid <- getUserState
      (cs, ps) <- callSymParser (parse_symb_items lid) 
                  (language_name lid) ""
      return (G_symb_items_list lid cs, ps) 

parseHiding :: LogicGraph -> AParser AnyLogic ([G_hiding], [Token])
parseHiding = parseMapOrHide G_logic_projection G_symb_list parseItemsList

------------------------------------------------------------------------
-- specs
------------------------------------------------------------------------

spec :: LogicGraph -> AParser AnyLogic (Annoted SPEC)
spec l = do (sps,ps) <- annoParser2 (specA l) `separatedBy` (asKey thenS)
            return (case sps of
                    [sp] -> sp
                    _ -> emptyAnno (Extension sps (map tokPos ps)))

specA :: LogicGraph -> AParser AnyLogic (Annoted SPEC)
specA l = do (sps,ps) <- annoParser2 (specB l) `separatedBy` (asKey andS)
             return (case sps of
                     [sp] -> sp
                     _ -> emptyAnno (Union sps (map tokPos ps)))

specB :: LogicGraph -> AParser AnyLogic (Annoted SPEC)
specB l = do    p1 <- asKey localS
                sp1 <- aSpec l
                p2 <- asKey withinS
                sp2 <- annoParser2 $ specB l
                return (emptyAnno $ Local_spec sp1 sp2 (map tokPos [p1,p2]))
          <|> specC l

specC :: LogicGraph -> AParser AnyLogic (Annoted SPEC)
specC lG = do
        Logic lid <- getUserState
        let l = Logic lid
            spD = annoParser $ specD lG
            rest = spD >>= translation_list lG Translation Reduction
        case data_logic lid of
          Nothing -> rest
          Just lD -> do
                         p1 <- asKey dataS -- not a keyword
                         setUserState lD
                         sp1 <- annoParser $ groupSpec lG
                         setUserState l
                         sp2 <- spD
                         return (emptyAnno $ Data lD l sp1 sp2 [tokPos p1])
                  <|> rest
          
translation_list :: LogicGraph -> (Annoted b -> RENAMING -> b)
                 -> (Annoted b -> RESTRICTION -> b) -> Annoted b 
                 -> AParser AnyLogic (Annoted b)
translation_list l ftrans frestr sp =
     do sp' <- translation l sp ftrans frestr
        translation_list l ftrans frestr (emptyAnno sp')
 <|> return sp

-- | Parse renaming
-- @
-- RENAMING ::= with SYMB-MAP-ITEMS-LIST
-- @
-- SYMB-MAP-ITEMS-LIST is parsed using parseMapping
renaming :: LogicGraph -> AParser AnyLogic RENAMING
renaming l =
    do kWith <- asKey withS
       (mappings, commas) <- parseMapping l
       return (Renaming mappings (map tokPos (kWith : commas)))


-- | Parse restriction
-- @
-- RESTRICTION ::= hide SYMB-ITEMS-LIST
--               | reveal SYMB-MAP-ITEMS-LIST
-- @
-- SYMB-ITEMS-LIST is parsed using parseHiding; SYMB-MAP-ITEMS-LIST is 
-- parsed using parseItemsMap
restriction :: LogicGraph -> AParser AnyLogic RESTRICTION
restriction l =
        -- hide
    do kHide <- asKey hideS
       (symbs, commas) <- parseHiding l
       return (Hidden symbs (map tokPos (kHide : commas)))
    <|> -- reveal
    do kReveal <- asKey revealS
       (mappings, commas) <- parseItemsMap
       return (Revealed mappings (map tokPos (kReveal : commas)))


translation :: LogicGraph -> a -> (a -> RENAMING -> b) 
            -> (a -> RESTRICTION -> b) -> AParser AnyLogic b
translation l sp ftrans frestr = 
    do r <- renaming l
       return (ftrans sp r)
    <|> 
    do r <- restriction l 
       return (frestr sp r)

groupSpecLookhead :: AParser AnyLogic Token
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

specD :: LogicGraph -> AParser AnyLogic SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l = do p <- asKey freeS `followedWith` groupSpecLookhead
             sp <- annoParser $ groupSpec l
             return (Free_spec sp [tokPos p])
      <|> do p <- asKey cofreeS `followedWith` groupSpecLookhead
             sp <- annoParser $ groupSpec l
             return (Cofree_spec sp [tokPos p])
      <|> do p <- asKey closedS `followedWith` groupSpecLookhead
             sp <- annoParser $ groupSpec l
             return (Closed_spec sp [tokPos p])
      <|> specE l
       
specE :: LogicGraph -> AParser AnyLogic SPEC
specE l = do lookAhead (try (oBraceT >> cBraceT)) 
                       -- avoid overlap with group spec
             basicSpec
      <|> logicSpec l
      <|> (lookAhead groupSpecLookhead >> groupSpec l)
      <|> basicSpec


-- | call a logic specific parser if it exists
callParser :: Maybe (AParser st a) -> String -> String -> AParser st a
callParser p name itemType = do
    case p of 
         Nothing -> fail ("no "++itemType++" parser for language " 
                            ++ name)
         Just pa -> pa

basicSpec :: AParser AnyLogic SPEC
basicSpec = do Logic lid <- getUserState
               bspec <- callParser (parse_basic_spec lid) (language_name lid)
                            "basic specification"
               return (Basic_spec (G_basic_spec lid bspec))


logicSpec :: LogicGraph -> AParser AnyLogic SPEC
logicSpec lG = do
   s1 <- asKey logicS
   lid <- logicName
   let Logic_name t _ = lid
   s2 <- asKey ":"
   oldlog <- getUserState
   lookupAndSetLogicName lid lG
   sp <- annoParser (specE lG)
   let sp1 = Qualified_spec lid sp (map tokPos [s1,t,s2])
   setUserState oldlog
   return sp1

lookupLogicName :: Monad m => Logic_name -> LogicGraph -> m AnyLogic
lookupLogicName (Logic_name lid _sublog) lg = 
    lookupLogic "Parser: " (tokStr lid) lg

lookupAndSetLogicName :: Logic_name -> LogicGraph -> AParser AnyLogic AnyLogic
lookupAndSetLogicName ln lg = do
    l <- lookupLogicName ln lg
    setUserState l
    return l


lookupAndSetComorphismName :: Token -> LogicGraph -> AParser AnyLogic ()
lookupAndSetComorphismName ctok lg = do
    Comorphism cid <- lookupComorphism (tokStr ctok) lg
    setUserState (Logic (targetLogic cid))

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

aSpec :: LogicGraph -> AParser AnyLogic (Annoted SPEC)
aSpec l = annoParser2 (spec l)

groupSpec :: LogicGraph -> AParser AnyLogic SPEC
groupSpec l = do b <- oBraceT
                 a <- aSpec l
                 c <- cBraceT
                 return (Group a (map tokPos [b, c])) 
              <|>
              do n <- simpleId
                 (f,ps) <- fitArgs l
                 return (Spec_inst n f ps)

fitArgs :: LogicGraph -> AParser AnyLogic ([Annoted FIT_ARG],[Pos])
fitArgs l = do fas <- many (fitArg l)
               let (fas1,ps) = unzip fas
               return (fas1,concat ps)

fitArg :: LogicGraph -> AParser AnyLogic (Annoted FIT_ARG,[Pos])
fitArg l = do b <- oBracketT   
              fa <- annoParser (fittingArg l)
              c <- cBracketT
              return (fa,[tokPos b,tokPos c])

fittingArg :: LogicGraph -> AParser AnyLogic FIT_ARG
fittingArg l = do (an,s) <- try (do an <- annos
                                    s <- asKey viewS
                                    return (an,s))
                  vn <- simpleId
                  (fa,ps) <- fitArgs l
                  return (Fit_view vn fa (tokPos s:ps) an)
            <|>
               do Logic lid <- getUserState
                  sp <- aSpec l
                  (symbit,ps) <- option (G_symb_map_items_list lid [],[])
                                 (do s <- asKey fitS               
                                     (m, qs) <- parseItemsMap
                                     return (m, map tokPos (s : qs)))
                  return (Fit_spec sp symbit ps)


optEnd :: AParser st (Maybe Token)
optEnd = option Nothing (fmap Just (asKey endS))
       
generics :: LogicGraph -> AParser AnyLogic GENERICITY
generics l = do 
   (pa,ps1) <- params l
   (imp,ps2) <- option ([],[]) (imports l)
   return (Genericity (Params pa) (Imported imp) (ps1++ps2))

params :: LogicGraph -> AParser AnyLogic ([Annoted SPEC],[Pos])
params l = do pas <- many (param l)
              let (pas1,ps) = unzip pas
              return (pas1,concat ps)

param :: LogicGraph -> AParser AnyLogic (Annoted SPEC,[Pos])
param l = do b <- oBracketT   
             pa <- aSpec l
             c <- cBracketT
             return (pa,[tokPos b,tokPos c])

imports :: LogicGraph -> AParser AnyLogic ([Annoted SPEC], [Pos])
imports l = do s <- asKey givenS
               (sps,ps) <- annoParser (groupSpec l) `separatedBy` anComma
               return (sps,map tokPos (s:ps))



