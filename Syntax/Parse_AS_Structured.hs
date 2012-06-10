{- |
Module      :  $Header$
Description :  parser for CASL (heterogeneous) structured specifications
Copyright   :  (c) Till Mossakowski, Christian Maeder, Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Parser for CASL (heterogeneous) structured specifications
   Concerning the homogeneous syntax, this follows Sect II:3.1.3
   of the CASL Reference Manual.
-}

module Syntax.Parse_AS_Structured
    ( annoParser2
    , groupSpec
    , aSpec
    , logicName
    , parseMapping
    , parseCorrespondences
    , translationList
    , hetIRI
    ) where

import Logic.Logic (AnyLogic (..), language_name, data_logic, Syntax (..))
import Logic.Comorphism (targetLogic, AnyComorphism (..))
import Logic.Grothendieck
    ( LogicGraph
    , setCurLogic
    , G_basic_spec (..)
    , G_symb_map_items_list (..)
    , G_symb_items_list (..)
    , lookupCurrentLogic
    , lookupComorphism)
import Syntax.AS_Structured

import Common.AS_Annotation
import Common.AnnoState
import Common.Id
import Common.IRI
import Common.Keywords
import Common.Lexer
import Common.Parsec
import Common.Token

import Text.ParserCombinators.Parsec

import Data.Char
import Data.Maybe
import Control.Monad

import Debug.Trace -- only commented out for future debugging purposes

hetIRI :: GenParser Char st IRI
hetIRI = try $ do
  i <- iriManchester
  skipSmart
  if iriToStringUnsecure i `elem` casl_reserved_words then
      unexpected $ show i
    else return i

-- | parse annotations and then still call an annotation parser
annoParser2 :: AParser st (Annoted a) -> AParser st (Annoted a)
annoParser2 =
  liftM2 (\ x (Annoted y pos l r) -> Annoted y pos (x ++ l) r) annos

-- * logic and encoding names

-- within sublogics we allow some further symbol characters
sublogicName :: AParser st String
sublogicName = many $ satisfy $ \ c -> notElem c ":./\\" && isSignChar c
    || elem c "_'" || isAlphaNum c

{- keep these identical in order to
decide after seeing ".", ":" or "->" what was meant -}
logicName :: AParser st Logic_name
logicName = do
      i <- iriManchester
      let (ft, rt) = break (== '.') $ abbrevPath i
      (e, ms) <- if null rt then return (i, Nothing)
         else do
           s <- sublogicName -- try more sublogic characters
           return (i { abbrevPath = ft}, Just . mkSimpleId $ tail rt ++ s)
      skipSmart
      mt <- optionMaybe $ oParenT >> iriCurie << cParenT
      return $ Logic_name e ms mt

-- * parse Logic_code

parseLogic :: LogicGraph -> AParser st (Logic_code, LogicGraph)
parseLogic lG = do
   lc <- parseLogicAux
   case lc of
     Logic_code _ _ (Just l) _ -> return (lc, setLogicName l lG)
     Logic_code (Just c) _ _ _ -> do
         nLg <- lookupAndSetComorphismName c lG
         return (lc, nLg)
     _ -> return (lc, lG)

parseLogicAux :: AParser st Logic_code
parseLogicAux =
    do l <- asKey logicS
       do e <- logicName -- try to parse encoding or logic source after "logic"
          case e of
              Logic_name f Nothing Nothing ->
                      do c <- colonT
                         parseLogAfterColon (Just f) [l, c]
                      <|> parseOptLogTarget Nothing (Just e) [l]
                      <|> return (Logic_code (Just f) Nothing Nothing
                                  $ tokPos l)
              _ -> parseOptLogTarget Nothing (Just e) [l]
         <|> do
           f <- asKey funS  -- parse at least a logic target after "logic"
           t <- logicName
           return $ Logic_code Nothing Nothing (Just t)
                                       $ tokPos l `appRange` tokPos f

-- parse optional logic source and target after a colon (given an encoding e)
parseLogAfterColon :: Maybe IRI -> [Token] -> AParser st Logic_code
parseLogAfterColon e l =
    do s <- logicName
       parseOptLogTarget e (Just s) l
         <|> return (Logic_code e (Just s) Nothing $ catRange l)
    <|> parseOptLogTarget e Nothing l

-- parse an optional logic target (given encoding e or source s)
parseOptLogTarget :: Maybe IRI -> Maybe Logic_name -> [Token]
                  -> AParser st Logic_code
parseOptLogTarget e s l =
    do f <- asKey funS
       let p = catRange $ l ++ [f]
       do t <- logicName
          return (Logic_code e s (Just t) p)
        <|> return (Logic_code e s Nothing p)

plainComma :: AParser st Token
plainComma = anComma `notFollowedWith` asKey logicS

-- * parse G_mapping

callSymParser :: Maybe (AParser st a) -> String -> String ->
                 AParser st ([a], [Token])
callSymParser p name itemType = case p of
    Nothing ->
        fail $ "no symbol" ++ itemType ++ " parser for language " ++ name
    Just pa -> separatedBy pa plainComma

parseItemsMap :: AnyLogic -> AParser st (G_symb_map_items_list, [Token])
parseItemsMap (Logic lid) = do
      (cs, ps) <- callSymParser (parse_symb_map_items lid)
                  (language_name lid) " maps"
      return (G_symb_map_items_list lid cs, ps)


parseMapping :: LogicGraph -> AParser st ([G_mapping], [Token])
parseMapping = parseMapOrHide G_logic_translation G_symb_map parseItemsMap

parseMapOrHide :: (Logic_code -> a) -> (t -> a)
               -> (AnyLogic -> AParser st (t, [Token])) -> LogicGraph
               -> AParser st ([a], [Token])
parseMapOrHide constrLogic constrMap pa lG =
    do (n, nLg) <- parseLogic lG
       do c <- anComma
          (gs, ps) <- parseMapOrHide constrLogic constrMap pa nLg
          return (constrLogic n : gs, c : ps)
        <|> return ([constrLogic n], [])
    <|> do
      l <- lookupCurrentLogic "parseMapOrHide" lG
      (m, ps) <- pa l
      do c <- anComma
         (gs, qs) <- parseMapOrHide constrLogic constrMap pa lG
         return (constrMap m : gs, ps ++ c : qs)
        <|> return ([constrMap m], ps)

-- * parse G_hiding

parseItemsList :: AnyLogic -> AParser st (G_symb_items_list, [Token])
parseItemsList (Logic lid) = do
      (cs, ps) <- callSymParser (parse_symb_items lid)
                  (language_name lid) ""
      return (G_symb_items_list lid cs, ps)

parseHiding :: LogicGraph -> AParser st ([G_hiding], [Token])
parseHiding = parseMapOrHide G_logic_projection G_symb_list parseItemsList

-- * specs

-- "then" is associative, therefore flatten extensions

flatExts :: [Annoted SPEC] -> [Annoted SPEC]
flatExts = concatMap $ \ as -> case item as of
   Extension sps _ -> sps
   Group sp _ -> case flatExts [sp] of
     [_] -> [as]
     sps -> sps
   _ -> [as]

spec :: LogicGraph -> AParser st (Annoted SPEC)
spec l = do
  (sps, ps) <- annoParser2 (specA l) `separatedBy` asKey thenS
  return $ case sps of
    [sp] -> sp
    _ -> emptyAnno (Extension (flatExts sps) $ catRange ps)

specA :: LogicGraph -> AParser st (Annoted SPEC)
specA l = do
  (sps, ps) <- annoParser2 (specB l) `separatedBy` asKey andS
  return $ case sps of
    [sp] -> sp
    _ -> emptyAnno (Union sps $ catRange ps)

specB :: LogicGraph -> AParser st (Annoted SPEC)
specB l = do
    p1 <- asKey localS
    sp1 <- aSpec l
    p2 <- asKey withinS
    sp2 <- annoParser2 $ specB l
    return (emptyAnno $ Local_spec sp1 sp2 $ tokPos p1 `appRange` tokPos p2)
  <|> specC l

specC :: LogicGraph -> AParser st (Annoted SPEC)
specC lG = do
    let spD = annoParser $ specD lG
        rest = spD >>= translationList lG Translation Reduction
    l@(Logic lid) <- lookupCurrentLogic "specC" lG
    {- if the current logic has an associated data_logic,
    parse "data SPEC1 SPEC2", where SPEC1 is in the data_logic
    SPEC1 needs to be a basic spec or a grouped spec
    SPEC2 is in the currrent logic -}
    case data_logic lid of
          Nothing -> rest
          Just lD@(Logic dl) -> do
              p1 <- asKey dataS -- not a keyword
              sp1 <- annoParser $ basicSpec lD
                  <|> groupSpec (setCurLogic (language_name dl) lG)
              sp2 <- spD
              return (emptyAnno $ Data lD l sp1 sp2 $ tokPos p1)
            <|> rest

translationList :: LogicGraph -> (Annoted b -> RENAMING -> b)
  -> (Annoted b -> RESTRICTION -> b) -> Annoted b -> AParser st (Annoted b)
translationList l ftrans frestr sp =
     do sp' <- translation l sp ftrans frestr
        translationList l ftrans frestr (emptyAnno sp')
  <|> return sp

{- | Parse renaming
@
RENAMING ::= with SYMB-MAP-ITEMS-LIST
@
SYMB-MAP-ITEMS-LIST is parsed using parseMapping -}
renaming :: LogicGraph -> AParser st RENAMING
renaming l =
    do kWith <- asKey withS
       (mappings, commas) <- parseMapping l
       return (Renaming mappings $ catRange $ kWith : commas)

{- | Parse restriction
@
RESTRICTION ::= hide SYMB-ITEMS-LIST
              | reveal SYMB-MAP-ITEMS-LIST
@
SYMB-ITEMS-LIST is parsed using parseHiding; SYMB-MAP-ITEMS-LIST is
parsed using parseItemsMap -}
restriction :: LogicGraph -> AParser st RESTRICTION
restriction lg =
        -- hide
    do kHide <- asKey hideS
       (symbs, commas) <- parseHiding lg
       return (Hidden symbs (catRange (kHide : commas)))
    <|> -- reveal
    do kReveal <- asKey revealS
       nl <- lookupCurrentLogic "reveal" lg
       (mappings, commas) <- parseItemsMap nl
       return (Revealed mappings (catRange (kReveal : commas)))

translation :: LogicGraph -> a -> (a -> RENAMING -> b)
            -> (a -> RESTRICTION -> b) -> AParser st b
translation l sp ftrans frestr =
    do r <- renaming l
       return (ftrans sp r)
    <|>
    do r <- restriction l
       return (frestr sp r)

groupSpecLookhead :: AParser st IRI
groupSpecLookhead =
  let tok2IRI = liftM simpleIdToIRI in
  (tok2IRI oBraceT) <|> followedWith (hetIRI << annos)
  (choice (map (tok2IRI . asKey) criticalKeywords)
   <|> tok2IRI cBraceT <|> tok2IRI oBracketT <|> tok2IRI cBracketT
   <|> (eof >> return nullIRI))

specD :: LogicGraph -> AParser st SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l = do
    p <- asKey freeS `followedWith` groupSpecLookhead
    sp <- annoParser $ groupSpec l
    return (Free_spec sp $ tokPos p)
  <|> do
    p <- asKey cofreeS `followedWith` groupSpecLookhead
    sp <- annoParser $ groupSpec l
    return (Cofree_spec sp $ tokPos p)
  <|> do
    p <- asKey closedS `followedWith` groupSpecLookhead
    sp <- annoParser $ groupSpec l
    return (Closed_spec sp $ tokPos p)
  <|> specE l

specE :: LogicGraph -> AParser st SPEC
specE l = logicSpec l
      <|> combineSpec
      <|> (lookAhead groupSpecLookhead >> groupSpec l)
      <|> (lookupCurrentLogic "basic spec" l >>= basicSpec)

-- | call a logic specific parser if it exists
callParser :: Maybe (AParser st a) -> String -> String -> AParser st a
callParser p name itemType =
  fromMaybe (fail $ "no " ++ itemType ++ " parser for language " ++ name) p

basicSpec :: AnyLogic -> AParser st SPEC
basicSpec (Logic lid) = do
    p <- getPos
    bspec <- callParser (parse_basic_spec lid) (language_name lid)
             "basic specification"
    q <- getPos
    return $ Basic_spec (G_basic_spec lid bspec) $ Range [p, q]

logicSpec :: LogicGraph -> AParser st SPEC
logicSpec lG = do
   s1 <- asKey logicS
   ln <- logicName
   s2 <- colonT
   sp <- annoParser $ specD $ setLogicName ln lG
   return $ Qualified_spec ln sp $ toRange s1 [] s2

combineSpec :: AParser st SPEC
combineSpec = do
    s1 <- asKey combineS
    oir <- commaSep1 hetIRI
    (exl, ps) <- (do
          s2 <- try $ asKey excludingS
          e <- commaSep1 hetIRI
          p <- getPos
          return (e, appRange (tokPos s2) $ Range [p])
        <|> return ([], nullRange)
      )
    return $ Combination oir exl $ appRange (tokPos s1) ps

lookupAndSetComorphismName :: IRI -> LogicGraph -> AParser st LogicGraph
lookupAndSetComorphismName cIRI lg = do
    Comorphism cid <- lookupComorphism (iriToStringUnsecure cIRI) lg
    return $ setCurLogic (language_name $ targetLogic cid) lg

aSpec :: LogicGraph -> AParser st (Annoted SPEC)
aSpec = annoParser2 . spec

groupSpec :: LogicGraph -> AParser st SPEC
groupSpec l = do
    b <- oBraceT
    do
      c <- cBraceT
      return $ EmptySpec $ catRange [b, c]
     <|> do
      a <- aSpec l
      c <- cBraceT
      return $ Group a $ catRange [b, c]
  <|> do
    n <- hetIRI
    (f, ps) <- fitArgs l
    return (Spec_inst n f ps)

fitArgs :: LogicGraph -> AParser st ([Annoted FIT_ARG], Range)
fitArgs l = do
  fas <- many (fitArg l)
  let (fas1, ps) = unzip fas
  return (fas1, concatMapRange id ps)

fitArg :: LogicGraph -> AParser st (Annoted FIT_ARG, Range)
fitArg l = do
  b <- oBracketT
  fa <- annoParser (fittingArg l)
  c <- cBracketT
  return (fa, toRange b [] c)

fittingArg :: LogicGraph -> AParser st FIT_ARG
fittingArg l = do
    s <- asKey viewS
    vn <- hetIRI
    (fa, ps) <- fitArgs l
    return (Fit_view vn fa (tokPos s `appRange` ps))
  <|> do
    sp <- aSpec l
    (symbit, ps) <- option ([], nullRange) $ do
        s <- asKey fitS
        (m, qs) <- parseMapping l
        return (m, catRange $ s : qs)
    return (Fit_spec sp symbit ps)


parseCorrespondences :: AParser st [CORRESPONDENCE]
parseCorrespondences = commaSep1 correspondence

correspondence :: AParser st CORRESPONDENCE
correspondence = do
    asKey "*"
    return Default_correspondence
  <|> do
    asKey relationS
    rref <- optionMaybe relationRef
    conf <- optionMaybe confidence
    oBraceT
    cs <- parseCorrespondences
    cBraceT
    return $ Correspondence_block rref conf cs
  <|> do
    (mcid, eRef, mrRef, mconf, toer) <- corr1
    trace (concat ["\t", show mcid, "    \t", show eRef, "\t", show mrRef, "    \t", show mconf, "   \t", show toer]) $ return () -- only commented out for future debugging purposes
    return $ Single_correspondence mcid eRef toer mrRef mconf

corr1 :: AParser st ( Maybe CORRESPONDENCE_ID, ENTITY_REF
                    , Maybe RELATION_REF, Maybe CONFIDENCE, TERM_OR_ENTITY_REF)
corr1 = do
    cid <- try correspondenceIdLookahead
    eRef <- hetIRI
    (mrRef, mconf, toer) <- corr2
    return (Just cid, eRef, mrRef, mconf, toer)
  <|> do
    eRef <- hetIRI
    (mrRef, mconf, toer) <- corr2
    return (Nothing, eRef, mrRef, mconf, toer)

corr2 :: AParser st (Maybe RELATION_REF, Maybe CONFIDENCE, TERM_OR_ENTITY_REF)
corr2 = do
    rRef <- try relationRefLookAhead
    (mconf, toer) <- corr3
    return (Just rRef, mconf, toer)
  <|> do
    (mconf, toer) <- corr3
    return (Nothing, mconf, toer)

corr3 :: AParser st (Maybe CONFIDENCE, TERM_OR_ENTITY_REF)
corr3 = do
    conf <- try confidence
    toer <- termOrEntityRef
    return (Just conf, toer)
  <|> do
    toer <- termOrEntityRef
    return (Nothing, toer)

correspondenceIdLookahead :: AParser st CORRESPONDENCE_ID
correspondenceIdLookahead = do
  cid <- hetIRI
  asKey equalS
  lookAhead (try $ hetIRI >> corr2)
  return cid

relationRefLookAhead :: AParser st RELATION_REF
relationRefLookAhead = do
    r <- relationRef
    lookAhead (confidenceBegin >> return ()) <|> lookAhead (try hetIRI >> return ())
    return r

relationRef :: AParser st RELATION_REF
relationRef = ((do
      asKey ">"
      return Subsumes
    <|> do
      asKey "<"
      return IsSubsumed
    <|> do
      asKey "="
      return Equivalent
    <|> do
      asKey "%"
      return Incompatible
    <|> do
      try $ asKey "$\\ni$"
      return HasInstance
    <|> do
      try $ asKey "$\\in$"
      return InstanceOf
    <|> do
      asKey "$\\mapsto$"
      return DefaultRelation
    ) << skipSmart)
  <|> do
    i <- hetIRI
    return $ Iri i

confidenceBegin :: AParser st Char
confidenceBegin = char '('

termOrEntityRef :: AParser st TERM_OR_ENTITY_REF
termOrEntityRef = do
    i <- hetIRI
    return $ Entity_ref i
  <|> term

-- TODO: implement
term :: AParser st a
term = fail "term parser not implemented yet"

confidence :: AParser st Double
confidence = char '(' >> confidenceNumber << char ')' << skipSmart

confidenceNumber :: AParser st Double
confidenceNumber = do
    d1 <- char '0'
    d <- (do
          d2 <- char '.'
          ds <- many digit
          return $ read $ d1 : d2 : ds
        <|>
          return 0
      )
    return d
  <|> do
    char '1'
    (do
          char '.'
          many $ char '0'
          return 1
        <|>
          return 1
      )
