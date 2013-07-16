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
    , logicDescr
    , parseMapping
    , parseCorrespondences
    , translationList
    , hetIRI
    ) where

import Logic.Logic
import Logic.Comorphism
import Logic.Grothendieck
import Logic.KnownIris

import Syntax.AS_Structured

import Common.AS_Annotation
import Common.AnnoState
import Common.AnnoParser
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

expandCurieM :: LogicGraph -> IRI -> GenParser Char st IRI
expandCurieM lG i =
  case expandCurie (prefixes lG) i of
    Just ei -> return ei
    Nothing -> if isSimple i
               then return i
               else fail $ "could not expand IRI " ++ show i

expandCurieMConservative :: LogicGraph -> IRI -> GenParser Char st IRI
expandCurieMConservative lG i = if isSimple i then return i
                                else expandCurieM lG i

hetIRI :: LogicGraph -> GenParser Char st IRI
hetIRI lG = try $ do
  i <- iriManchester
  skipSmart
  if iriToStringUnsecure i `elem` casl_reserved_words then
      unexpected $ show i
    else expandCurieM lG i

-- | parse annotations and then still call an annotation parser
annoParser2 :: AParser st (Annoted a) -> AParser st (Annoted a)
annoParser2 =
  liftM2 (\ x (Annoted y pos l r) -> Annoted y pos (x ++ l) r) annos

-- * logic and encoding names

-- within sublogics we allow some further symbol characters
sublogicChars :: AParser st String
sublogicChars = many $ satisfy $ \ c -> notElem c ":./\\" && isSignChar c
    || elem c "_'" || isAlphaNum c

lookupLogicM :: IRI -> AParser st String
lookupLogicM i = if isSimple i
                 then return l
                 else case lookupLogicName l of
                   Just s -> return s
                   Nothing -> fail $ "logic " ++ show i ++ " not found"
  where l = iriToStringUnsecure i
                           
{- keep these identical in order to
decide after seeing ".", ":" or "->" what was meant -}
logicName :: LogicGraph -> AParser st Logic_name
logicName l = do
      i <- iriManchester >>= expandCurieMConservative l
      let (ft, rt) = if isSimple i
                     then break (== '.') $ abbrevPath i -- HetCASL
                     else (abbrevPath i, [])
      (e, ms) <- if null rt then return (i, Nothing)
         else do
           s <- sublogicChars -- try more sublogic characters
           return (i { abbrevPath = ft}, Just . mkSimpleId $ tail rt ++ s)
      skipSmart
      -- an optional spec name for a sublogic based on a theory #171
      mt <- optionMaybe
            $ oParenT >> (iriCurie >>= expandCurieMConservative l) << cParenT
      lo <- lookupLogicM e
      return $ Logic_name lo ms mt

logicDescr :: LogicGraph -> AParser st LogicDescr
logicDescr l = do
  n@(Logic_name ln _ _) <- logicName l
  option (nameToLogicDescr n) $ do
     r <- asKey serializationS
     sp <- sneakAhead iriManchester
     case sp of
       Left _ -> iriManchester >> error "logicDescr" -- reproduce the error
       Right s -> do
         s' <- if isSimple s then return s else expandCurieMConservative l s
         let ld = LogicDescr n (Just s') $ tokPos r
         (Logic lid, sm) <- lookupCurrentSyntax "logicDescr" $ setLogicName ld l
         case basicSpecParser sm lid of
           Just _ -> iriManchester >> return ld -- consume and return
           Nothing -> (unexpected $ "serialization \"" ++ show s
                       ++ "\" for logic " ++ show ln)
                      <|> choice (map (\pn -> pzero <?> '"' : pn ++ "\"")
                                  (filter (not . null)
                                   (basicSpecSyntaxes lid)))

-- * parse Logic_code

parseLogic :: LogicGraph -> AParser st (Logic_code, LogicGraph)
parseLogic lG = do
   lc <- parseLogicAux lG
   case lc of
     Logic_code _ _ (Just l) _ ->
         return (lc, setLogicName (nameToLogicDescr l) lG)
     Logic_code (Just c) _ _ _ -> do
         nLg <- lookupAndSetComorphismName c lG
         return (lc, nLg)
     _ -> return (lc, lG)

parseLogicAux :: LogicGraph -> AParser st Logic_code
parseLogicAux lG =
    do l <- asKey logicS
       do e <- logicName lG
               -- try to parse encoding or logic source after "logic"
          case e of
              Logic_name f Nothing Nothing ->
                      do c <- colonT
                         parseLogAfterColon lG (Just f) [l, c]
                      <|> parseOptLogTarget lG Nothing (Just e) [l]
                      <|> return (Logic_code (Just f) Nothing Nothing
                                  $ tokPos l)
              _ -> parseOptLogTarget lG Nothing (Just e) [l]
         <|> do
           f <- asKey funS  -- parse at least a logic target after "logic"
           t <- logicName lG
           return $ Logic_code Nothing Nothing (Just t)
                                       $ tokPos l `appRange` tokPos f

-- parse optional logic source and target after a colon (given an encoding e)
parseLogAfterColon :: LogicGraph -> Maybe String -> [Token]
                      -> AParser st Logic_code
parseLogAfterColon lG e l =
    do s <- logicName lG
       parseOptLogTarget lG e (Just s) l
         <|> return (Logic_code e (Just s) Nothing $ catRange l)
    <|> parseOptLogTarget lG e Nothing l

-- parse an optional logic target (given encoding e or source s)
parseOptLogTarget :: LogicGraph -> Maybe String -> Maybe Logic_name -> [Token]
                  -> AParser st Logic_code
parseOptLogTarget lG e s l =
    do f <- asKey funS
       let p = catRange $ l ++ [f]
       do t <- logicName lG
          return (Logic_code e s (Just t) p)
        <|> return (Logic_code e s Nothing p)

plainComma :: AParser st Token
plainComma = anComma `notFollowedWith` asKey logicS

-- * parse G_symbol

parseSymbolAux :: AnyLogic -> AParser st G_symbol
parseSymbolAux (Logic lid) = 
   case parse_symbol lid of
    Nothing ->
        fail $ "no symbol parser for language " ++ (language_name lid)
    Just pa -> do s <- pa 
                  return (G_symbol lid s)

parseSymbol :: LogicGraph -> AParser st G_symbol
parseSymbol l = lookupCurrentLogic "symbol" l >>= parseSymbolAux

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
          Approximation Minimization
    l@(Logic lid) <- lookupCurrentLogic "specC" lG
    {- if the current logic has an associated data_logic,
    parse "data SPEC1 SPEC2", where SPEC1 is in the data_logic
    SPEC1 needs to be a basic spec or a grouped spec
    SPEC2 is in the currrent logic -}
    case data_logic lid of
          Nothing -> rest
          Just lD@(Logic dl) -> do
              p1 <- asKey dataS -- not a keyword
              sp1 <- annoParser $ basicSpec lG (lD, Nothing)
                  <|> groupSpec (setCurLogic (language_name dl) lG)
              sp2 <- spD
              return (emptyAnno $ Data lD l sp1 sp2 $ tokPos p1)
            <|> rest

translationList :: LogicGraph -> (Annoted b -> RENAMING -> b)
  -> (Annoted b -> RESTRICTION -> b) -> (Annoted b -> APPROXIMATION -> b) 
  -> (Annoted b -> MINIMIZATION -> b) -> Annoted b -> AParser st (Annoted b)
translationList l ftrans frestr fapprox fminimize sp =
     do sp' <- translation l sp ftrans frestr fapprox fminimize
        translationList l ftrans frestr fapprox fminimize (emptyAnno sp')
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

{- | Parse approximation -}
approximation :: LogicGraph -> AParser st APPROXIMATION
approximation lg =
 do p1 <- asKey approximateS
        -- with
    do p2 <- asKey withS
       n <- hetIRI lg
       return $ (Named_Approx n) $ tokPos p1 `appRange` tokPos p2
{-    <|> -- in with 
    do ...
-}

minimization :: LogicGraph -> AParser st MINIMIZATION
minimization lg =
   do p <- asKey minimizeS
      (cm,_) <- separatedBy (hetIRI lg) spaceT
      do _ <- asKey varsS
         (cv,_) <- separatedBy (hetIRI lg) spaceT
         return $ Mini cm cv $ tokPos p
       <|> (return $ Mini cm [] $ tokPos p)
      



translation :: LogicGraph -> a -> (a -> RENAMING -> b)
            -> (a -> RESTRICTION -> b) -> (a -> APPROXIMATION -> b)
            -> (a -> MINIMIZATION -> b) -> AParser st b
translation l sp ftrans frestr fapprox fminimization =
    do r <- renaming l
       return (ftrans sp r)
    <|>
    do r <- restriction l
       return (frestr sp r)
    <|>
    do r <- approximation l
       return (fapprox sp r)
    <|>
    do r <- minimization l
       return (fminimization sp r)

groupSpecLookhead :: LogicGraph -> AParser st IRI
groupSpecLookhead lG =
  let tok2IRI = liftM simpleIdToIRI in
  tok2IRI oBraceT <|> followedWith (hetIRI lG << annos)
  (choice (map (tok2IRI . asKey) criticalKeywords)
   <|> tok2IRI cBraceT <|> tok2IRI oBracketT <|> tok2IRI cBracketT
   <|> (eof >> return nullIRI))

specD :: LogicGraph -> AParser st SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l = do
    p <- asKey freeS `followedWith` (groupSpecLookhead l)
    sp <- annoParser $ groupSpec l
    return (Free_spec sp $ tokPos p)
  <|> do
    p <- asKey cofreeS `followedWith` (groupSpecLookhead l)
    sp <- annoParser $ groupSpec l
    return (Cofree_spec sp $ tokPos p)
  <|> do
    p <- asKey minimizeS `followedWith` (groupSpecLookhead l)
    sp <- annoParser $ groupSpec l
    return (Minimize_spec sp $ tokPos p)
  <|> do
    p <- asKey closedworldS `followedWith` (groupSpecLookhead l)
    sp <- annoParser $ groupSpec l
    return (Minimize_spec sp $ tokPos p)
  <|> do
    p <- asKey closedS `followedWith` (groupSpecLookhead l)
    sp <- annoParser $ groupSpec l
    return (Closed_spec sp $ tokPos p)
  <|> specE l

specE :: LogicGraph -> AParser st SPEC
specE l = logicSpec l
      <|> combineSpec l
      <|> (lookAhead (groupSpecLookhead l) >> groupSpec l)
      <|> (lookupCurrentSyntax "basic spec" l >>= basicSpec l)

-- | call a logic specific parser if it exists
callParser :: Maybe (AParser st a) -> String -> String -> AParser st a
callParser p name itemType =
  fromMaybe (unexpected $ "no " ++ itemType ++ " parser for " ++ name) p

basicSpec :: LogicGraph -> (AnyLogic, Maybe IRI) -> AParser st SPEC
basicSpec lG (Logic lid, sm) = do
    p <- getPos
    bspec <- callParser
             (liftM (\ps -> ps (prefixes lG)) (basicSpecParser sm lid))
             (showSyntax lid sm) "basic specification"
    q <- getPos
    return $ Basic_spec (G_basic_spec lid bspec) $ Range [p, q]

logicSpec :: LogicGraph -> AParser st SPEC
logicSpec lG = do
   s1 <- asKey logicS
   ln <- logicDescr lG
   s2 <- colonT
   sp <- annoParser $ specD $ setLogicName ln lG
   return $ Qualified_spec ln sp $ toRange s1 [] s2

combineSpec :: LogicGraph -> AParser st SPEC
combineSpec lG = do
    s1 <- asKey combineS
    (oir, ps1) <- separatedBy (hetIRI lG) commaT
    (exl, ps) <- option ([], []) $ do
          s2 <- asKey excludingS
          (e, ps2) <- separatedBy (hetIRI lG) commaT
          return (e, s2 : ps2)
    return $ Combination oir exl $ catRange $ s1 : ps1 ++ ps

lookupAndSetComorphismName :: String -> LogicGraph -> AParser st LogicGraph
lookupAndSetComorphismName c lg = do
    Comorphism cid <- lookupComorphism c lg
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
    n <- hetIRI l
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
    vn <- hetIRI l
    (fa, ps) <- fitArgs l
    return (Fit_view vn fa (tokPos s `appRange` ps))
  <|> do
    sp <- aSpec l
    (symbit, ps) <- option ([], nullRange) $ do
        s <- asKey fitS
        (m, qs) <- parseMapping l
        return (m, catRange $ s : qs)
    return (Fit_spec sp symbit ps)


parseCorrespondences :: LogicGraph -> AParser st [CORRESPONDENCE]
parseCorrespondences l = commaSep1 $ correspondence l

correspondence :: LogicGraph -> AParser st CORRESPONDENCE
correspondence l = do
    asKey "*"
    return Default_correspondence
  <|> do
    asKey relationS
    rref <- optionMaybe $ relationRef l
    conf <- optionMaybe confidence
    oBraceT
    cs <- parseCorrespondences l
    cBraceT
    return $ Correspondence_block rref conf cs
  <|> do
    (mcid, eRef, mrRef, mconf, toer) <- corr1 l
    {- trace (concat ["\t", show mcid, "    \t", show eRef, "\t", show mrRef,
       "    \t", show mconf, "   \t", show toer]) $ return ()
    only commented out for future debugging purposes -}
    return $ Single_correspondence mcid eRef toer mrRef mconf

corr1 :: LogicGraph
      -> AParser st ( Maybe CORRESPONDENCE_ID, G_symbol
                    , Maybe RELATION_REF, Maybe CONFIDENCE, G_symbol)
corr1 l = do
    eRef <- parseSymbol l
    (mrRef, mconf, toer) <- corr2 l
    cids <- annotations
    if not (null cids || null (tail cids))
      then fail "more than one correspondence id"
      else return (listToMaybe cids, eRef, mrRef, mconf, toer)

corr2 :: LogicGraph
      -> AParser st (Maybe RELATION_REF, Maybe CONFIDENCE, G_symbol)
corr2 l = do
    rRef <- try $ relationRefWithLookAhead l
    (mconf, toer) <- corr3 l
    return (Just rRef, mconf, toer)
  <|> do
    (mconf, toer) <- corr3 l
    return (Nothing, mconf, toer)

corr3 :: LogicGraph -> AParser st (Maybe CONFIDENCE,G_symbol)
corr3 l = do
    conf <- try confidence
    sym <- parseSymbol l
    return (Just conf, sym)
  <|> do
    sym <- parseSymbol l
    return (Nothing, sym)

relationRefWithLookAhead :: LogicGraph -> AParser st RELATION_REF
relationRefWithLookAhead lG = do
    r <- relationRef lG
    lookAhead (confidenceBegin >> return nullIRI)
      <|> lookAhead (try $ hetIRI lG)
    return r

relationRef :: LogicGraph -> AParser st RELATION_REF
relationRef lG = ((do
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
    i <- hetIRI lG
    return $ Iri i

confidenceBegin :: AParser st Char
confidenceBegin = char '('

confidence :: AParser st Double
confidence = char '(' >> confidenceNumber << char ')' << skipSmart

confidenceNumber :: AParser st Double
confidenceNumber = do
    d1 <- char '0'
    option 0 $ do
          d2 <- char '.'
          ds <- many digit
          return $ read $ d1 : d2 : ds
  <|> do
    char '1'
    option 1 $ do
          char '.'
          many $ char '0'
          return 1
