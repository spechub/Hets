{- |
Module      :  ./Syntax/Parse_AS_Structured.hs
Description :  parser for DOL OMS and CASL (heterogeneous) structured specifications
Copyright   :  (c) Till Mossakowski, Christian Maeder, Uni Bremen 2002-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Parser for CASL (heterogeneous) structured specifications
   Concerning the homogeneous syntax, this follows Sect II:3.1.3
   of the CASL Reference Manual.
Parser for DOL ontologies, models and specifications and networks.
   Follows the DOL OMG standard, clauses 9.4 and 9.5
-}

module Syntax.Parse_AS_Structured
    ( annoParser2
    , basicSpec
    , caslGroupSpec
    , groupSpec
    , aSpec
    , qualification
    , parseMapping
    , parseCorrespondences
    , parseItemsList
    , parseItemsMap
    , translationList
    , renaming
    , restriction
    , hetIRI
    , parseNetwork
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

import Debug.Trace

expandCurieM :: LogicGraph -> IRI -> GenParser Char st IRI
expandCurieM lG i =
  case expandCurie (prefixes lG) i of
    Just ei -> return ei
    Nothing -> return i

expandCurieMConservative :: LogicGraph -> IRI -> GenParser Char st IRI
expandCurieMConservative lG i = if isSimple i then return i
                                else expandCurieM lG i

hetIriCurie :: GenParser Char st IRI
hetIriCurie = try $ do
  i <- iriCurie
  if iriToStringUnsecure i `elem`
     (casl_reserved_words ++ casl_reserved_fops ++ map (: []) ")(,|;")
    then unexpected $ show i
    else return i

hetIRI :: LogicGraph -> GenParser Char st IRI
hetIRI lG = (hetIriCurie >>= expandCurieM lG) << skipSmart

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
      i <- hetIriCurie >>= expandCurieMConservative l
      let (ft, rt) = if isSimple i
                     then break (== '.') $ show $ iriPath i -- DOL
                     else (show $ iriPath i, [])
      (e, ms) <- if null rt then return (i, Nothing)
         else do
           s <- sublogicChars -- try more sublogic characters
           return (i { iriPath = stringToId ft},
                   Just . mkSimpleId $ tail rt ++ s)
      skipSmart
      -- an optional spec name for a sublogic based on a theory #171
      mt <- optionMaybe
            $ char '(' >> (iriCurie >>= expandCurieMConservative l) << cParenT
      lo <- lookupLogicM e
      return $ Logic_name lo ms mt

qualification :: LogicGraph -> AParser st (Token, LogicDescr)
qualification l =
  pair (asKey logicS) (logicDescr l)
  <|> do
    s <- asKey serializationS <|> asKey "language"
    i <- iriCurie
    skipSmart
    return (s,
      (if tokStr s == serializationS then SyntaxQual else LanguageQual) i)

logicDescr :: LogicGraph -> AParser st LogicDescr
logicDescr l = do
  n@(Logic_name ln _ _) <- logicName l
  option (nameToLogicDescr n) $ do
     r <- asKey serializationS
     sp <- sneakAhead iriCurie
     case sp of
       Left _ -> iriCurie >> error "logicDescr" -- reproduce the error
       Right s -> do
         s' <- if isSimple s then return s else expandCurieMConservative l s
         let ld = LogicDescr n (Just s') $ tokPos r
         (Logic lid, sm) <- lookupCurrentSyntax "logicDescr" $ setLogicName ld l
         case basicSpecParser sm lid of
           Just _ -> iriCurie >> skipSmart >> return ld -- consume and return
           Nothing -> unexpected ("serialization \"" ++ show s
                       ++ "\" for logic " ++ show ln)
                      <|> choice (map (\ pn -> pzero <?> '"' : pn ++ "\"")
                                  (filter (not . null)
                                   (basicSpecSyntaxes lid)))

-- * parse Logic_code

parseLogic :: String -> LogicGraph -> AParser st (Logic_code, LogicGraph)
parseLogic altKw lG = do
   lc <- parseLogicAux altKw lG
   case lc of
     Logic_code _ _ (Just l) _ ->
         return (lc, setLogicName (nameToLogicDescr l) lG)
     Logic_code (Just c) _ _ _ -> do
         nLg <- lookupAndSetComorphismName c lG
         return (lc, nLg)
     _ -> return (lc, lG)

parseLogicAux :: String -> LogicGraph -> AParser st Logic_code
parseLogicAux altKw lG =
    do l <- asKey logicS <|> asKey altKw
       do
           f <- asKey funS  -- parse at least a logic target after "logic"
           t <- logicName lG
           return $ Logic_code Nothing Nothing (Just t)
                                       $ tokPos l `appRange` tokPos f
         <|> do
          e <- logicName lG
               -- try to parse encoding or logic source after "logic"
          case e of
              Logic_name f Nothing Nothing ->
                      do c <- colonT
                         parseLogAfterColon lG (Just f) [l, c]
                      <|> parseOptLogTarget lG Nothing (Just e) [l]
                      <|> return (Logic_code (Just f) Nothing Nothing
                                  $ tokPos l)
              _ -> parseOptLogTarget lG Nothing (Just e) [l]

-- parse optional logic source and target after a colon (given an encoding e)
parseLogAfterColon :: LogicGraph -> Maybe String -> [Token]
                      -> AParser st Logic_code
parseLogAfterColon lG e l = parseOptLogTarget lG e Nothing l
    <|>
    do s <- logicName lG
       parseOptLogTarget lG e (Just s) l
         <|> return (Logic_code e (Just s) Nothing $ catRange l)

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

-- * parse G_mapping

callSymParser :: Bool -> Maybe (AParser st a) -> String -> String ->
                 AParser st ([a], [Token])
callSymParser oneOnly p name itemType = case p of
    Nothing ->
        fail $ "no symbol" ++ itemType ++ " parser for language " ++ name
    Just pa -> if oneOnly then do
        s <- pa
        return ([s], [])
      else separatedBy pa plainComma

parseItemsMap :: AnyLogic -> AParser st (G_symb_map_items_list, [Token])
parseItemsMap (Logic lid) = do
      (cs, ps) <- callSymParser False (parse_symb_map_items lid)
                  (language_name lid) " maps"
      return (G_symb_map_items_list lid cs, ps)


parseMapping :: LogicGraph -> AParser st ([G_mapping], [Token])
parseMapping =
  parseMapOrHide "translation" G_logic_translation G_symb_map parseItemsMap

parseMapOrHide :: String -> (Logic_code -> a) -> (t -> a)
               -> (AnyLogic -> AParser st (t, [Token])) -> LogicGraph
               -> AParser st ([a], [Token])
parseMapOrHide altKw constrLogic constrMap pa lG =
    do (n, nLg) <- parseLogic altKw lG
       do optional anComma
          (gs, ps) <- parseMapOrHide altKw constrLogic constrMap pa nLg
          return (constrLogic n : gs, ps)
        <|> return ([constrLogic n], [])
    <|> do
      l <- lookupCurrentLogic "parseMapOrHide" lG
      (m, ps) <- pa l
      do optional anComma
         (gs, qs) <- parseMapOrHide altKw constrLogic constrMap pa lG
         return (constrMap m : gs, ps ++ qs)
        <|> return ([constrMap m], ps)

-- * parse G_hiding

parseItemsList :: AnyLogic -> AParser st (G_symb_items_list, [Token])
parseItemsList (Logic lid) = do
      (cs, ps) <- callSymParser False (parse_symb_items lid)
                  (language_name lid) ""
      return (G_symb_items_list lid cs, ps)

parseSingleSymb :: AnyLogic -> AParser st (G_symb_items_list, [Token])
parseSingleSymb (Logic lid) = do
      (cs, ps) <- callSymParser True (parseSingleSymbItem lid)
                  (language_name lid) ""
      return (G_symb_items_list lid cs, ps)

parseHiding :: LogicGraph -> AParser st ([G_hiding], [Token])
parseHiding =
  parseMapOrHide "along" G_logic_projection G_symb_list parseItemsList

-- * specs

-- "then" is associative, therefore flatten extensions

flatExts :: [Annoted SPEC] -> [Annoted SPEC]
flatExts = concatMap $ \ as -> case item as of
   Extension sps _ -> sps
   Group sp _ -> case flatExts [sp] of
     [_] -> [as]
     sps -> sps
   _ -> [as]

spec :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
spec l flag = do
  sp1 <- annoParser2 (specThen l flag)
  option sp1 $ do
    k <- asKey "bridge"
    rs <- many (renaming l)
    sp2 <- annoParser2 (specThen l flag)
    return . emptyAnno . Bridge sp1 rs sp2 $ tokPos k

specThen :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
specThen l flag = do
  (sps, ps) <- annoParser2 (specA l flag) `separatedBy` asKey thenS
  return $ case sps of
    [sp] -> sp
    _ -> emptyAnno (Extension (flatExts sps) $ catRange ps)

specA :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
specA l flag = do
  sp <- annoParser2 $ specB l flag
  option sp $ do
    t <- asKey andS <|> asKey intersectS
    (sps, ts) <- annoParser2 (specB l flag) `separatedBy` asKey (tokStr t)
    let cons = case tokStr t of
                 "and" -> Union
                 _ -> Intersection
    return $ emptyAnno (cons (sp : sps) $ catRange (t : ts))

specB :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
specB l flag = do
    p1 <- asKey localS
    sp1 <- aSpec l flag
    p2 <- asKey withinS
    sp2 <- annoParser2 $ specB l flag
    return (emptyAnno $ Local_spec sp1 sp2 $ tokPos p1 `appRange` tokPos p2)
  <|> specC l flag

specC :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
specC lG flag = do
    let spD = annoParser $ specD lG flag
        rest = spD >>= translationList
          [ (`fmap` extraction lG) . Extraction
          , (`fmap` renaming lG) . Translation
          , (`fmap` restriction lG) . Reduction
          , (`fmap` approximation lG) . Approximation
          , (`fmap` filtering lG flag) . Filtering
          , (`fmap` minimization lG) . Minimization]
    l@(Logic lid) <- lookupCurrentLogic "specC" lG
    {- if the current logic has an associated data_logic,
    parse "data SPEC1 SPEC2", where SPEC1 is in the data_logic
    SPEC1 needs to be a basic spec or a grouped spec
    SPEC2 is in the currrent logic -}
    case data_logic lid of
          Nothing -> rest
          Just lD@(Logic dl) -> do
              p1 <- asKey dataS -- not a keyword
              sp1 <- annoParser $ basicSpec lG flag (lD, Nothing)
                  <|> caslGroupSpec (setCurLogic (language_name dl) lG) flag
              sp2 <- spD
              return (emptyAnno $ Data lD l sp1 sp2 $ tokPos p1)
            <|> rest

translationList :: [Annoted b -> AParser st b] -> Annoted b
  -> AParser st (Annoted b)
translationList cs sp =
     do sp' <- choice $ map ($ sp) cs
        translationList cs (emptyAnno sp')
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

-- | Parse approximation
approximation :: LogicGraph -> AParser st APPROXIMATION
approximation lg =
 do p1 <- asKey forgetS <|> asKey keepS
    (hs, _) <- parseHiding lg
    li <- optionMaybe $ asKey keepS >> hetIRI lg
    return $ ForgetOrKeep (tokStr p1 /= keepS) hs li $ tokPos p1

minimization :: LogicGraph -> AParser st MINIMIZATION
minimization lg = do
   p <- minimizeKey <|> asKey freeS <|> asKey cofreeS
   (cm) <- many1 (hetIRI lg)
   (cv, p2) <- option ([], []) $ do
       p3 <- asKey varsS
       ct <- many1 (hetIRI lg)
       return (ct, [p3])
   return . Mini p cm cv . catRange $ p : p2

extraction :: LogicGraph -> AParser st EXTRACTION
extraction lg = do
  p <- asKey extractS <|> asKey removeS
  (is,commas) <- separatedBy (hetIRI lg) commaT
  return . ExtractOrRemove (tokStr p == extractS) is $ catRange (p:commas)

filtering :: LogicGraph -> Bool -> AParser st FILTERING
filtering lg flag = do
  p <- asKey selectS <|> asKey rejectS
  filtering_aux p lg flag

filtering_aux :: Token -> LogicGraph -> Bool -> AParser st FILTERING
filtering_aux p lg flag =
  do 
    s <- lookupCurrentSyntax "filtering" lg
    Basic_spec bs _ <- basicSpec lg flag s
    return . FilterBasicSpec (tokStr p == selectS) bs $ tokPos p
 <|>
  do
    s <- lookupCurrentSyntax "filtering" lg
    (g_symb_items_list,ps) <- parseItemsList (fst s)
    return . FilterSymbolList (tokStr p == selectS) 
               g_symb_items_list $ catRange (p : ps)

groupSpecLookhead :: LogicGraph -> AParser st IRI
groupSpecLookhead lG =
  let tok2IRI = liftM simpleIdToIRI in
  tok2IRI oBraceT <|> followedWith (hetIRI lG << annos)
  (choice (map (tok2IRI . asKey) criticalKeywords)
   <|> tok2IRI cBraceT <|> tok2IRI oBracketT <|> tok2IRI cBracketT
   <|> (eof >> return nullIRI))

minimizeKey :: AParser st Token
minimizeKey = choice $ map asKey [minimizeS, closedworldS, "maximize"]

specD :: LogicGraph -> Bool -> AParser st SPEC
           -- do some lookahead for free spec, to avoid clash with free type
specD l flag = do
    p <- asKey freeS `followedWith` groupSpecLookhead l
    sp <- annoParser $ groupSpec l flag
    return (Free_spec sp $ tokPos p)
  <|> do
    p <- asKey cofreeS `followedWith` groupSpecLookhead l
    sp <- annoParser $ groupSpec l flag
    return (Cofree_spec sp $ tokPos p)
  <|> do
    p <- minimizeKey `followedWith` groupSpecLookhead l
    sp <- annoParser $ groupSpec l flag
    return (Minimize_spec sp $ tokPos p)
  <|> do
    p <- asKey closedS `followedWith` groupSpecLookhead l
    sp <- annoParser $ groupSpec l flag
    return (Closed_spec sp $ tokPos p)
  <|> specE l flag

specE :: LogicGraph -> Bool -> AParser st SPEC
specE l flag = logicSpec l flag
      <|> combineSpec l
      <|> (lookAhead (groupSpecLookhead l) >> groupSpec l flag)
      <|> (lookupCurrentSyntax "basic spec" l >>= basicSpec l flag)

-- | call a logic specific parser if it exists
callParser :: Maybe (AParser st a) -> String -> String -> AParser st a
callParser p name itemType =
  fromMaybe (unexpected $ "no " ++ itemType ++ " parser for " ++ name) p

basicSpec :: LogicGraph -> Bool -> (AnyLogic, Maybe IRI) -> AParser st SPEC
basicSpec lG flag (Logic lid, sm) = do
    p <- getPos
    let whichParser = if flag then basicSpecParser sm lid else macroParser sm lid
    bspec <- callParser
             (liftM (\ ps -> ps (prefixes lG)) whichParser)
             (showSyntax lid sm) "basic specification"
    q <- getPos
    return $ Basic_spec (G_basic_spec lid bspec) $ Range [p, q]

logicSpec :: LogicGraph -> Bool -> AParser st SPEC
logicSpec lG flag = do
   (s1, ln) <- qualification lG
   many $ qualification lG -- ignore multiple qualifications for now
   s2 <- colonT
   sp <- annoParser $ specD (setLogicName ln lG) flag
   return $ Qualified_spec ln sp $ toRange s1 [] s2

combineSpec :: LogicGraph -> AParser st SPEC
combineSpec lG = do
    s1 <- asKey combineS
    n <- parseNetwork lG
    return $ Combination n $ tokPos s1

parseNetwork :: LogicGraph -> AParser st Network
parseNetwork lG = do
    (oir, ps1) <- separatedBy (parseLabeled lG) commaT
    (exl, ps) <- option ([], []) $ do
          s2 <- asKey excludingS
          (e, ps2) <- separatedBy (hetIRI lG) commaT
          return (e, s2 : ps2)
    return $ Network oir exl $ catRange $ ps1 ++ ps

parseLabeled :: LogicGraph -> AParser st LABELED_ONTO_OR_INTPR_REF
parseLabeled lG = do
    x <- option Nothing $ do
        str <- try (simpleId `followedWith` colonT)
        colonT
        return $ Just str
    y <- hetIRI lG
    return $ Labeled x y

lookupAndSetComorphismName :: String -> LogicGraph -> AParser st LogicGraph
lookupAndSetComorphismName c lg = do
    Comorphism cid <- lookupComorphism c lg
    return $ setCurLogic (language_name $ targetLogic cid) lg

aSpec :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
aSpec lg flag = annoParser2 $  spec lg flag

-- | grouped spec or spec-inst without optional DOL import
caslGroupSpec :: LogicGraph -> Bool -> AParser st SPEC
caslGroupSpec = groupSpecAux False

-- | grouped spec or spec-inst with optional import
groupSpec :: LogicGraph -> Bool -> AParser st SPEC
groupSpec  = groupSpecAux True

groupSpecAux :: Bool -> LogicGraph -> Bool -> AParser st SPEC
groupSpecAux withImport l flag = do
    b <- oBraceT
    do
      c <- cBraceT
      return $ EmptySpec $ catRange [b, c]
     <|> do
      a <- aSpec l flag
      addAnnos
      c <- cBraceT
      return $ Group a $ catRange [b, c]
  <|> do
    n <- hetIRI l
    {- (f, ps) <- fitArgs l flag
    mi <- if withImport then optionMaybe (hetIRI l) else return Nothing
    case f of
     [] -> return $ UnsolvedName n nullRange
     _ -> return (Spec_inst n f mi ps)
    -} 
    mf <- optionMaybe (fitArgsPattern l flag withImport) 
    case mf of
     Nothing -> return $ UnsolvedName n nullRange
     Just ((f, mi), ps) -> let inst =  Spec_inst n f mi ps 
                           in -- trace ("inst:" ++ show inst) $ 
                              return inst

fitArgsPattern :: LogicGraph -> Bool -> Bool -> AParser st (([Annoted FIT_ARG], Maybe IRI), Range)
fitArgsPattern l flag withImport = do
  o <- oBracketT
  (fas, _) <- separatedBy (fitArg l flag) semiT 
  let (fas1, _ps) = unzip fas
  c <- cBracketT
  return ((fas1, Nothing), toRange o [] c)

fitArgs :: LogicGraph -> Bool -> AParser st ([Annoted FIT_ARG], Range)
fitArgs l flag = do
  fas <- many (fitArg l flag)
  let (fas1, ps) = unzip fas
  return (fas1, concatMapRange id ps)

fitArg :: LogicGraph -> Bool -> AParser st (Annoted FIT_ARG, Range)
fitArg l flag = do
    let emptyParam = do
          _ <- lookAhead $ try semiT <|> try cBracketT
          return $ Missing_arg nullRange
    fa <- annoParser emptyParam
    trace ("**** just scanned 1: " ++ show fa) $ return (fa, nullRange)
  <|> do
    -- b <- oBracketT
    fa <- annoParser $ fitString l flag
    -- c <- cBracketT
    trace ("**** just scanned 2: " ++ show fa) $  return (fa, nullRange)
  <|> do 
    fa <- annoParser $ fittingArg l flag
    trace ("**** just scanned 3: " ++ show fa) $ return (fa, nullRange)
  <|> do
   s <- scanString
   trace ("**** just scanned 4: " ++ s) $ return (Annoted (Fit_string (mkIRI s) nullRange) nullRange [][], nullRange)
  <|> do
    _b <- oBracketT
    (aspecs, _) <- separatedBy (iParser l flag) commaT
    _c <- cBracketT
    return (Annoted (Fit_spec (Annoted (OntoList aspecs) nullRange [] []) [] nullRange) nullRange [] [], nullRange)

iParser :: LogicGraph -> Bool -> AParser st (Annoted SPEC)
iParser l flag = do
          i <- compoundIriCurie
          _ <- option () skip
          trace ("tks:" ++ show (getTokens $ iriPath i) ++ " cmps:" ++ show (getComps $ iriPath i)) $ return $ Annoted (UnsolvedName i nullRange) nullRange [][]
        <|> aSpec l flag
 
fitString :: LogicGraph -> Bool -> AParser st FIT_ARG
fitString l flag = do
  (s, _) <- separatedBy (iParser l flag) doubleColonT
  case s of
   [] -> error "should be caught by the other case"
   [x] -> return $ Fit_spec x [] nullRange
   _ -> return $ Fit_spec (Annoted (OntoList s) nullRange [][]) [] nullRange --  Fit_list s nullRange

fittingArg :: LogicGraph -> Bool -> AParser st FIT_ARG
fittingArg l flag = do
    s <- asKey viewS
    vn <- hetIRI l
    (fa, ps) <- fitArgs l flag
    return (Fit_view vn fa (tokPos s `appRange` ps))
  <|> do
    sp <- aSpec l flag
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
      -> AParser st ( Maybe Annotation, G_symb_items_list
                    , Maybe RELATION_REF, Maybe CONFIDENCE, G_symb_items_list)
corr1 l = do
    al <- lookupCurrentLogic "correspondence" l
    (eRef, _) <- parseSingleSymb al
    (mrRef, mconf, toer) <- corr2 l
    cids <- annotations
    if not (null cids || null (tail cids))
      then fail "more than one correspondence id"
      else return (listToMaybe cids, eRef, mrRef, mconf, toer)

corr2 :: LogicGraph
      -> AParser st (Maybe RELATION_REF, Maybe CONFIDENCE, G_symb_items_list)
corr2 l = do
    rRef <- optionMaybe . try $ relationRefWithLookAhead l
    (mconf, toer) <- corr3 l
    return (rRef, mconf, toer)

corr3 :: LogicGraph -> AParser st (Maybe CONFIDENCE, G_symb_items_list)
corr3 l = do
    al <- lookupCurrentLogic "corr3" l
    conf <- optionMaybe $ try confidence
    (sym, _) <- parseSingleSymb al
    return (conf, sym)

relationRefWithLookAhead :: LogicGraph -> AParser st RELATION_REF
relationRefWithLookAhead lG = do
    r <- relationRef lG
    lookAhead (confidenceBegin >> return nullIRI)
      <|> lookAhead (try $ hetIRI lG)
    return r

relationRef :: LogicGraph -> AParser st RELATION_REF
relationRef lG = do
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
      try $ asKey "ni"
      return HasInstance
    <|> do
      try $ asKey "in"
      return InstanceOf
     <|> do
      try $ asKey mapsTo
      return DefaultRelation
 <|> do
    i <- hetIRI lG
    return $ Iri i

confidenceBegin :: AParser st Char
confidenceBegin = char '0' <|> char '1'

confidence :: AParser st Double
confidence = confidenceNumber << skipSmart

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
