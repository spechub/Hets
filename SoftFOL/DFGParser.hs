{- |
Module      :  $Header$
Description :  A parser for the SPASS Input Syntax
Copyright   :  (c) C. Immanuel Normann, Heng Jiang, C.Maeder, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

A parser for the SPASS Input Syntax taken from
<http://spass.mpi-sb.mpg.de/download/binaries/spass-input-syntax15.pdf >.
-}

module SoftFOL.DFGParser (parseSPASS) where

import SoftFOL.Sign

import Text.ParserCombinators.Parsec

import Common.AS_Annotation
import Common.Id
import Common.Lexer
import Common.Parsec

import Control.Monad

import Data.Char (isSpace)
import Data.Maybe
import qualified Data.Map as Map

-- * lexical matter

wordChar :: Parser Char
wordChar = alphaNum <|> oneOf "_"

anyWord :: Parser String
anyWord = do
    c <- wordChar
    r <- many wordChar
    whiteSpace
    return $ c : r

reservedList :: [String]
reservedList = ["end_of_list", "sort", "subsort", "predicate"]

identifierS :: Parser String
identifierS = try $ anyWord >>=
    (\ s -> if elem s reservedList then unexpected $ show s else return s)

identifierT :: Parser Token
identifierT = liftM2 (\ p s -> Token s (Range [p])) getPos identifierS

arityT :: Parser Int
arityT = fmap read $ many1 digit <|> try (string "-1" << notFollowedBy digit)

commentLine :: Parser ()
commentLine = char '%' >> manyTill anyChar newline >> return ()

whiteSpace :: Parser ()
whiteSpace = skipMany $ (satisfy isSpace >> return ()) <|> commentLine

symbolT :: String -> Parser String
symbolT = (<< whiteSpace) . tryString

keywordT :: String -> Parser String
keywordT s = try (string s << notFollowedBy wordChar) << whiteSpace

dot :: Parser String
dot = symbolT "."

comma :: Parser String
comma = symbolT ","

commaSep :: Parser a -> Parser [a]
commaSep p = sepBy1 p comma

parens :: Parser a -> Parser a
parens p = symbolT "(" >> p << symbolT ")"

squares :: Parser a -> Parser a
squares p = symbolT "[" >> p << symbolT "]"

parensDot :: Parser a -> Parser a
parensDot p = symbolT "(" >> p << symbolT ")."

squaresDot :: Parser a -> Parser a
squaresDot p = symbolT "[" >> p << symbolT "]."

text :: Parser String
text = fmap (reverse . dropWhile isSpace . reverse) $
    symbolT "{*" >> manyTill anyChar (symbolT "*}")

listOf :: String -> Parser String
listOf = symbolT . ("list_of_" ++)

listOfDot :: String -> Parser String
listOfDot = listOf . (++ ".")

endOfList :: Parser String
endOfList = symbolT "end_of_list."

mapTokensToData :: [(String, a)] -> Parser a
mapTokensToData ls = choice (map tokenToData ls)
    where tokenToData (s,t) = keywordT s >> return t

-- * SPASS Problem
{- |
   This is the main function of the module
-}

parseSPASS :: Parser SPProblem
parseSPASS = whiteSpace >> problem

problem :: Parser SPProblem
problem = do
    symbolT "begin_problem"
    i  <- parensDot identifierS
    dl <- descriptionList
    lp <- logicalPartP
    s  <- settingList
    symbolT "end_problem."
    many anyChar
    eof
    return SPProblem
      { identifier = i
      , description = dl
      , logicalPart = lp
      , settings = s}

-- ** SPASS Descriptions

{- | A description is mandatory for a SPASS problem. It has to specify
  at least a 'name', the name of the 'author', the 'status' (see also
  'SPLogState' below), and a (verbose) description. -}
descriptionList :: Parser SPDescription
descriptionList = do
    listOfDot "descriptions"
    keywordT "name"
    n <- parensDot text
    keywordT "author"
    a <- parensDot text
    v <- optionMaybe (keywordT "version" >> parensDot text)
    l <- optionMaybe (keywordT "logic" >> parensDot text)
    s <- keywordT "status" >> parensDot (mapTokensToData
      [ ("satisfiable", SPStateSatisfiable)
      , ("unsatisfiable", SPStateUnsatisfiable)
      , ("unknown", SPStateUnknown)])
    keywordT "description"
    de <- parensDot text
    da <- optionMaybe (keywordT "date" >> parensDot text)
    endOfList
    return SPDescription
      { name = n
      , author = a
      , version = v
      , logic = l
      , status = s
      , desc = de
      , date = da }

-- ** SPASS Logical Parts

{- |
  A SPASS logical part consists of a symbol list, a declaration list, and a
  set of formula lists. Support for clause lists and proof lists hasn't
  been implemented yet.
-}
logicalPartP :: Parser SPLogicalPart
logicalPartP = do
    sl <- optionMaybe symbolListP
    dl <- optionMaybe declarationListP
    fs <- many formulaList
    cl <- many clauseList
    pl <- many proofList
    return SPLogicalPart
      { symbolList = sl
      , declarationList = dl
      , formulaLists = fs
      , clauseLists = cl
      , proofLists = pl }

-- *** Symbol List

{- |
  SPASS Symbol List
-}
symbolListP :: Parser SPSymbolList
symbolListP = do
    listOfDot "symbols"
    fs <- optionL (signSymFor "functions")
    ps <- optionL (signSymFor "predicates")
    ss <- optionL sortSymFor
    endOfList
    return emptySymbolList
      { functions = fs
      , predicates = ps
      , sorts = ss }

signSymFor :: String -> Parser [SPSignSym]
signSymFor kind = keywordT kind >> squaresDot
    (commaSep $ parens signSym <|> fmap SPSimpleSignSym identifierT)

sortSymFor :: Parser [SPSignSym]
sortSymFor = keywordT "sorts" >> squaresDot
    (commaSep $ fmap SPSimpleSignSym identifierT)

signSym :: Parser SPSignSym
signSym = do
    s <- identifierT
    comma
    a <- arityT
    return SPSignSym {sym = s, arity = a}

functList :: Parser [SPIdentifier]
functList = squaresDot $ commaSep identifierT

-- *** Formula List

{- |
  SPASS Formula List
-}
formulaList :: Parser SPFormulaList
formulaList = do
    listOf "formulae"
    ot <- parensDot $ mapTokensToData
      [ ("axioms", SPOriginAxioms)
      , ("conjectures", SPOriginConjectures)]
    fs <- many $ formula $ case ot of
      SPOriginAxioms -> True
      _ -> False
    endOfList
    return SPFormulaList { originType = ot, formulae = fs }

clauseList :: Parser SPClauseList
clauseList = do
    listOf "clauses"
    (ot, ct) <- parensDot $ do
        ot <- mapTokensToData
          [ ("axioms", SPOriginAxioms)
          , ("conjectures", SPOriginConjectures)]
        comma
        ct <- mapTokensToData [("cnf", SPCNF), ("dnf", SPDNF)]
        return (ot, ct)
    fs <- many $ clause ct $ case ot of
      SPOriginAxioms -> True
      _ -> False
    endOfList
    return SPClauseList
      { coriginType = ot
      , clauseType  = ct
      , clauses = fs }

clause :: SPClauseType -> Bool -> Parser SPClause
clause ct bool = keywordT "clause" >> parensDot (do
    sen  <- clauseFork ct
    cname <- optionL (comma >> identifierS)
    return (makeNamed cname sen) { isAxiom = bool })

clauseFork :: SPClauseType -> Parser NSPClause
clauseFork ct = do
  termWsList1@(TWL ls b) <- termWsList
  do  symbolT "||"
      termWsList2 <- termWsList
      symbolT "->"
      termWsList3 <- termWsList
      return (BriefClause termWsList1 termWsList2 termWsList3)
    <|> case ls of
          [t] | not b -> toNSPClause ct t
          _ -> unexpected "clause term"

toNSPClause :: Monad m => SPClauseType -> SPTerm -> m NSPClause
toNSPClause ct t = case t of
    SPQuantTerm q vl l | q == SPForall && ct == SPCNF
        || q == SPExists && ct == SPDNF -> do
        b <- toClauseBody ct l
        return $ QuanClause vl b
    _ -> do
        b <- toClauseBody ct t
        return $ SimpleClause b

termWsList :: Parser TermWsList
termWsList = do
    twl <- many term
    p <- optionMaybe (symbolT "+")
    return $ TWL twl $ isJust p

formula :: Bool -> Parser (Named SoftFOL.Sign.SPTerm)
formula bool = keywordT "formula" >> parensDot (do
     sen <- term
     fname <- optionL (comma >> identifierS)
     return (makeNamed fname sen) { isAxiom = bool })

declarationListP :: Parser [SPDeclaration]
declarationListP = do
    listOfDot "declarations"
    decl <- many declaration
    endOfList
    return decl

declaration :: Parser SPDeclaration
declaration = do
    keywordT "sort"
    sortName <- identifierT
    maybeFreely <- option False (keywordT "freely" >> return True)
    keywordT "generated by"
    funList <- functList
    return SPGenDecl
      { sortSym = sortName
      , freelyGenerated = maybeFreely
      , funcList = funList }
  <|> do
    keywordT "subsort"
    (s1, s2) <- parensDot $ do
        s1 <- identifierT
        comma
        s2 <- identifierT
        return (s1, s2)
    return SPSubsortDecl { sortSymA = s1, sortSymB = s2 }
  <|> do
    keywordT "predicate"
    (pn, sl) <- parensDot $ do
        pn <- identifierT
        comma
        sl <- commaSep identifierT
        return (pn, sl)
    return SPPredDecl { predSym  = pn, sortSyms = sl }
  <|> do
    t <- term
    dot
    return $ case t of
      SPQuantTerm SPForall tlist tb ->
          SPTermDecl { termDeclTermList = tlist, termDeclTerm = tb }
      _ -> SPSimpleTermDecl t

-- | SPASS Proof List
proofList :: Parser SPProofList
proofList = do
    listOf "proof"
    pa <- optionMaybe $ parensDot $ do
        pt <- optionMaybe getproofType
        assList <- option Map.empty (comma >> assocList)
        return (pt, assList)
    steps <- many proofStep
    endOfList
    return $ case pa of
      Nothing -> SPProofList
        { proofType = Nothing
        , plAssocList = Map.empty
        , step = steps}
      Just (pt, mal) -> SPProofList
        { proofType = pt
        , plAssocList = mal
        , step = steps}

getproofType :: Parser SPIdentifier
getproofType = identifierT

assocList :: Parser SPAssocList
assocList = fmap Map.fromList $ squares $ commaSep
  $ pair getKey $ symbolT ":" >> getValue

getKey :: Parser SPKey
getKey = fmap PKeyTerm term

getValue :: Parser SPValue
getValue = fmap PValTerm term

proofStep :: Parser SPProofStep
proofStep = do
    keywordT "step"
    (ref, res, rule, pl, mal) <- parensDot takeStep
    return SPProofStep
      { reference = ref
      , result = res
      , ruleAppl = rule
      , parentList = pl
      , stepAssocList = mal}
  where takeStep = do
          ref <- getReference
          comma
          res <- getResult
          comma
          rule <- getRuleAppl
          comma
          pl <- getParentList
          mal <- option Map.empty (comma >> assocList)
          return (ref, res, rule, pl, mal)

        getReference = fmap PRefTerm term
        getResult = fmap PResTerm term
        getRuleAppl = do
          t <- term
          let r = PRuleTerm t
          return $ case t of
            SPComplexTerm (SPCustomSymbol ide) [] -> case lookup (tokStr ide)
                $ map ( \ z -> (show z, z))
                [GeR, SpL,
                 SpR, EqF,
                 Rew, Obv,
                 EmS, SoR,
                 EqR, Mpm,
                 SPm, OPm,
                 SHy, OHy,
                 URR, Fac,
                 Spt, Inp,
                 Con, RRE,
                 SSi, ClR,
                 UnC, Ter] of
              Just u -> PRuleUser u
              Nothing -> r
            _ -> r
        getParentList = squares $ commaSep getParent
        getParent = fmap PParTerm term

-- SPASS Settings.
settingList :: Parser [SPSetting]
settingList  = many setting

setting :: Parser SPSetting
setting = do
    listOfDot "general_settings"
    entriesList <- many settingEntry
    endOfList
    return SPGeneralSettings {entries = entriesList}
  <|> do
    listOf "settings"
    slabel <- parensDot getLabel
    symbolT "{*"
    t <- many clauseFormulaRelation
    symbolT "*}"
    endOfList
    return SPSettings {settingName = slabel, settingBody = t}

settingEntry :: Parser SPHypothesis
settingEntry = do
    keywordT "hypothesis"
    slabels <- squaresDot (commaSep identifierT)
    return (SPHypothesis slabels)

getLabel :: Parser SPSettingLabel
getLabel = mapTokensToData $ map ( \ z -> (showSettingLabel z, z))
    [KIV, LEM, OTTER, PROTEIN, SATURATE, ThreeTAP, SETHEO, SPASS]

-- SPASS Clause-Formula Relation

clauseFormulaRelation :: Parser SPSettingBody
clauseFormulaRelation = do
    keywordT "set_ClauseFormulaRelation"
    cfr <- parensDot $ flip sepBy comma $ parens $ do
        i1 <- identifierS
        comma
        i2 <- identifierS
        return $ SPCRBIND i1 i2
    return (SPClauseRelation cfr)
  <|> do
    t' <- identifierS
    al <- parensDot (commaSep identifierS)
    return (SPFlag t' al)

-- *** Terms

{- |
  A SPASS Term.
-}

term :: Parser SPTerm
term = do
    i <- identifierT
    let iStr = tokStr i
    case lookup iStr [("true", SPTrue), ("false", SPFalse)] of
      Just s -> return $ simpTerm s
      Nothing -> do
        let s = spSym i
        option (simpTerm s) $ do
          (ts, as@(a : _)) <- parens $ do
            ts <- optionL (squares (commaSep term) << comma)
            as <- if null ts then commaSep term
                  else fmap (: []) term
            return (ts, as)
          if null ts then if elem iStr [ "forall", "exists", "true", "false"]
              then unexpected $ show iStr else return $ compTerm
               (case lookup iStr $ map ( \ z -> (showSPSymbol z, z))
                         [ SPEqual
                         , SPOr
                         , SPAnd
                         , SPNot
                         , SPImplies
                         , SPImplied
                         , SPEquiv] of
                   Just ks -> ks
                   Nothing -> s) as
            else return SPQuantTerm
              { quantSym = case lookup iStr
                           [("forall", SPForall), ("exists", SPExists)] of
                   Just q -> q
                   Nothing -> SPCustomQuantSym i
              , variableList = ts, qFormula = a }

toClauseBody :: Monad m => SPClauseType -> SPTerm -> m NSPClauseBody
toClauseBody b t = case t of
    SPComplexTerm n ts | b == SPCNF && n == SPOr || b == SPDNF && n == SPAnd ->
      do ls <- mapM toLiteral ts
         return $ NSPClauseBody b ls
    _ -> fail $ "expected " ++ show b ++ "-application"
