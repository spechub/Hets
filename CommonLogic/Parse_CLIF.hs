{- |
Module      :  $Header$
Description :  Parser of common logic interchange format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interchange format
-}

{-
  Ref. Common Logic ISO/IEC IS 24707:2007(E)
-}

module CommonLogic.Parse_CLIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic
import Common.Id as Id
import Common.Lexer as Lexer
import Common.Keywords as Keywords

import Data.Either (lefts, rights)
import qualified Data.Set as Set -- used for parsing roleset
import qualified CommonLogic.Tools as Tools

import CommonLogic.Lexer_CLIF

import Text.ParserCombinators.Parsec as Parsec

-- | parser for cltext
cltext :: CharParser st TEXT
cltext = do
    nt <- try namedtext
    return nt
  <|> do
    t <- text
    return t

namedtext :: CharParser st TEXT
namedtext = parens $ do
    clTextKey
    n <- name
    t <- text
    return $ Named_text n t nullRange
  <|> do
    clTextKey
    n <- name
    return $ Named_text n (Text [] nullRange) nullRange

text :: CharParser st TEXT
text = do
    phr <- many1 phrase --was many1 (not as in standard)
    return $ Text phr nullRange

-- remove the try
-- keys set here to prevent try in more complex parser to get the right
-- error message in ex. the following text
phrase :: CharParser st PHRASE
phrase = do
    try (oParenT >> clModuleKey)
    spaces
    m <- pModule
    spaces
    cParenT
    return $ Module m
  <|> do
    try (oParenT >> clImportsKey)
    spaces
    i <- importation
    spaces
    cParenT
    return $ Importation i
  <|> do
    try (oParenT >> clCommentKey)
    spaces
    c <- quotedstring <|> enclosedname
    spaces
    t <- comment_txt <?> "comment: 3"
    spaces
    cParenT
    return $ Comment_text (Comment c nullRange) t nullRange
  <|> do
    s <- sentence
    return $ Sentence s

comment_txt :: CharParser st TEXT
comment_txt = do
   t <- try text
   return $ t
  <|> do
   return $ Text [] nullRange

-- | parser for module
pModule :: CharParser st MODULE
pModule = do
    t <- identifier
    (exs,txt) <- pModExcl
    case exs of
         [] -> return $ Mod t txt nullRange
         _  -> return $ Mod_ex t exs txt nullRange

-- | parser for
pModExcl :: CharParser st ([NAME], TEXT)
pModExcl = do
    try (oParenT >> clExcludesKey)
    exs <- many identifier
    cParenT
    txt <- text
    return (exs, txt)
  <|> do
    txt <- text
    return ([], txt)

importation :: CharParser st IMPORTATION
importation = do
     -- clImportsKey
     n <- identifier
     return $ Imp_name n

-- | parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens $ do
    ck <- try clCommentKey
    spaces
    c <- quotedstring <|> enclosedname
    spaces
    s <- sentence
    return $ Comment_sent (Comment c $ Range $ rangeSpan c) s
           $ Range $ joinRanges [rangeSpan ck, rangeSpan c, rangeSpan s]
  <|> do
    t0 <- try rolesetTerm
    nts <- many rolesetNT
    cParenT
    return $ rolesetSentence t0 nts
  <|> do
    at <- atom <?> "predicate"
    return $ Atom_sent at $ Range $ rangeSpan at
  <|> do
    c <- andKey
    s <- many sentence -- joinRanges with s = []?
    return $ Bool_sent (Conjunction s) $ Range $ joinRanges [rangeSpan c,
             rangeSpan s]
  <|> do
    c <- orKey
    s <- many sentence
    return $ Bool_sent (Disjunction s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- notKey
    s <- sentence
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- try iffKey -- with try? yes.
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Biconditional s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- ifKey
    s1 <- sentence
    s2 <- sentence
    return $ Bool_sent (Implication s1 s2) $ Range $ joinRanges [rangeSpan c,
                                                   rangeSpan s1, rangeSpan s1]
  <|> do
    c <- forallKey
    quantsent1 True c
  <|> do
    c <- existsKey
    quantsent1 False c

quantsent1 :: Bool -> Token -> CharParser st SENTENCE
quantsent1 t c = do
    g <- identifier -- according to grammar in standard there may be a name
    quantsent2 t c $ Just g -- Quant_sent using syntactic sugar
  <|>
    quantsent2 t c Nothing -- normal Quant_sent

quantsent2 :: Bool -> Token -> Maybe NAME -> CharParser st SENTENCE
quantsent2 t c mg = do
    bl <- parens boundlist
    s <- sentence
    return $ quantsent3 t mg (rights bl) (lefts bl) s
           $ Range $ joinRanges [rangeSpan c, rangeSpan s]

quantsent3 :: Bool -> Maybe NAME -> [NAME_OR_SEQMARK]
                   -> [(NAME_OR_SEQMARK, TERM)] -> SENTENCE -> Range -> SENTENCE
quantsent3 t mg bs ((n,trm):nts) s rn = -- Quant_sent using syntactic sugar
  let functerm = case n of
       Name nm -> Atom (Funct_term trm [Term_seq $ Name_term nm] nullRange) []
       SeqMark sqm -> Atom (Funct_term trm [Seq_marks sqm] nullRange) []
  in case t of
        True -> Quant_sent (Universal [n] $ quantsent3 t mg bs nts (
                  Bool_sent (Implication (Atom_sent functerm rn) s) rn
                ) rn) rn
        False -> Quant_sent (Universal [n] $ quantsent3 t mg bs nts (
                  Bool_sent (Conjunction [Atom_sent functerm rn, s]) rn
                ) rn) rn
quantsent3 t mg bs [] s rn =
  let quantType = if t then Universal else Existential
  in case mg of
    Nothing -> Quant_sent (quantType bs s) rn -- normal Quant_sent
    Just g ->                                -- Quant_sent using syntactic sugar
      let functerm = Atom (Funct_term (Name_term g) (map (Term_seq . Name_term)
                      $ Set.elems $ Tools.indvC_sen s) nullRange) []
      in case t of
          True  -> -- TODO: check whether indvC_sen is the right function to get free names
            Quant_sent (Universal bs (Bool_sent (Implication
              (Atom_sent functerm nullRange) s) rn)) rn
          False ->
            Quant_sent (Existential bs (Bool_sent (Conjunction
              [Atom_sent functerm nullRange, s]) rn)) rn

boundlist :: CharParser st [Either (NAME_OR_SEQMARK, TERM) NAME_OR_SEQMARK]
boundlist = many $ do
    nos <- intNameOrSeqMark
    return $ Right nos
  <|> do
    oParenT
    nos <- intNameOrSeqMark
    t <- term
    cParenT
    return $ Left $ (nos,t) -- TODO: check what to do with the term @t@

intNameOrSeqMark :: CharParser st NAME_OR_SEQMARK
intNameOrSeqMark = do
    s <- seqmark -- fix seqmark parser for one
    return $ SeqMark s
  <|> do
    n <- identifier
    return $ Name n

atom :: CharParser st ATOM
atom = do
    Lexer.pToken $ string "="
    t1 <- term
    t2 <- term
    return $ Equation t1 t2
  <|> do
    t <- term
    ts <- many termseq
    return $ Atom t ts

term :: CharParser st TERM
term = do
     t <- identifier
     return $ Name_term t
   <|> do
     oParenT
     spaces
     term_fun_cmt

term_fun_cmt :: CharParser st TERM
term_fun_cmt = do
  ck <- try clCommentKey
  spaces
  c <- quotedstring <|> enclosedname
  spaces
  t <- term
  spaces
  cParenT
  return $ Comment_term t (Comment c $ Range $ rangeSpan c)
         $ Range $ joinRanges [rangeSpan ck, rangeSpan c, rangeSpan t]
 <|> do
  t <- term
  ts <- many1 termseq -- many1? yes, because it's a functional term
  cParenT
  return $ Funct_term t ts $ Range $ joinRanges [rangeSpan t, rangeSpan ts]

termseq :: CharParser st TERM_SEQ
termseq = do
  x <- seqmark
  return $ Seq_marks $ x
  <|> do
   t <- term
   return $ Term_seq t

rolesetTerm :: CharParser st TERM
rolesetTerm = do
  t0 <- term
  spaces
  oParenT
  clRolesetKey
  spaces
  return t0

rolesetNT :: CharParser st (NAME, TERM)
rolesetNT = parens $ do
  n <- identifier
  t <- term
  return (n,t)
  
rolesetSentence :: TERM -> [(NAME, TERM)] -> SENTENCE
rolesetSentence t0 nts =
  let x = rolesetFreeName t0 nts
  in  Quant_sent (Existential [Name x] (Bool_sent (Conjunction $
          (rolesetAddToTerm x t0) : map (rolesetMixTerm x) nts
        ) nullRange)) $ Range $ rangeSpan t0

rolesetFreeName :: TERM -> [(NAME, TERM)] -> NAME
rolesetFreeName trm nts =
  let usedNames = Set.union (Tools.setUnion_list
                    (\(n,t) -> Set.union (Tools.indvC_term t) (Set.singleton n))
                    nts) (Tools.indvC_term trm)
  in fst $ Tools.freeName ("x", 0) usedNames
  

rolesetAddToTerm :: NAME -> TERM -> SENTENCE
rolesetAddToTerm x trm = Atom_sent (Atom trm [Term_seq $ Name_term x]) nullRange

rolesetMixTerm :: NAME -> (NAME, TERM) -> SENTENCE
rolesetMixTerm  x (n, t) =
  Atom_sent (Atom (Name_term n) [Term_seq $ Name_term x, Term_seq t]) nullRange

-- | Toplevel parser for basic specs
basicSpec :: AnnoState.AParser st BASIC_SPEC
basicSpec = do
    bi <- parseAxItems
    return $ bi
  <|> do
    bi <- AnnoState.allAnnoParser parseBasicItems
    return $ Basic_spec $ [bi]
--  <|> (Lexer.oBraceT >> Lexer.cBraceT >> return (Basic_spec []))

-- function to parse different syntaxes
-- parsing: axiom items with dots, clif sentences, clif text
-- first getting only the sentences
parseBasicItems :: AnnoState.AParser st BASIC_ITEMS
parseBasicItems = try parseSentences
              <|> parseClText
              -- parseClText

parseSentences :: AnnoState.AParser st BASIC_ITEMS
parseSentences = do
    xs <- aFormula
    return $ Axiom_items xs

-- FIX
parseClText :: AnnoState.AParser st BASIC_ITEMS
parseClText = do
  tx <- cltext
  return $ Axiom_items (textToAn tx)

textToAn :: TEXT -> Annotation.Annoted TEXT
textToAn x = Annotation.Annoted x nullRange [] []

-- | parser for Axiom_items
parseAxItems :: AnnoState.AParser st BASIC_SPEC
parseAxItems = do
       d <- AnnoState.dotT
       (fs, ds) <- (AnnoState.allAnnoParser parseAx) `Lexer.separatedBy` AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _ = Id.catRange (d : ds)
           ns = init fs ++ [Annotation.appendAnno (last fs) an]
       return $ Basic_spec ns

-- | Toplevel parser for formulae
parseAx :: AnnoState.AParser st (BASIC_ITEMS)
parseAx = do
  t <- aFormula
  return $ Axiom_items t

-- | Toplevel parser for formulae
aFormula :: AnnoState.AParser st (Annotation.Annoted TEXT)
aFormula = do
     AnnoState.allAnnoParser cltext

{- old unfinished function - TODO: remove as soon as the new one works
-- | collect all the names and sequence markers
symbItems :: GenParser Char st NAME
symbItems = do
  return (Token "x" nullRange)
-}

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([NAME_OR_SEQMARK], [Token])
symbs = do
       s <- intNameOrSeqMark
       do   c <- commaT `followedWith` intNameOrSeqMark
            (is, ps) <- symbs
            return (s:is, c:ps)
         <|> return ([s], [])



-- | parse a list of symbol mappings
symbMapItems :: GenParser Char st SYMB_MAP_ITEMS
symbMapItems = do
  (is, ps) <- symbMaps
  return (Symb_map_items is $ catRange ps)

-- | parse a comma separated list of symbol mappings
symbMaps :: GenParser Char st ([SYMB_OR_MAP], [Token])
symbMaps = do
  s <- symbMap
  do  c <- commaT `followedWith` intNameOrSeqMark
      (is, ps) <- symbMaps
      return (s:is, c:ps)
    <|> return ([s], [])

-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = do
    seqMarkMap <- symbMapS
    return seqMarkMap
  <|> do
    nameMap <- symbMapN
    return nameMap

symbMapS :: GenParser Char st SYMB_OR_MAP
symbMapS = do
  s <- seqmark
  do  f <- pToken $ toKey mapsTo
      t <- seqmark
      return (Symb_mapS s t $ tokPos f)
    <|> return (Symb $ SeqMark s)

symbMapN :: GenParser Char st SYMB_OR_MAP
symbMapN = do
  s <- identifier
  do  f <- pToken $ toKey mapsTo
      t <- identifier
      return (Symb_mapN s t $ tokPos f)
    <|> return (Symb $ Name s)
