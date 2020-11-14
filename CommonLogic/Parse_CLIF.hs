{- |
Module      :  ./CommonLogic/Parse_CLIF.hs
Description :  Parser of common logic interchange format
Copyright   :  (c) Karl Luc, DFKI Bremen 2010, Eugen Kuksa and Uni Bremen 2011
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  eugenk@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Parser of common logic interchange format
-}

-- Ref. Common Logic ISO/IEC IS 24707:2007(E)

module CommonLogic.Parse_CLIF where

import qualified Common.AnnoState as AnnoState
import qualified Common.AS_Annotation as Annotation
import CommonLogic.AS_CommonLogic as AS
import Common.Id as Id
import Common.IRI
import Common.Lexer as Lexer hiding (oParenT, cParenT, pToken, parens)
import Common.Keywords (colonS, mapsTo)
import Common.GlobalAnnotations (PrefixMap)
import Common.Parsec
import Common.Token

import Data.Either (lefts, rights)
import qualified Data.HashSet as Set
import qualified Data.HashMap.Strict as Map
import qualified CommonLogic.Tools as Tools

import CommonLogic.Lexer_CLIF

import Text.ParserCombinators.Parsec as Parsec
import Control.Monad (liftM)

-- | parser for getText
cltext :: PrefixMap -> CharParser st TEXT_META
cltext pm = many white >> (do
    try $ oParenT >> clTextKey
    (nt, prfxs) <- namedtext
    cParenT
    return $ tm nt prfxs
  <|> do
    (t, prfxs) <- text <?> "text"
    return $ tm t prfxs
  )
  where tm :: TEXT -> [PrefixMapping] -> TEXT_META
        tm t prfxs = emptyTextMeta { AS.getText = t
                                   , prefix_map = Map.toList pm ++ prfxs
                                   }

namedtext :: CharParser st (TEXT, [PrefixMapping])
namedtext = do
    n <- identifier <?> "name after \"cl-text\""
    (t, prfxs) <- option (Text [] nullRange, []) text
    return (Named_text n t nullRange, prfxs)

text :: CharParser st (TEXT, [PrefixMapping])
text = do
    phrPrfxs <- many1 phrase
    let (phr, prfxs) = unzip phrPrfxs
    return (Text (concat phr) nullRange, concat prfxs)

{- remove the try
keys set here to prevent try in more complex parser to get the right
error message in ex. the following text -}
phrase :: CharParser st ([PHRASE], [PrefixMapping])
phrase = many white >> (do
    try (oParenT >> clModuleKey)
    (m, prfxs) <- pModule
    cParenT
    return ([Module m], prfxs)
  <|> do
    try (oParenT >> clImportsKey)
    i <- importation
    cParenT
    return ([Importation i], [])
  <|> do
    try (oParenT >> clCommentKey)
    c <- (quotedstring <|> enclosedname) <?> "comment after \"cl-comment\""
    (t, prfxs) <- comment_txt <?> "text after \"cl-comment <comment>\""
    cParenT
    return ([Comment_text (Comment c nullRange) t nullRange], prfxs)
  <|> do
    try (oParenT >> clPrefixKey)
    pm <- prefix
    cParenT
    return ([], pm)
  <|> do
    s <- sentence <?> "sentence"
    return ([Sentence s], [])
  )

prefix :: CharParser st [PrefixMapping]
prefix = do
  p <- do
      string colonS
      return colonS
    <|> do
      x <- ncname
      string colonS
      return $ x ++ colonS
  many white
  i <- iriCurie
  many white
  return [(p, i)]

comment_txt :: CharParser st (TEXT, [PrefixMapping])
comment_txt = try text <|> return (Text [] nullRange, [])

-- | parser for module
pModule :: CharParser st (MODULE, [PrefixMapping])
pModule = do
    t <- identifier <?> "module name after \"cl-module\""
    (exs, (txt, prfxs)) <- pModExcl <?> "text in module"
    case exs of
         [] -> return (Mod t txt nullRange, prfxs)
         _ -> return (Mod_ex t exs txt nullRange, prfxs)

-- | parser for
pModExcl :: CharParser st ([NAME], (TEXT, [PrefixMapping]))
pModExcl = many white >> (do
    try (oParenT >> clExcludesKey)
    exs <- many identifier <?> "only names in module-exclusion list"
    cParenT
    tp <- text
    return (exs, tp)
  <|> do
    tp <- text
    return ([], tp)
  )

importation :: CharParser st IMPORTATION
importation = do
     -- clImportsKey
     n <- identifier <?> "importation name after \"cl-imports\""
     return $ Imp_name n

-- | parser for sentences
sentence :: CharParser st SENTENCE
sentence = parens (do
    ck <- try clCommentKey
    c <- (quotedstring <|> enclosedname) <?> "comment after \"cl-comment\""
    s <- sentence <?> "sentence after \"cl-comment <comment>\""
    return $ Comment_sent (Comment c $ Range $ rangeSpan c) s
           $ Range $ joinRanges [rangeSpan ck, rangeSpan c, rangeSpan s]
  <|> do
    t0 <- try rolesetTerm
    nts <- many rolesetNT
    cParenT
    return $ rolesetSentence t0 nts
  <|> do
    at <- atom
    return $ Atom_sent at $ Range $ rangeSpan at
  <|> do
    c <- andKey
    s <- many sentence -- joinRanges with s = []?
    return $ Bool_sent (Junction Conjunction s)
      $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|> do
    c <- orKey
    s <- many sentence
    return $ Bool_sent (Junction Disjunction s)
      $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|> do
    c <- notKey
    s <- sentence <?> "sentence after \"not\""
    return $ Bool_sent (Negation s) $ Range $ joinRanges [rangeSpan c,
               rangeSpan s]
  <|> do
    c <- try iffKey
    s1 <- sentence <?> "sentence after \"iff\""
    s2 <- sentence <?> "second sentence after \"iff\""
    return $ Bool_sent (BinOp Biconditional s1 s2)
      $ Range $ joinRanges [rangeSpan c, rangeSpan s1, rangeSpan s1]
  <|> do
    c <- ifKey
    s1 <- sentence <?> "sentence after \"if\""
    s2 <- sentence <?> "second sentence after \"if\""
    return $ Bool_sent (BinOp Implication s1 s2)
      $ Range $ joinRanges [rangeSpan c, rangeSpan s1, rangeSpan s1]
  <|> do
    c <- forallKey
    quantsent1 True c
  <|> do
    c <- existsKey
    quantsent1 False c
  )

quantsent1 :: Bool -> Token -> CharParser st SENTENCE
quantsent1 t c = do
    g <- identifier <?> "predicate after quantifier"
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
quantsent3 t mg bs ((n, trm) : nts) s rn = -- Quant_sent using syntactic sugar
  let functerm = case n of
       Name nm -> Atom (Funct_term trm [Term_seq $ Name_term nm] nullRange) []
       SeqMark sqm -> Atom (Funct_term trm [Seq_marks sqm] nullRange) []
  in if t
        then Quant_sent Universal [n] (quantsent3 t mg bs nts (
                  Bool_sent (BinOp Implication (Atom_sent functerm rn) s) rn
                ) rn) rn
        else Quant_sent Universal [n] (quantsent3 t mg bs nts (
                  Bool_sent (Junction Conjunction [Atom_sent functerm rn, s]) rn
                ) rn) rn
quantsent3 t mg bs [] s rn =
  let quantType = if t then Universal else Existential
  in case mg of
    Nothing -> Quant_sent quantType bs s rn -- normal Quant_sent
    Just g ->                                -- Quant_sent using syntactic sugar
      let functerm = Atom (Funct_term (Name_term g) (map (Term_seq . Name_term)
                      $ Set.toList $ Tools.indvC_sen s) nullRange) []
      in if t
          then Quant_sent Universal bs (Bool_sent (BinOp Implication
              (Atom_sent functerm nullRange) s) rn) rn
          else
            Quant_sent Existential bs (Bool_sent (Junction Conjunction
              [Atom_sent functerm nullRange, s]) rn) rn

boundlist :: CharParser st [Either (NAME_OR_SEQMARK, TERM) NAME_OR_SEQMARK]
boundlist = many (do
    nos <- intNameOrSeqMark
    return $ Right nos
  <|> parens (do
    nos <- intNameOrSeqMark
    t <- term
    return $ Left (nos, t)
    )
  )

atom :: CharParser st ATOM
atom = do
    clEqualsKey
    t1 <- term <?> "term after \"=\""
    t2 <- term <?> "second term after \"=\""
    return $ Equation t1 t2
  <|> do
    t <- term <?> "term"
    ts <- many termseq
    return $ Atom t ts

term :: CharParser st TERM
term = do
     t <- identifier
     return $ Name_term t
   <|> term_fun_cmt

term_fun_cmt :: CharParser st TERM
term_fun_cmt = parens (do
    ck <- try clCommentKey
    c <- (quotedstring <|> enclosedname) <?> "comment after \"cl-comment\""
    t <- term <?> "term after \"cl-comment <comment>\""
    return $ Comment_term t (Comment c $ Range $ rangeSpan c)
           $ Range $ joinRanges [rangeSpan ck, rangeSpan c, rangeSpan t]
  <|> do
    c <- try thatKey
    s <- sentence
    return $ That_term s $ Range $ joinRanges [rangeSpan c, rangeSpan s]
  <|> do
    t <- liftM Name_term $ pToken quotedstring
    return $ Funct_term t [] $ Range $ rangeSpan t
  <|> do
    t <- term
    ts <- many termseq
    return $ Funct_term t ts $ Range $ joinRanges [rangeSpan t, rangeSpan ts]
 )

termseq :: CharParser st TERM_SEQ
termseq = do
   x <- seqmark
   return $ Seq_marks x
  <|> do
   t <- term
   return $ Term_seq t
  <?> "term or sequence marker in term sequence"

rolesetTerm :: CharParser st TERM
rolesetTerm = do
  t0 <- term
  oParenT
  clRolesetKey
  return t0

rolesetNT :: CharParser st (NAME, TERM)
rolesetNT = parens $ do
  n <- identifier
  t <- term <?> "term"
  return (n, t)

rolesetSentence :: TERM -> [(NAME, TERM)] -> SENTENCE
rolesetSentence t0 nts =
  let x = rolesetFreeName t0 nts
  in Quant_sent Existential [Name x] (Bool_sent (Junction Conjunction $
          rolesetAddToTerm x t0 : map (rolesetMixTerm x) nts
        ) nullRange) $ Range $ rangeSpan t0

rolesetFreeName :: TERM -> [(NAME, TERM)] -> NAME
rolesetFreeName trm nts =
  let usedNames = Set.union (Tools.setUnion_list
                    (\ (n, t) -> Set.union (Tools.indvC_term t)
                                           (Set.singleton n))
                    nts) (Tools.indvC_term trm)
  in fst $ Tools.freeName ("x", 0) usedNames


rolesetAddToTerm :: NAME -> TERM -> SENTENCE
rolesetAddToTerm x trm = Atom_sent (Atom trm [Term_seq $ Name_term x]) nullRange

rolesetMixTerm :: NAME -> (NAME, TERM) -> SENTENCE
rolesetMixTerm x (n, t) =
  Atom_sent (Atom (Name_term n) [Term_seq $ Name_term x, Term_seq t]) nullRange

symbIdentifier :: CharParser st Token
symbIdentifier =
  pToken (reserved (reservedelement ++ casl_reserved_words) scanClSymbol)
  <?> "symbol"

scanClSymbol :: CharParser st String
scanClSymbol = quotedstring <|> enclosedname <|>
 (satisfy (\ c -> clLetters c && notElem c "%{}[],;=")
  <:> many clLetter <?> "words")

intNameOrSeqMark :: CharParser st NAME_OR_SEQMARK
intNameOrSeqMark = do
    s <- seqmark -- fix seqmark parser for one
    return $ SeqMark s
  <|> do
    n <- symbIdentifier
    return $ Name n

-- | Parse a list of comma separated symbols.
symbItems :: GenParser Char st SYMB_ITEMS
symbItems = do
  (is, ps) <- symbs
  return (Symb_items is $ catRange ps)

-- | parse a comma separated list of symbols
symbs :: GenParser Char st ([NAME_OR_SEQMARK], [Token])
symbs = do
       s <- intNameOrSeqMark
       do c <- commaT `followedWith` intNameOrSeqMark
          (is, ps) <- symbs
          return (s : is, c : ps)
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
  many white
  do c <- commaT `followedWith` intNameOrSeqMark
     (is, ps) <- symbMaps
     return (s : is, c : ps)
   <|> return ([s], [])

-- | parsing one symbol or a mapping of one to a second symbol
symbMap :: GenParser Char st SYMB_OR_MAP
symbMap = symbMapS <|> symbMapN

symbMapS :: GenParser Char st SYMB_OR_MAP
symbMapS = do
  s <- seqmark
  do f <- pToken $ toKey mapsTo
     t <- seqmark
     return (Symb_mapS s t $ tokPos f)
   <|> return (Symb $ SeqMark s)

symbMapN :: GenParser Char st SYMB_OR_MAP
symbMapN = do
  s <- symbIdentifier
  do f <- pToken $ toKey mapsTo
     t <- symbIdentifier
     return (Symb_mapN s t $ tokPos f)
   <|> return (Symb $ Name s)


-- | Toplevel parser for basic specs
basicSpec :: PrefixMap -> AnnoState.AParser st BASIC_SPEC
basicSpec pm = parseAxItems pm
  <|> do
    bi <- AnnoState.allAnnoParser $ parseBasicItems pm
    return $ Basic_spec [bi]

{- function to parse different syntaxes
parsing: axiom items with dots, clif sentences, clif text
first getting only the sentences -}
parseBasicItems :: PrefixMap -> AnnoState.AParser st BASIC_ITEMS
parseBasicItems pm = try (parseSentences pm)
              <|> parseClText pm
              -- parseClText

parseSentences :: PrefixMap -> AnnoState.AParser st BASIC_ITEMS
parseSentences pm = do
    xs <- many1 $ aFormula pm
    return $ Axiom_items xs

-- FIX
parseClText :: PrefixMap -> AnnoState.AParser st BASIC_ITEMS
parseClText pm = do
  tx <- cltext pm
  return $ Axiom_items (textToAn [tx])

textToAn :: [TEXT_META] -> [Annotation.Annoted TEXT_META]
textToAn = map Annotation.emptyAnno

-- | parser for Axiom_items
parseAxItems :: PrefixMap -> AnnoState.AParser st BASIC_SPEC
parseAxItems pm = do
       d <- AnnoState.dotT
       (fs, ds) <- AnnoState.allAnnoParser (parseAx pm) `Lexer.separatedBy`
                   AnnoState.dotT
       (_, an) <- AnnoState.optSemi
       let _ = Id.catRange (d : ds)
           ns = init fs ++ [Annotation.appendAnno (last fs) an]
       return $ Basic_spec ns

-- | Toplevel parser for formulae
parseAx :: PrefixMap -> AnnoState.AParser st BASIC_ITEMS
parseAx pm = do
  t <- many $ aFormula pm
  return $ Axiom_items t

-- | Toplevel parser for formulae
aFormula :: PrefixMap -> AnnoState.AParser st (Annotation.Annoted TEXT_META)
aFormula pm = AnnoState.allAnnoParser (cltext pm)
