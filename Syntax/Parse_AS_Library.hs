{- |
Module      :  ./Syntax/Parse_AS_Library.hs
Description :  parser for DOL documents and CASL specification librariess
Copyright   :  (c) Maciek Makowski, Uni Bremen 2002-2016
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Parser for CASL specification libraries
   Follows Sect. II:3.1.5 of the CASL Reference Manual.
Parser for DOL documents
   Follows the DOL OMG standard, clause 9.3
-}

module Syntax.Parse_AS_Library (library) where

import Logic.Grothendieck
import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Parse_AS_Structured
import Syntax.Parse_AS_Architecture

import Common.AS_Annotation
import Common.AnnoParser
import Common.AnnoState
import Common.Id
import Common.IRI

import Common.Keywords
import Common.Lexer
import Common.LibName
import Common.Parsec
import Common.Token

import Text.ParserCombinators.Parsec
import Data.List
import Data.Maybe (maybeToList)
import qualified Data.Map as Map
import Control.Monad

import Framework.AS

import Debug.Trace

lGAnnos :: LogicGraph -> AParser st (LogicGraph, [Annotation])
lGAnnos lG = do
  as <- annos
  let (pfx, _) = partPrefixes as
  return (lG { prefixes = Map.union pfx $ prefixes lG }, as)

-- * Parsing functions

-- | Parse a library of specifications
library :: LogicGraph -> AParser st LIB_DEFN
library lG = do
    (lG1, an1) <- lGAnnos lG
    (ps, ln) <- option (nullRange, iriLibName nullIRI) $ do
      s1 <- asKey libraryS <|> asKey "distributed-ontology"
      n <- libName lG1
      return (tokPos s1, n)
    (lG2, an2) <- lGAnnos lG1
    ls <- libItems lG2
    return (Lib_defn ln ls ps (an1 ++ an2))

-- | Parse library name
libName :: LogicGraph -> AParser st LibName
libName lG = liftM2 mkLibName (hetIRI lG)
  $ if dolOnly lG then return Nothing else optionMaybe version

-- | Parse the library version
version :: AParser st VersionNumber
version = do
    s <- asKey versionS
    pos <- getPos
    n <- sepBy1 (many1 digit) (string dotS)
    skip
    return (VersionNumber n (tokPos s `appRange` Range [pos]))

-- | Parse the library elements
libItems :: LogicGraph -> AParser st [Annoted LIB_ITEM]
libItems l =
     (eof >> return [])
    <|> do
      r <- libItem l
      la <- lineAnnos
      (l', an) <- lGAnnos l
      is <- libItems (case r of
             Logic_decl logD _ ->
                 setLogicName logD l'
             _ -> l')
      case is of
        [] -> return [Annoted r nullRange [] $ la ++ an]
        Annoted i p nl ra : rs ->
          return $ Annoted r nullRange [] la : Annoted i p (an ++ nl) ra : rs

dolImportItem :: LogicGraph -> AParser st LIB_ITEM
dolImportItem l = do
    s1 <- asKey "import"
    iln <- libName l
    return (Download_items iln (ItemMaps []) $ getRange s1)

networkDefn :: LogicGraph -> AParser st LIB_ITEM
networkDefn l = do
    kGraph <- asKey "network"
    name <- hetIRI l
    kEqu <- equalT
    n <- parseNetwork l
    kEnd <- asKey endS
    return . Network_defn name n
         . catRange $ [kGraph, kEqu, kEnd]

emptyParams :: GENERICITY
emptyParams = Genericity (Params []) (Imported []) nullRange

-- CASL spec-defn or DOL OMSDefn
specDefn :: LogicGraph -> AParser st LIB_ITEM
specDefn l = do
    s <- choice $ map asKey
      ["specification", specS, ontologyS, "onto", "model", "OMS"]
    n <- hetIRI l
    g <- generics l
    e <- equalT
    a <- aSpec l True -- OMS, not macros
    q <- optEnd
    trace ("spec:" ++ show (Spec_defn n g a nullRange)) $
     return . Spec_defn n g a
       . catRange $ [s, e] ++ maybeToList q

-- CASL view-defn or DOL IntprDefn
viewDefn :: LogicGraph -> AParser st LIB_ITEM
viewDefn l = do
    s1 <- choice $ map asKey [viewS, interpretationS, refinementS]
    vn <- hetIRI l
    do
       kEqu <- equalT
       rsp <- refSpec l
       kEnd <- optEnd
       return . Ref_spec_defn vn rsp
                   . catRange $ [s1, kEqu] ++ maybeToList kEnd
      <|> do
       g <- generics l
       _ <- annotations -- TODO: store annotations
       s2 <- colonT
       vt <- viewType l
       (symbMap, ps) <- option ([], []) $ do
         s <- equalT
         (m, _) <- parseMapping l
         return (m, [s])
       q <- optEnd
       return . View_defn vn g vt symbMap
         . catRange $ [s1, s2] ++ ps ++ maybeToList q

entailDefn :: LogicGraph -> AParser st LIB_ITEM
entailDefn l = do
  s <- asKey entailmentS
  n <- hetIRI l
  e <- equalT
  et <- entailType l
  q <- optEnd
  return . Entail_defn n et . catRange $ [s, e] ++ maybeToList q

queryDefn :: LogicGraph -> AParser st LIB_ITEM
queryDefn l = do
  q <- asKey "query"
  n <- hetIRI l
  e <- equalT
  s <- asKey selectS
  lg <- lookupCurrentLogic "query-defn" l
  (vs, cs) <- parseItemsList lg
  w <- asKey whereS
  Basic_spec bs _ <- lookupCurrentSyntax "query-defn" l >>= basicSpec l True
  i <- asKey inS
  oms <- aSpec l True
  mt <- optionMaybe $ asKey "along" >> hetIRI l
  o <- optEnd
  return . Query_defn n vs bs oms mt . catRange
    $ [q, e, s, w] ++ cs ++ [i] ++ maybeToList o

substDefn :: LogicGraph -> AParser st LIB_ITEM
substDefn l = do
  q <- asKey "substitution"
  n <- hetIRI l
  c <- colonT
  vt <- viewType l
  e <- equalT
  lg <- lookupCurrentLogic "subst-defn" l
  (m, cs) <- parseItemsMap lg
  o <- optEnd
  return . Subst_defn n vt m . catRange
    $ [q, c, e] ++ cs ++ maybeToList o

resultDefn :: LogicGraph -> AParser st LIB_ITEM
resultDefn l = do
  q <- asKey resultS
  n <- hetIRI l
  (sns, cs) <- separatedBy (hetIRI l) anComma
  f <- asKey forS
  r <- hetIRI l
  a <- annotations
  o <- optEnd
  return . Result_defn n sns r (any (identAnno "complete") a)
    . catRange $ q : cs ++ [f] ++ maybeToList o

-- | Parse an element of the library
libItem :: LogicGraph -> AParser st LIB_ITEM
libItem l = specDefn l
  <|> viewDefn l
  <|> dolImportItem l
  <|> entailDefn l
  <|> queryDefn l
  <|> substDefn l
  <|> resultDefn l
  <|> -- equiv defn
    do s1 <- asKey equivalenceS
       en <- hetIRI l
       s2 <- colonT
       et <- equivType l
       s3 <- equalT
       sp <- fmap MkOms $ aSpec l True
       ep <- optEnd
       return . Equiv_defn en et sp
         . catRange $ s1 : s2 : s3 : maybeToList ep
  <|> -- align defn
    do s1 <- asKey alignmentS
       an <- hetIRI l
       ar <- optionMaybe alignArities
       s2 <- colonT
       at <- viewType l
       (corresps, ps, sem) <- option ([], [], SingleDomain) $ do
         s <- equalT
         cs <- parseCorrespondences l
         aSem <- option SingleDomain $ do
            _ <- asKey "assuming"
            choice $ map (\ d -> asKey (show d) >> return d)
              [minBound .. maxBound]
         return (cs, [s], aSem)
       q <- optEnd
       return . Align_defn an ar at corresps sem
         . catRange $ [s1, s2] ++ ps ++ maybeToList q
  <|> -- module defn
    do s1 <- asKey moduleS
       mn <- hetIRI l
       _ <- annotations -- TODO: store annotations
       s2 <- colonT
       mt <- moduleType l
       s3 <- asKey forS
       rs <- restrictionSignature l
       kEnd <- optEnd
       return . Module_defn mn mt rs
         . catRange $ s1 : s2 : s3 : maybeToList kEnd
  <|> -- unit spec
    do kUnit <- asKey unitS
       kSpec <- asKey specS
       name <- hetIRI l
       kEqu <- equalT
       usp <- unitSpec l
       kEnd <- optEnd
       return (Unit_spec_defn name usp
                (catRange ([kUnit, kSpec, kEqu] ++ maybeToList kEnd)))
  <|> networkDefn l
  <|> -- arch spec
    do kArch <- asKey archS
       kASpec <- asKey specS
       name <- hetIRI l
       kEqu <- equalT
       asp <- annotedArchSpec l
       kEnd <- optEnd
       return (Arch_spec_defn name asp
                (catRange ([kArch, kASpec, kEqu] ++ maybeToList kEnd)))
  <|> -- download
    do s1 <- asKey fromS
       iln <- libName l
       s2 <- asKey getS
       (il, ps) <- downloadItems l
       q <- optEnd
       return (Download_items iln il
                (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- use (to be removed eventually)
    do asKey "use"
       fmap (addDownloadAux False) $ hetIRI l
  <|> -- logic
    do (s, logD) <- qualification l
       return $ Logic_decl logD $ tokPos s
  <|> -- newlogic
    do (n, s1) <- newlogicP
       s2 <- equalT
       (ml, s3) <- metaP
       (s, s4) <- syntaxP
       (m, s5) <- modelsP
       (f, s6) <- foundationP
       (p, s7) <- proofsP
       (pa, s8) <- patternsP
       q <- optEnd
       return (Newlogic_defn (LogicDef n ml s m f p pa)
          (catRange ([s1, s2, s3, s4, s5, s6, s7, s8] ++ maybeToList q)))
   <|> -- newcomorphism
     do (n, s1) <- newcomorphismP
        s2 <- equalT
        (ml, s3) <- metaP
        (s, s4) <- sourceP
        (t, s5) <- targetP
        (sv, s6) <- syntaxP
        (pv, s8) <- proofsP
        (mv, s7) <- modelsP
        q <- optEnd
        return (Newcomorphism_defn (ComorphismDef n ml s t sv pv mv)
           (catRange ([s1, s2, s3, s4, s5, s6, s7, s8] ++ maybeToList q)))
  <|> -- just a spec (turned into "spec spec = sp")
     do p1 <- getPos
        a <- aSpec l True
        p2 <- getPos
        if p1 == p2 then fail "cannot parse spec" else
          return (Spec_defn nullIRI
               (Genericity (Params []) (Imported []) nullRange) a nullRange)
  <|> -- pattern defn
      patternParser l

patternParser :: LogicGraph -> AParser st LIB_ITEM
patternParser l = do 
        s1 <- asKey "pattern"
        n <- hetIRI l
        (pars, ps1) <- macroParams l
        (imp, ps2) <- option ([], nullRange) (imports l)
        s2 <- equalT
        a <- --trace ("parsed equal:" ++ show pars) $ 
             localOrSpec l 
        q <- optEnd
        let pattern = Pattern_defn n pars (Imported imp) a nullRange
        trace ("pattern:" ++ show pattern) $ 
         return .  Pattern_defn n pars (Imported imp) a 
          . catRange $ [s1, s2] ++ maybeToList q

localOrSpec :: LogicGraph -> AParser st LocalOrSpec
localOrSpec l = do
       _s1 <- asKey "let"
       locals <- many1 (patternParser l) -- separatedBy (patternParser l) skip -- this might have problems
       _s2 <- asKey "in"
       a <- aSpec l False
       return $ Local_pattern locals a 
     <|> do
       a <- aSpec l False -- TODO: this makes sure that the bodies are parsed as macros and not as ontologies
       return $ Spec_pattern a

downloadItems :: LogicGraph -> AParser st (DownloadItems, [Token])
downloadItems l = do
    (il, ps) <- separatedBy (itemNameOrMap l) anSemiOrComma
    return (ItemMaps il, ps)
  <|> do
    s <- asKey mapsTo
    i <- hetIRI l
    return (UniqueItem i, [s])

entailType :: LogicGraph -> AParser st ENTAIL_TYPE
entailType l = do
    sp1 <- omsOrNetwork l
    do
        r <- asKey entailsS
        sp2 <- omsOrNetwork l
        return $ Entail_type sp1 sp2 $ tokPos r
      <|> case sp1 of
            MkOms (Annoted (Spec_inst n [] Nothing _) _ _ _) -> do
              i <- asKey inS
              nw <- parseNetwork l
              r <- asKey entailsS
              g <- groupSpec l True
              return . OMSInNetwork n nw g $ catRange [i, r]
            _ -> fail "OMSName expected"

omsOrNetwork :: LogicGraph -> AParser st OmsOrNetwork
omsOrNetwork l = fmap (MkOms . emptyAnno) $ groupSpec l True -- no macros in networks

equivType :: LogicGraph -> AParser st EQUIV_TYPE
equivType l = do
    sp1 <- omsOrNetwork l
    r <- equiT
    sp2 <- omsOrNetwork l
    return $ Equiv_type sp1 sp2 $ tokPos r

alignArities :: AParser st ALIGN_ARITIES
alignArities = do
  asKey alignArityForwardS
  f <- alignArity
  asKey alignArityBackwardS
  b <- alignArity
  return $ Align_arities f b

alignArity :: AParser st ALIGN_ARITY
alignArity = choice $ map (\ a -> asKey (showAlignArity a) >> return a)
  [minBound .. maxBound]

-- | Parse view type also used in alignments
viewType :: LogicGraph -> AParser st VIEW_TYPE
viewType l = do
    sp1 <- annoParser (groupSpec l True)
    s <- asKey toS
    sp2 <- annoParser (groupSpec l True)
    return $ View_type sp1 sp2 $ tokPos s

moduleType :: LogicGraph -> AParser st MODULE_TYPE
moduleType l = do
  sp1 <- aSpec l True
  s <- asKey ofS
  sp2 <- aSpec l True
  return $ Module_type sp1 sp2 (tokPos s)

restrictionSignature :: LogicGraph -> AParser st G_symb_items_list
restrictionSignature lG = do
  l <- lookupCurrentLogic "restrictionSignature" lG
  fmap fst $ parseItemsList l


simpleIdOrDDottedId :: GenParser Char st Token
simpleIdOrDDottedId = pToken $ liftM2 (++)
  (reserved casl_structured_reserved_words scanAnyWords)
  $ optionL $ try $ string ".." <++> scanAnyWords

-- | Parse item name or name map
itemNameOrMap :: LogicGraph -> AParser st ItemNameMap
itemNameOrMap l = do
    i1 <- liftM simpleIdToIRI simpleIdOrDDottedId <|> hetIRI l
    i2 <- optionMaybe $ do
        _ <- asKey mapsTo
        if isInfixOf ".." $ iriToStringUnsecure i1
            then liftM simpleIdToIRI simpleIdOrDDottedId
            else hetIRI l
    return $ ItemNameMap i1 i2

optEnd :: AParser st (Maybe Token)
optEnd = try
    (addAnnos >> optionMaybe (pToken $ keyWord $ string endS))
    << addLineAnnos

generics :: LogicGraph -> AParser st GENERICITY
generics l = do
    (pa, ps1) <- params l
    (imp, ps2) <- option ([], nullRange) (imports l)
    return $ Genericity (Params pa) (Imported imp) $ appRange ps1 ps2

params :: LogicGraph -> AParser st ([Annoted SPEC], Range)
params l = do
    pas <- many (param l)
    let (pas1, ps) = unzip pas
    return (pas1, concatMapRange id ps)

param :: LogicGraph -> AParser st (Annoted SPEC, Range)
param l = do
    b <- oBracketT
    pa <- aSpec l True 
    -- macros not allowed in params of CASL generic specs
    c <- cBracketT
    return (pa, toRange b [] c)

macroParams :: LogicGraph -> AParser st ([PatternParam], Range)
macroParams l = do 
  _o <- oBracketT  
  (pars, _ps) <- separatedBy (macroParam l) semiT
  _c <- cBracketT
  return (pars, nullRange) --TODO: get the range right


macroParam :: LogicGraph -> AParser st PatternParam
macroParam l = do
 (elems, _ps) <- separatedBy (elemParser l) doubleColonT
 case elems of
  [(x, isOpt)] -> return $ OntoParam isOpt x
  _ -> return $ ListParam $ OntoListCons $ map fst elems

elemParser :: LogicGraph -> AParser st (Annoted SPEC, Bool)
elemParser lg =  do
  optParam <- option nullTok $ asKey "?"
  a <- aSpec lg True
  return (a, (optParam /= nullTok))
 -- TODO: always True, macros not allowed as parameters 
 -- TODO: for now, but we need to handle the empty list

imports :: LogicGraph -> AParser st ([Annoted SPEC], Range)
imports l = do
    s <- asKey givenS
    (sps, ps) <- separatedBy (annoParser $ groupSpec l True) anComma -- macro not allowed in imports, always True
    return (sps, catRange (s : ps))

newlogicP :: AParser st (IRI, Token)
newlogicP = do
  s <- asKey newlogicS
  n <- simpleId
  return (simpleIdToIRI n, s)

metaP :: AParser st (FRAM, Token)
metaP = do
  s <- asKey metaS
  f <- framP
  return (f, s)

framP :: AParser st FRAM
framP = do
    asKey lfS
    return LF
  <|> do
    asKey isabelleS
    return Isabelle
  <|> do
    asKey maudeS
    return Maude

syntaxP :: AParser st (IRI, Token)
syntaxP = do
  s <- asKey syntaxS
  t <- simpleIdOrDDottedId
  return (simpleIdToIRI t, s)

modelsP :: AParser st (IRI, Token)
modelsP = do
    s <- asKey modelsS
    m <- simpleIdOrDDottedId
    return (simpleIdToIRI m, s)
  <|> return (nullIRI, nullTok)

foundationP :: AParser st (IRI, Token)
foundationP = do
    s <- asKey foundationS
    f <- simpleId
    return (simpleIdToIRI f, s)
  <|> return (nullIRI, nullTok)

proofsP :: AParser st (IRI, Token)
proofsP = do
    s <- asKey proofsS
    p <- simpleIdOrDDottedId
    return (simpleIdToIRI p, s)
  <|> return (nullIRI, nullTok)

patternsP :: AParser st (Token, Token)
patternsP = do
    s <- asKey patternsS
    p <- simpleId
    return (p, s)
  <|> return (nullTok, nullTok)

newcomorphismP :: AParser st (IRI, Token)
newcomorphismP = do
  -- add newcomorphismS = "newcomorphism" in
  s <- asKey newcomorphismS
  n <- simpleId
  return (simpleIdToIRI n, s)

sourceP :: AParser st (IRI, Token)
sourceP = do
  s <- asKey sourceS
  sl <- simpleIdOrDDottedId
  return (simpleIdToIRI sl, s)

targetP :: AParser st (IRI, Token)
targetP = do
  s <- asKey targetS
  tl <- simpleIdOrDDottedId
  return (simpleIdToIRI tl, s)
