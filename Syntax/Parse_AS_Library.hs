{- |
Module      :  $Header$
Description :  parser for CASL specification librariess
Copyright   :  (c) Maciek Makowski, Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Parser for CASL specification librariess
   Follows Sect. II:3.1.5 of the CASL Reference Manual.
-}

module Syntax.Parse_AS_Library (library) where

import Logic.Grothendieck (LogicGraph)
import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Parse_AS_Structured
    (logicName, groupSpec, aSpec, parseMapping, parseCorrespondences)
import Syntax.Parse_AS_Architecture

import Common.AS_Annotation
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
import qualified Data.Map as Map (empty)
import Data.Maybe (maybeToList)
import Data.Char
import Control.Monad

import Framework.AS

-- * Parsing functions

-- | Parse a library of specifications
library :: LogicGraph -> AParser st LIB_DEFN
library lG = do
    (ps, ln) <- option (nullRange, emptyLibName "") $ do
      s1 <- asKey libraryS <|> asKey distributedOntologyS
      n <- libName
      return (tokPos s1, n)
    an <- annos
    ls <- libItems lG
    return (Lib_defn ln ls ps an)

-- | Parse library name
libName :: AParser st LibName
libName = do
    libid <- libId
    v <- optionMaybe version
    return $ LibName libid v

-- | Parse the library version
version :: AParser st VersionNumber
version = do
    s <- asKey versionS
    pos <- getPos
    n <- sepBy1 (many1 digit) (string dotS)
    skip
    return (VersionNumber n (tokPos s `appRange` Range [pos]))

-- | Parse library ID
libId :: AParser st LibId
libId = do
      pos <- getPos
      i <- try iriCurie
      return $ IndirectLink (iriToStringUnsecure i) (Range [pos]) "" noTime
  <|> do -- is this case still relevant?
    pos <- getPos
    path <- sepBy1 (many1 $ satisfy $ \ c -> isAlphaNum c || elem c "_-+'")
            (string "/")
    skip
    return $ IndirectLink (intercalate "/" path) (Range [pos])
        "" noTime
    -- ??? URL need to be added

-- | Parse the library elements
libItems :: LogicGraph -> AParser st [Annoted LIB_ITEM]
libItems l =
     (eof >> return [])
    <|> do
      r <- libItem l
      la <- lineAnnos
      an <- annos
      is <- libItems $ case r of
             Logic_decl logN _ _ ->
                 setLogicName logN l
             _ -> l
      case is of
        [] -> return [Annoted r nullRange [] $ la ++ an]
        Annoted i p nl ra : rs ->
          return $ Annoted r nullRange [] la : Annoted i p (an ++ nl) ra : rs

-- | Parse an element of the library
libItem :: LogicGraph -> AParser st LIB_ITEM
libItem l =
     -- spec defn
    do s <- asKey specS <|> asKey ontologyS
       n <- iriCurie
       g <- generics l
       e <- equalT
       a <- aSpec l
       q <- optEnd
       return (Syntax.AS_Library.Spec_defn n g a
               (catRange ([s, e] ++ maybeToList q)))
  <|> -- view defn
    do s1 <- asKey viewS <|> asKey interpretationS
       vn <- liftM simpleIdToIRI simpleId
       g <- generics l
       s2 <- asKey ":"
       vt <- viewType l
       (symbMap, ps) <- option ([], []) $ do
         s <- equalT
         (m, _) <- parseMapping l
         return (m, [s])
       q <- optEnd
       return (Syntax.AS_Library.View_defn vn g vt symbMap
                    (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- align defn
    do s1 <- asKey alignmentS
       an <- iriCurie
       g <- generics l
       s2 <- asKey ":"
       at <- alignType l
       (corresps, ps) <- option ([], []) $ do
         s <- equalT
         cs <- parseCorrespondences
         return (cs, [s])
       q <- optEnd
       return (Syntax.AS_Library.Align_defn an g at corresps
                    (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- unit spec
    do kUnit <- asKey unitS
       kSpec <- asKey specS
       name <- liftM simpleIdToIRI simpleId
       kEqu <- equalT
       usp <- unitSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Unit_spec_defn name usp
                (catRange ([kUnit, kSpec, kEqu] ++ maybeToList kEnd)))
  <|> -- ref spec
    do kRef <- asKey refinementS
       name' <- simpleId
       let name = simpleIdToIRI name'
       kEqu <- equalT
       rsp <- refSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Ref_spec_defn name rsp
                   (catRange ([kRef, kEqu] ++ maybeToList kEnd)))
  <|> -- arch spec
    do kArch <- asKey archS
       kASpec <- asKey specS
       name <- simpleId
       kEqu <- equalT
       asp <- annotedArchSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Arch_spec_defn name asp
                (catRange ([kArch, kASpec, kEqu] ++ maybeToList kEnd)))
  <|> -- download
    do s1 <- asKey fromS
       iln <- libName
       s2 <- asKey getS
       (il, ps) <- downloadItems
       q <- optEnd
       return (Download_items iln il
                (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- logic
    do s <- asKey logicS
       logN@(Logic_name t _ _) <- logicName
       syn <- optionMaybe $ do
            asKey serializationS
            iriCurie
       return $ Logic_decl logN syn $ Range $ concatMap rangeToList
                  [tokPos s, iriPos t]
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
        a <- aSpec l
        p2 <- getPos
        if p1 == p2 then fail "cannot parse spec" else
          return (Syntax.AS_Library.Spec_defn nullIRI
               (Genericity (Params []) (Imported []) nullRange) a nullRange)

downloadItems :: AParser st (DownloadItems, [Token])
downloadItems = do
    (il, ps) <- separatedBy itemNameOrMap anSemiOrComma
    return (ItemMaps il, ps)
  <|> do
    s <- asKey mapsTo
    i <- liftM simpleIdToIRI simpleId
    return (UniqueItem i, [s])


-- | Parse view type
viewType :: LogicGraph -> AParser st VIEW_TYPE
viewType l = do
    (sp1, sp2, r) <- viewOrAlignType l
    return (View_type sp1 sp2 r)

-- | Parse align type
alignType :: LogicGraph -> AParser st ALIGN_TYPE
alignType l = do
    (sp1, sp2, r) <- viewOrAlignType l
    return (Align_type sp1 sp2 r)

viewOrAlignType :: LogicGraph -> AParser st (Annoted SPEC, Annoted SPEC, Range)
viewOrAlignType l = do
    sp1 <- annoParser (groupSpec l)
    s <- asKey toS
    sp2 <- annoParser (groupSpec l)
    return (sp1, sp2, tokPos s)

simpleIdOrDDottedId :: GenParser Char st Token
simpleIdOrDDottedId = pToken $ liftM2 (++)
  (reserved casl_structured_reserved_words scanAnyWords)
  $ optionL $ try $ string ".." <++> scanAnyWords

-- | Parse item name or name map
itemNameOrMap :: AParser st ItemNameMap
itemNameOrMap = do
    i1 <- liftM (expandCurie Map.empty . simpleIdToIRI) simpleIdOrDDottedId
    i2 <- optionMaybe $ liftM simpleIdToIRI $ do
        _ <- asKey mapsTo
        if isInfixOf ".." $ iriToStringUnsecure i1
            then simpleIdOrDDottedId
            else simpleId
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
    pa <- aSpec l
    c <- cBracketT
    return (pa, toRange b [] c)

imports :: LogicGraph -> AParser st ([Annoted SPEC], Range)
imports l = do
    s <- asKey givenS
    (sps, ps) <- separatedBy (annoParser $ groupSpec l) anComma
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
