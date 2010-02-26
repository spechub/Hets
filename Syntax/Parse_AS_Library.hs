{- |
Module      :  $Header$
Description :  parser for CASL specification librariess
Copyright   :  (c) Maciek Makowski, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Parser for CASL specification librariess
   Follows Sect. II:3.1.5 of the CASL Reference Manual.
-}

module Syntax.Parse_AS_Library (library) where

import Logic.Grothendieck (LogicGraph(currentLogic))
import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Parse_AS_Structured
    (logicName, groupSpec, aSpec, parseMapping)
import Syntax.Parse_AS_Architecture
import Common.AS_Annotation
import Common.AnnoState
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Id
import Common.LibName
import Text.ParserCombinators.Parsec
import Data.List (intercalate)
import Data.Maybe (maybeToList)

-- * Parsing functions

-- | Parse a library of specifications
library :: LogicGraph -> AParser st LIB_DEFN
library lG = do
    (ps, ln) <- option (nullRange, emptyLibName "") $ do
      s1 <- asKey libraryS
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
    path <- sepBy1 scanAnyWords (string "/")
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
             Logic_decl (Logic_name logN _) _ ->
                 l { currentLogic = tokStr logN }
             _ -> l
      case is of
        [] -> return [Annoted r nullRange [] $ la ++ an]
        Annoted i p nl ra : rs ->
          return $ Annoted r nullRange [] la : Annoted i p (an ++ nl) ra : rs

-- | Parse an element of the library
libItem :: LogicGraph -> AParser st LIB_ITEM
libItem l =
     -- spec defn
    do s <- asKey specS
       n <- simpleId
       g <- generics l
       e <- equalT
       a <- aSpec l
       q <- optEnd
       return (Syntax.AS_Library.Spec_defn n g a
               (catRange ([s, e] ++ maybeToList q)))
  <|> -- view defn
    do s1 <- asKey viewS
       vn <- simpleId
       g <- generics l
       s2 <- asKey ":"
       vt <- viewType l
       (symbMap,ps) <- option ([],[])
                        (do s <- equalT
                            (m, _) <- parseMapping l
                            return (m,[s]))
       q <- optEnd
       return (Syntax.AS_Library.View_defn vn g vt symbMap
                    (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- unit spec
    do kUnit <- asKey unitS
       kSpec <- asKey specS
       name <- simpleId
       kEqu <- equalT
       usp <- unitSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Unit_spec_defn name usp
                (catRange ([kUnit, kSpec, kEqu] ++ maybeToList kEnd)))
  <|> -- ref spec
    do kRef <- asKey refinementS
       name <- simpleId
       kEqu <- equalT
       rsp <- refSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Ref_spec_defn name rsp
                   (catRange ([kRef, kEqu] ++ maybeToList kEnd)))
  <|> -- arch spec
    do kArch <- asKey archS
       kSpec <- asKey specS
       name <- simpleId
       kEqu <- equalT
       asp <- annotedArchSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Arch_spec_defn name asp
                (catRange ([kArch, kSpec, kEqu] ++ maybeToList kEnd)))
  <|> -- download
    do s1 <- asKey fromS
       iln <- libName
       s2 <- asKey getS
       (il,ps) <- separatedBy itemNameOrMap anComma
       q <- optEnd
       return (Download_items iln il
                (catRange ([s1, s2] ++ ps ++ maybeToList q)))
  <|> -- logic
    do s1 <- asKey logicS
       logN@(Logic_name t _) <- logicName
       return (Logic_decl logN (catRange [s1, t]))
  <|> -- just a spec (turned into "spec spec = sp")
     do p1 <- getPos
        a <- aSpec l
        p2 <- getPos
        if p1 == p2 then fail "cannot parse spec" else
          return (Syntax.AS_Library.Spec_defn (mkSimpleId "")
               (Genericity (Params []) (Imported []) nullRange) a nullRange)

-- | Parse view type
viewType :: LogicGraph -> AParser st VIEW_TYPE
viewType l = do
    sp1 <- annoParser (groupSpec l)
    s <- asKey toS
    sp2 <- annoParser (groupSpec l)
    return (View_type sp1 sp2 $ tokPos s)

-- | Parse item name or name map
itemNameOrMap :: AParser st ITEM_NAME_OR_MAP
itemNameOrMap = do
    i1 <- simpleId
    i' <- optionMaybe $ do
        s <- asKey mapsTo
        i <- simpleId
        return (i, s)
    return $ case i' of
        Nothing -> Item_name i1
        Just (i2, s) -> Item_name_map i1 i2 $ tokPos s

optEnd :: AParser st (Maybe Token)
optEnd = try
    (addAnnos >> optionMaybe (pToken $ keyWord $ string endS))
    << addLineAnnos

generics :: LogicGraph -> AParser st GENERICITY
generics l = do
    (pa, ps1) <- params l
    (imp, ps2) <- option ([], nullRange) (imports l)
    return $ Genericity (Params pa) (Imported imp) $ appRange ps1 ps2

params :: LogicGraph -> AParser st ([Annoted SPEC],Range)
params l = do
    pas <- many (param l)
    let (pas1, ps) = unzip pas
    return (pas1, concatMapRange id ps)

param :: LogicGraph -> AParser st (Annoted SPEC,Range)
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
