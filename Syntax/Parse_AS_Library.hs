{-| 
   
Module      :  $Header$
Copyright   :  (c) Maciek Makowski, Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

   Parsing the specification library.
-}

{-
   www.cofi.info
   from 25 March 2001

   C.2.4 Specification Libraries

   TODO:
   - architectural specs
   - move structured parsing from libItem to Parse_AS_Structured (?)
-}

module Syntax.Parse_AS_Library where

import Logic.Grothendieck
import Logic.Logic
-- import CASL.Logic_CASL  -- we need the default logic
import Syntax.AS_Structured
-- import Syntax.AS_Architecture
import Syntax.AS_Library
import Syntax.Parse_AS_Structured
import Syntax.Parse_AS_Architecture
import Common.AS_Annotation
import Common.AnnoState
import Common.Id(tokPos)
import Common.Keywords
import Common.Lexer
import Common.Token
import Common.Lib.Parsec
import Common.Lib.Parsec.Char (digit)
-- import qualified Common.Lib.Map as Map
import Common.Id
import Data.List
import Data.Maybe(maybeToList)


------------------------------------------------------------------------
-- * Parsing functions


-- | Parse a library of specifications
library :: (AnyLogic, LogicGraph) -> AParser LIB_DEFN
library l = do s1 <- asKey libraryS -- 'library' keyword
	       ln <- libName        -- library name
               an <- annos          -- annotations 
               ls <- libItems l     -- librart elements
               eof
               return (Lib_defn ln ls [tokPos s1] an)
               
-- | Parse library name
libName :: AParser LIB_NAME
libName = do libid <- libId
             v <- option Nothing (fmap Just version)
             return (case v of
               Nothing -> Lib_id libid
               Just v1 -> Lib_version libid v1)

-- | Parse the library version
version :: AParser VERSION_NUMBER
version = do s <- asKey versionS
             pos <- getPosition
             n <- many1 digit `sepBy1` (string ".")
             skip
             return (Version_number n ([tokPos s, pos]))


-- | Parse library ID
libId :: AParser LIB_ID
libId = do pos <- getPosition
           path <- scanAnyWords `sepBy1` (string "/")
           skip
           return (Indirect_link (concat (intersperse "/" path)) [pos])
           -- ??? URL need to be added

-- | Parse the library elements
libItems :: (AnyLogic, LogicGraph) -> AParser [Annoted LIB_ITEM]
libItems l@(_, lG) = option [] $ do 
    (r, newlog) <- libItem l
    an <- annos 
    is <- libItems (newlog, lG)
    return ((Annoted r [] [] an) : is)


-- | Parse an element of the library
libItem :: (AnyLogic, LogicGraph) -> AParser (LIB_ITEM, AnyLogic)
libItem l@(lgc, lG) = 
     -- spec defn
    do s <- asKey specS 
       n <- simpleId
       g <- generics l
       e <- asKey equalS
       a <- aSpec l
       q <- optEnd
       return (Syntax.AS_Library.Spec_defn n g a 
	       (map tokPos ([s, e] ++ maybeToList q)), lgc)
  <|> -- view defn
    do s1 <- asKey viewS
       vn <- simpleId
       g <- generics l
       s2 <- asKey ":"
       vt <- viewType l
       (symbMap,ps) <- option ([],[]) 
                        (do s <- asKey equalS               
                            (m, _) <- parseMapping l
                            return (m,[s]))          
       q <- optEnd
       return (Syntax.AS_Library.View_defn vn g vt symbMap 
                    (map tokPos ([s1, s2] ++ ps ++ maybeToList q)), lgc)
  <|> -- unit spec
    do kUnit <- asKey unitS
       kSpec <- asKey specS
       name <- simpleId
       kEqu <- asKey equalS
       usp <- unitSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Unit_spec_defn name usp
	           (map tokPos ([kUnit, kSpec, kEqu] ++ maybeToList kEnd)), 
	       lgc)
  <|> -- arch spec
    do kArch <- asKey archS
       kSpec <- asKey specS
       name <- simpleId
       kEqu <- asKey equalS
       asp <- annotedArchSpec l
       kEnd <- optEnd
       return (Syntax.AS_Library.Arch_spec_defn name asp
	           (map tokPos ([kArch, kSpec, kEqu] ++ maybeToList kEnd)), 
	       lgc)
  <|> -- download
    do s1 <- asKey fromS
       ln <- libName
       s2 <- asKey getS
       (il,ps) <- itemNameOrMap `separatedBy` anComma
       q <- optEnd
       return (Download_items ln il 
                (map tokPos ([s1, s2] ++ ps ++ maybeToList q)), lgc)
  <|> -- logic
    do s1 <- asKey logicS
       logN <- logicName
       let Logic_name t _ = logN
       return (Logic_decl logN (map tokPos [s1,t]),
	      lookupLogicName logN lG)

-- | Parse view type
viewType :: (AnyLogic, LogicGraph) -> AParser VIEW_TYPE
viewType l = do sp1 <- annoParser (groupSpec l)
                s <- asKey toS
                sp2 <- annoParser (groupSpec l)
                return (View_type sp1 sp2 [tokPos s])


-- | Parse item name or name map
itemNameOrMap :: AParser ITEM_NAME_OR_MAP
itemNameOrMap = do i1 <- simpleId
                   i' <- option Nothing (do
                      s <- asKey "|->"
                      i <- simpleId
                      return (Just (i,s)))
                   return (case i' of
                      Nothing -> Item_name i1
                      Just (i2,s) -> Item_name_map i1 i2 [tokPos s])

