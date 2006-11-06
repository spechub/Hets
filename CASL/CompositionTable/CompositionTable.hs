{-# OPTIONS -cpp #-}
{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@tzi.de
Stability   :  provisional
Portability :  non-portable(uni-HaXml package)

XML output for composition tables

-}
module CASL.CompositionTable.CompositionTable where

{-
DTD unter http://www.tzi.de/cofi/hets/CompositionTable.dtd

-- hets --spec=RCC8 -o comptable.xml Calculi/Space/RCC8.het
-- writes Calculi/Space/RCC8.comptable.xml

eliminate ops on rhs, resulting in list of base relations
add equations for id
-}

import Text.XML.HaXml.Xml2Haskell
import Text.XML.HaXml.Types
import Text.XML.HaXml.Pretty
import Text.PrettyPrint.HughesPJ (Doc, vcat, render)

{-
Using HaXml it is not very easy to just add a DOCTYPE to the derivated
XmlContent-instances so the following code takes care to create it.
Reading in the created files with standard HaXml-functions is not a problem.
-}

-- Public identifier (suggestion)
publicId::String
publicId = "-//CoFI//DTD CompositionTable 1.1//EN"

-- System URI
systemURI::String
systemURI = "http://www.tzi.de/cofi/hets/CompositionTable.dtd"
-- for testing
--systemURI = "CompositionTable.dtd"

-- The root tag to use (derivated from Table-datatye)
rootTag::String
rootTag = "table"

-- Create DTD without internal entities
table_dtd::DocTypeDecl
table_dtd = DTD rootTag
    (Just (PUBLIC (PubidLiteral publicId) (SystemLiteral systemURI))) []

-- Create a Prolog for XML-Version 1.0 and UTF-8 encoding (or ISO ?)
table_prolog::Prolog
table_prolog = Prolog
    (Just (XMLDecl "1.0absd" (Just (EncodingDecl "UTF-8")) Nothing))
#ifdef HAXML_PACKAGE
    [] (Just table_dtd) []
#else 
    (Just table_dtd)
#endif

-- This function renders a Table-instance into a Doc-instance (pretty printing)
table_document::Table->Doc
table_document t = vcat $ (prolog table_prolog):(map content (toElem t))

-- This function should be used when writing out a Table-instance
-- It adds a DOCTYPE-Element and encoding information to the generated Xml
-- HaXmlS fWriteXml-function would omit this extra-information
writeTable::FilePath->Table->IO ()
writeTable f t = writeFile f $ render $ table_document t

-- Shortcut to 'fReadXml f :: (IO Table)'
readTable::FilePath->(IO Table)
readTable = fReadXml

{-Type decls-}

data Table = Table Table_Attrs Compositiontable Conversetable Models
             deriving (Eq,Show)

data Table_Attrs = Table_Attrs
    { tableName :: String
    , tableIdentity :: String
    , baseRelations :: [Baserel]
    } deriving (Eq, Show)

newtype Compositiontable = Compositiontable [Cmptabentry]
    deriving (Eq, Show)
data Conversetable = Conversetable [Contabentry] |
	Conversetable_Ternary
      	{ inverse, shortcut, homing :: [Contabentry_Ternary] }
    deriving (Eq, Show)
newtype Models = Models [Model]
    deriving (Eq, Show)

data Cmptabentry = Cmptabentry Cmptabentry_Attrs [Baserel]
                   deriving (Eq, Show)

data Cmptabentry_Attrs = Cmptabentry_Attrs
    { cmptabentryArgBaserel1 :: Baserel
    , cmptabentryArgBaserel2 :: Baserel
    } deriving (Eq, Show)

data Contabentry = Contabentry
    { contabentryArgBaseRel :: Baserel
    , contabentryConverseBaseRel :: Baserel
    } deriving (Eq, Show)

data Contabentry_Ternary = Contabentry_Ternary
    { contabentry_TernaryArgBaseRel :: Baserel
    , contabentry_TernaryConverseBaseRels :: [Baserel]
    } deriving (Eq, Show)


data Model = Model
    { modelString1 :: String
    , modelString2 :: String
    } deriving (Eq, Show)

data Baserel = Baserel
    { baserelBaserel :: String
    } deriving (Eq,Ord,Show)

{-Instance decls-}

instance XmlContent Table where
    fromElem (CElem (Elem "table" as c0):rest) =
        (\(a,ca)->
           (\(b,cb)->
              (\(c, _)->
                 (Just (Table (fromAttrs as) a b c), rest))
              (definite fromElem "<models>" "table" cb))
           (definite fromElem "<conversetable>" "table" ca))
        (definite fromElem "<compositiontable>" "table" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Table as a b c) =
        [CElem (Elem "table" (toAttrs as) (toElem a ++ toElem b ++
                                           toElem c))]
instance XmlAttributes Table_Attrs where
    fromAttrs as =
        Table_Attrs
          { tableName = definiteA fromAttrToStr "table" "name" as
          , tableIdentity = definiteA fromAttrToStr "table" "identity" as
          , baseRelations = []
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "name" (tableName v)
        , toAttrFrStr "identity" (tableIdentity v)
        ]

instance XmlContent Compositiontable where
    fromElem (CElem (Elem "compositiontable" [] c0):rest) =
        (\(a, _)->
           (Just (Compositiontable a), rest))
        (many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Compositiontable a) =
        [CElem (Elem "compositiontable" [] (concatMap toElem a))]

instance XmlContent Conversetable where
    fromElem (CElem (Elem "conversetable" [] c0):rest) =
        (\(a, _)->
           (Just (Conversetable a), rest))
        (many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem ct = case ct of
        Conversetable a ->
           [CElem (Elem "conversetable" [] (concatMap toElem a))]
        _ -> []

instance XmlContent Models where
    fromElem (CElem (Elem "models" [] c0):rest) =
        (\(a, _)->
           (Just (Models a), rest))
        (many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Models a) =
        [CElem (Elem "models" [] (concatMap toElem a))]

instance XmlContent Cmptabentry where
    fromElem (CElem (Elem "cmptabentry" as c0):rest) =
        (\(a, _)->
           (Just (Cmptabentry (fromAttrs as) a), rest))
        (many fromElem c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Cmptabentry as a) =
        [CElem (Elem "cmptabentry" (toAttrs as) (concatMap toElem a))]

instance XmlAttributes Cmptabentry_Attrs where
    fromAttrs as =
        Cmptabentry_Attrs
          { cmptabentryArgBaserel1 = Baserel (definiteA fromAttrToStr
				     "cmptabentry" "argBaserel1" as)
          , cmptabentryArgBaserel2 = Baserel (definiteA fromAttrToStr
				     "cmptabentry" "argBaserel2" as)
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "argBaserel1" (baserelBaserel(cmptabentryArgBaserel1 v))
        , toAttrFrStr "argBaserel2" (baserelBaserel(cmptabentryArgBaserel2 v))
        ]

instance XmlContent Contabentry where
    fromElem (CElem (Elem "contabentry" as []):rest) =
        (Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
        [CElem (Elem "contabentry" (toAttrs as) [])]

instance XmlAttributes Contabentry where
    fromAttrs as =
        Contabentry
          { contabentryArgBaseRel = Baserel (definiteA fromAttrToStr
					    "contabentry"
					    "argBaseRel" as)
          , contabentryConverseBaseRel = Baserel (definiteA fromAttrToStr
						 "contabentry"
						 "converseBaseRel" as)
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "argBaseRel" (baserelBaserel(contabentryArgBaseRel v))
        , toAttrFrStr "converseBaseRel" (baserelBaserel
					(contabentryConverseBaseRel v))
        ]

instance XmlContent Model where
    fromElem (CElem (Elem "model" as []):rest) =
        (Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
        [CElem (Elem "model" (toAttrs as) [])]

instance XmlAttributes Model where
    fromAttrs as =
        Model
          { modelString1 = definiteA fromAttrToStr "model" "string1" as
          , modelString2 = definiteA fromAttrToStr "model" "string2" as
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "string1" (modelString1 v)
        , toAttrFrStr "string2" (modelString2 v)
        ]

instance XmlContent Baserel where
    fromElem (CElem (Elem "baserel" as []):rest) =
        (Just (fromAttrs as), rest)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem as =
        [CElem (Elem "baserel" (toAttrs as) [])]

instance XmlAttributes Baserel where
    fromAttrs as =
        Baserel
          { baserelBaserel = definiteA fromAttrToStr "baserel" "baserel" as
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "baserel" (baserelBaserel v)
        ]
