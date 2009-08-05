{- |
Module      :  $Header$
Description :  XML output for composition tables of qualitative calculi
Copyright   :  (c) Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  till@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable(HaXml package)

XML output for composition tables
-}

module CASL.CompositionTable.ToXml (table_document) where

{-
DTD see systemURI

-- hets -v2 -n RCC8CompositionTable -o comptable.xml Calculi/Space/RCC8.het

-- writes Calculi/Space/RCC8_RCC8CompositionTable.comptable.xml

eliminate ops on rhs, resulting in list of base relations
add equations for id
-}

import CASL.CompositionTable.CompositionTable
import Text.XML.HaXml.Xml2Haskell
import Text.XML.HaXml.Types
import Text.XML.HaXml.Pretty
import Text.PrettyPrint.HughesPJ (Doc, vcat)

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
systemURI =
  "http://www.informatik.uni-bremen.de/cofi/hets/CompositionTable.dtd"

-- The root tag to use (derivated from Table-datatype)
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
    [] (Just table_dtd) []

-- This function renders a Table-instance into a Doc-instance (pretty printing)
table_document::Table->Doc
table_document t = vcat $ (prolog table_prolog):(map content (toElem t))

instance XmlContent Table where
    fromElem (CElem (Elem "table" as c0):rest) =
        (\(a,ca)->
           (\(b,cb)->
              (\(c, _)->
                 (Just (Table (fromAttrs as) a b (Reflectiontable []) c),
                  rest))
              (definite fromElem "<models>" "table" cb))
           (definite fromElem "<conversetable>" "table" ca))
        (definite fromElem "<compositiontable>" "table" c0)
    fromElem (CMisc _:rest) = fromElem rest
    fromElem rest = (Nothing, rest)
    toElem (Table as a b (Reflectiontable _) c) =
        [CElem (Elem "table" (toAttrs as) (toElem a ++ toElem b ++
                                           toElem c))]
instance XmlAttributes Table_Attrs where
    fromAttrs as =
        Table_Attrs
          { tableName = definiteA fromAttrToStr "table" "name" as
          , tableIdentity = Baserel $ definiteA fromAttrToStr "table"
                            "identity" as
          , baseRelations = []
          }
    toAttrs v = catMaybes
        [ toAttrFrStr "name" (tableName v)
        , toAttrFrStr "identity" (baserelBaserel (tableIdentity v))
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
