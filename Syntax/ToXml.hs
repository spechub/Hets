{- |
Module      :  $Header$
Description :  xml output of Hets specification libaries
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml printing of Hets specification libaries
-}

module Syntax.ToXml
    (
      printLibDefnXml
    ) where

import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Print_AS_Structured()

import Common.Id
import Common.LibName
import Common.Result ()
import Common.AS_Annotation
import Common.DocUtils

import Logic.Logic
import Logic.Grothendieck

import Text.XML.Light

import Data.Maybe

-- one can add global annos if necessary
-- | Prints the Library to an xml string
printLibDefnXml :: LIB_DEFN -> String
printLibDefnXml ld = case toXml ld of (Elem e) -> ppTopElement e
                                      c -> ppContent c


-- if necessary replace Content by a custom data type

{- |
  This class defines the interface for writing XML
-}
class XmlPrintable a where
  -- | render instance to an XML Element
  toXml :: a -> Content

{- |
  Use this class if you can render something as an xml element list
-}
class XmlListPrintable a where
  -- | render instance to an xml element list
  toLst :: a -> [Content]

{- |
  Use this class if you can render something as an xml attribute value
-}
class PrintableAsXmlAttr a where
  -- | render instance to an xml attribute value
  toStr :: a -> String

class XmlAttrList a where
  -- | Everything what can be output to an attribute list
  mkAtts :: a -> [Attr]

-- for empty lists use this datatype
data Empty = Empty
instance XmlAttrList Empty where mkAtts _ = []
instance XmlListPrintable Empty where toLst _ = []


instance XmlPrintable LIB_DEFN where
    toXml (Lib_defn n il rg an) =
        mkEl "Lib" ["name", toStr n]
                 $ maybeToList (printAnnotations rg an []) ++ map (toXml . item) il

instance XmlPrintable LIB_ITEM where
    toXml (Spec_defn n g as rg)
        = withRg rg $ mkEl "Spec" ["name", toString n]
          $ toLst g ++ [toXml as]
    toXml (View_defn n g (View_type from to _) mapping rg)
        = withRg rg $ mkEl "View" ["name", toString n]
          $ toLst g ++ [mkPEl "From" [toXml from], mkPEl "To" [toXml to]] ++
            toLst mapping
    toXml (Download_items n mapping rg)
        = withRg rg $ mkEl "Import" ["name", toString n] $ toLst mapping
    toXml (Logic_decl n rg)
        = withRg rg $ mkFEl "Logic" ["name", toStr n]
    toXml x = mkComment $ take 15 (show x)  ++ "- not Supported"

instance XmlPrintable (Annoted SPEC) where
    toXml a@(Annoted s _ _ _) =
        let mkAEl x y z = withAnno a $ mkEl x y z
            mkAPEl x z = withAnno a $ mkPEl x z
        in case s of
             Basic_spec bs rg -> withRg rg $ mkAPEl "Basic" $ toLst bs
             EmptySpec _ -> mkAPEl "Emptyspec" []
             Translation as (Renaming m _) -> mkAPEl "Renaming"
                                              $ toXml as : toLst m
             Reduction as m -> mkAPEl "Restriction"
                               $ toXml as : toLst m
             Union asl rg -> withRg rg $ mkAPEl "Union" $ toLst asl
             Extension asl rg -> withRg rg $ mkAPEl "Extension"
                                 $ toLst asl
             Free_spec as rg -> withRg rg $ mkAPEl "Free" [toXml as]
             Cofree_spec as rg -> withRg rg $ mkAPEl "Cofree" [toXml as]
             Local_spec as ins rg -> withRg rg $ mkAPEl "Local"
                                     [toXml as, toXml ins]
             Closed_spec as rg -> withRg rg $ mkAPEl "Closed" [toXml as]
             Group as rg -> withRg rg $ mkAPEl "Group" [toXml as]
             Spec_inst n fa rg ->
                 withRg rg $ mkAEl "Inst" ["name", toString n] $ toLst fa
             Qualified_spec ln as rg -> withRg rg $ mkAEl "Qualified"
                                        ["logic", toString ln] [toXml as]
             Data _ _ _ _ _ -> mkComment "DATA not supported"

instance XmlPrintable (Annoted FIT_ARG) where
    toXml a@(Annoted farg _ _ _) =
        let mkAEl x y z = withAnno a $ mkEl x y z
            mkAPEl x z = withAnno a $ mkPEl x z
        in case farg of
             Fit_spec as _ rg ->  withRg rg $ mkAPEl "Fitspec" [toXml as]
             Fit_view n fargs rg ->
                 withRg rg $ mkAEl "Fitview" ["name", toString n]
                            $ toLst fargs

instance XmlPrintable Annotation where
    toXml x = mkPEl "Annotation" [toText x]

instance XmlPrintable ITEM_NAME_OR_MAP where
    toXml (Item_name name) = mkFEl "Item" ["name", toString name]
    toXml (Item_name_map name as _)
        = mkFEl "Item" ["name", toString name, "as", toString as]

instance XmlPrintable G_mapping where
    toXml (G_symb_map l) = mkPEl "Mapping" $ toLst l
    toXml (G_logic_translation lc) = mkFEl "Logictranslation" lc

instance XmlPrintable G_hiding where
    toXml (G_symb_list l) = mkPEl "Hiding" $ toLst l
    toXml (G_logic_projection lc) = mkFEl "Logicprojection" lc



instance PrintableAsXmlAttr LIB_NAME where
    toStr l = case l of
                Lib_version i _ -> toString i
                Lib_id i -> toString i

instance PrintableAsXmlAttr Token where toStr = tokStr

instance PrintableAsXmlAttr Logic_name where toStr (Logic_name t _) = toStr t

--instance PrintableAsXmlAttr SIMPLE_ID where toStr = toString


instance XmlPrintable a => XmlListPrintable [a] where
    toLst = map toXml

instance XmlListPrintable G_basic_spec where
    toLst (G_basic_spec lid bs) = map printBasicSpecItem
                                  $ toAnnotedStrings lid bs

instance XmlListPrintable GENERICITY where
    toLst (Genericity (Params pl) (Imported il) _)
        = let f n l = map (mkPEl n . (: []) . toXml) l
          in f "Param" pl ++ f "Given" il

instance XmlListPrintable RESTRICTION where
    toLst (Hidden m _) = toLst m
    toLst (Revealed m _) = toLst m

instance XmlListPrintable G_symb_items_list where
    toLst (G_symb_items_list _ l) = map toText l

instance XmlListPrintable G_symb_map_items_list where
    toLst (G_symb_map_items_list _ l) = map toText l

instance XmlAttrList [String] where
    mkAtts (x:y:l) = (Attr (unqual x) y) : mkAtts l
    mkAtts _ = []

instance XmlAttrList [(String, String)] where
    mkAtts ((x,y):l) = (Attr (unqual x) y) : mkAtts l
    mkAtts _ = []

instance XmlAttrList Logic_code where
    mkAtts (Logic_code enc src trg _)
        = let f n o = fmap ((,) n . toStr) o
          in mkAtts $ catMaybes
                 [f "encoding" enc, f "source" src, f "target" trg]

printBasicSpecItem :: Annoted String -> Content
-- TOCHECK: As the range for these items stems from the Annotation
--          they have empty range for the moment (see printAnnotations)
printBasicSpecItem as@(Annoted s rg _ _)
    = withRg rg $ withAnno as
      $ mkPEl (if notImplied as then "Theoryitem" else "Assertion") [toText s]


printAnnotated :: Annoted a -> Maybe Content
printAnnotated (Annoted _ rg la ra) = printAnnotations rg la ra

printAnnotations :: Range -> [Annotation] -> [Annotation] -> Maybe Content
printAnnotations _ [] [] = Nothing
-- TOCHECK: Annoted-Items have empty range for the moment
printAnnotations rg lan ran
    = Just $ withRg rg $ mkPEl "Annotations"
      $ let f n l = (case l of [] -> []
                               _ -> [printPXmlList n l])
        in f "Left" lan ++ f "Right" ran

-- check if one can remove this by generalizing mkEl such as for attribs
printXmlList :: XmlPrintable a => String -> [String] -> [a] -> Content
printXmlList n attrs l = mkEl n attrs $ toLst l

printPXmlList :: XmlPrintable a => String -> [a] -> Content
printPXmlList n l = printXmlList n [] l


withAnno :: Annoted a -> Content -> Content
withAnno a c@(Elem e) = case printAnnotated a of
                        Just ac -> Elem $ e { elContent = ac : elContent e }
                        _ -> c

withAnno _ _ = error "withAnno only applies to elements"

withRg :: Range -> Content -> Content
withRg rg c@(Elem e) =
    case rangeToAttribs rg of [] -> c
                              as -> Elem $ add_attrs as e
withRg _ _ = error "withRg only applies to elements"

posString :: Pos -> String
posString (SourcePos _ l c) = show l ++ ":" ++ show c

rangeToAttribs :: Range -> [Attr]
rangeToAttribs (Range []) = [Attr (unqual "range") "empty"]
rangeToAttribs (Range l) =
    zipWith (\x y -> Attr (unqual x) (posString y))
             ["rangestart", "rangeend"] [head l, last l]

toString :: Pretty a => a -> String
toString = show . pretty

toText :: Pretty a => a -> Content
toText = mkText . toString

mkComment :: String -> Content
mkComment s = Text $ CData CDataRaw ("<!-- \n" ++ s ++ "\n -->") Nothing

mkText :: String -> Content
mkText s = Text $ CData CDataText s Nothing

-- make element
mkEl :: XmlAttrList a => String -> a -> [Content] -> Content
mkEl n a c = Elem $ node (unqual n) (mkAtts a, c)

-- make final element (no children)
mkFEl :: XmlAttrList a => String -> a -> Content
mkFEl n a = mkEl n a []

-- make pure element (no attributes)
mkPEl :: String -> [Content] -> Content
mkPEl n c = mkEl n Empty c

