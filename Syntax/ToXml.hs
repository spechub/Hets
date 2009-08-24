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
import Common.Item
import Common.LibName
import Common.Result ()
import Common.AS_Annotation
import Common.DocUtils
import Common.GlobalAnnotations

import Logic.Logic
import Logic.Grothendieck

import Text.XML.Light

import Data.Maybe
import Data.List

-- one can add global annos if necessary
-- | Prints the Library to an xml string
printLibDefnXml :: GlobalAnnos -> LIB_DEFN -> String
printLibDefnXml ga ld = case toXml ga ld of
  Elem e -> ppTopElement e
  c -> ppContent c


-- if necessary replace Content by a custom data type

{- |
  This class defines the interface for writing XML
-}
class XmlPrintable a where
  -- | render instance to an XML Element
  toXml :: GlobalAnnos -> a -> Content

{- |
  Use this class if you can render something as an xml element list
-}
class XmlListPrintable a where
  -- | render instance to an xml element list
  toLst :: GlobalAnnos -> a -> [Content]

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
instance XmlListPrintable Empty where toLst _ _ = []


-- the trivial instances!
instance XmlPrintable Content where
    toXml _ = id
instance XmlAttrList [Attr] where
    mkAtts = id


instance XmlPrintable LIB_DEFN where
    toXml ga (Lib_defn n il rg an) =
        withRg rg $ mkEl "Lib" ["name", toStr n]
                   $ maybeToList (printAnnotations ga nullRange an [])
                         ++ map (toXml ga . item) il

instance XmlPrintable LIB_ITEM where
    toXml ga (Spec_defn n g as rg)
        = withRg rg $ mkEl "Spec" ["name", toString n]
          $ toLst ga g ++ [toXml ga as]
    toXml ga (View_defn n g (View_type from to _) mapping rg)
        = withRg rg $ mkEl "View" ["name", toString n]
          $ toLst ga g ++ [mkPEl "From" [toXml ga from], mkPEl "To" [toXml ga to]]
                ++ toLst ga mapping
    toXml ga (Download_items n mapping rg)
        = withRg rg $ mkEl "Import" ["name", toString n] $ toLst ga mapping
    toXml _ (Logic_decl n rg)
        = withRg rg $ mkFEl "Logic" ["name", toStr n]
    toXml _ x = mkComment $ take 15 (show x)  ++ "- not Supported"

instance XmlPrintable (Annoted SPEC) where
    toXml ga a@(Annoted s _ _ _) =
        let mkAEl x y z = withAnno ga a $ mkEl x y z
            mkAPEl x z = withAnno ga a $ mkPEl x z
        in case s of
             Basic_spec bs rg -> withRg rg $ mkAPEl "Basic" $ toLst ga bs
             EmptySpec _ -> mkAPEl "Emptyspec" []
             Translation as (Renaming m _) -> mkAPEl "Renaming"
                                              $ toXml ga as : toLst ga m
             Reduction as m -> mkAPEl "Restriction"
                               $ toXml ga as : toLst ga m
             Union asl rg -> withRg rg $ mkAPEl "Union" $ toLst ga asl
             Extension asl rg -> withRg rg $ mkAPEl "Extension"
                                 $ toLst ga asl
             Free_spec as rg -> withRg rg $ mkAPEl "Free" [toXml ga as]
             Cofree_spec as rg -> withRg rg $ mkAPEl "Cofree" [toXml ga as]
             Local_spec as ins rg -> withRg rg $ mkAPEl "Local"
                                     [toXml ga as, toXml ga ins]
             Closed_spec as rg -> withRg rg $ mkAPEl "Closed" [toXml ga as]
             Group as rg -> withRg rg $ mkAPEl "Group" [toXml ga as]
             Spec_inst n fa rg ->
                 withRg rg $ mkAEl "Inst" ["name", toString n] $ toLst ga fa
             Qualified_spec ln as rg -> withRg rg $ mkAEl "Qualified"
                                        ["logic", toString ln] [toXml ga as]
             Data _ _ _ _ _ -> mkComment "DATA not supported"

instance XmlPrintable (Annoted FIT_ARG) where
    toXml ga a@(Annoted farg _ _ _) =
        let mkAEl x y z = withAnno ga a $ mkEl x y z
            mkAPEl x z = withAnno ga a $ mkPEl x z
        in case farg of
             Fit_spec as _ rg ->  withRg rg $ mkAPEl "Fitspec" [toXml ga as]
             Fit_view n fargs rg ->
                 withRg rg $ mkAEl "Fitview" ["name", toString n]
                            $ toLst ga fargs

instance XmlPrintable Annotation where
    toXml _ x = withRg (getRange x) $ mkPEl "Annotation" [toText x]

instance XmlPrintable ITEM_NAME_OR_MAP where
    toXml _ (Item_name name) = mkFEl "Item" ["name", toString name]
    toXml _ (Item_name_map name as _)
        = mkFEl "Item" ["name", toString name, "as", toString as]

instance XmlPrintable G_mapping where
    toXml ga (G_symb_map l) = mkPEl "Mapping" $ toLst ga l
    toXml _ (G_logic_translation lc) = mkFEl "Logictranslation" lc

instance XmlPrintable G_hiding where
    toXml ga (G_symb_list l) = mkPEl "Hiding" $ toLst ga l
    toXml _ (G_logic_projection lc) = mkFEl "Logicprojection" lc

instance PrintableAsXmlAttr LIB_NAME where
    toStr l = case l of
                Lib_version i _ -> toString i
                Lib_id i -> toString i

instance PrintableAsXmlAttr Token where toStr = tokStr

instance PrintableAsXmlAttr Logic_name where toStr (Logic_name t _) = toStr t

instance XmlPrintable a => XmlListPrintable [a] where
    toLst ga = map $ toXml ga

instance XmlListPrintable G_basic_spec where
    toLst ga (G_basic_spec lid bs) =
        let i = toItem lid bs
        in map (fromAnno ga . fmap (itemToXml ga)) $ items i

instance XmlListPrintable GENERICITY where
    toLst ga (Genericity (Params pl) (Imported il) _)
        = let f n l = map (mkPEl n . (: []) . toXml ga) l
          in f "Param" pl ++ f "Given" il

instance XmlListPrintable RESTRICTION where
    toLst ga (Hidden m _) = toLst ga m
    toLst ga (Revealed m _) = toLst ga m

instance XmlListPrintable G_symb_items_list where
    toLst _ (G_symb_items_list _ l) = map toText l

instance XmlListPrintable G_symb_map_items_list where
    toLst _ (G_symb_map_items_list _ l) = map toText l

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

printAnnotated :: GlobalAnnos -> Annoted a -> Maybe Content
printAnnotated ga (Annoted _ rg la ra) = printAnnotations ga rg la ra

printAnnotations
    :: GlobalAnnos -> Range -> [Annotation] -> [Annotation] -> Maybe Content
printAnnotations _ _ [] [] = Nothing
-- TOCHECK: Annoted-Items have empty range for the moment
printAnnotations ga rg lan ran
    = Just $ withRg rg $ mkPEl "Annotations"
      $ let f n l = (case l of [] -> []
                               _ -> [printPXmlList ga n l])
        in f "Left" lan ++ f "Right" ran

-- check if one can remove this by generalizing mkEl such as for attribs
printXmlList :: XmlPrintable a
    => GlobalAnnos -> String -> [String] -> [a] -> Content
printXmlList ga n attrs l = mkEl n attrs $ toLst ga l

printPXmlList :: XmlPrintable a => GlobalAnnos -> String -> [a] -> Content
printPXmlList ga n l = printXmlList ga n [] l

fromAnno :: XmlPrintable a => GlobalAnnos -> Annoted a -> Content
fromAnno ga a = withAnno ga a $ toXml ga $ item a

withAnno :: GlobalAnnos -> Annoted a -> Content -> Content
withAnno ga a c@(Elem e) = case printAnnotated ga a of
                        Just ac -> Elem $ e { elContent = ac : elContent e }
                        _ -> c
withAnno _ _ _ = error "withAnno only applies to elements"

withText :: String -> Content -> Content
withText s (Elem e) = Elem $ e { elContent = mkText s : elContent e }
withText _ _ = error "withText only applies to elements"

withAttrs :: [Attr] -> Content -> Content
withAttrs as (Elem e) = Elem $ add_attrs as e
withAttrs _ _ = error "withAttrs only applies to elements"


withRg :: Range -> Content -> Content
withRg rg c@(Elem e) =
    case rangeToAttribs rg of [] -> c
                              as -> Elem $ add_attrs as e
withRg _ _ = error "withRg only applies to elements"

posString :: Pos -> String
posString (SourcePos _ l c) = show l ++ ":" ++ show c

rangeToAttribs :: Range -> [Attr]
rangeToAttribs (Range []) = []
rangeToAttribs (Range l) = [Attr (unqual "range") $ intercalate ","
                                     $ map posString $ sortRange [] l]

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
mkEl n a c = Elem $ unode n (mkAtts a, c)

-- make final element (no children)
mkFEl :: XmlAttrList a => String -> a -> Content
mkFEl n a = mkEl n a []

-- make pure element (no attributes)
mkPEl :: String -> [Content] -> Content
mkPEl n c = mkEl n Empty c

mkAttr :: String -> String -> Attr
mkAttr n = Attr (unqual n)

------------------------------------------------------------------------------

itemToXml :: GlobalAnnos -> Item -> Content
itemToXml ga i =
    let IT name attrs mdoc = itemType i
        content = withRg (range i)
                  $ mkPEl name
                  $ map (fromAnno ga . fmap (itemToXml ga)) $ items i
    in withAttrs (map (uncurry mkAttr) attrs) $ case mdoc of
         Nothing -> content
         Just d -> withText (show $ useGlobalAnnos ga d) content
