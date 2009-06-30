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
      XmlPrintable
    , printLibDefnXml
    ) where

import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Print_AS_Structured()

import Common.Id (Range)
import Common.Result ()
import Common.AS_Annotation
import Common.DocUtils

import Text.XML.Light

-- one can add global annos if necessary
-- | Prints the Library to an xml string
printLibDefnXml :: LIB_DEFN -> String
printLibDefnXml ld = case toXml ld of (Elem e) -> ppTopElement e
                                      c -> ppContent c


-- if necessary replace Content by a custom data type

{- |
  this class defines the interface for writing XML
-}
class XmlPrintable a where
  -- | render instance to an XML Element
  toXml :: a -> Content

instance XmlPrintable LIB_DEFN where
    toXml (Lib_defn n il rg an) =
        mkEl "LIB_DEFN" ["name", toString n]
                 $ printAnnotations rg an [] : map (toXml . item) il

instance XmlPrintable LIB_ITEM where
--    toXml (Spec_defn si (Genericity aa@(Params pl) ab@(Imported il) _) ac' _) =
    toXml (Spec_defn n _ as rg) =
        withRg rg $ mkEl "SPEC" ["name", toString n] [toXml as]
    toXml (View_defn n _ vt mapping rg) = withRg rg $ mkFEl "VIEW" []
    toXml (Download_items n mapping rg) = withRg rg $ mkFEl "FROM" []
    toXml (Logic_decl n rg) = withRg rg $ mkFEl "LOGIC" []
    toXml x = mkComment $ take 15 (show x)  ++ "- not Supported"

instance XmlPrintable (Annoted SPEC) where
    toXml a@(Annoted s toprg la ra) =
        let mkAEl x y z = withAnno a $ mkEl x y z
            mkAPEl x z = withAnno a $ mkPEl x z
        in case s of
             Basic_spec bs rg -> withRg rg $ mkAPEl "Basic" [toText bs]
             EmptySpec _ -> mkAPEl "EmptySpec" []
             Translation as m -> mkAPEl "Translation" [toXml as, toText m]
             Reduction as m -> mkAPEl "Reduction" [toXml as, toText m]
             Union asl rg -> withRg rg $ mkAPEl "Union" $ map toXml asl
             Extension asl rg -> withRg rg $ mkAPEl "Extension"
                                 $ map toXml asl
             Free_spec as rg -> withRg rg $ mkAPEl "Free" [toXml as]
             Cofree_spec as rg -> withRg rg $ mkAPEl "Cofree" [toXml as]
             Local_spec as ins rg -> withRg rg $ mkAPEl "Local"
                                     [toXml as, toXml ins]
             Closed_spec as rg -> withRg rg $ mkAPEl "Closed" [toXml as]
             Group as rg -> withRg rg $ mkAPEl "Group" [toXml as]
             Spec_inst n fa rg ->
                 withRg rg $ mkAEl "Inst" ["name", toString n] $ map toXml fa
             Qualified_spec ln as rg ->
                 withRg rg $ mkAEl "Qualified" ["logic", toString ln] [toXml as]
             Data _ _ s1 s2 _ -> mkComment "DATA not supported"

instance XmlPrintable (Annoted FIT_ARG) where
    toXml a@(Annoted farg toprg la ra) =
        let mkAEl x y z = withAnno a $ mkEl x y z
            mkAPEl x z = withAnno a $ mkPEl x z
        in case farg of
             Fit_spec as _ rg ->  withRg rg $ mkAPEl "Fitspec" [toXml as]
             Fit_view n fargs rg ->
                 withRg rg $ mkAEl "Fitview" ["name", toString n]
                            $ map toXml fargs

instance XmlPrintable Annotation where
    toXml x = mkPEl "Annotation" [toText x]

withAnno :: Annoted a -> Content -> Content
withAnno a (Elem e) = Elem $ e { elContent = printAnnotated a : elContent e }
withAnno a _ = error "withAnno only applies to elements"

withRg :: Range -> Content -> Content
withRg rg (Elem e) = Elem $ add_attr (Attr (unqual "range") $ toString rg) e
withRg rg _ = error "withRg only applies to elements"

printAnnotated :: Annoted a -> Content
printAnnotated (Annoted _ rg la ra) = printAnnotations rg la ra

printAnnotations :: Range -> [Annotation] -> [Annotation] -> Content
printAnnotations rg lan ran =
    withRg rg $ mkPEl "Annotations" 
               [printPXmlList "Left" lan, printPXmlList "Right" ran]

{-
withNewLine :: String -> String
withNewLine s = "\n" ++ s ++ "\n"

toComment :: Pretty a => a -> Content
toComment = mkComment . toString

toVerb :: Pretty a => a -> Content
toVerb = mkVerb . toString

mkVerb :: String -> Content
mkVerb s = Text $ CData CDataVerbatim s $ Just 50

-}

printXmlList :: XmlPrintable a => String -> [String] -> [a] -> Content
printXmlList n attrs l = mkEl n attrs $ map toXml l

printPXmlList :: XmlPrintable a => String -> [a] -> Content
printPXmlList n l = printXmlList n [] l

toString :: Pretty a => a -> String
toString = show . pretty

toText :: Pretty a => a -> Content
toText = mkText . toString

mkComment :: String -> Content
mkComment s = Text $ CData CDataRaw ("<!-- \n" ++ s ++ "\n -->") Nothing

mkText :: String -> Content
mkText s = Text $ CData CDataText s Nothing

-- make element
mkEl :: String -> [String] -> [Content] -> Content
mkEl n a c = Elem $ node (unqual n) (mkAtts a, c)

-- make final element (no children)
mkFEl :: String -> [String] -> Content
mkFEl n a = mkEl n a []

-- make pure element (no attributes)
mkPEl :: String -> [Content] -> Content
mkPEl n c = mkEl n [] c

mkAtts :: [String] -> [Attr]
mkAtts (x:y:l) = (Attr (unqual x) y) : mkAtts l
mkAtts _ = []

