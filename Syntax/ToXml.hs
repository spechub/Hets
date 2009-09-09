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
    ( printLibDefnXml
    ) where

import Syntax.AS_Structured
import Syntax.AS_Library
import Syntax.Print_AS_Library ()

import Common.AS_Annotation
import Common.Id
import Common.Item
import Common.LibName
import Common.Result
import Common.DocUtils
import Common.GlobalAnnotations
import Common.ToXml

import Logic.Logic
import Logic.Grothendieck

import Text.XML.Light

import Data.Maybe
import Data.List

-- | Prints the Library to an xml string
printLibDefnXml :: GlobalAnnos -> LIB_DEFN -> String
printLibDefnXml ga = ppTopElement . libDefn ga

libDefn :: GlobalAnnos -> LIB_DEFN -> Element
libDefn ga (Lib_defn n il rg an) =
  add_attrs (mkNameAttr (show $ getLIB_ID n) : rgAttrs rg)
     $ unode "Lib" $ annos "Global" ga an ++ map (annoted libItem ga) il

libItem :: GlobalAnnos -> LIB_ITEM -> Element
libItem ga li = case li of
  Spec_defn n g as rg ->
    add_attrs (mkNameAttr (tokStr n) : rgAttrs rg)
      $ unode "SpecDefn" $ genericity ga g ++ [annoted spec ga as]
  View_defn n g (View_type from to _) mapping rg ->
    add_attrs (mkNameAttr (tokStr n) : rgAttrs rg)
      $ unode "ViewDefn" $ genericity ga g
        ++ [ unode "Source" $ annoted spec ga from
           , unode "Target" $ annoted spec ga to ]
        ++ concatMap (gmapping ga) mapping
  Download_items n mapping rg ->
    add_attrs (mkNameAttr (show $ getLIB_ID n) : rgAttrs rg)
      $ unode "Import" $ map itemNameOrMap mapping
  Logic_decl n rg ->
    add_attrs (mkNameAttr (show n) : rgAttrs rg)
      $ unode "Logic" ()
  _ -> prettyElem "Unsupported" ga li

spec :: GlobalAnnos -> SPEC -> Element
spec ga s = case s of
  Basic_spec bs rg -> withRg rg $ gBasicSpec ga bs
  EmptySpec rg -> withRg rg $ unode "Empty" ()
  Translation as (Renaming m _) ->
    unode "Translation" $ annoted spec ga as : concatMap (gmapping ga) m
  Reduction as m ->
    unode "Restriction" $ annoted spec ga as : restriction ga m
  Union asl rg -> withRg rg $ unode "Union"
    $ map (unode "Spec" . annoted spec ga) asl
  Extension asl rg -> withRg rg $ unode "Extension"
   $ map (unode "Spec" . annoted spec ga) asl
  Free_spec as rg -> withRg rg $ unode "Free" $ annoted spec ga as
  Cofree_spec as rg -> withRg rg $ unode "Cofree" $ annoted spec ga as
  Local_spec as ins rg -> withRg rg $ unode "Local"
    [unode "Spec" $ annoted spec ga as, unode "Within" $ annoted spec ga ins]
  Closed_spec as rg -> withRg rg $ unode "Closed" $ annoted spec ga as
  Group as rg -> withRg rg $ unode "Group" $ annoted spec ga as
  Spec_inst n fa rg ->
    add_attrs (mkNameAttr (tokStr n) : rgAttrs rg)
    $ unode "Actuals" $ map (annoted fitArg ga) fa
  Qualified_spec ln as rg -> withRg rg $ unode "Qualified"
    [prettyElem "Logic" ga ln, annoted spec ga as]
  Data l1 _ s1 s2 rg ->
    add_attrs (mkAttr "data-logic" (show l1) : rgAttrs rg)
      $ unode "Data" [annoted spec ga s1, annoted spec ga s2]

fitArg :: GlobalAnnos -> FIT_ARG -> Element
fitArg ga fa = case fa of
  Fit_spec as m rg -> withRg rg $ unode "Spec"
    $ annoted spec ga as : concatMap (gmapping ga) m
  Fit_view n fargs rg ->
    add_attrs (mkNameAttr (tokStr n) : rgAttrs rg)
    $ unode "Spec" $ unode "Actuals" $ map (annoted fitArg ga) fargs

itemNameOrMap :: ITEM_NAME_OR_MAP -> Element
itemNameOrMap itm = (case itm of
  Item_name name -> add_attr (mkNameAttr $ tokStr name)
  Item_name_map name as _ ->
    add_attrs [mkNameAttr $ tokStr name, mkAttr "as" $ tokStr as])
  $ unode "Item" ()

gmapping :: GlobalAnnos -> G_mapping -> [Element]
gmapping ga gm = case gm of
  G_symb_map l -> subnodes "Mapping" $ gSymbMapItemList ga l
  G_logic_translation lc -> [ add_attrs (logicCode lc)
    $ unode "Logictranslation" () ]

ghiding :: GlobalAnnos -> G_hiding -> Element
ghiding ga gm = case gm of
  G_symb_list l -> unode "Hiding" $ gSymbItemList ga l
  G_logic_projection lc -> add_attrs (logicCode lc)
    $ unode "Logicprojection" ()

gBasicSpec :: GlobalAnnos -> G_basic_spec -> Element
gBasicSpec ga (G_basic_spec lid bs) = itemToXml ga $ toItem lid bs

genericity :: GlobalAnnos -> GENERICITY -> [Element]
genericity ga (Genericity (Params pl) (Imported il) rg) =
  if null pl then [] else
    unode "Parameters" (spec ga $ Union pl rg)
    : if null il then [] else
      [ unode "Imports" $ spec ga $ Union il rg ]

restriction :: GlobalAnnos -> RESTRICTION -> [Element]
restriction ga restr = case restr of
  Hidden m _ -> map (ghiding ga) m
  Revealed m _ -> gSymbMapItemList ga m

gSymbItemList :: GlobalAnnos -> G_symb_items_list -> [Element]
gSymbItemList ga (G_symb_items_list _ l) = map (prettyElem "SymbItems" ga) l

gSymbMapItemList :: GlobalAnnos -> G_symb_map_items_list -> [Element]
gSymbMapItemList ga (G_symb_map_items_list _ l) =
  map (prettyElem "SymbMapItems" ga) l

logicCode :: Logic_code -> [Attr]
logicCode (Logic_code enc src trg _) =
  (case enc of
    Nothing -> []
    Just t -> [mkAttr "encoding" $ tokStr t])
  ++ (case src of
        Nothing -> []
        Just l -> [mkAttr "source" $ show $ pretty l])
  ++ case trg of
        Nothing -> []
        Just l -> [mkAttr "target" $ show $ pretty l]

isEmptyItem :: Annoted Item -> Bool
isEmptyItem ai =
  let i = item ai
      IT _ attrs mdoc = itemType i
  in null (rgAttrs $ range i) && null attrs && isNothing mdoc
     && null (l_annos ai) && null (r_annos ai)
     && all isEmptyItem (items i)

itemToXml :: GlobalAnnos -> Item -> Element
itemToXml ga i =
    let IT name attrs mdoc = itemType i
    in add_attrs (map (uncurry mkAttr) attrs ++ rgAttrs (range i))
       $ unode name $ (case mdoc of
          Nothing -> []
          Just d -> [mkText $ show $ useGlobalAnnos ga d])
        ++ map (Elem . annoted itemToXml ga)
           (filter (not . isEmptyItem) $ items i)

-- range attribute without file name
rgAttrs :: Range -> [Attr]
rgAttrs = rangeAttrsF $ show . prettyRange . map (\ p -> p { sourceName = "" })

annos :: String -> GlobalAnnos -> [Annotation] -> [Element]
annos str ga = subnodes str
  . map (annotationF rgAttrs ga)

annoted :: (GlobalAnnos -> a -> Element) -> GlobalAnnos -> Annoted a -> Element
annoted f ga a = let
  e = f ga $ item a
  l = annos "Left" ga $ l_annos a
  r = annos "Right" ga $ r_annos a
  in e { elContent = map Elem l ++ elContent e ++ map Elem r }

withRg :: Range -> Element -> Element
withRg = add_attrs . rgAttrs

mkText :: String -> Content
mkText s = Text $ CData CDataText s Nothing
