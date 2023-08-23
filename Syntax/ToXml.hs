{- |
Module      :  ./Syntax/ToXml.hs
Description :  xml output of Hets specification libaries
Copyright   :  (c) Ewaryst Schulz, Uni Bremen 2009
License     :  GPLv2 or higher, see LICENSE.txt
Maintainer  :  Ewaryst.Schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Grothendieck)

Xml printing of Hets specification libaries
-}

module Syntax.ToXml (xmlLibDefn) where

import Syntax.AS_Structured
import Syntax.Print_AS_Structured
import Syntax.AS_Library
import Syntax.Print_AS_Library ()

import Common.AS_Annotation
import Common.Id
import Common.IRI
import Common.Item
import Common.LibName
import Common.Result
import Common.DocUtils
import Common.GlobalAnnotations
import Common.ToXml
import Common.XUpdate

import Logic.Logic
import Logic.Grothendieck

import Text.XML.Light

import Data.Maybe

iriToStr :: IRI -> String
iriToStr = iriToStringShortUnsecure . setAngles False

xmlLibDefn :: LogicGraph -> GlobalAnnos -> LIB_DEFN -> Element
xmlLibDefn lg ga (Lib_defn n il rg an) =
  add_attrs (mkNameAttr (show $ setAngles False $ getLibId n) : rgAttrs rg)
     $ unode "Lib" $ annos "Global" ga an ++ libItems lg ga il

libItems :: LogicGraph -> GlobalAnnos -> [Annoted LIB_ITEM] -> [Element]
libItems lg ga is = case is of
  [] -> []
  i : rs -> annoted libItem lg ga i : libItems (case item i of
    Logic_decl aa _ -> setLogicName aa lg
    _ -> lg) ga rs

unsupported :: PrettyLG a => LogicGraph -> GlobalAnnos -> a -> Element
unsupported lg ga =
  unode "Unsupported" . show . useGlobalAnnos ga . prettyLG lg

libItem :: LogicGraph -> GlobalAnnos -> LIB_ITEM -> Element
libItem lg ga li = case li of
  Spec_defn n g as rg ->
    add_attrs (mkNameAttr (iriToStr n) : rgAttrs rg)
      $ unode "SpecDefn" $ genericity lg ga g ++ [annoted spec lg ga as]
  View_defn n g (View_type from to _) mapping rg ->
    add_attrs (mkNameAttr (iriToStr n) : rgAttrs rg)
      $ unode "ViewDefn" $ genericity lg ga g
        ++ [ unode "Source" $ annoted spec lg ga from
           , unode "Target" $ annoted spec lg ga to ]
        ++ concatMap (gmapping ga) mapping
  Download_items n mapping rg ->
    add_attrs (mkNameAttr (show $ getLibId n) : rgAttrs rg)
      $ unode "Import" $ downloadItems mapping
  Logic_decl n rg ->
    add_attrs (mkNameAttr (showDoc n "") : rgAttrs rg)
      $ unode "Logic" ()
  _ -> unsupported lg ga li

downloadItems :: DownloadItems -> [Element]
downloadItems d = case d of
  ItemMaps l -> map itemNameOrMap l
  UniqueItem i -> [add_attr (mkAttr "as" $ iriToStr i)
    $ unode "Item" ()]

spec :: LogicGraph -> GlobalAnnos -> SPEC -> Element
spec lg ga s = case s of
  Basic_spec bs rg -> withRg rg $ gBasicSpec lg ga bs
  EmptySpec rg -> withRg rg $ unode "Empty" ()
  Translation as (Renaming m _) ->
    unode "Translation" $ annoted spec lg ga as : concatMap (gmapping ga) m
  Reduction as m ->
    unode "Restriction" $ annoted spec lg ga as : restriction ga m
  Union asl rg -> withRg rg $ unode "Union"
    $ map (unode "Spec" . annoted spec lg ga) asl
  Extension asl rg -> withRg rg $ unode "Extension"
   $ map (unode "Spec" . annoted spec lg ga) asl
  Free_spec as rg -> withRg rg $ unode "Free" $ annoted spec lg ga as
  Cofree_spec as rg -> withRg rg $ unode "Cofree" $ annoted spec lg ga as
  Minimize_spec as rg -> withRg rg $ unode "Minimize" $ annoted spec lg ga as
  Local_spec as ins rg -> withRg rg $ unode "Local"
    [ unode "Spec" $ annoted spec lg ga as
    , unode "Within" $ annoted spec lg ga ins]
  Closed_spec as rg -> withRg rg $ unode "Closed" $ annoted spec lg ga as
  Group as rg -> withRg rg $ unode "Group" $ annoted spec lg ga as
  Spec_inst n fa _ rg ->
    add_attrs (mkNameAttr (iriToStr n) : rgAttrs rg)
    $ unode "Actuals" $ map (annoted fitArg lg ga) fa
  Qualified_spec ln as rg -> withRg rg $ unode "Qualified"
    [prettyElem "Logic" ga ln, annoted spec (setLogicName ln lg) ga as]
  Data l1 _ s1 s2 rg ->
    add_attrs (mkAttr "data-logic" (show l1) : rgAttrs rg)
      $ unode "Data" [ annoted spec (setCurLogic (show l1) lg) ga s1
                     , annoted spec lg ga s2]
  _ -> unsupported lg ga s

fitArg :: LogicGraph -> GlobalAnnos -> FIT_ARG -> Element
fitArg lg ga fa = case fa of
  Fit_spec as m rg -> withRg rg $ unode "Spec"
    $ annoted spec lg ga as : concatMap (gmapping ga) m
  Fit_view n fargs rg ->
    add_attrs (mkNameAttr (iriToStr n) : rgAttrs rg)
    $ unode "Spec" $ unode "Actuals" $ map (annoted fitArg lg ga) fargs

itemNameOrMap :: ItemNameMap -> Element
itemNameOrMap (ItemNameMap name m) =
  add_attrs (mkNameAttr (iriToStr name) : case m of
    Nothing -> []
    Just as -> [mkAttr "as" $ iriToStr as])
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

gBasicSpec :: LogicGraph -> GlobalAnnos -> G_basic_spec -> Element
gBasicSpec lg ga (G_basic_spec lid bs) = itemToXml lg ga $ toItem lid bs

genericity :: LogicGraph -> GlobalAnnos -> GENERICITY -> [Element]
genericity lg ga (Genericity (Params pl) (Imported il) rg) =
  if null pl then [] else
    unode "Parameters" (spec lg ga $ Union pl rg)
    : if null il then [] else
      [ unode "Imports" $ spec lg ga $ Union il rg ]

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
    Just t -> [mkAttr "encoding" t])
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

itemToXml :: LogicGraph -> GlobalAnnos -> Item -> Element
itemToXml lg ga i =
    let IT name attrs mdoc = itemType i
    in add_attrs (map (uncurry mkAttr) attrs ++ rgAttrs (range i))
       $ unode name $ (case mdoc of
          Nothing -> []
          Just d -> [mkText $ show $ useGlobalAnnos ga d])
        ++ map (Elem . annoted itemToXml lg ga)
           (filter (not . isEmptyItem) $ items i)

-- range attribute without file name
rgAttrs :: Range -> [Attr]
rgAttrs = rangeAttrsF $ show . prettyRange . map (\ p -> p { sourceName = "" })

annos :: String -> GlobalAnnos -> [Annotation] -> [Element]
annos str ga = subnodes str
  . map (annotationF rgAttrs ga)

annoted :: (LogicGraph -> GlobalAnnos -> a -> Element) -> LogicGraph
  -> GlobalAnnos -> Annoted a -> Element
annoted f lg ga a = let
  e = f lg ga $ item a
  l = annos "Left" ga $ l_annos a
  r = annos "Right" ga $ r_annos a
  in e { elContent = map Elem l ++ elContent e ++ map Elem r }

withRg :: Range -> Element -> Element
withRg r e = if isJust (getAttrVal "range" e) then e else
   add_attrs (rgAttrs r) e
