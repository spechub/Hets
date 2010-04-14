{-# LANGUAGE
  FlexibleInstances
  , TypeSynonymInstances
 #-}

{- |
Module      :  $Header$
Description :  OMDoc-to/from-XML conversion
Copyright   :  (c) Ewaryst Schulz, DFKI 2009
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  provisional
Portability :  non-portable(Logic)

The transformation of the OMDoc intermediate representation to and from XML.
-}



module OMDoc.XmlInterface where

import OMDoc.DataTypes

import Text.XML.Light

import Data.Maybe
import Data.List

import Network.URI (isUnescapedInURI, escapeURIString, unEscapeString)

import Common.Utils (splitBy)
import Common.Result
import Common.Id

-- | The implemented OMDoc version
omdoc_current_version :: String
omdoc_current_version = "1.6"

toQN :: String -> QName
toQN s = blank_name { qName = s }
toQNOM :: String -> QName
toQNOM s = blank_name { qName = s , qPrefix = Just "om" }

-- | often used element names

el_omdoc, el_theory, el_view, el_structure, el_type, el_adt, el_sortdef
 , el_constructor, el_argument, el_insort, el_selector
 , el_conass, el_constant, el_notation, el_text, el_definition, el_omobj
 , el_ombind, el_oms, el_ombvar, el_omattr, el_omatp, el_omv, el_oma :: QName

el_omdoc = toQN "omdoc"
el_theory = toQN "theory"
el_view = toQN "view"
el_structure = toQN "structure"
el_type = toQN "type"
el_adt = toQN "adt"
el_sortdef = toQN "sortdef"
el_constructor = toQN "constructor"
el_argument = toQN "argument"
el_insort = toQN "insort"
el_selector = toQN "selector"
el_conass = toQN "conass"
el_constant = toQN "constant"
el_notation = toQN "notation"
el_text = toQN "text"
el_definition = toQN "definition"

el_omobj = toQN "OMOBJ"

el_ombind = toQNOM "OMBIND"
el_oms = toQNOM "OMS"
el_ombvar = toQNOM "OMBVAR"
el_omattr = toQNOM "OMATTR"
el_omatp = toQNOM "OMATP"
el_omv = toQNOM "OMV"
el_oma = toQNOM "OMA"

at_version, at_module, at_name, at_meta, at_role, at_type, at_total
 , at_for, at_from, at_to, at_value, at_base :: QName

at_version = toQN "version"
at_module = toQN "module"
at_name = toQN "name"
at_meta = toQN "meta"
at_role = toQN "role"
at_type = toQN "type"
at_total = toQN "total"
at_for = toQN "for"
at_from = toQN "from"
at_to = toQN "to"
at_value = toQN "value"
at_base = toQN "base"


attr_om :: Attr
attr_om = Attr (blank_name { qName = "om" , qPrefix = Just "xmlns" })
          "http://www.openmath.org/OpenMath"


mkElement :: QName -> [Attr] -> [Content] -> Content
mkElement qn atts elems = Elem $ Element qn atts elems Nothing

{- |
  this class defines the interface to read from and write to XML
-}
class XmlRepresentable a where
  -- | render instance to an XML Element
  toXml :: a -> Content
  -- | read instance from an XML Element
  fromXml :: Element -> Result (Maybe a)


xmlOut :: XmlRepresentable a => a -> String
xmlOut obj = case toXml obj of (Elem e) -> ppTopElement e
                               c -> ppContent c

xmlIn :: String -> Result OMDoc
xmlIn s = case parseXMLDoc s of
            Just e -> fromXml e >>= maybeToMonad "xmlIn"
            _ -> fail "xmlIn: Root element missing"


listToXml :: XmlRepresentable a => [a] -> [Content]
listToXml l = map toXml l

listFromXml :: XmlRepresentable a => [Content] -> Result [a]
listFromXml elms = fmap catMaybes $ mapR fromXml (onlyElems elms)

makeComment :: String -> Content
makeComment s = Text $ CData CDataRaw ("<!-- " ++ s ++ " -->") Nothing


inAContent :: QName -> [Attr] -> Maybe Content -> Content
inAContent qn a c = mkElement qn a $ maybeToList c

inContent :: QName -> Maybe Content -> Content
inContent qn c = inAContent qn [] c

toOmobj :: Content -> Content
toOmobj c = inAContent el_omobj [attr_om] $ Just c


-- TODO: URL-encode/decode the ids

-- url escaping and unescaping.
-- We use ? and / as special characters, so we need them to be encoded in names
urlEscape :: String -> String
urlEscape = escapeURIString (\ c -> isUnescapedInURI c && notElem c "/?")

urlUnescape :: String -> String
urlUnescape = unEscapeString


-- encoding

uriEncodeCDName :: OMCD -> OMName -> String
uriEncodeCDName omcd omname = uriEncodeCD omcd ++ "?" ++ encodeOMName omname

uriEncodeCD :: OMCD -> String
uriEncodeCD cd = let [x,y] = cdToList cd
                 in concat [urlEscape x, "?", urlEscape y]

encodeOMName :: OMName -> String
encodeOMName on = intercalate "/" $ map urlEscape $ path on ++ [name on]

tripleEncodeOMS :: OMCD -> OMName -> [Attr]
tripleEncodeOMS omcd omname
    = pairEncodeCD omcd ++ [Attr at_name $ encodeOMName omname]

pairEncodeCD :: OMCD -> [Attr]
pairEncodeCD cd = let f x y = fmap (Attr x . urlEscape) y
                  in catMaybes $ zipWith f [at_base, at_module]
                         $ cdToMaybeList cd

-- decoding

uriDecodeCD :: Show a => a -> String -> OMCD
uriDecodeCD _ = cdFromList . map urlUnescape . splitBy '?'

uriDecodeCDName :: String -> OMQualName
uriDecodeCDName s = case splitBy '?' s of
                      (b:cd:n:[]) -> ( cdFromList $ map urlUnescape [b, cd]
                                     , decodeOMName n)
                      _ -> error $ concat [ "uriDecodeCDName: The value "
                                          , "has to contain exactly two '?'"]

decodeOMName :: String -> OMName
decodeOMName s = let l = map urlUnescape $ splitBy '/' s
                 in OMName (last l) $ init l


tripleDecodeOMS :: String -> String -> String -> (OMCD, OMName)
tripleDecodeOMS cd base nm =
    let cdl = map urlUnescape $ filter (not . null) [cd, base]
    in if null cd && not (null base)
       then error "tripleDecodeOMS: base not empty but cd not given!"
       else (CD cdl, decodeOMName nm)


warnIfNothing :: String -> (Maybe a -> b)  -> Maybe a -> Result b
warnIfNothing s f v = let o = f v in
                      case v of Nothing -> warning () s  nullRange >> return o
                                _ -> return o

warnIf :: String -> Bool -> Result ()
warnIf s b = if b then warning () s  nullRange else return ()

elemIsOf :: Element -> QName -> Bool
elemIsOf e qn = let en = elName e in
                (qName en, qPrefix en) == (qName qn, qPrefix qn)

oneOfMsg :: Element -> [QName] -> String
oneOfMsg e l = let printName = qName in
               concat [ "Couldn't find expected element {"
                      , intercalate ", " (map printName l), "}"
                      , fromMaybe "" $ fmap ((" at line "++).show) $ elLine e
                      , " but found ", printName $ elName e, "."
                      ]

------------------------- Monad and Maybe interplay -------------------------

justReturn :: Monad m => a -> m (Maybe a)
justReturn = return . Just

fmapMaybe :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
fmapMaybe f v = encapsMaybe $ fmap f v

fmapFromMaybe :: Monad m => (a -> m (Maybe b)) -> Maybe a -> m (Maybe b)
fmapFromMaybe f = flattenMaybe . fmapMaybe f

encapsMaybe :: Monad m => Maybe (m a) -> m (Maybe a)
encapsMaybe v = case v of
  Just x -> x >>= justReturn
  _ -> return Nothing

flattenMaybe :: Monad m => m (Maybe (Maybe a)) -> m (Maybe a)
flattenMaybe v = v >>= return . fromMaybe Nothing


-- | Function to extract the Just values from maybes with a default missing
--   error in case of Nothing
missingMaybe :: String -> String -> Maybe a -> a
missingMaybe el misses =
    fromMaybe (error $ el ++ " element must have a " ++ misses ++ ".")


------------------------------ Class instances ------------------------------


-- | The root instance for representing OMDoc in XML
instance XmlRepresentable OMDoc where
    toXml (OMDoc omname elms) =
        mkElement
        el_omdoc [Attr at_version omdoc_current_version, Attr at_name omname]
                     $ listToXml elms
    fromXml e
        | elemIsOf e el_omdoc =
            do
              nm <- warnIfNothing "No name in omdoc element." (fromMaybe "")
                    $ findAttr at_name e
              vs <- warnIfNothing "No version in omdoc element."
                    (fromMaybe "1.6") $ findAttr at_version e
              warnIf "Wrong OMDoc version." $ vs /= omdoc_current_version
              tls <- listFromXml $ elContent e
              justReturn $ OMDoc nm tls
        | otherwise = fail "OMDoc fromXml: toplevel element is no omdoc."


-- | toplevel OMDoc elements to XML and back
instance XmlRepresentable TLElement where
    toXml (TLTheory tname meta elms) =
        mkElement
        el_theory ((Attr at_name tname)
                   : case meta of Nothing -> []
                                  Just mtcd ->
                                      [Attr at_meta $ uriEncodeCD mtcd])
                      $ listToXml elms
    toXml (TLView nm from to morph) =
        mkElement
        el_view [Attr at_name nm, Attr at_from $ uriEncodeCD from,
                      Attr at_to $ uriEncodeCD to]
                    $ map assignmentToXml morph

    fromXml e
        | elemIsOf e el_theory =
            let nm = missingMaybe "Theory" "name" $ findAttr at_name e
                mt = fmap (uriDecodeCD (elLine e)) $ findAttr at_meta e
            in do
              tcl <- listFromXml $ elContent e
              justReturn $ TLTheory nm mt tcl

        | elemIsOf e el_view =
            let musthave at s = missingMaybe "View" s $ findAttr at e
                nm = musthave at_name "name"
                from = uriDecodeCD (elLine e) $ musthave at_from "from"
                to = uriDecodeCD (elLine e) $ musthave at_to "to"
            in do
              morph <- mapR xmlToAssignment (findChildren el_conass e)
              justReturn $ TLView nm from to morph
        | otherwise = return Nothing


-- | theory constitutive OMDoc elements to XML and back
instance XmlRepresentable TCElement where
    toXml (TCSymbol sname symtype role defn) =
        constantToXml sname (show role) symtype defn
    toXml (TCNotation (cd, nm) val) =
        inAContent
        el_notation
        [Attr at_for $ uriEncodeCDName cd nm, Attr at_role "constant"]
        $ Just $ inAContent el_text [Attr at_value val] Nothing
    toXml (TCADT sds) = mkElement el_adt [] $ listToXml sds
    toXml (TCComment c) = makeComment c
    toXml (TCImport nm from morph) =
        mkElement
        el_structure [Attr at_name nm, Attr at_from $ uriEncodeCD from]
                         $ map assignmentToXml morph

    fromXml e
        | elemIsOf e el_constant =
            let musthave s v = missingMaybe "Constant" s v
                nm = musthave "name" $ findAttr at_name e
                role = fromMaybe Obj $ fmap read $ findAttr at_role e
            in do
              typ <- fmap (musthave "typ") $ omelementFrom el_type e
              defn <- omelementFrom el_definition e
              justReturn $ TCSymbol nm typ role defn
        | elemIsOf e el_notation =
            let musthave s v = missingMaybe "Notation" s v
                nm = musthave "for" $ findAttr at_for e
                role = musthave "role" $ findAttr at_role e
                text = musthave "text" $ findChild el_text e
                val = musthave "value" $ findAttr at_value text
            in if role == "constant"
               then justReturn $ TCNotation (uriDecodeCDName nm) val
               else return Nothing
        | elemIsOf e el_structure =
            let musthave at s = missingMaybe "Structure" s $ findAttr at e
                nm = musthave at_name "name"
                from = uriDecodeCD (elLine e) $ musthave at_from "from"
            in do
              morph <- mapR xmlToAssignment (findChildren el_conass e)
              justReturn $ TCImport nm from morph
        | elemIsOf e el_adt =
            do
              sds <- listFromXml $ elContent e
              justReturn $ TCADT sds
        | otherwise =
            fail $ oneOfMsg e [el_constant, el_structure, el_adt, el_notation]


-- | OMDoc - Algebraic Data Types
instance XmlRepresentable OmdADT where
    toXml (ADTSortDef n b cs) =
        mkElement el_sortdef
                      [Attr at_name n, Attr at_type $ show b]
                      $ listToXml cs
    toXml (ADTConstr n args) =
        mkElement el_constructor [Attr at_name n] $ listToXml args
    toXml (ADTArg t sel) =
        mkElement el_argument []
                      $ typeToXml t :
                        case sel of Nothing -> []
                                    Just s -> [toXml s]
    toXml (ADTSelector n total) =
        mkElement el_selector [Attr at_name n, Attr at_total $ show total] []
    toXml (ADTInsort (d,n)) =
        mkElement el_insort [Attr at_for $ uriEncodeCDName d n] []

    fromXml e
        | elemIsOf e el_sortdef =
            let musthave s at = missingMaybe "Sortdef" s $ findAttr at e
                nm = musthave "name" at_name
                typ = read $ musthave "type" at_type
            in do
              entries <- listFromXml $ elContent e
              justReturn $ ADTSortDef nm typ entries
        | elemIsOf e el_constructor =
            do
              let nm = missingMaybe "Constructor" "name" $ findAttr at_name e
              entries <- listFromXml $ elContent e
              justReturn $ ADTConstr nm entries
        | elemIsOf e el_argument =
            do
              typ <- fmap (missingMaybe "Argument" "typ")
                     $ omelementFrom el_type e
              sel <- fmapFromMaybe fromXml $ findChild el_selector e
              justReturn $ ADTArg typ sel
        | elemIsOf e el_selector =
            let musthave s at = missingMaybe "Selector" s $ findAttr at e
                nm = musthave "name" at_name
                total = read $ musthave "total" at_total
            in justReturn $ ADTSelector nm total
        | elemIsOf e el_insort =
            do
              let nm = missingMaybe "Insort" "for" $ findAttr at_for e
              justReturn $ ADTInsort $ uriDecodeCDName nm
        | otherwise =
            fail $ oneOfMsg e [ el_sortdef, el_constructor, el_argument
                              , el_selector, el_insort]


-- | OpenMath elements to XML and back
instance XmlRepresentable OMElement where
    toXml (OMS (d, n)) = mkElement el_oms (tripleEncodeOMS d n) []
    toXml (OMV n) = mkElement el_omv [Attr at_name (name n)] []
    toXml (OMATTT elm attr) = mkElement el_omattr [] [toXml attr, toXml elm]
    toXml (OMA args) = mkElement el_oma [] $ listToXml args
    toXml (OMBIND symb vars body) =
        mkElement el_ombind []
                      [ toXml symb
                      , mkElement el_ombvar [] $ listToXml vars
                      , toXml body]

    fromXml e
        | elemIsOf e el_oms =
            let nm = missingMaybe "OMS" "name" $ findAttr at_name e
                omcd = fromMaybe "" $ findAttr at_module e
                cdb = fromMaybe "" $ findAttr at_base e
            in justReturn $ OMS $ tripleDecodeOMS omcd cdb nm
        | elemIsOf e el_omv =
            let nm = missingMaybe "OMV" "name" $ findAttr at_name e
            in justReturn $ OMV $ decodeOMName nm
        | elemIsOf e el_omattr =
            let [atp, el] = elChildren e
                musthave s v = missingMaybe "OMATTR" s v
            in do
              atp' <- fromXml atp
              el' <- fromXml el
              justReturn $ OMATTT (musthave "attributed value" el')
                             (musthave "attribution" atp')
        | elemIsOf e el_oma =
            do
              entries <- listFromXml $ elContent e
              justReturn $ OMA entries
        | elemIsOf e el_ombind =
            let [bd, bvar, body] = elChildren e
                musthave s v = missingMaybe "OMBIND" s v
            in do
              bd' <- fromXml bd
              bvar' <- listFromXml $ elContent bvar
              body' <- fromXml body
              justReturn $ OMBIND (musthave "binder" bd') bvar'
                             (musthave "body" body')
        | otherwise =
            fail $ oneOfMsg e [el_oms, el_omv, el_omattr, el_oma, el_ombind]


-- | Helper instance for OpenMath attributes
instance XmlRepresentable OMAttribute where
    toXml (OMAttr e1 e2) = mkElement el_omatp [] [toXml e1, toXml e2]
    fromXml e
        | elemIsOf e el_omatp =
            do
              [key, val] <- listFromXml $ elContent e
              justReturn $ OMAttr key val
        | otherwise =
            fail $ oneOfMsg e [el_omatp]


------------------------------ fromXml methods ------------------------------

-- | Get an OMElement from an child element of type qn of the given element,
--   hence containing an OMOBJ
omelementFrom :: QName -> Element -> Result (Maybe OMElement)
omelementFrom qn e = fmapFromMaybe omelementFromOmobj $ findChild qn e

omelementFromOmobj :: Element -> Result (Maybe OMElement)
omelementFromOmobj e = fmapMaybe omobjToOMElement $ findChild el_omobj e

-- | Get an OMElement from an OMOBJ xml element
omobjToOMElement :: Element -> Result OMElement
omobjToOMElement e = case elChildren e of
                       [om] ->
                           do
                             omelem <- fromXml om
                             case omelem of
                               Nothing ->
                                   fail
                                   $ concat [ "omobjToOMElement: "
                                            , "No OpenMath element found."]
                               Just x -> return x
                       _ -> fail "OMOBJ element must have a unique child."


-- | The input is assumed to be a conass element
xmlToAssignment :: Element -> Result (OMName, OMElement)
xmlToAssignment e =
    let musthave s v = missingMaybe "Conass" s v
        nm = musthave "name" $ findAttr at_name e
    in do
      omel <- omelementFromOmobj e
      return (decodeOMName nm, musthave "OMOBJ element" omel)


------------------------------ toXml methods ------------------------------

typeToXml :: OMElement -> Content
typeToXml t = inContent el_type $ Just $ toOmobj $ toXml t

assignmentToXml :: (OMName, OMElement) -> Content
assignmentToXml (from, to) =
    inAContent el_conass [Attr at_name $ encodeOMName from]
                   $ Just . toOmobj . toXml $ to

constantToXml :: String -> String -> OMElement -> Maybe OMElement -> Content
constantToXml n r tp prf =
    Elem $ Element el_constant
             [Attr at_name n, Attr at_role r]
             ([typeToXml tp]
              ++ map (inContent el_definition . Just . toOmobj . toXml)
                     (maybeToList prf))
             Nothing
