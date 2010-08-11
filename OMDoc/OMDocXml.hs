{- |
Module      :  $Header$
Description :  XML conversion for OMDoc-model (in\/out)
Copyright   :  (c) Hendrik Iben, Uni Bremen 2005-2007
License     :  GPLv2 or higher

Maintainer  :  hiben@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

XmlRepresentations for the OMDoc modelled in OMDoc.OMDocInterface
-}
module OMDoc.OMDocXml where

import OMDoc.OMDocInterface
import qualified OMDoc.Util as Util
import qualified OMDoc.XmlHandling as XML

import qualified OMDoc.Base64 as Base64
import Common.Utils (trim)

import Text.XML.HXT.Parser ( (.>), (+=), (+++), getValue )
import qualified Text.XML.HXT.Parser as HXT hiding (run, trace, when)

import qualified Network.URI as URI
import qualified Numeric as Numeric
import qualified Data.List as List
import Data.Char

import Debug.Trace (trace)

{- debug -}
maybeGetXml::String->IO (Maybe HXT.XmlTrees)
maybeGetXml source =
  do
    xml <- HXT.run' $
      HXT.parseDocument
        [
            (HXT.a_source, source)
          , (HXT.a_issue_errors, HXT.v_0)
          , (HXT.a_check_namespaces, HXT.v_1)
          , (HXT.a_validate, HXT.v_0)
        ]
        HXT.emptyRoot
    return
      (let
        status = (read $ HXT.xshow $ getValue "status" (head xml))::Int
        result = if status < HXT.c_err then (Just xml) else Nothing
      in
        result)
{--}

{- |
  this class defines functions an instance has to provide to write it to
  or read it from a HXT-Xml-structure
-}
class XmlRepresentable a where
  -- | render instance to an XmlFilter
  toXml :: a -> HXT.XmlFilter
  -- | try to construct an instance from a single node
  fromXml :: HXT.XmlTree -> Maybe a

getAllFromXml::forall a . (XmlRepresentable a)=>HXT.XmlTrees->[a]
getAllFromXml trees =
  foldl
    (\as xa ->
      case fromXml xa of
        Nothing -> as
        (Just a) -> as ++ [a]
    )
    []
    trees

instance (XmlRepresentable x1, XmlRepresentable x2)=>XmlRepresentable (Either x1 x2) where
  toXml (Left l) = toXml l
  toXml (Right r) = toXml r
  fromXml t =
    case fromXml t of
      Nothing ->
        case fromXml t of
          Nothing -> Nothing
          (Just r) -> Just $ Right r
      (Just l) -> Just $ Left l

-- | XML-representable Structure (convenience class, mostly used via inference)
class XmlRepStructure a where
  toXmlS::a->HXT.XmlFilter
  fromXmlS::HXT.XmlTrees->Maybe a

-- | structure of two sequential lists
instance (XmlRepresentable x1, XmlRepresentable x2)=>XmlRepStructure ([x1], [x2]) where
  toXmlS (t1l, t2l) =
    let
      t1f =
        foldl
          (\ts t ->
            ts +++ toXml t +++ XML.xmlNL
          )
          XML.xmlNullFilter
          t1l
      t2f =
        foldl
          (\ts t ->
            ts +++ toXml t +++ XML.xmlNL
          )
          XML.xmlNullFilter
          t2l
    in
      t1f +++ t2f
  fromXmlS xl =
    let
      (t1l, t2l, _) =
        until
          (\(_, _, (xl', _)) -> null xl' )
          (\(t1l', t2l', (h:xl', get1)) ->
            if get1
              then
                case fromXml h of
                  Nothing -> (t1l', t2l', (h:xl', False))
                  (Just t1) -> (t1l' ++ [t1::x1], t2l', (xl', get1))
              else
                case fromXml h of
                  Nothing -> (t1l', t2l', ([], get1))
                  (Just t2) -> (t1l', t2l' ++ [t2::x2], (xl', get1))

          )
          ([],[],(XML.applyXmlFilter HXT.isXTag xl, True))
    in
      Just (t1l, t2l)

-- | structure of a tupel-list
instance (XmlRepresentable x1, XmlRepresentable x2) => XmlRepStructure [(x1, x2)] where
  toXmlS tl =
    foldl
      (\xs (t1,t2) ->
        xs +++ toXml t1 +++ toXml t2 +++ XML.xmlNL
      )
      XML.xmlNullFilter
      tl
  fromXmlS xl =
    let
      (l, _) =
        until
          (\(_, xl') -> length xl' < 2)
          (\(l', (x1:x2:xr)) ->
            case (fromXml x1, fromXml x2) of
              (Just t1, Just t2) ->
                (l' ++ [(t1, t2)], xr)
              _ -> (l', [])
          )
          ([], xl)
    in
      Just l

-- | Any list of XmlRepresentable-instances can be written in sequence
instance (XmlRepresentable x)=>XmlRepStructure [x] where
  toXmlS tl =
    foldl
      (\ts t ->
        ts +++ toXml t +++ XML.xmlNL
      )
      XML.xmlNullFilter
      tl
  fromXmlS = Just . getAllFromXml

-- | OMDoc
instance XmlRepresentable OMDoc where
  toXml o =
    HXT.etag "omdoc"
      += (
        HXT.sattr "xmlns" "http://www.mathweb.org/omdoc"
        +++
        XML.qualattr "xml" "id" (omdocId o)
        +++
        foldl
          (\ts t ->
            ts +++ XML.xmlNL +++ toXml t
          )
          XML.xmlNullFilter
          (omdocTheories o)
        +++
        foldl
          (\is i ->
            is +++ XML.xmlNL +++ toXml i
          )
          XML.xmlNullFilter
          (omdocInclusions o)
      )
  fromXml t =
    case (HXT.isTag "omdoc" t) of
      [] -> Nothing
      _ ->
        let
          children = HXT.getChildren t
          ids = HXT.xshow $ XML.getQualValue "xml" "id" t
          thes =
            getAllFromXml children
          incs =
            getAllFromXml children
        in
          Just $ OMDoc ids thes incs

-- | Theory
instance XmlRepresentable Theory where
  toXml the =
    let
      tId = theoryId the
      (mTheoryPres, _, trempres) =
        until
          (\(_, rp, _) -> null rp)
          (\(_, (p:pr), rl) ->
            if tId == (presentationForId p)
              then
                (Just p, [], rl ++ pr)
              else
                (Nothing, pr, rl ++ [p])
          )
          (Nothing, (theoryPresentations the), [])

      (conx, conrempres) =
        foldl
          (\(cx, rp) con ->
            let
              presnames =
                getIdsForPresentation con
              (thispres, rempres) =
                List.partition
                  (\pres ->
                    elem (presentationForId pres) presnames
                  )
                  rp
            in
              (
                cx
                +++
                toXml con
                +++
                toXmlS thispres
                , rempres
              )
          )
          (XML.xmlNullFilter, trempres)
          (theoryConstitutives the)
    in
      HXT.etag "theory"
        += (
          XML.qualattr "xml" "id" (theoryId the)
          +++
          case theoryComment the of
            Nothing -> XML.xmlNullFilter
            (Just s) -> HXT.cmt s +++ XML.xmlNL
          +++
          (
            case mTheoryPres of
              Nothing -> XML.xmlNullFilter
              (Just p) -> toXml p
          )
          +++
          conx
          +++
          toXmlS conrempres
        )
  fromXml t =
    case (HXT.isTag "theory") t of
      [] -> Nothing
      _ ->
        let
          comments = HXT.getXCmt t
          tcom =
            case trim (HXT.xshow comments) of
              [] -> Nothing
              cs -> Just cs
          children = HXT.getChildren t
          ids = HXT.xshow $ XML.getQualValue "xml" "id" t
          cons = getAllFromXml children
          pres =
            getAllFromXml children
        in
          Just $ (Theory ids cons pres tcom)

-- | Imports
instance XmlRepresentable Imports where
  toXml imp =
    HXT.etag "imports"
      += (
        HXT.sattr "from" (showURI $ importsFrom imp)
        +++
        (
          case (importsId imp) of
            (Just i) -> XML.qualattr "xml" "id" i
            _ -> XML.xmlNullFilter
        )
{-        +++
        (
          case importsMorphism imp of
            Nothing -> XML.xmlNullFilter
            (Just m) ->
              case morphismHiding m of
                [] -> XML.xmlNullFilter
                h -> HXT.sattr "hiding" (List.intercalate " " h)
{-
          if null (importsHiding imp)
            then
              XML.xmlNullFilter
            else
              HXT.sattr "hiding" (List.intercalate " " (importsHiding imp))
-}
        )-}
        +++
        (
          HXT.sattr
            "type"
            (
              case (importsType imp) of
                ITLocal -> "local"
                ITGlobal -> "global"
            )
        )
        +++
        (
          case (importsConservativity imp) of
            CNone -> XML.xmlNullFilter
            c -> HXT.sattr "conservativity" (show c)
        )
        +++
        (
          case (importsMorphism imp) of
            Nothing ->
              XML.xmlNullFilter
            (Just m) -> XML.xmlNL +++ toXml m +++ XML.xmlNL
        )
      )
  fromXml t =
    case (HXT.isTag "imports") t of
      [] -> Nothing
      _ ->
        let
          froms = HXT.xshow $ HXT.getValue "from" t
          mfromuri =
            if length froms < 1
              then
                Nothing
              else
                URI.parseURIReference froms
{-          hidings =
            filter
              (not . null)
              $
              map
                trim
                  $
                  Util.explode
                    " "
                    $
                    HXT.xshow
                      $
                      HXT.getValue "hiding" t -}
          mid =
            case HXT.xshow $ XML.getQualValue "xml" "id" t of
              [] -> Nothing
              s -> Just s
          itype =
            case map toLower $ HXT.xshow $ HXT.getValue "type" t of
              [] -> ITGlobal
              "global" -> ITGlobal
              "local" -> ITLocal
              u -> trace ("Unknown Import-Type : " ++ u) ITGlobal
          mm =
            case (HXT.getChildren .> HXT.isTag "morphism") t of
              [] -> Nothing
              (xm:_) -> fromXml xm
          conss = HXT.xshow $ HXT.getValue "conservativity" t
          cons =
            case readsPrec 0 conss of
              [] -> CNone
              ((c,_):_) -> c
        in
          case mfromuri of
            Nothing ->
              trace ("No 'from' in Imports!") Nothing
            (Just u) ->
              Just $ Imports u mm mid itype cons

-- | Use
instance XmlRepresentable Use where
  toXml u =
    HXT.etag "use"
      += (
        HXT.sattr "format" (useFormat u)
        +++
        HXT.txt (useValue u)
      )
  fromXml t =
    case (HXT.isTag "use") t of
      [] -> Nothing
      _ ->
        let
          formats = HXT.xshow $ HXT.getValue "format" t
          values = HXT.xshow $ HXT.getChildren t
        in
          Just $ Use formats values

-- | Presentation
instance XmlRepresentable Presentation where
  toXml pres =
    let
      xuses =
        if length (presentationUses pres) == 0
          then
            XML.xmlNullFilter
          else
            foldl
              (\us u ->
                us +++ toXml u +++ XML.xmlNL
              )
              XML.xmlNL
              (presentationUses pres)
    in
      HXT.etag "presentation"
        += (
          HXT.sattr "for" ("#" ++ (presentationForId pres))
          +++
          (
            case (presentationSystem pres) of
              Nothing -> XML.xmlNullFilter
              (Just sys) -> HXT.sattr "system" sys
          )
          +++
          xuses
        )
  fromXml t =
    case (HXT.isTag "presentation") t of
      [] -> Nothing
      _ ->
        let
          fors' = HXT.xshow $ HXT.getValue "for" t
          fors =
            case fors' of
              [] -> trace ("Missing 'for' attribute in presentation...") ""
              ('#':rid) -> rid
              s -> trace ("Presentation 'for' attribute is no omdocref...") s
          systems = case HXT.xshow $ HXT.getValue "system" t of
            [] -> Nothing
            s -> Just s
          uses =
            getAllFromXml (HXT.getChildren t)
        in
          Just $ Presentation fors systems uses

-- | Symbol
instance XmlRepresentable Symbol where
  toXml s =
    HXT.etag "symbol"
      += (
        HXT.sattr "role" (show $ symbolRole s)
        +++
        HXT.sattr "name" (symbolId s)
        +++
        (
          case (symbolGeneratedFrom s) of
            Nothing -> XML.xmlNullFilter
            (Just g) ->
              HXT.sattr "generated-from" g
        )
        +++
        (
          case (symbolType s) of
            Nothing -> XML.xmlNullFilter
            (Just t) ->
              XML.xmlNL
              +++
              toXml t
              +++
              XML.xmlNL
        )
      )
  fromXml t =
    case (HXT.isTag "symbol") t of
      [] -> Nothing
      _ ->
        let
          roles = HXT.xshow $ HXT.getValue "role" t
          names = HXT.xshow $ HXT.getValue "name" t
          ids = HXT.xshow $ XML.getQualValue "xml" "id" t
          sname =
            case names of
              [] -> ids
              _ -> names
          mgf =
            case HXT.xshow $ HXT.getValue "generated-from" t of
              [] -> Nothing
              gf -> Just gf
        in
          case readsPrec 0 roles of
            [] ->
              if List.isPrefixOf "ymmud" (reverse sname)
                then
                  Nothing
                else
                  trace ("Unknown role \"" ++ roles ++ "\" for symbol " ++ sname)
              Nothing
            (sr,_):_ ->
              let
                typechilds = (HXT.getChildren .> HXT.isTag "type") t
              in
                case typechilds of
                  [] -> Just $ Symbol mgf sname sr Nothing
                  _ ->
                    case fromXml (head typechilds) of
                      Nothing -> trace ("cant parse type...") Nothing
                      jty -> Just $ Symbol mgf sname sr jty

-- | Type
instance XmlRepresentable Type where
  toXml t =
    HXT.etag "type"
      += (
        (
          case typeSystem t of
            Nothing -> XML.xmlNullFilter
            (Just ts) -> HXT.sattr "system" (showURI ts)
        )
        +++
        XML.xmlNL
        +++
        toXml (typeOMDocMathObject t)
        +++
        XML.xmlNL
      )
  fromXml t =
    case (HXT.isTag "type") t of
      [] -> Nothing
      _ ->
        let
          systems = HXT.xshow $ HXT.getValue "system" t
          omchilds =
            (
              HXT.getChildren .>
                (
                  HXT.isTag "OMOBJ"
                  +++
                  HXT.isTag "math"
                  +++
                  HXT.isTag "legacy"
                )
            ) t
        in
          case omchilds of
            [] -> trace ("No Math-Object in type!") Nothing
            _ ->
              case fromXml (head omchilds) of
                Nothing -> trace "error parsing omobj..." Nothing
                (Just omobj) ->
                  let
                    typebody = (\u -> Type { typeSystem = u, typeOMDocMathObject = omobj })
                  in
                    if length systems > 0
                      then
                        case URI.parseURIReference systems of
                          Nothing -> trace ("Error parsing system-URI") Nothing
                          jsuri -> Just $ typebody jsuri
                      else
                        Just $ typebody Nothing

-- | Any Constitutive
instance XmlRepresentable Constitutive where
  toXml (CAx ax) = toXml ax
  toXml (CDe de) = toXml de
  toXml (CSy sy) = toXml sy
  toXml (CIm im) = toXml im
  toXml (CAd ad) = toXml ad
  toXml (CCo { conComCmt = cmt, conComCon = con }) =
    HXT.cmt cmt +++ XML.xmlNL +++ (toXml con)
  fromXml t =
    case fromXml t of
      (Just a) -> Just $ CAx a
      Nothing ->
        case fromXml t of
          (Just d) -> Just $ CDe d
          Nothing ->
            case fromXml t of
              (Just s) -> Just $ CSy s
              Nothing ->
                case fromXml t of
                  (Just i) -> Just $ CIm i
                  Nothing ->
                    case fromXml t of
                      (Just a) -> Just $ CAd a
                      Nothing -> Nothing

-- | Axiom
instance XmlRepresentable Axiom where
  toXml axiom =
    HXT.etag "axiom"
      += (
        XML.qualattr "xml" "id" (axiomName axiom)
        +++
        (
          if null $ axiomCMPs axiom
            then
              XML.xmlNullFilter
            else
              toXmlS (axiomCMPs axiom)
        )
        +++
        (
          if null $ axiomFMPs axiom
            then
              XML.xmlNullFilter
            else
              toXmlS (axiomFMPs axiom)
        )
      )
  fromXml t =
    case (HXT.isTag "axiom") t of
      [] -> Nothing
      _ ->
        let
          ids = HXT.xshow $ XML.getQualValue "xml" "id" t
          children = HXT.getChildren t
          cmps = getAllFromXml children
          fmps = getAllFromXml children
        in
          case ids of
            [] -> trace "no id for axiom!" Nothing
            _ -> Just $ Axiom ids cmps fmps

-- | CMP
instance XmlRepresentable CMP where
  toXml cmp =
    HXT.etag "CMP"
      += (
        XML.xmlNL
        +++
        toXml (cmpContent cmp)
      )
  fromXml t =
    case (HXT.isTag "CMP") t of
      [] -> Nothing
      _ -> Just $ CMP $ MTextText $ HXT.xshow $ HXT.getChildren t

-- | FMP
instance XmlRepresentable FMP where
  toXml fmp =
    HXT.etag "FMP"
      += (
        (
          case fmpLogic fmp of
            Nothing -> XML.xmlNullFilter
            (Just l) -> HXT.sattr "logic" l
        )
        +++
        case fmpContent fmp of
          (Left o) -> toXml o
          (Right ac) -> toXmlS ac
      )
  fromXml t =
    case (HXT.isTag "FMP") t of
      [] -> Nothing
      _ ->
        let
          logics = HXT.xshow $ HXT.getValue "logic" t
          logic = if length logics < 1 then Nothing else Just logics
          children = HXT.getChildren t
          omchildren = (HXT.getChildren .> HXT.isTag "OMOBJ") t
        in
          case children of
            [] -> trace ("empty FMP!") Nothing
            _ ->
              case omchildren of
                [] ->
                  case fromXmlS children of
                    Nothing -> trace "Wierd!" Nothing
                    (Just ac) -> Just $ FMP logic (Right ac)
                _ ->
                  case fromXml $ head omchildren of
                    Nothing -> Nothing
                    (Just o) -> Just $ FMP logic (Left o)

-- | Assumption
instance XmlRepresentable Assumption where
  toXml _ = HXT.etag "assumption"
  fromXml t =
    case (HXT.isTag "assumption") t of
      [] -> Nothing
      _ -> Just Assumption

-- | Conclusion
instance XmlRepresentable Conclusion where
  toXml _ = HXT.etag "conclusion"
  fromXml t =
    case (HXT.isTag "conclusion") t of
      [] -> Nothing
      _ -> Just Conclusion

-- | Definition
instance XmlRepresentable Definition where
  toXml def =
    HXT.etag "symbol"
      += (
        XML.qualattr "xml" "id" ((definitionId def) ++ "-dummy")
      )
    +++
    XML.xmlNL
    +++
    HXT.etag "definition"
      += (
        XML.qualattr "xml" "id" (definitionId def)
        +++
        HXT.sattr "for" ((++) "#" $ (++) (definitionId def) "-dummy" )
        +++
        HXT.sattr "type" "implicit"
        +++
        toXmlS (definitionCMPs def)
        +++
        toXmlS (definitionFMPs def)

      )
  fromXml t =
    case (HXT.isTag "definition") t of
      [] -> Nothing
      _ ->
        let
          ids = HXT.xshow $ XML.getQualValue "xml" "id" t
          fors =
            case HXT.xshow $ HXT.getValue "for" t of
              '#':r -> r
              r -> r
          ids' = case ids of
                   [] -> fors
                   _ -> ids
          children = HXT.getChildren t
          cmps = getAllFromXml children
          fmps = getAllFromXml children
        in
          case ids' of
            [] -> trace "no id in definition" Nothing
            _ -> Just $ Definition ids' cmps fmps

-- | SortDef
instance XmlRepresentable SortDef where
  toXml sd =
    HXT.etag "sortdef"
      += (
        HXT.sattr "name" (sortDefName sd)
        +++
        HXT.sattr "role" (show $ sortDefRole sd)
        +++
        HXT.sattr "type" (show $ sortDefType sd)
        +++
        toXmlS (sortDefConstructors sd)
        +++
        toXmlS (sortDefInsorts sd)
        +++
        toXmlS (sortDefRecognizers sd)
      )
  fromXml t =
    case HXT.isTag "sortdef" t of
      [] -> Nothing
      _ ->
        let
          sdNameS = HXT.xshow $ HXT.getValue "name" t
          sdRoleS = HXT.xshow $ HXT.getValue "role" t
          sdTypeS = HXT.xshow $ HXT.getValue "type" t
          sdRole =
            case sdRoleS of
              [] -> SRSort
              _ ->
                case readsPrec 0 sdRoleS of
                  [] -> trace ("Invalid Role : \"" ++ sdRoleS ++ "\"") SRSort
                  ((sdR,_):_) -> sdR
          sdType =
            case sdTypeS of
              [] -> STFree
              _ ->
                case readsPrec 0 sdTypeS of
                  [] -> trace ("Invalid Type : \"" ++ sdTypeS ++ "\"") STFree
                  ((sdT,_):_) -> sdT
          xchildren = HXT.getChildren t
          cons = getAllFromXml xchildren
          insorts = getAllFromXml xchildren
          recognizers = getAllFromXml xchildren
        in
          case sdNameS of
            [] -> trace ("SortDef for Nothing!") Nothing
            _ ->
              Just $ SortDef sdNameS sdRole sdType cons insorts recognizers

-- | Constructor
instance XmlRepresentable Constructor where
  toXml con =
    HXT.etag "constructor"
      += (
        HXT.sattr "name" (constructorName con)
        +++
        HXT.sattr "role" (show $ constructorRole con)
        +++
        (
          foldl
            (\cx a ->
              cx
              +++
              HXT.etag "argument"
                += (
                  toXml a
                )
              +++
              XML.xmlNL
            )
            XML.xmlNullFilter
            (constructorArguments con)
        )
      )
  fromXml t =
    case HXT.isTag "constructor" t of
      [] -> Nothing
      _ ->
        let
          cNameS = HXT.xshow $ HXT.getValue "name" t
          cRoleS = HXT.xshow $ HXT.getValue "role" t
          cRole =
            case cRoleS of
              [] -> SRObject
              _ ->
                case readsPrec 0 cRoleS of
                  [] -> trace ("Invalid Role : \"" ++ cRoleS ++ "\"") SRObject
                  ((cR,_):_) -> cR
          argsxml = (HXT.getChildren .> HXT.isTag "argument") t
          args =
            foldl
              (\as at ->
                let
                  typechilds = (HXT.getChildren .> HXT.isTag "type") at
                in
                  case typechilds of
                    [] -> trace ("no type in argument!") as
                    [tc] ->
                      case fromXml tc of
                        Nothing -> trace ("could not parse type!") as
                        (Just ty) -> as ++ [ty]
                    (tc:_) ->
                      case fromXml tc of
                        Nothing -> trace ("could not parse type and there are more!") as
                        (Just ty) -> trace ("more than one type in argument!") (as ++ [ty])
              )
              []
              argsxml
        in
          case cNameS of
            [] -> trace ("No Name for Constructor!") Nothing
            _ -> Just $ Constructor cNameS cRole args

-- | Insort
instance XmlRepresentable Insort where
  toXml i =
    HXT.etag "insort"
      += (
        HXT.sattr "for" (showURI $ insortFor i)
      )
  fromXml t =
    case HXT.isTag "insort" t of
      [] -> Nothing
      _ ->
        let
          forS = HXT.xshow $ HXT.getValue "for" t
        in
          case URI.parseURIReference forS of
            Nothing -> trace ("No for...") Nothing
            (Just u) -> Just $ Insort u

-- | Recognizer
instance XmlRepresentable Recognizer where
  toXml i =
    HXT.etag "recognizer"
      += (
        HXT.sattr "name" (recognizerName i)
      )
  fromXml t =
    case HXT.isTag "recognizer" t of
      [] -> Nothing
      _ ->
        let
          nameS = HXT.xshow $ HXT.getValue "name" t
        in
          case nameS of
            "" -> trace ("No name...") Nothing
            _ -> Just $ Recognizer nameS

-- | ADT
instance XmlRepresentable ADT where
  toXml adt =
    HXT.etag "adt"
      += (
        (
          case adtId adt of
            Nothing -> XML.xmlNullFilter
            (Just aid) -> XML.qualattr "xml" "id" aid
        )
        +++
        (
          toXmlS (adtSortDefs adt)
        )
      )
  fromXml t =
    case (HXT.isTag "adt") t of
      [] -> Nothing
      _ ->
        let
          xchildren = HXT.getChildren t
          maid =
            case HXT.xshow $ XML.getQualValue "xml" "id" t of
              [] -> Nothing
              s -> Just s
          sds = getAllFromXml xchildren
        in
          Just $ ADT maid sds

-- | Inclusion
instance XmlRepresentable Inclusion where
  toXml ti@(TheoryInclusion {}) =
    HXT.etag "theory-inclusion"
      += (incBody ti)
  toXml ai@(AxiomInclusion {}) =
    HXT.etag "axiom-inclusion"
      += (incBody ai)
  fromXml t =
    case (HXT.isTag "axiom-inclusion") t of
      [] ->
        case (HXT.isTag "theory-inclusion") t of
          [] -> Nothing
          _ ->
            case getIncBody of
              Nothing -> Nothing
              (Just (from,to,mm,mi,c)) -> Just $ TheoryInclusion from to mm mi c
      _ ->
        case getIncBody of
          Nothing -> Nothing
          (Just (from,to,mm,mi,c)) -> Just $ AxiomInclusion from to mm mi c
    where
    getIncBody::Maybe (URI.URI, URI.URI, Maybe Morphism, Maybe XmlId, Conservativity)
    getIncBody =
      let
        froms = HXT.xshow $ HXT.getValue "from" t
        tos = HXT.xshow $ HXT.getValue "to" t
        fromuri = URI.parseURIReference froms
        touri = URI.parseURIReference tos
        ids = HXT.xshow $ XML.getQualValue "xml" "id" t
        mid = if (length ids) > 0 then Just ids else Nothing
        conss = HXT.xshow $ HXT.getValue "conservativity" t
        cons =
          case readsPrec 0 conss of
            [] -> CNone
            ((c,_):_) -> c
        mm = case (HXT.getChildren .> HXT.isTag "morphism") t of
          [] -> Nothing
          (xm:_) -> fromXml xm
      in
        if ( (length froms) < 1 || (length tos) < 1 )
          then
            trace
              ("No 'from' or no 'to' in Inclusion!")
              Nothing
          else
            case (fromuri, touri) of
              (Just fu, Just tu) ->
                Just (fu, tu, mm, mid, cons)
              _ -> trace ("Error parsing inclusion source or target!") Nothing

-- | used by Inclusion
incBody::
    Inclusion
  ->HXT.XmlFilter
incBody tinc =
  (
    HXT.sattr "from" (showURI $ inclusionFrom tinc)
    +++
    HXT.sattr "to" (showURI $ inclusionTo tinc)
    +++
    (
      case (inclusionId tinc) of
        (Just i) -> XML.qualattr "xml" "id" i
        _ -> XML.xmlNullFilter
    )
-- conservativity has been removed from OMDoc-RNG
{-
    +++
    (
      case (inclusionConservativity tinc) of
        CNone -> XML.xmlNullFilter
        c -> HXT.sattr "conservativity" (show c)
    )
-}
    +++
    (
      case (inclusionMorphism tinc) of
        (Just m) -> XML.xmlNL +++ toXml m +++ XML.xmlNL
        _ -> XML.xmlNullFilter
    )
  )

-- | Mathematical Text
instance XmlRepresentable MText where
  toXml (MTextText x) = HXT.txt x
  toXml (MTextTerm x) = HXT.etag "term" += (HXT.txt x)
  toXml (MTextPhrase x) = HXT.etag "phrase" += (HXT.txt x)
  toXml (MTextOM omobj) = toXml omobj
  fromXml t =
    case (HXT.isTag "term") t of
      [] ->
        case (HXT.isTag "phrase") t of
          [] ->
            case (HXT.isTag "OMOBJ") t of
              [] -> Nothing
              _ ->
                case fromXml t of
                  Nothing -> Nothing
                  (Just omobj) -> Just $ MTextOM omobj
          _ ->
            Just $ MTextPhrase (HXT.xshow $ HXT.getChildren t)
      _ ->
        Just $ MTextTerm (HXT.xshow $ HXT.getChildren t)

-- | Math Object
instance XmlRepresentable OMDocMathObject where
  toXml (OMOMOBJ omobj) = toXml omobj
  toXml (OMLegacy x) = HXT.etag "legacy" += (HXT.txt x)
  toXml (OMMath x) = HXT.etag "math" += (HXT.txt x)
  fromXml t =
    case fromXml t of
      (Just x) -> Just $ OMOMOBJ x
      _ ->
        case (HXT.isTag "legacy") t of
          [] ->
            case (HXT.isTag "math") t of
              [] -> Nothing
              _ -> Just $ OMMath (HXT.xshow $ HXT.getChildren t)
          _ ->
            Just $ OMLegacy (HXT.xshow $ HXT.getChildren t)

-- | OpenMath Object
instance XmlRepresentable OMObject where
  toXml (OMObject e) =
    HXT.etag "OMOBJ"
      +=(
        HXT.sattr "xmlns" "http://www.openmath.org/OpenMath"
        +++
        XML.xmlNL
        +++
        toXml e
        +++
        XML.xmlNL
      )
  fromXml t =
    case (HXT.isTag "OMOBJ") t of
      [] -> Nothing
      _ ->
        case (HXT.getChildren .> HXT.isXTag) t of
          [] -> trace ("Empty OMOBJ!") Nothing
          xoe ->
            case fromXml (head xoe) of
              Nothing -> Nothing
              (Just e) -> Just $ OMObject e

-- | OMS
instance XmlRepresentable OMSymbol where
  toXml oms =
    HXT.etag "OMS"
      += (
        (
        case omsCDBase oms of
          Nothing ->
            XML.xmlNullFilter
          (Just uri) ->
            HXT.sattr "cdbase" (showURI uri)
        )
        +++ HXT.sattr "cd" (omsCD oms)
        +++ HXT.sattr "name" (omsName oms)
      )
  fromXml t =
    case (HXT.isTag "OMS") t of
      [] -> Nothing
      _ ->
        let
          cdbases = HXT.xshow $ getValue "cdbase" t
          cds = HXT.xshow $ getValue "cd" t
          names = HXT.xshow $ getValue "name" t
          mref =
            case cdbases of
              [] ->
                Nothing
              s ->
                case URI.parseURIReference s of
                  Nothing ->
                    trace
                      ("Invalid CDBase in OMS!")
                      Nothing
                  mValidURI ->
                    mValidURI
        in
          Just $ OMS mref cds names

-- | OMI
instance XmlRepresentable OMInteger where
  toXml omi =
    HXT.etag "OMI"
      += ( HXT.txt (show $ omiInt omi) )
  fromXml t =
    case (HXT.isTag "OMI") t of
      [] -> Nothing
      _ ->
        let
          content = HXT.xshow $ HXT.getChildren t
        in
          case readsPrec 0 content of
            [] ->
              trace
                ("Invalid Integer in OMI : \"" ++ content ++ "\"!")
                Nothing
            ((i,_):_) -> Just $ OMI i

-- | A Variable (OMV, OMATTR)
instance XmlRepresentable OMVariable where
  toXml (OMVS omv) = toXml omv
  toXml (OMVA omattr) = toXml omattr
  fromXml t =
    case (HXT.isTag "OMV") t of
      [] ->
        case (HXT.isTag "OMATTR") t of
          [] -> Nothing
          _ ->
            case fromXml t of
              Nothing -> Nothing
              (Just omattr) -> Just (OMVA omattr)
      _ ->
        case fromXml t of
          Nothing -> Nothing
          (Just omv) -> Just (OMVS omv)

-- | OMV
instance XmlRepresentable OMSimpleVariable where
  toXml omv =
    HXT.etag "OMV"
      += (HXT.sattr "name" (omvName omv))
  fromXml t =
    case (HXT.isTag "OMV") t of
      [] -> Nothing
      _ ->
        let
          names = HXT.xshow $ getValue "name" t
        in
          if null names
            then
              trace
                ("Variable with empty name : \"" ++ (HXT.xshow [t]) ++ "\"!")
                Nothing
            else
              Just $ OMV names

-- | OMATTR
instance XmlRepresentable OMAttribution where
  toXml attr =
    HXT.etag "OMATTR"
      += ( toXml (omattrATP attr) +++ toXml (omattrElem attr) )
  fromXml t =
    case (HXT.isTag "OMATTR") t of
      [] -> Nothing
      _ ->
        case (HXT.getChildren .> HXT.isXTag) t of
          [xatp, xe] ->
            case (fromXml xatp, fromXml xe) of
              (Just atp, Just e) -> Just $ OMATTR atp e
              _ -> trace ("Error processing OMATTR!") Nothing
          _ -> trace ("Invalid OMATTR-Content!") Nothing

-- | OMATP
instance XmlRepresentable OMAttributionPart where
  toXml atp =
    HXT.etag "OMATP"
      += (
        foldl
          (\a (s, e) ->
            a +++ (toXml s) +++ (toXml e) +++ XML.xmlNL
          )
          XML.xmlNullFilter
          (omatpAttribs atp)
      )
  fromXml t =
    case (HXT.isTag "OMATP") t of
      [] -> Nothing
      _ ->
        let
          attribs =
            foldl
              (\a (xs, xe) ->
                case (fromXml xs, fromXml xe) of
                  (Just s, Just e) ->
                    a ++ [(s, e)]
                  _ ->
                    trace
                      ("Error processing attribution...")
                      a
              )
              []
              (Util.makeTupel ( (HXT.getChildren .> HXT.isXTag) t ) )
        in
          Just $ OMATP attribs

-- | OMBVAR
instance XmlRepresentable OMBindingVariables where
  toXml ombvar =
    HXT.etag "OMBVAR"
      += (
        foldl
          (\vs v ->
            vs +++ toXml v
          )
          XML.xmlNullFilter
          (ombvarVars ombvar)
      )
  fromXml t =
    case (HXT.isTag "OMBVAR") t of
      [] -> Nothing
      _ ->
        let
          xchildren = (HXT.getChildren .> HXT.isXTag) t
          vars =
            foldl
              (\vs xv ->
                case fromXml xv of
                  Nothing ->
                    trace
                      ("error processing variable in binding")
                      vs
                  (Just v) -> vs ++ [v]
              )
              []
              xchildren
        in
          Just $ OMBVAR vars

-- | OMB
instance XmlRepresentable OMBase64 where
  toXml omb =
    HXT.etag "OMB"
      += ( HXT.txt (Base64.encode (ombContent omb)) )
  fromXml t =
    case (HXT.isTag "OMB") t of
      [] -> Nothing
      _ -> Just $ OMB $ Base64.decode $ HXT.xshow $ HXT.getChildren t

-- | OMSTR
instance XmlRepresentable OMString where
  toXml omstr =
    HXT.etag "OMSTR"
      += ( HXT.txt (omstrText omstr) )
  fromXml t =
    case (HXT.isTag "OMSTR") t of
      [] -> Nothing
      _ ->
        let
          content = HXT.xshow $ HXT.getChildren t
        in
          Just $ OMSTR content

-- | OMF
instance XmlRepresentable OMFloat where
  toXml omf =
    HXT.etag "OMF"
      += ( HXT.sattr "dec" (show (omfFloat omf) ) )
  fromXml t =
    case (HXT.isTag "OMF") t of
      [] -> Nothing
      _ ->
        let
          deccontent = HXT.xshow $ HXT.getValue "dec" t
          hexcontent = HXT.xshow $ HXT.getValue "hex" t
          dec = Numeric.readSigned Numeric.readFloat deccontent
          hex = Numeric.readSigned Numeric.readHex hexcontent
          decerror = ("error parsing float : \"" ++ deccontent ++ "\"")
          hexerror = ("error parsing float : \"" ++ hexcontent ++ "\"")

        in
          if length deccontent > 0
            then
              case dec of
                [] -> trace decerror Nothing
                (d,r):_ ->
                  case r of
                    [] -> Just $ OMF d
                    _ -> trace decerror Nothing
            else
              if length hexcontent > 0
                then
                  case hex of
                    [] -> trace hexerror Nothing
                    (h,r):_ ->
                      case r of
                        [] -> Just $ OMF (fromIntegral (h::Integer))
                        _ -> trace hexerror Nothing
                else
                  trace ("No Number!") Nothing

-- | OMA
instance XmlRepresentable OMApply where
  toXml oma =
    HXT.etag "OMA"
      += (
        foldl
          (\es e ->
            es +++ toXml e
          )
          XML.xmlNullFilter
          (omaElements oma)
        )
  fromXml t =
    case (HXT.isTag "OMA") t of
      [] -> Nothing
      _ ->
        let
          xchildren = (HXT.getChildren .> HXT.isXTag) t
          elems =
            foldl
              (\es xe ->
                case fromXml xe of
                  Nothing -> trace ("error processing OMA Element!") es
                  (Just e) -> es ++ [e]
              )
              []
              xchildren
        in
          Just $ OMA elems

-- | OME
instance XmlRepresentable OMError where
  toXml ome =
    HXT.etag "OME"
      += (
        toXml (omeSymbol ome) +++ XML.xmlNL
        +++
        foldl
          (\es e ->
            es +++ toXml e +++ XML.xmlNL
          )
          XML.xmlNullFilter
          (omeExtra ome)
      )
  fromXml t =
    case (HXT.isTag "OME") t of
      [] -> Nothing
      _ ->
        let
          xchildren = (HXT.getChildren .> HXT.isXTag) t
        in
          case xchildren of
            [] -> trace ("No children in OME!") Nothing
            (xs:xel) ->
              let
                elems =
                  foldl
                    (\es xe ->
                      case fromXml xe of
                        Nothing -> trace ("error reading error element!") es
                        (Just e) -> es ++ [e]
                    )
                    []
                    xel
              in
                case fromXml xs of
                  (Just (oms@(OMS {}))) -> Just $ OME oms elems
                  _ -> trace ("OME does not start with OMS-element!") Nothing

-- | OMR
instance XmlRepresentable OMReference where
  toXml omr =
    HXT.etag "OMR"
      += (HXT.sattr "href" (showURI (omrHRef omr)))
  fromXml t =
    case (HXT.isTag "OMR") t of
      [] -> Nothing
      _ ->
        let
          uris = HXT.xshow $ HXT.getValue "href" t
        in
          case URI.parseURIReference uris of
            Nothing -> trace ("Error parsing OMR-URI!") Nothing
            (Just uri) -> Just $ OMR uri

-- | OMBIND
instance XmlRepresentable OMBind where
  toXml ombind =
    HXT.etag "OMBIND"
      += (
        toXml (ombindBinder ombind) +++ XML.xmlNL
        +++
        toXml (ombindVariables ombind) +++ XML.xmlNL
        +++
        toXml (ombindExpression ombind)
      )
  fromXml t =
    case (HXT.isTag "OMBIND") t of
      [] -> Nothing
      _ ->
        let
          xchildren = (HXT.getChildren .> HXT.isXTag) t
        in
          case xchildren of
            [xbinder, xvars, xexpr] ->
              case (fromXml xbinder, fromXml xvars, fromXml xexpr) of
                (Just binder, Just vars, Just expr) ->
                  Just $ OMBIND binder vars expr
                _ -> trace ("error reading OMBIND!") Nothing
            _ -> trace ("invalid OMBIND-content!") Nothing

-- | Any OpenMath Element
instance XmlRepresentable OMElement where
  toXml (OMES s) = toXml s
  toXml (OMEV v) = toXml v
  toXml (OMEI i) = toXml i
  toXml (OMEB b) = toXml b
  toXml (OMESTR s) = toXml s
  toXml (OMEF f) = toXml f
  toXml (OMEA a) = toXml a
  toXml (OMEBIND b) = toXml b
  toXml (OMEE e) = toXml e
  toXml (OMEATTR a) = toXml a
  toXml (OMER r) = toXml r
  toXml (OMEC me c) =
    case me of
      Nothing ->
        HXT.cmt c
      (Just e) ->
        (HXT.cmt c) +++ XML.xmlNL +++ (toXml e)
  fromXml t =
    case HXT.getNode t of
      (HXT.XTag qn _) ->
        case HXT.localPart qn of
          "OMS" ->
            case fromXml t of
              Nothing -> Nothing
              (Just s) -> Just $ OMES s
          "OMV" ->
            case fromXml t of
              Nothing -> Nothing
              (Just v) -> Just $ OMEV v
          "OMI" ->
            case fromXml t of
              Nothing -> Nothing
              (Just i) -> Just $ OMEI i
          "OMB" ->
            case fromXml t of
              Nothing -> Nothing
              (Just b) -> Just $ OMEB b
          "OMSTR" ->
            case fromXml t of
              Nothing -> Nothing
              (Just s) -> Just $ OMESTR s
          "OMF" ->
            case fromXml t of
              Nothing -> Nothing
              (Just f) -> Just $ OMEF f
          "OMA" ->
            case fromXml t of
              Nothing -> Nothing
              (Just a) -> Just $ OMEA a
          "OMBIND" ->
            case fromXml t of
              Nothing -> Nothing
              (Just b) -> Just $ OMEBIND b
          "OME" ->
            case fromXml t of
              Nothing -> Nothing
              (Just e) -> Just $ OMEE e
          "OMATTR" ->
            case fromXml t of
              Nothing -> Nothing
              (Just a) -> Just $ OMEATTR a
          "OMR" ->
            case fromXml t of
              Nothing -> Nothing
              (Just r) -> Just $ OMER r
          _ -> Nothing
      _ -> Nothing

-- | OMDoc Morphism
instance XmlRepresentable Morphism where
  toXml morphism =
    let
      idattr =
        case morphismId morphism of
          Nothing -> XML.xmlNullFilter
          (Just mid) -> XML.qualattr "xml" "id" mid
      hidingattr =
        if null (morphismHiding morphism)
          then
            XML.xmlNullFilter
          else
            HXT.sattr "hiding" (List.intercalate " " (map (\h -> '#':h) (morphismHiding morphism)))
      baseattr =
        if null (morphismBase morphism)
          then
            XML.xmlNullFilter
          else
            HXT.sattr "base" (List.intercalate " " (map (\h -> '#':h) (morphismBase morphism)))
      requations =
        if null (morphismRequations morphism)
          then
            XML.xmlNullFilter
          else
            foldl
              (\rs (so, to) ->
                rs +++ XML.xmlNL
                +++
                HXT.etag "requation"
                  += (
                    toXml so +++ toXml to
                  )
              )
              XML.xmlNullFilter
              (morphismRequations morphism)
    in
      HXT.etag "morphism"
        += (
          idattr
          +++
          baseattr
          +++
          hidingattr
          +++
          requations
        )
  fromXml t =
    case (HXT.isTag "morphism") t of
      [] -> Nothing
      _ ->
        let
          reconstructIds =
            (\idstring ->
              filter
                (not . null)
                  $
                  map
                    (\s ->
                      case s of
                        '#':r -> r
                        _ -> s
                    )
                    $
                    map
                      trim
                      $
                      Util.explodeNonEsc
                        " "
                        idstring
            )
          mid =
            case HXT.xshow $ XML.getQualValue "xml" "id" t of
              [] -> Nothing
              mids -> Just mids
          hiding = reconstructIds $ HXT.xshow $ getValue "hiding" t
          base = reconstructIds $ HXT.xshow $ getValue "base" t
          xrequations = (HXT.getChildren .> HXT.isTag "requation") t
          requations =
            foldl
              (\r xr ->
                let
                  xomobjs = (HXT.getChildren .> HXT.isXTag) xr
                in
                  case fromXmlS xomobjs of
                    (Just [(o1,o2)]) ->
                      r ++ [ (o1, o2) ]
                    _ -> trace ("error in morphism") r
              )
              []
              xrequations
          morphism = Morphism mid hiding base requations
        in
          Just morphism
