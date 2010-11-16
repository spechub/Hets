{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  luecke@informatik.uni-bremen.de
Stability   :  provisional
Portability :  non-portable (imports Control.Monad.Error)

MMiSSOntology provides the abstract data type for an Ontology
-}

{-
Within the MMiSS project a language for defining and representing
ontologies has been created. In general classes, relations, predicates
and operations between classes, objects and links between objects can
be expressed. Inheritance is possible for classes and
relations. Further details about ontologies in MMiSS are given in the
paper "Semantic Interrelation with Ontologies".

At the moment, the module ist designed for storing ontologies in the
"MMiSS sense". Later on, it should be investigated, if it is
reasonable to adapt the module for OWL or KIF ontologies.

The module defines a data type \tt{MMISSOntology} which stores all
information contained in a MMiSS-Ontology. \tt{emptyMMiSSOntology}
provides a fresh, clean ontology labeld with the delivered name. After
creating an empty ontology, the insertion functions () should be used
to fill the ontology. -}

module Taxonomy.MMiSSOntology
    ( MMiSSOntology
    , ClassName
    , ClassGraph
    , ObjectName
    , SuperClass
    , DefaultText
    , Cardinality
    , SuperRel
    , RelName
    , RelationProperty(..)
    , InsertMode(..)
    , OntoObjectType(..)
    , ClassType(..)
    , weither
    , fromWithError
    , WithError
    , emptyMMiSSOntology
    , insertClass
    , insertObject
    , insertBaseRelation
    , insertRelationType
    , insertLink
    , isComplete
    , exportOWL
    , getOntologyName
    , getRelationNames
    , getClassGraph
    , getRelationGraph
    , hasError
    , hasValue
    , gselName
    , gselType
    , findLNode
    ) where

import Control.Monad.Error ()
import Data.List
import Data.Char (toLower)

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Common.Lib.Graph
import qualified Data.Map as Map
import Common.Taxonomy

type ClassName = String
type ObjectName = String
type SuperClass = String
type DefaultText = String
type Cardinality = String
type SuperRel = String
type RelName = String
type RelationText = String
type AutoInserted = Bool

type WithError = Either String
type ClassGraph = Gr (String, String, OntoObjectType) String

hasError :: String -> WithError a
hasError = Left

hasValue :: a -> WithError a
hasValue = Right

-- | like either
weither :: (String -> b) -> (a -> b) -> WithError a -> b
weither = either

-- | convert to another monad
fromWithError :: (Monad m) => WithError a -> m a
fromWithError = either fail return

data RelationProperty = InversOf String | Functional deriving (Eq, Read, Show)

{--
   AutoInsert: When a new class is to be inserted and the given
               SuperClass is not present in the ontology, it is
               automatically inserted with just it's name.  The caller
               can later on insert the missing class without getting
               an error message (the class information is beeing
               updated).  The same happens if a SuperRelation is not
               present when a new relation is inserted.
   ThrowError: The insertClass or insertRelation function calls will
               throw an error instead of performing an autoinsert.
--}

data InsertMode = AutoInsert | ThrowError deriving (Eq, Read, Show)

data ClassType = SubSort | Predicate deriving (Eq, Read, Show)

data MMiSSOntology = MMiSSOntology
    { getOntologyName :: String
    , classes :: Map.Map String ClassDecl
    , objects :: Map.Map String ObjectDecl
    , relations :: Map.Map String RelationDecl
    , objectLinks :: [ObjectLink]
    , mode :: InsertMode
    , getClassGraph :: ClassGraph
    , getRelationGraph :: Gr String String }

data ClassDecl = ClassDecl
    ClassName
    DefaultText
    [SuperClass]
    [(RelName, [ClassName])]
    AutoInserted
    (Maybe ClassType)

data ObjectDecl = ObjectDecl ObjectName DefaultText ClassName

data RelationDecl = RelationDecl
    RelName
    (Maybe Cardinality)
    RelationText
    [RelationTypeDecl]
    (Maybe SuperRel)
    AutoInserted

data RelationTypeDecl = RelationTypeDecl ClassName ClassName

data ObjectLink = ObjectLink ObjectName ObjectName RelName

emptyMMiSSOntology :: String -> InsertMode -> MMiSSOntology
emptyMMiSSOntology ontoName insertMode = MMiSSOntology
    { getOntologyName = ontoName
    , classes = Map.empty
    , objects = Map.empty
    , relations = Map.empty
    , objectLinks = []
    , mode = insertMode
    , getClassGraph = empty
    , getRelationGraph = empty }

getRelationNames :: MMiSSOntology -> [String]
getRelationNames = Map.keys . relations

insError :: String -> String -> WithError a
insError s r = hasError $ "Insertion of " ++ s ++ r

insErr :: String -> WithError a
insErr str = insError str " doesn't exist in the Ontology.\n"

mkMsgStr :: String -> String -> String -> WithError a
mkMsgStr str nam e = insErr $
    map toLower str ++ ": " ++ nam ++ " -> " ++ str ++ e

writeErr :: String -> String -> WithError a
writeErr str nam = mkMsgStr str nam
    " is properly defined and can't be overridden. (AutoInsert is on).\n"

dupErr :: String -> String -> WithError a
dupErr str nam = mkMsgStr str nam
    " is already defined in Ontology.\n"

insertClass :: MMiSSOntology -> ClassName -> DefaultText -> [SuperClass]
            -> (Maybe ClassType) -> WithError MMiSSOntology
insertClass onto className optText superCs maybeType =
  maybe
    (myInsertClass className optText superCs maybeType)
    ( \ (ClassDecl _ _ _ _ auto _) ->
      case mode onto of
        AutoInsert ->
          if auto
            then myInsertClass className optText superCs maybeType
            else writeErr "Class" className
        _ -> dupErr "Class" className)
    $ Map.lookup className $ classes onto
  where
    myInsertClass cn opt super classType =
      let class1 = (cn, (ClassDecl cn opt super [] False classType))
      in case super of
           []          -> addClasses' [class1] super
           superClasses ->
               let undefSC =
                       filter ( \ sC -> not $ Map.member sC $ classes onto)
                              superClasses
                   sClassDecls =
                       map ( \ sC -> (sC, (ClassDecl sC "" [] []
                                              True Nothing))) undefSC
               in if null undefSC
                then addClasses' [class1] super
                else case mode onto of
                      AutoInsert -> addClasses' (class1 : sClassDecls) super
                      _  -> insErr $ "class: " ++ cn ++
                                     " -> Superclass " ++ show undefSC
    addClasses' :: [(String, ClassDecl)] -> [SuperClass]
                -> WithError MMiSSOntology
    addClasses' cList superCls =
       let g = getClassGraph onto
           newgraph =
               case cList of
               [] -> g
               [(classNam, ClassDecl _ _ _ _ _ cType)] ->
                     let (g1, node1) = getInsNode g classNam cType
                     in foldl (addIsaEdge node1) g1 superCls
               (subClass, ClassDecl _ _ _ _ _ subcType) : _ ->
                   let (g1, node1) = getInsNode g subClass subcType
                   in foldl (insClass node1) g1 superCls
       in hasValue $ (addOnlyClasses onto cList) { getClassGraph = newgraph }
    getInsNode g cl clType =
        maybe (let n = head (newNodes 1 g)
               in (insNode (n,(cl,"", getClassNodeType clType)) g, n))
              (\ node -> (g, node))
              (findLNode g cl)
    insClass node1 g1 sC =
        case getInsNode g1 sC Nothing of
        -- at this place all autoinserted classes have type
        -- Nothing (s. def. of sClassDecls)
        (g2,node2) -> insEdge (node1, node2, "isa") g2
    addIsaEdge node1 g1 =
        maybe g1 (\ sNode -> insEdge (node1, sNode, "isa") g1)
                 . findLNode g1
    getClassNodeType = maybe OntoClass ( \ cType -> case cType of
                               Predicate -> OntoPredicate
                               _ -> OntoClass)

addRelations :: MMiSSOntology -> [(String, RelationDecl)] -> MMiSSOntology
addRelations o rList = o
       { relations = Map.union (relations o) $ Map.fromList rList }

{- | inserts a new Relation into the Ontology. It throws an error if
  the relation name already exists. -}
insertBaseRelation :: MMiSSOntology -> RelName -> DefaultText
                   -> Maybe SuperRel -> Maybe Cardinality
                   -> WithError MMiSSOntology
insertBaseRelation onto relName defText superRel card =
  case Map.lookup relName (relations onto) of
    Nothing -> myInsertRel relName defText superRel card
    Just(RelationDecl _ _ _ _ _ auto) ->
      case mode onto of
        AutoInsert ->
          if auto
            then myInsertRel relName defText superRel card
            else writeErr "Relation" relName
        _ -> dupErr "Relation" relName
  where
    addRels = hasValue . addRelations onto
    myInsertRel rn def super c =
      let rel1 = (rn, (RelationDecl rn c def [] super False))
      in case super of
           Nothing -> addRels [rel1]
           Just superR ->
             if Map.member superR $ relations onto
               then addRels [rel1]
               else case mode onto of
                      AutoInsert ->
                          let rel2 = (superR, (RelationDecl superR Nothing ""
                                               [] Nothing True))
                          in addRels [rel1, rel2]
                      _  -> insErr $ "relation: " ++ rn ++
                                     " -> Superrelation " ++ superR

addOnlyClasses :: MMiSSOntology -> [(String, ClassDecl)] -> MMiSSOntology
addOnlyClasses o cList =
    o { classes = Map.union (classes o) $ Map.fromList cList }

addClasses :: MMiSSOntology -> [(String, ClassDecl)] -> MMiSSOntology
addClasses o cList = (addOnlyClasses o cList)
    { getClassGraph = foldl addClassNodeWithoutDecl (getClassGraph o) cList }

insertClasses :: MMiSSOntology -> ClassName -> String
              -> WithError MMiSSOntology
insertClasses o className str = case Map.lookup className $ classes o of
    Nothing -> case mode o of
        AutoInsert -> return $ addClasses o
             [(className, ClassDecl className "" [] [] True Nothing)]
        _ -> insErr $ str ++ className
    _ -> return o

{- | inserts a new RelationType declaration into the Ontology. It
  throws an error if the relation name doesn't exist. -}
insertRelationType :: MMiSSOntology -> RelName -> ClassName -> ClassName
                   -> WithError MMiSSOntology
insertRelationType onto relName source target =
  do o1 <- lookupClass onto source
     o2 <- lookupClass o1 target
     o3 <- case Map.lookup relName (relations o2) of
             Nothing -> case mode o2 of
               AutoInsert -> return $ addRelations o2
                 [(relName, RelationDecl relName Nothing "" [] Nothing True)]
               _ -> insErr $ "relation type: Relation " ++ relName
             Just (RelationDecl nam card defText typeList super inserted) ->
               let newType = RelationTypeDecl source target
                   newRel = (RelationDecl nam card defText
                             (typeList ++ [newType]) super inserted)
               in  return (addRelations o2 [(nam, newRel)])
     addEdge o3 (getClassGraph o3) relName source target
  where
    lookupClass o className =
       case Map.lookup className $ classes o of
         Nothing -> insertClasses o className "relation type: Class "
         Just (ClassDecl cn defT sup typeList ai classType) ->
           if cn == source
             then let mayTypeDecl = find ((relName ==) . fst) typeList
                      newClassList = case mayTypeDecl of
                                       Just (_, clist) -> clist ++ [target]
                                       Nothing -> [target]
                      newTypeList = deleteBy isEqualTypelist (relName, [])
                                     typeList ++ [(relName, newClassList)]
                  in return (addClasses o
                             [(className, (ClassDecl cn defT sup newTypeList
                                                     ai classType))])
             else return o
    addEdge ontol g rel src tar =
      case findLNode g src of
        Nothing -> return ontol
        Just snode  -> case findLNode g tar of
                         Nothing -> return ontol
                         Just tnode -> return ontol
                             { getClassGraph = insEdge (snode, tnode, rel) g }

isEqualTypelist :: (RelName, [ClassName]) -> (RelName, [ClassName]) -> Bool
isEqualTypelist (r1, _) (r2, _) = r1 == r2

insertObject :: MMiSSOntology -> ObjectName -> DefaultText -> ClassName
             -> WithError MMiSSOntology
insertObject onto objectName defText className =
  do o1 <- if Map.member objectName (objects onto)
             then hasError("Insertion of object: " ++ objectName
                           ++ " already exists.")
             else return onto
     o2 <- insertClasses o1 className $
           "object: " ++ objectName ++ " -> Class "
     return onto
         { classes = classes o2
         , objects = Map.insert objectName
                     (ObjectDecl objectName defText className) $ objects onto
         , getClassGraph = addObjectToGraph objectName className
                                         $ getClassGraph onto }
  where
    addObjectToGraph nam classNam g =
       case findLNode g nam of
         Nothing -> let n = head (newNodes 1 g)
                    in insNode (n, ("_" ++ nam ++ "_", classNam,
                                             OntoObject)) g
         Just _ -> g

{- | inserts a new link of type RelationName between the two given
  objects.  Throws an error if RelationName, SourceObject or
  TargetObject doesn't exist. -}
insertLink :: MMiSSOntology -> String -> String -> String
           -> WithError MMiSSOntology
insertLink onto source target relName = do
    let objs = objects onto
    case Map.lookup source objs of
      Just _ -> return ()
      Nothing -> insErr' "Object" source
    case Map.lookup target objs of
      Just _ -> return ()
      Nothing -> insErr' "Object" target
    case Map.lookup relName $ relations onto of
      Just _ -> return ()
      Nothing -> insErr' "Relation" relName
    return onto
      { objectLinks = objectLinks onto ++ [ObjectLink source target relName]
      , getClassGraph = addObjectLinkToGraph source target
                                         relName $ getClassGraph onto }
  where
    insErr' str val =
        insErr $ map toLower str ++ " link: " ++ str ++ " " ++ val
    addObjectLinkToGraph src tar relNam g =
       case findLNode g $ "_" ++ src ++ "_" of
         Nothing -> g
         Just sNode  -> case findLNode g $ "_" ++ tar ++ "_"  of
                          Nothing -> g
                          Just tNode -> insEdge (sNode, tNode, relNam) g

{- | is checking ontologies which have been created in AutoInsert
      mode.  For these ontologies there could be classes and relations
      that were inserted automatically rather than defined properly
      via insertClass or insertRelation.  If the InsertMode of the
      provided ontology is 'ThrowError' returns an empty list.  If
      there are no classes or relations with AutoInserted mark returns
      also an empty list, otherwise it returns a list of error
      messages stating, which class or which relation definition is
      missing. -}
isComplete :: MMiSSOntology -> [String]
isComplete onto = case mode onto of
    ThrowError -> []
    _ -> Map.foldrWithKey checkClass [] (classes onto)
            ++ Map.foldrWithKey checkRel [] (relations onto)
  where
    mkMsg str nam = [str ++ nam ++ " is not properly defined."]
    checkClass className (ClassDecl _ _ _ _ inserted _) l =
      if inserted then l ++ mkMsg "Class " className else l
    checkRel relName (RelationDecl _ _ _ _ _ inserted) l =
      if inserted then l ++ mkMsg "Relation " relName else l

exportOWL :: MMiSSOntology -> String
exportOWL onto =
  let startStr = owlStart $ getOntologyName onto
      relationsStr = foldl writeOWLRelation "" $ Map.elems $ relations onto
      classesStr =  foldl writeOWLClass "" $ Map.elems $ classes onto
      objectsStr = foldl writeOWLObject "" $ Map.elems $ objects onto
      linksStr = foldl writeOWLLink "" $ objectLinks onto
      endStr = "</rdf:RDF>"
  in startStr ++ classesStr ++ relationsStr ++ objectsStr ++ linksStr ++ endStr

writeOWLLink :: String -> ObjectLink -> String
writeOWLLink inStr (ObjectLink object1 object2 relName) =
 let start = "<rdf:Description rdf:about=\"#" ++ object1 ++ "\">\n"
     propStr = "<" ++ relName ++ " rdf:resource=\"#" ++ object2 ++ "\"/>\n"
     end = "</rdf:Description>\n"
 in inStr ++ start ++ propStr ++ end

writeOWLObject :: String -> ObjectDecl -> String
writeOWLObject inStr (ObjectDecl nam defText instanceOf) =
 let start = "<rdf:Description" ++ " rdf:about=\"#" ++ nam ++ "\">\n"
     defTextStr = "<MPhrase>" ++ latexToEntity defText ++ "</MPhrase>\n"
     classStr = "<rdf:type>\n  <owl:Class rdf:about=\"#" ++ instanceOf
                ++ "\"/>\n</rdf:type>"
     end = "</rdf:Description>"
 in inStr ++ start ++ defTextStr ++ classStr ++ end

writeOWLClass :: String -> ClassDecl -> String
writeOWLClass inStr (ClassDecl nam defText super relTypes _ _) =
 let start = "<owl:Class rdf:ID=\"" ++ nam ++ "\">\n"
     defTextStr = "  <MPhrase>" ++ latexToEntity defText ++ "</MPhrase>\n"
     superStr =
         concatMap (\ str -> "<rdfs:subClassOf rdf:resource=\"#" ++
                             str ++ "\"/>\n" ) super
     propertyRestrictions = foldl writePropRestriction "" relTypes
     end = "</owl:Class>\n"
 in inStr ++ start ++ defTextStr ++ superStr ++ propertyRestrictions ++ end

writePropRestriction :: String -> (RelName, [ClassName]) -> String
writePropRestriction inStr (relName, classList) =
  case classList of
    [] -> inStr
    [hd] -> let
             start = "<rdfs:subClassOf>\n  <owl:Restriction>\n"
             classStr = "    <owl:allValuesFrom>\n" ++
                        "      <owl:Class rdf:about=\"#" ++ hd
                        ++ "\"/>\n" ++
                        "    </owl:allValuesFrom>\n"
             onPropStr = "    <owl:onProperty>\n"
                         ++ "      <owl:ObjectProperty rdf:about=\"#"
                         ++ relName ++ "\"/>\n"
                         ++ "    </owl:onProperty>\n"
             end = "  </owl:Restriction>\n</rdfs:subClassOf>\n"
          in inStr ++ start ++ onPropStr ++ classStr ++ end
    _ -> let start = "<rdfs:subClassOf>\n  <owl:Restriction>\n    " ++
                     "<owl:onProperty>\n" ++
                     "        <owl:ObjectProperty rdf:about=\"#" ++ relName ++
                     "\"/>\n" ++
                     "    </owl:onProperty>\n" ++
                     "    <owl:allValuesFrom>\n" ++
                     "     <owl:Class>\n" ++
                     "        <owl:unionOf rdf:parseType=\"Collection\">\n"
             restrictions = foldl writeSingleClassRestriction "" classList
             end = "</owl:unionOf>\n</owl:Class>\n</owl:allValuesFrom>\n" ++
                   "</owl:Restriction>\n</rdfs:subClassOf>\n"
         in inStr ++ start ++ restrictions ++ end

writeSingleClassRestriction :: String -> ClassName -> String
writeSingleClassRestriction inStr className =
    inStr ++ "<owl:Class rdf:about=\"#" ++ className ++  "\"/>\n"

writeOWLRelation :: String -> RelationDecl -> String
writeOWLRelation inStr (RelationDecl relName card relText _ super _) =
 let start = "<owl:ObjectProperty rdf:ID=\"" ++ relName ++ "\">\n"
     propStr = case card of
       Just "->"  -> "  <rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>"
       Just ">"   -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
       Just ">="  -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
       Just "="   -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
           ++ "  <rdf:type rdf:resource=\"&owl;SymmetricProperty\"/>"
       Just "<->" -> "  <rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>"
           ++ "  <rdf:type rdf:resource=\"&owl;InverseFunctionalProperty\"/>"
       _ -> ""
     cardStr = case card of
                 Just str -> "  <MCardinality>" ++ latexToEntity str
                              ++  "</MCardinality>\n"
                 Nothing -> ""
     defText = "  <MPhrase>" ++ relText ++ "</MPhrase>\n"
     superStr = case super of
                  Just str -> "  <rdfs:subPropertyOf rdf:resource=\"#" ++ str
                               ++ "\"/>\n"
                  Nothing -> ""
     end = "</owl:ObjectProperty>\n"
 in inStr ++ start ++ propStr ++ cardStr ++ defText ++ superStr ++ end

owlStart :: String -> String
owlStart nam = unlines
  [ "<?xml version=\"1.0\"?>"
  , "<!DOCTYPE rdf:RDF ["
  , "    <!ENTITY rdf  \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">"
  , "    <!ENTITY rdfs \"http://www.w3.org/2000/01/rdf-schema#\" >"
  , "    <!ENTITY xsd  \"http://www.w3.org/2001/XMLSchema#\" >"
  , "    <!ENTITY owl  \"http://www.w3.org/2002/07/owl#\">"
  , "  ]>"
  , "<rdf:RDF"
  , "xmlns:rdf=\"&rdf;\""
  , "xmlns:rdfs=\"&rdfs;\""
  , "xmlns:owl=\"&owl;\""
  , "xmlns:vcard=\"http://www.w3.org/2001/vcard-rdf/3.0#\""
  , "xmlns:daml=\"http://www.daml.org/2001/03/daml+oil#\""
  , "xmlns:dc=\"http://purl.org/dc/elements/1.1/\""
  , "xmlns=\"" ++ nam ++ ".owl\">"
  , "<owl:Ontology rdf:about=\"" ++ nam ++ "\">"
  , "<rdfs:comment>OWL ontology created by MMiSS OntoTool v0.2. " ++
    "For more information about the MMiSS project please visit " ++
    "http://www.mmiss.de</rdfs:comment>" ++
    "</owl:Ontology>"
  , "  <owl:AnnotationProperty rdf:ID=\"MPhrase\">"
  , "    <rdfs:range rdf:resource=" ++
    "\"http://www.w3.org/2001/XMLSchema#string\"/>"
  , "    <rdf:type rdf:resource=" ++
    "\"http://www.w3.org/2002/07/owl#DatatypeProperty\"/>"
  , "  </owl:AnnotationProperty>"
  , "  <owl:AnnotationProperty rdf:ID=\"MCardinality\">"
  , "    <rdfs:range rdf:resource=" ++
    "\"http://www.w3.org/2001/XMLSchema#string\"/>"
  , "    <rdf:type rdf:resource=" ++
    "\"http://www.w3.org/2002/07/owl#DatatypeProperty\"/>"
  , "  </owl:AnnotationProperty>"
  ]

latexToEntityList :: [(String, String)]
latexToEntityList = [("<", "&#38;#60;"), (">", "&#62;"), ("&", "&#38;#38;")]
                    ++ [("'", "&#39;"), ("\"", "&#34;")]

latexToEntity :: String -> String
latexToEntity inStr = foldl (applyTranslation "") inStr latexToEntityList

applyTranslation :: String -> String -> (String, String) -> String
applyTranslation outStr inStr (search, replaceStr)
   | lenInStr < lenSearch = outStr ++ inStr
   | isPrefixOf search inStr = applyTranslation (outStr ++ replaceStr)
                     (genericDrop lenSearch inStr)  (search, replaceStr)
   | otherwise = applyTranslation (outStr ++ take 1 inStr)
                     (drop 1 inStr)  (search, replaceStr)
   where
   lenInStr = genericLength inStr
   lenSearch = genericLength search :: Integer

gselLab :: ((String, String, OntoObjectType) -> Bool) -> ClassGraph
        -> [Context (String, String, OntoObjectType) String]
gselLab f = gsel ( \ (_, _, l, _) -> f l)

gselName :: String -> ClassGraph
         -> [Context (String, String, OntoObjectType) String]
gselName n = gselLab ( \ (l, _, _) -> n == l)

gselType :: (OntoObjectType -> Bool) -> ClassGraph
         -> [Context (String, String, OntoObjectType) String]
gselType f = gselLab ( \ (_, _, t) -> f t)

findLNode :: ClassGraph -> String -> Maybe Node
findLNode gr label = case gselName label gr of
    [] -> Nothing
    hd : _ -> Just $ node' hd

{- | Insert a class-node into the graph. The ClassDecl doesn't have to
be considered, because classes added here have no Superclass (they are
inserted in AutoInsert-Mode). -}
addClassNodeWithoutDecl :: ClassGraph -> (String, ClassDecl) -> ClassGraph
addClassNodeWithoutDecl g (cn, _) = case findLNode g cn of
    Just _ -> g
    Nothing ->
      let node = head (newNodes 1 g)
      in  insNode (node, (cn, "", OntoClass)) g
