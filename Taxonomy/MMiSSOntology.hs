{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2004-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

MMiSSOntology provides the abstract data type for an Ontology
-}

{-- \section*{Modul: MMiSSOntology}
\subsection*{Introduction}

Within the MMiSS project a language for defining and representing
ontologies has been created. In general classes, relations, predicates
and operations between classe, objects and links between objects can
be expressed. Inheritance is possible for classes and
relations. Further details about ontologies in MMiSS are given in the
paper "Semantic Interrelation with Ontologies".

At the moment, the module ist designed for storing ontologies in the
"MMiSS sense". Later on, it should be investigated, if it is
reasonable to adapt the module for OWL or KIF ontologies.

\subsection*{Interface}

The module defines a data type \tt{MMISSOntology} which stores all
information contained in a MMiSS-Ontology. \tt{emptyMMiSSOntology}
provides a fresh, clean ontology labeld with the delivered name. After
creating an empty ontology, the insertion functions () should be used
to fill the ontology.  --}

{-
   todo: add a new edge type for equivalence which should be visited only once
-}

module Taxonomy.MMiSSOntology (
  MMiSSOntology,
  ClassName,
  ObjectName,
  SuperClass,
  DefaultText,
  Cardinality,
  SuperRel,
  RelName,
  RelationProperty(..),
  -- data RelationProperty = InversOf String
  --                       | Functional
  InsertMode(..),
  OntoObjectType(..),
  ClassType(..),
  weither, -- like either
  fromWithError, -- convert to another monad
  WithError,

  {--
   AutoInsert: When a new class is to be inserted and the given
               SuperClass is not present in the ontology, it is
               automatically inserted with just it's name.  The caller
               can later on insert the missing class without getting
               an error message (the class information is beeing
               updated).  The same happens if a SuperRelation is not
               present when a new relation is inserted.  ThrowError:
               The insertClass or insertRelation function calls will
               throw an error instead auf performing an autoinsert.
  --}

  emptyMMiSSOntology,

  insertClass,

  insertObject,

  {-- insertBaseRelation inserts a new Relation into the Ontology. It
  throws an error if the relation name already exists.  --}
  insertBaseRelation,

  {-- insertRelationType inserts a new RelationType declaration into
  the Ontology. It throws an error if the relation name doesn't exist.
  --}
  insertRelationType,

  {-- insertLink inserts a new link of type RelationName between the
  two given objects.  Throws an error if RelationName, SourceObject or
  TargetObject doesn't exist.  --}
  insertLink,

  {-- isComplete is checking ontologies which has been created in
      AutoInsert mode.  For these ontologies there could be classes
      and relations that were inserted automatically rather than
      defined properly via insertClass or insertRelation.  If the
      InsertMode of the provided ontology is 'ThrowError' returns an
      empty list.  If there are no classes or relations with
      AutoInserted mark returns also an empty list, otherwise it
      returns a list of error messages stating, which class or which
      relation definition is missing.  --}
  isComplete,
  -- :: MMiSSOntology -> [String]

  exportOWL,
  -- :: MMiSSOntology -> [String]

  getOntologyName,
  -- :: MMiSSOntology -> String

  getRelationNames,
  -- :: MMiSSOntology -> [String]

  getClassGraph,
  -- :: MMiSSOntology -> Gr (String, String, OntoObjectType) String

  getRelationGraph,
  -- :: MMiSSOntology -> Gr String String

  hasError, hasValue
)

where

import Control.Monad (liftM)
import Data.List

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Basic
import Common.Lib.Graph
import qualified Data.Map as Map

type ClassName = String
type ObjectName = String
type SuperClass = String
type DefaultText = String
type Cardinality = String
type SuperRel = String
type RelName = String
type RelationText = String
type AutoInserted = Bool

data WithError a = HasError String | HasValue a

instance Functor WithError where
  fmap                = liftM

instance Monad WithError where
  return              = HasValue
  HasValue x >>= f    = f x
  HasError x >>= f    = HasError x

hasError :: String -> WithError a
hasError = HasError

hasValue :: a -> WithError a
hasValue = HasValue

weither :: (String -> b) -> (a -> b) -> WithError a -> b
weither ef vf we = case we of
                   HasError s -> ef s
                   HasValue v -> vf v

fromWithError :: (Monad m) => WithError a -> m a
fromWithError = weither (\err -> fail err) (\x -> return x)

data RelationProperty = InversOf String | Functional
                        deriving (Eq, Read, Show)

data InsertMode = AutoInsert | ThrowError
                  deriving (Eq, Read, Show)

data OntoObjectType = OntoClass | OntoObject | OntoPredicate
                      deriving (Show, Eq)

data ClassType = SubSort | Predicate deriving (Eq, Read, Show)

data MMiSSOntology = MMiSSOntology {
  name :: String,
  classes :: Map.Map String ClassDecl,
  objects :: Map.Map String ObjectDecl,
  relations :: Map.Map String RelationDecl,
  objectLinks :: [ObjectLink],
  mode :: InsertMode,
  classGraph :: Gr (String, String, OntoObjectType) String,
  relationGraph :: Gr String String
}



data ClassDecl = ClassDecl ClassName
                           DefaultText
                           [SuperClass]
                          [(RelName, [ClassName])]
                           AutoInserted
                          (Maybe ClassType)

data ObjectDecl = ObjectDecl ObjectName
                             DefaultText
                             ClassName

data RelationDecl = RelationDecl  RelName
                                 (Maybe Cardinality)
                                  RelationText
                                 [RelationTypeDecl]
                                 (Maybe SuperRel)
                                  AutoInserted
--  baseProperties :: [RelationProperty]

data RelationTypeDecl = RelationTypeDecl ClassName ClassName


data ObjectLink = ObjectLink ObjectName ObjectName RelName


emptyMMiSSOntology :: String -> InsertMode -> MMiSSOntology
emptyMMiSSOntology ontoName insertMode =
  MMiSSOntology {
    name = ontoName,
    classes = Map.empty,
    objects = Map.empty,
    relations = Map.empty,
    objectLinks = [],
    mode = insertMode,
    classGraph = empty,
    relationGraph = empty
  }

getRelationNames :: MMiSSOntology -> [String]
getRelationNames onto = Map.keys (relations onto)

getOntologyName :: MMiSSOntology -> String
getOntologyName o = name o

getClassGraph :: MMiSSOntology -> Gr (String, String, OntoObjectType) String
getClassGraph o = classGraph o

getRelationGraph :: MMiSSOntology -> Gr String String
getRelationGraph o = relationGraph o

insertClass :: MMiSSOntology -> ClassName -> DefaultText -> [SuperClass]
            -> (Maybe ClassType)
            -> WithError (MMiSSOntology)
insertClass onto className optText superCs maybeType =
  maybe
    (myInsertClass className optText superCs maybeType)
    (\ (ClassDecl _ _ _ _ auto _) ->
      case (mode onto) of
        AutoInsert ->
          if (auto == True)
            then myInsertClass className optText superCs maybeType
            else hasError("Insertion of class: " ++ className ++
                          " -> Class is properly defined and "++
                          "can't be overridden. (AutoInsert is on).\n")
        _ -> hasError("Insertion of class: " ++ className  ++
                      " -> Class is already defined in Ontology.\n"))
    (Map.lookup className $ classes onto)
  where
    myInsertClass cn opt super classType =
      let class1 = (cn, (ClassDecl cn opt super [] False classType))
      in case super of
           []          -> addClasses [class1] super
           superClasses ->
               let (defSC,undefSC) =
                       partition (\sC -> Map.member sC (classes onto))
                                 superClasses
                   sClassDecls =
                       map (\sC -> (sC, (ClassDecl sC "" [] []
                                              True Nothing))) undefSC
               in if null undefSC
                then addClasses [class1] super
                else case (mode onto) of
                      AutoInsert -> addClasses (class1:sClassDecls) super
                      _  -> hasError("Insertion of class: " ++ cn ++
                                     " -> Superclass " ++ show undefSC ++
                                     " not defined in Ontology.\n")
    addClasses :: [(String, ClassDecl)] -> [SuperClass]
               -> WithError MMiSSOntology
    addClasses cList superCs =
       let g = classGraph onto
           newgraph =
               case cList of
               [] -> g
               [(className, ClassDecl _ _ _ _ _ cType)] ->
                     let (g1, node1) = getInsNode g className cType
                     in foldl (addIsaEdge node1) g1 superCs
               (subClass, ClassDecl _ _ _ _ _ subcType) : _ ->
                   let (g1, node1) = getInsNode g subClass subcType
                   in foldl (insClass node1) g1 superCs
       in
         hasValue( onto { classes = Map.union (classes onto)
                                    $ Map.fromList cList,
                          classGraph = newgraph} )
    getInsNode g cl clType =
        maybe (let n = head (newNodes 1 g)
               in ((insNode (n,(cl,"", getClassNodeType clType)) g), n))
              (\node -> (g, node))
              (findLNode g cl)
    insClass node1 g1 sC =
        case getInsNode g1 sC Nothing of
        -- at this place all autoinserted classes have type
        -- Nothing (s. def. of sClassDecls)
        (g2,node2) -> insEdge (node1, node2, "isa") g2
    addIsaEdge node1 g1 superClass =
        maybe g1 (\ sNode -> insEdge (node1, sNode, "isa") g1)
                 (findLNode g1 superClass)
    getClassNodeType = maybe OntoClass (\ cType -> if cType == Predicate
                                        then OntoPredicate
                                        else OntoClass)

{--
data RelationDecl = RelationDecl  RelName
                                 (Maybe Cardinality)
                                  RelationText
                                 [RelationTypeDecl]
                                 (Maybe SuperRel)
                                  AutoInserted
--}

insertBaseRelation :: MMiSSOntology -> RelName -> DefaultText
                   -> Maybe SuperRel -> Maybe Cardinality
                   -> WithError (MMiSSOntology)
insertBaseRelation onto relName defText superRel card =
  case Map.lookup relName (relations onto) of
    Nothing -> myInsertRel relName defText superRel card
    Just(RelationDecl _ _ _ _ _ auto) ->
      case (mode onto) of
        AutoInsert ->
          if (auto == True)
            then myInsertRel relName defText superRel card
            else hasError("Insertion of relation: " ++ relName
                          ++ " -> Relation is properly defined " ++
                          "and can't be overridden. (AutoInsert is on).\n")
        _ -> hasError("Insertion of relation: " ++ relName
                      ++ " -> Relation is already defined in Ontology.\n")
  where
    myInsertRel rn def super c =
      let rel1 = (rn, (RelationDecl rn c def [] super False))
      in case super of
           Nothing          -> addRelations [rel1]
           Just(superR) ->
             if (Map.member superR (relations onto))
               then addRelations [rel1]
               else case (mode onto) of
                      AutoInsert ->
                          let rel2 = (superR, (RelationDecl superR Nothing ""
                                               [] Nothing True))
                          in addRelations (rel1:(rel2:[]))
                      _  -> hasError("Insertion of relation: " ++ rn ++
                                     " -> Superrelation " ++ superR ++
                                     " not defined in Ontology.\n")
    addRelations rList =
       hasValue( MMiSSOntology {name = name onto,
                                classes = classes onto,
                                objects = objects onto,
                                relations = Map.union (relations onto)
                                            $ Map.fromList rList,
                                objectLinks = objectLinks onto,
                                mode = mode onto,
                                classGraph = classGraph onto,
                                relationGraph = relationGraph onto} )

insertRelationType :: MMiSSOntology -> RelName -> ClassName -> ClassName
                   -> WithError (MMiSSOntology)
insertRelationType onto relName source target =
  do o1 <- lookupClass onto source
     o2 <- lookupClass o1 target
     o3 <- case Map.lookup relName (relations o2) of
             Nothing ->
                 if ((mode o2) == AutoInsert)
                 then return (addRelations o2
                              [(relName, (RelationDecl relName Nothing "" []
                                                       Nothing True))])
                 else hasError("Insertion of relation type: Relation " ++
                               relName ++ " doesn't exist in the Ontology.\n")
             Just((RelationDecl name card defText typeList super inserted)) ->
               let newType = RelationTypeDecl source target
                   newRel = (RelationDecl name card defText
                             (typeList ++ [newType]) super inserted)
               in  return (addRelations o2 [(name, newRel)])
     o4 <- addEdge o3 (classGraph o3) relName source target
     return o4
  where
    addClasses o cList =
                 MMiSSOntology {name = name o,
                                classes = Map.union (classes o)
                                          $ Map.fromList cList,
                                objects = objects o,
                                relations = relations o,
                                objectLinks = objectLinks o,
                                mode = mode o,
                                classGraph = foldl addClassNodeWithoutDecl
                                             (classGraph o) cList,
                                relationGraph = relationGraph onto}
    addRelations o rList =
                 MMiSSOntology {name = name o,
                                classes = classes o,
                                objects = objects o,
                                relations = Map.union (relations o)
                                            $ Map.fromList rList,
                                objectLinks = objectLinks o,
                                mode = mode o,
                                classGraph = classGraph o,
                                relationGraph = relationGraph onto}
    lookupClass o className =
       case Map.lookup className (classes o) of
         Nothing -> if ((mode o) == AutoInsert)
                      then return (addClasses o
                                   [(className, (ClassDecl className "" []
                                                 [] True Nothing))])
                      else hasError("Insertion of relation type: Class "
                                    ++ className
                                    ++ " doesn't exist in the Ontology.\n")
         Just((ClassDecl cn defT sup typeList ai classType)) ->
           if (cn == source)
             then let mayTypeDecl = (find ((relName ==) . fst) typeList)
                      newClassList = case mayTypeDecl of
                                       Just((_, clist)) -> clist ++ [target]
                                       Nothing -> [target]
                      newTypeList = (deleteBy isEqualTypelist (relName, [])
                                     typeList) ++ [(relName, newClassList)]
                  in return (addClasses o
                             [(className, (ClassDecl cn defT sup newTypeList
                                                     ai classType))])
             else  return o
    addEdge onto g rel source target =
      case findLNode g source of
        Nothing -> return(onto)
        Just(snode) -> case findLNode g target of
                         Nothing -> return(onto)
                         Just(tnode) ->
                            let newg = insEdge (snode, tnode, rel) g
                            in return (MMiSSOntology
                                       {name = name onto,
                                        classes = classes onto,
                                        objects = objects onto,
                                        relations = relations onto,
                                        objectLinks = objectLinks onto,
                                        mode = mode onto,
                                        classGraph = newg,
                                        relationGraph = relationGraph onto} )

isEqualTypelist :: (RelName, [ClassName]) -> (RelName, [ClassName]) -> Bool
isEqualTypelist (r1, _) (r2, _) = r1 == r2

insertObject :: MMiSSOntology -> ObjectName -> DefaultText -> ClassName
             -> WithError (MMiSSOntology)
insertObject onto objectName defText className =
  do o1 <- if (Map.member objectName (objects onto))
             then hasError("Insertion of object: " ++ objectName
                           ++ " already exists.")
             else return onto
     o2 <- lookupClass o1 className
     return (MMiSSOntology {name = name onto,
                            classes = classes o2,
                            objects = Map.insert objectName
                                     (ObjectDecl objectName defText className)
                                     (objects onto),
                            relations = relations onto,
                            objectLinks = objectLinks onto,
                            mode = mode onto,
                            classGraph = addObjectToGraph objectName className
                                         (classGraph onto),
                            relationGraph = relationGraph onto} )
  where
    addClasses o cList =
                 MMiSSOntology {name = name o,
                                classes = Map.union (classes o)
                                          $ Map.fromList cList,
                                objects = objects o,
                                relations = relations o,
                                objectLinks = objectLinks o,
                                mode = mode o,
                                classGraph = foldl addClassNodeWithoutDecl
                                             (classGraph onto) cList,
                                relationGraph = relationGraph onto}
    lookupClass o className =
       case Map.lookup className (classes o) of
         Nothing -> if ((mode o) == AutoInsert)
                      then return (addClasses o
                                   [(className, (ClassDecl className "" [] []
                                                 True Nothing))])
                      else hasError("Insertion of object: " ++ objectName ++
                                    " -> Class " ++ className
                                    ++ " doesn't exist in the Ontology.\n")
         Just(_) -> return o

    addObjectToGraph name className g =
       case (findLNode g name) of
         Nothing -> let n = head (newNodes 1 g)
                        newG = (insNode (n, (("_" ++ name ++ "_"), className,
                                             OntoObject)) g)
                    in newG
         Just(node) -> g

insertLink onto source target relName =
  do o1 <- case Map.lookup source (objects onto) of
             Just(_) -> return onto
             Nothing -> hasError("Insertion of object link: Object " ++ source
                                        ++ " doesn't exist in the Ontology.\n")
     o2 <- case Map.lookup target (objects o1) of
             Just(_) -> return o1
             Nothing -> hasError("Insertion of object link: Object " ++ target
                                        ++ " doesn't exist in the Ontology.\n")
     o3 <- case Map.lookup relName (relations o2) of
             Just(_) -> return o2
             Nothing -> hasError("Insertion of object link: Relation "
                                 ++ relName
                                 ++ " doesn't exist in the Ontology.\n")
     return (MMiSSOntology {name = name o3,
                            classes = classes o3,
                            objects = objects o3,
                            relations = relations o3,
                            objectLinks = (objectLinks o3) ++
                                          [(ObjectLink source target relName)],
                            mode = mode o3,
                            classGraph = addObjectLinkToGraph source target
                                         relName (classGraph onto),
                            relationGraph = relationGraph onto} )
  where
    addObjectLinkToGraph source target relName g =
       case (findLNode g ("_" ++ source ++ "_")) of
         Nothing -> g
         Just(sNode) -> case (findLNode g ("_" ++ target ++ "_")) of
                          Nothing -> g
                          Just(tNode) -> insEdge (sNode, tNode, relName) g

isComplete :: MMiSSOntology -> [String]
isComplete onto =
  if ((mode onto) == ThrowError)
    then []
    else  (Map.foldWithKey checkClass [] (classes onto))
            ++ (Map.foldWithKey checkRel [] (relations onto))
  where
    checkClass className (ClassDecl _ _ _ _ inserted _) l =
      if inserted
        then (l ++ ["Class " ++ className ++ " is not properly defined."])
        else l
    checkRel relName (RelationDecl _ _ _ _ _ inserted) l =
      if inserted
        then (l ++ ["Relation " ++ relName ++ " is not properly defined."])
        else l

exportOWL :: MMiSSOntology -> String
exportOWL onto =
  let startStr = owlStart (name onto)
      relationsStr = foldl writeOWLRelation "" (Map.elems (relations(onto)))
      classesStr =  foldl writeOWLClass "" (Map.elems (classes(onto)))
      objectsStr = foldl writeOWLObject "" (Map.elems (objects(onto)))
      linksStr = foldl writeOWLLink "" (objectLinks(onto))
      endStr = "</rdf:RDF>"
  in startStr ++ classesStr ++ relationsStr ++ objectsStr ++ linksStr ++ endStr

writeOWLLink :: String -> ObjectLink -> String
writeOWLLink inStr (ObjectLink object1 object2 relName) =
 let start = "<rdf:Description rdf:about=\"#" ++ object1 ++ "\">\n"
     propStr = "<" ++ relName ++ " rdf:resource=\"#" ++ object2 ++ "\"/>\n"
     end = "</rdf:Description>\n"
 in inStr ++ start ++ propStr ++ end

writeOWLObject :: String -> ObjectDecl -> String
writeOWLObject inStr (ObjectDecl name defText instanceOf) =
 let start = "<rdf:Description" ++ " rdf:about=\"#" ++ name ++ "\">\n"
     defTextStr = "<MPhrase>" ++ (latexToEntity defText) ++ "</MPhrase>\n"
     classStr = "<rdf:type>\n  <owl:Class rdf:about=\"#" ++ instanceOf
                ++ "\"/>\n</rdf:type>"
     end = "</rdf:Description>"
 in inStr ++ start ++ defTextStr ++ classStr ++ end

writeOWLClass :: String -> ClassDecl -> String
writeOWLClass inStr (ClassDecl name defText super relTypes _ _) =
 let start = "<owl:Class rdf:ID=\"" ++ name ++ "\">\n"
     defTextStr = "  <MPhrase>" ++ (latexToEntity defText) ++ "</MPhrase>\n"
     superStr =
         concatMap (\ str -> "<rdfs:subClassOf rdf:resource=\"#" ++
                             str ++ "\"/>\n" ) super
     propertyRestrictions = foldl writePropRestriction "" relTypes
     end = "</owl:Class>\n"
 in inStr ++ start ++ defTextStr ++ superStr ++ propertyRestrictions ++ end

writePropRestriction :: String -> (RelName, [ClassName]) -> String
writePropRestriction inStr (relName, classList) =
  case length classList of
    0 -> inStr
    1 -> let start = "<rdfs:subClassOf>\n  <owl:Restriction>\n"
             classStr = "    <owl:allValuesFrom>\n" ++
                        "      <owl:Class rdf:about=\"#" ++ (head classList)
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
writeSingleClassRestriction inStr className
  = inStr ++ "<owl:Class rdf:about=\"#" ++ className ++  "\"/>\n"

writeOWLRelation :: String -> RelationDecl -> String
writeOWLRelation inStr (RelationDecl relName card relText _ super _) =
 let start = "<owl:ObjectProperty rdf:ID=\"" ++ relName ++ "\">\n"
     propStr = case card of
       Just("->")  -> "  <rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>"
       Just(">")   -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
       Just(">=")  -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
       Just("=")   -> "  <rdf:type rdf:resource=\"&owl;TransitiveProperty\"/>"
           ++ "  <rdf:type rdf:resource=\"&owl;SymmetricProperty\"/>"
       Just("<->") -> "  <rdf:type rdf:resource=\"&owl;FunctionalProperty\"/>"
           ++ "  <rdf:type rdf:resource=\"&owl;InverseFunctionalProperty\"/>"
       otherwise -> ""
     cardStr = case card of
                 Just(str) -> "  <MCardinality>" ++ (latexToEntity str)
                              ++  "</MCardinality>\n"
                 Nothing -> ""
     defText = "  <MPhrase>" ++ relText ++ "</MPhrase>\n"
     superStr = case super of
                  Just(str) -> "  <rdfs:subPropertyOf rdf:resource=\"#" ++ str
                               ++ "\"/>\n"
                  Nothing -> ""
     end = "</owl:ObjectProperty>\n"
 in inStr ++ start ++ propStr ++ cardStr ++ defText ++ superStr ++ end

owlStart :: String -> String
owlStart name = "<?xml version=\"1.0\"?>\n" ++
   "<!DOCTYPE rdf:RDF [\n" ++
   "    <!ENTITY rdf  \"http://www.w3.org/1999/02/22-rdf-syntax-ns#\">\n" ++
   "    <!ENTITY rdfs \"http://www.w3.org/2000/01/rdf-schema#\" >\n" ++
   "    <!ENTITY xsd  \"http://www.w3.org/2001/XMLSchema#\" >\n" ++
   "    <!ENTITY owl  \"http://www.w3.org/2002/07/owl#\">\n" ++
   "  ]>\n" ++
    "<rdf:RDF\n" ++
    "xmlns:rdf=\"&rdf;\"\n" ++
    "xmlns:rdfs=\"&rdfs;\"\n" ++
    "xmlns:owl=\"&owl;\"\n" ++
    "xmlns:vcard=\"http://www.w3.org/2001/vcard-rdf/3.0#\"\n" ++
    "xmlns:daml=\"http://www.daml.org/2001/03/daml+oil#\"\n" ++
    "xmlns:dc=\"http://purl.org/dc/elements/1.1/\"\n" ++
    "xmlns=\"" ++ name ++ ".owl\">\n" ++
    "<owl:Ontology rdf:about=\"" ++ name ++ "\">\n" ++
    "<rdfs:comment>OWL ontology created by MMiSS OntoTool v0.2. For more information about the MMiSS project please visit http://www.mmiss.de</rdfs:comment>" ++
    "</owl:Ontology>\n" ++
    "  <owl:AnnotationProperty rdf:ID=\"MPhrase\">\n" ++
    "    <rdfs:range rdf:resource=\"http://www.w3.org/2001/XMLSchema#string\"/>\n" ++
    "    <rdf:type rdf:resource=\"http://www.w3.org/2002/07/owl#DatatypeProperty\"/>\n" ++
    "  </owl:AnnotationProperty>\n" ++
    "  <owl:AnnotationProperty rdf:ID=\"MCardinality\">\n" ++
    "    <rdfs:range rdf:resource=\"http://www.w3.org/2001/XMLSchema#string\"/>\n" ++
    "    <rdf:type rdf:resource=\"http://www.w3.org/2002/07/owl#DatatypeProperty\"/>\n" ++
    "  </owl:AnnotationProperty>\n"

latexToEntityList = [("<", "&#38;#60;"), (">", "&#62;"), ("&", "&#38;#38;")]
                    ++ [("'", "&#39;"), ("\"", "&#34;")]

latexToEntity :: String -> String
latexToEntity inStr = foldl (applyTranslation "") inStr latexToEntityList

applyTranslation :: String -> String -> (String, String) -> String
applyTranslation outStr inStr (search, replaceStr) =
   if lenInStr < lenSearch
     then outStr ++ inStr
     else if (isPrefixOf search inStr)
            then applyTranslation (outStr ++ replaceStr)
                     (genericDrop lenSearch inStr)  (search, replaceStr)
            else applyTranslation (outStr ++ (take 1 inStr))
                     (drop 1 inStr)  (search, replaceStr)
   where
   lenInStr = genericLength inStr
   lenSearch = genericLength search :: Integer

findLNode :: Gr (String, String, OntoObjectType) String -> String -> Maybe Node
findLNode gr label = case (gsel (\(p,v,(l, _, _),s) -> l == label) gr) of
                      [] -> Nothing
                      conList -> Just(node' (head conList))

{- Insert a class-node into the graph. The ClassDecl doesn't have to
be considered, because classes added here have no Superclass (they are
inserted in AutoInsert-Mode). -}
addClassNodeWithoutDecl :: Gr (String, String, OntoObjectType) String
                        -> (String, ClassDecl)
                        -> Gr (String, String, OntoObjectType) String
addClassNodeWithoutDecl g (cn, _) =
  case findLNode g cn of
    Just(_) -> g
    Nothing ->
      let node = head (newNodes 1 g)
      in  insNode (node, (cn, "", OntoClass)) g
