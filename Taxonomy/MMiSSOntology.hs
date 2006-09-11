{-- \section*{Modul: MMiSSOntology}
\subsection*{Introduction}
Within the MMiSS project a language for defining and representing ontologies has been created. In general classes, relations, predicates and operations between classe, objects and links between objects can be expressed. Inheritance is possible for classes and relations. Further details about ontologies in MMiSS are given in the paper "Semantic Interrelation with Ontologies".

At the moment, the module ist designed for storing ontologies in the "MMiSS sense". Later on, it should be investigated, if it is reasonable to adapt the module for OWL or KIF ontologies. 

\subsection*{Interface}
The module defines a data type \tt{MMISSOntology} which stores all information contained in a MMiSS-Ontology. \tt{emptyMMiSSOntology} provides a fresh, clean ontology labeld with the delivered name. After creating an empty ontology, the insertion functions () should be used to fill the ontology. 
--}

{-- | 
      MMiSSOntology provides the abstract data type for an Ontology

   todo: add a new edge type for equivalence which should be visited only once
--}

module MMiSSOntology (
  MMiSSOntology,
  MMiSSOntologyFlat,
  RelationProperty(..), 
  InsertMode(..),
  OntoObjectType(..),
  ClassType(..),
  ClassName,
  ObjectName,
  SuperClass,
  DefaultText,
  Cardinality,
  SuperRel,
  RelName,
  RelationText,
  PackagePath,
  AutoInserted,
  ImportMode(..),

  {-- 
   AutoInsert: When a new class is to be inserted and the given SuperClass is not
               present in the ontology, it is automatically inserted with just it's name.
               The caller can later on insert the missing class without getting an
               error message (the class information is beeing updated).
               The same happens if a SuperRelation is not present when a new relation
               is inserted.
   ThrowError: The insertClass or insertRelation function calls will throw an error
               instead auf performing an autoinsert.
  --} 

  emptyMMiSSOntology, 
  -- :: String - > InsertMode -> MMiSSOntology 

  emptyMMiSSOntologyFlat, 
  -- :: -> MMiSSOntologyFlat 

  toFlat,
  -- :: MMiSSOntology -> MMiSSOntologyFlat

  fromFlat,
  -- :: MMiSSOntologyFlat -> MMiSSOntology
  
  insertClass, 
  -- :: MMiSSOntology -> ClassName -> DefaultText -> [SuperClass] 
  --        -> (Maybe ClassType) -> (Maybe (ClassName, PackagePath)) -> (Maybe ImportMode)  
  --        -> WithError (MMiSSOntology)

  insertObject,
  -- :: MMiSSOntology -> ObjectName -> DefaultText -> ClassName 
  --        -> (Maybe (ClassName, PackagePath)) -> (Maybe ImportMode) -> WithError (MMiSSOntology)

  {-- 
  insertBaseRelation inserts a new Relation into the Ontology. It throws an error if the 
  relation name already exists. 
  Example:   \RelationName{contains}{contains}
  --}
  insertBaseRelation,
  -- :: MMiSSOntology -> RelName -> DefaultText -> (Maybe (RelName, PackagePath)) -> (Maybe ImportMode)
  --      -> WithError (MMiSSOntology)

  {-- 
  insertRelationType inserts a new RelationType declaration into the Ontology. It throws an error if the 
  relation name doesn't exist. 
  Example:     \Relation[<-]{contains}{ProofSE}{ProofSE}{comprises}
  --}
  insertRelationType,
  -- :: MMiSSOntology -> RelName -> ClassName -> ClassName -> Maybe SuperRel -> Maybe Cardinality
  --      -> Maybe PackagePath -> Maybe ImportMode -> WithError (MMiSSOntology)

  {-- 
  insertLink inserts a new link of type RelationName between the two given objects.
  Throws an error if RelationName, SourceObject or TargetObject doesn't exist.
  --}
  insertLink,
  -- :: MMiSSOntology -> ObjectName -> ObjectName -> RelName -> -> Maybe PackagePath -> Maybe ImportMode 
  --    -> WithError (MMiSSOntology)

  insertDefine,
  -- :: MMiSSOntology -> String -> PackagePath -> WithError(MMiSSOntology)


  {-- isComplete is checking ontologies which has been created in AutoInsert mode.
      For these ontologies there could be classes and relations that were inserted automatically
      rather than defined properly via insertClass or insertRelation.
      If the InsertMode of the provided ontology is 'ThrowError' returns an empty list.
      If there are no classes or relations with AutoInserted mark returns also an empty list,
      otherwise it returns a list of error messages stating, which class or which relation definition
      is missing.
   --}

  isComplete, 
  -- :: MMiSSOntology -> [String]

  exportOWL,
  -- :: MMiSSOntology -> String

  exportSpaceTree,
  --  :: MMiSSOntology -> String

  exportLatexIndex,
  --  :: MMiSSOntology -> String

  getOntologyName, 
  -- :: MMiSSOntology -> String

  getClasses,
  -- :: MMiSSOntology -> [(ClassName, OptText, [SuperClass], Maybe ClassType, 
  --    Maybe (ClassName, PackagePath), Maybe ImportMode)]

  getRelations, 
  -- :: MMiSSOntology -> [(RelName, RelationText, (Maybe (RelName, PackagePath)), 
  --    -> (Maybe ImportMode))]

  getAllRelationTypes, 
  -- :: MMiSSOntology -> [(RelName, ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath,
  --                       Maybe ImportMode)]

  getRelationTypes, 
  -- :: MMiSSOntology -> RelName -> [(ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath,
  --                                  Maybe ImportMode)]

  getObjects,
  -- :: MMiSSOntology -> [(ObjectName, DefaultText, ClassName, 
  --                               Maybe (ClassName, PackagePath), (Maybe ImportMode))]

  getObjectLinks,
  -- :: MMiSSOntology -> [(ObjectName, ObjectName, RelName, Maybe PackagePath, Maybe ImportMode)]

  getRelationNames,
  -- :: MMiSSOntology -> [String]

  getDefines,
  -- :: MMiSSOntology -> Data.Map.Map String String

  getClassGraph,
  -- :: MMiSSOntology -> Gr (String, String, OntoObjectType) String

  getRelationGraph,
  -- :: MMiSSOntology -> Gr String String

  graphvizNodeAtts, 
  -- :: (String, String, OntoObjectType) -> String

  graphvizEdgeAtts,
  -- :: String -> String
  
  hasError, hasValue  
)

where

import Computation hiding (try)
import ExtendedPrelude(mapEq)
import CodedValue
import BinaryInstances

import qualified Data.Map as Map
import Data.Graph.Inductive
import Data.List
import Control.Monad
import Maybe

import Text.Read
import qualified Text.Read.Lex as L
import GHC.Read 


type ClassName = String
type ObjectName = String
type SuperClass = String
type DefaultText = String
type Cardinality = String
type SuperRel = String
type RelName = String
type RelationText = String
type PackagePath = String
type AutoInserted = Bool


data RelationProperty = InversOf String | Functional 
                        deriving (Eq, Read, Show)

data InsertMode = AutoInsert | ThrowError
                  deriving (Eq, Read, Show)

data OntoObjectType = OntoClass | OntoObject | OntoPredicate deriving (Show, Read, Eq)

data ClassType = SubSort | Predicate deriving (Eq, Read, Show)

{-- Der Klassengraph ist als fgl-Graph definiert:
  
    classGraph :: Gr (String, String, OntoObjectType) String,
    
    Knotenlabel: 
      (Klassenname, "", OntoClass)  fr Klassen
      (Klassenname, "", OntoPredicate)  fr Predikate aus CASL
      ("_"++Objektname++"_", Klasse des Objektes, OntoObject) fr Objekte

    Kantenlabel:
      "isa" fr Subklassenbeziehungen
       Name der Relation fr normale Relationen zwischen Klassen oder Objekten

--}

data MMiSSOntology = MMiSSOntology {
  name :: String,
  classes :: Map.Map String ClassDecl,
  objects :: Map.Map String ObjectDecl,
  relations :: Map.Map String RelationDecl,
  objectLinks :: [ObjectLink],
  defines :: Map.Map String String,
  mode :: InsertMode,
  classGraph :: Gr (String, String, OntoObjectType) String,
  relationGraph :: Gr String String
}

data MMiSSOntologyFlat = MMiSSOntologyFlat {
  nameFlat :: String,
  classesFlat :: [(String, ClassDecl)],
  objectsFlat :: [(String, ObjectDecl)],
  relationsFlat :: [(String, RelationDecl)],
  objectLinksFlat :: [ObjectLink],
  definesFlat :: [(String,String)],
  modeFlat :: InsertMode,
  classGraphFlat :: ([LNode (String, String, OntoObjectType)],[LEdge String]),
  relationGraphFlat :: ([(LNode String)], [(LEdge String)])
} deriving (Eq, Show, Read)


data ClassDecl = ClassDecl ClassName 
                           DefaultText 
                           [SuperClass]
                          [(RelName, [ClassName])] 
                           AutoInserted
                          (Maybe ClassType)
                          (Maybe (ClassName, PackagePath))
                          (Maybe ImportMode)
                   deriving (Eq, Read, Show)

data ObjectDecl = ObjectDecl ObjectName 
                             DefaultText
                             ClassName
                             (Maybe (ClassName, PackagePath))
                             (Maybe ImportMode)
                   deriving (Eq, Read, Show)

data RelationDecl = RelationDecl  RelName
                                  RelationText 
                                 [RelationTypeDecl]
                                  (Maybe (RelName, PackagePath))
                                  (Maybe ImportMode)
                                  AutoInserted
                    deriving (Eq, Read, Show)

data RelationTypeDecl = RelationTypeDecl ClassName 
                                         ClassName
                                         (Maybe Cardinality) 
                                         (Maybe SuperRel)
                                         (Maybe PackagePath)
                                         (Maybe ImportMode)
                        deriving (Eq, Read, Show)

data ObjectLink = ObjectLink ObjectName ObjectName RelName (Maybe PackagePath) (Maybe ImportMode)
                    deriving (Eq, Read, Show)

data ImportMode = GlobalImp | LocalImp 
                        deriving (Eq, Read, Show)


emptyMMiSSOntology :: String -> InsertMode -> MMiSSOntology 
emptyMMiSSOntology ontoName insertMode = 
  MMiSSOntology {
    name = ontoName,
    classes = Map.empty,
    objects = Map.empty,
    relations = Map.empty,
    objectLinks = [],
    defines = Map.empty,
    mode = insertMode,
    classGraph = empty,
    relationGraph = empty
  }

{--
  MMiSSOntologyFlat enthält dieselben Daten wie MMiSSOntology, klopft aber 
  die Maps sowie die Graphen in Listen flach, um leichter eine Read/Show-Instanz
  anlegen zu können.
--}

emptyMMiSSOntologyFlat :: MMiSSOntologyFlat
emptyMMiSSOntologyFlat = toFlat(emptyMMiSSOntology "" AutoInsert)


toFlat :: MMiSSOntology -> MMiSSOntologyFlat

toFlat o = 
  MMiSSOntologyFlat {
    nameFlat = name o,
    classesFlat = Map.toList (classes o),
    objectsFlat = Map.toList (objects o),
    relationsFlat = Map.toList (relations o),
    objectLinksFlat = objectLinks o,
    definesFlat = Map.toList (defines o),
    modeFlat = mode o,
    classGraphFlat = ((labNodes (classGraph o)),(labEdges (classGraph o))),
    relationGraphFlat = ((labNodes (relationGraph o)),(labEdges (relationGraph o)))
  }

fromFlat :: MMiSSOntologyFlat -> MMiSSOntology

fromFlat o =
  MMiSSOntology {
    name = nameFlat o,
    classes = Map.fromList (classesFlat o),
    objects = Map.fromList (objectsFlat o),
    relations = Map.fromList (relationsFlat o),
    objectLinks = objectLinksFlat o,
    defines = Map.fromList (definesFlat o),
    mode = modeFlat o,
    classGraph = mkGraph (fst (classGraphFlat o)) (snd (classGraphFlat o)),
    relationGraph = mkGraph (fst (relationGraphFlat o)) (snd (relationGraphFlat o))
  }


{---------------------------------------------------------------------------------------------

 Funktionen für das Auslesen von Ontologie-Elementen:

----------------------------------------------------------------------------------------------}

getRelationNames :: MMiSSOntology -> [String]
getRelationNames onto = Map.keys (relations onto)

getOntologyName :: MMiSSOntology -> String
getOntologyName onto = name onto

getClassGraph :: MMiSSOntology -> Gr (String, String, OntoObjectType) String
getClassGraph onto = classGraph onto

getRelationGraph :: MMiSSOntology -> Gr String String
getRelationGraph onto = relationGraph onto

{-- Get a list of all objectlinks included in an ontology --}
getObjectLinks :: MMiSSOntology -> [(ObjectName, ObjectName, RelName, Maybe PackagePath, Maybe ImportMode)]
getObjectLinks onto = map extractObjectLink (objectLinks onto)
                      where
                      extractObjectLink (ObjectLink a b c d e) = (a, b, c, d, e)

{-- Get a list of all relations included in an ontology --}
getRelations :: MMiSSOntology -> [(RelName, 
                                   RelationText, 
                                   (Maybe (RelName, PackagePath)), 
                                   (Maybe ImportMode))]
getRelations onto = map extractRelationDecl (Map.elems(relations onto))
   where
        extractRelationDecl :: RelationDecl -> (RelName, RelationText, 
                                               (Maybe (RelName, PackagePath)), 
                                               (Maybe ImportMode))
        extractRelationDecl (RelationDecl a b _ d e _) = (a, b, d, e)

{-- Get a list of all relationtypes included in an ontology --}
getAllRelationTypes :: MMiSSOntology -> [(RelName, ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath, Maybe ImportMode)]
getAllRelationTypes onto = concat (map getRTDList (Map.elems(relations onto)))
  where
    getRTDList :: RelationDecl -> [(RelName, ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath, Maybe ImportMode)]
    getRTDList (RelationDecl relName _ typeList _ _ _) = map (combineRelTypes relName) typeList

    combineRelTypes :: RelName -> RelationTypeDecl
                      -> (RelName, ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath, Maybe ImportMode)
    combineRelTypes relName (RelationTypeDecl b c d e f g) = (relName, b, c, d, e, f, g)
--    extractRTD :: 
--        (RelName, RelationTypeDecl) 
--          -> (RelName, ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath, Maybe ImportMode)
--    extractRTD (a, (RelationTypeDecl b c d e f g)) = (a, b, c, d, e, f, g)


getRelationTypes :: MMiSSOntology -> RelName -> [(ClassName, ClassName, Maybe SuperRel, Maybe Cardinality, Maybe PackagePath, Maybe ImportMode)]

getRelationTypes onto relname =
  if (Map.member relname (relations onto))
    then let (RelationDecl _ _ l _ _ _) = (relations onto)Map.!relname
         in map (\(RelationTypeDecl a b c d e f) -> (a, b, d, c, e, f)) l
    else []


{-- Get a list of all objects included in an ontology --}
getObjects :: MMiSSOntology -> [(ObjectName, DefaultText, ClassName, 
                                 Maybe (ClassName, PackagePath), (Maybe ImportMode))]
getObjects onto = map extractObjectDecl (Map.elems(objects onto))
                  where
                  extractObjectDecl :: ObjectDecl -> (ObjectName, DefaultText, ClassName, 
                                                                    (Maybe (ClassName, PackagePath)), (Maybe ImportMode))
                  extractObjectDecl (ObjectDecl a b c d e) = (a, b, c, d, e)

{-- Get a list of all classes included in an ontology --}
getClasses :: MMiSSOntology -> [(ClassName, DefaultText, [SuperClass], 
                                          Maybe ClassType, Maybe (ClassName, PackagePath), Maybe ImportMode)]
getClasses onto = map extractClassDecl (Map.elems(classes onto))
                  where
                  extractClassDecl :: ClassDecl -> (ClassName, DefaultText, [SuperClass], 
                                          Maybe ClassType, (Maybe (ClassName, PackagePath)), Maybe ImportMode)
                  extractClassDecl (ClassDecl cln dft scl _ _ clt pack immo) = (cln, dft, scl, clt, pack, immo) 


getDefines :: MMiSSOntology -> Map.Map String String
getDefines o = defines o
 

{---------------------------------------------------------------------------------------------

 Funktionen für das Eintragen von Ontologie-Elementen:

----------------------------------------------------------------------------------------------}

insertDefine :: MMiSSOntology -> String -> String -> WithError MMiSSOntology
insertDefine onto elementName packagePath =
  let defs = defines onto
  in if (Map.member elementName defs)
       then hasError("IsAlreadyDefined: Insertion of a definition: The class/relation/object '" ++ elementName 
                     ++ "' already has a definition.")
       else let newDefs = Map.insert elementName packagePath defs
            in hasValue(
                MMiSSOntology {name = name onto, 
	  	 	       classes = classes onto,
			       objects = objects onto,
			       relations = relations onto,
			       objectLinks = objectLinks onto,
                               defines = newDefs,
			       mode = mode onto,
                               classGraph = classGraph onto,
                               relationGraph = relationGraph onto}
               )


insertClass :: MMiSSOntology -> ClassName -> DefaultText -> [SuperClass] 
            -> (Maybe ClassType) -> (Maybe (ClassName, PackagePath)) -> (Maybe ImportMode)  
            -> WithError (MMiSSOntology)

insertClass onto className optText superCs maybeType package importMode =
  maybe
    (myInsertClass className optText superCs maybeType package importMode)
    (\ (ClassDecl _ _ _ _ auto _ _ _) -> 
      case (mode onto) of
        AutoInsert -> 
          if (auto == True)
            then myInsertClass className optText superCs maybeType package importMode
            else hasError("ClassAlreadyDefined: Insertion of class: " ++ className ++ 
                          " -> Class is properly defined and "++
                          "can't be overridden. (AutoInsert is on).\n")
        _ -> hasError("ClassAlreadyDefined: Insertion of class: " ++ className  ++
                      " -> Class is already defined in Ontology.\n"))
    (Map.lookup className (classes onto))
  where 
    myInsertClass cn opt super classType package importMode =
      let class1 = (cn, (ClassDecl cn opt super [] False classType package importMode))
      in case super of
           []          -> addClasses [class1] super 
           superClasses -> 
               let (_,undefSC) = 
                       partition (\sC -> Map.member sC (classes onto))
                                 superClasses
                   sClassDecls = 
                       map (\sC -> (sC, (ClassDecl sC "" [] [] 
                                              True Nothing Nothing (Just(GlobalImp))))) undefSC
               in if null undefSC
                 then addClasses [class1] super 
                 else case (mode onto) of
                        AutoInsert -> addClasses (class1:sClassDecls) super
                        _  -> hasError("SuperClassNotDefined: Insertion of class: " ++ cn ++ 
                                     " -> Superclass " ++ show undefSC ++ 
                                     " not defined in Ontology.\n")
    addClasses :: [(String, ClassDecl)] -> [SuperClass] 
               -> WithError MMiSSOntology
    addClasses cList superCs = 
       let g = classGraph onto
           newgraph = 
               case length cList of
               x | x == 0 -> g
                 | x == 1 -> 
                     let (className, (ClassDecl _ _ _ _ _ cType _ _)) = head cList
                         (g1, node1) = getInsNode g className cType 
                     in foldl (addIsaEdge node1) g1 superCs		  
                 | x > 1 -> 
                   let (subClass, (ClassDecl _ _ _ _ _ subcType _ _)) = head cList
                       (g1, node1) = getInsNode g subClass subcType
                   in foldl (insClass node1) g1 superCs
       in
         hasValue( onto { classes = addListToMap (classes onto) cList,
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



insertBaseRelation :: MMiSSOntology -> RelName -> DefaultText -> (Maybe (RelName, PackagePath))
                      -> (Maybe ImportMode) -> WithError (MMiSSOntology)

insertBaseRelation onto relName defText origNameAndPackage importMode =
  case Map.lookup relName (relations onto) of
    Nothing -> myInsertRel relName defText
    Just(RelationDecl _ _ _ _ _ auto) -> 
      case (mode onto) of
        AutoInsert -> 
          if (auto == True)
            then myInsertRel relName defText
            else hasError("Insertion of relation: " ++ relName ++ " -> Relation is properly defined and can't be overridden. (AutoInsert is on).\n")
        _ -> hasError("Insertion of relation: " ++ relName ++ " -> Relation is already defined in Ontology.\n")
  where 
    myInsertRel rn def =
      let rel1 = (rn, (RelationDecl rn def [] origNameAndPackage importMode False))
      in addRelations [rel1]
    addRelations rList = 
       hasValue( MMiSSOntology {name = name onto, 
	  		        classes = classes onto,
			        objects = objects onto,
			        relations = addListToMap (relations onto) rList,
			        objectLinks = objectLinks onto,
                                defines = defines onto,
			        mode = mode onto,
                                classGraph = classGraph onto,
                                relationGraph = relationGraph onto} )



insertRelationType :: MMiSSOntology -> RelName -> ClassName -> ClassName -> 
                       Maybe SuperRel -> Maybe Cardinality -> Maybe PackagePath -> 
                       Maybe ImportMode -> WithError (MMiSSOntology)

insertRelationType onto relName source target super cardOpt packagePath importMode =
  do o1 <- lookupClass onto source
     o2 <- lookupClass o1 target
     o3 <- case Map.lookup relName (relations o2) of
             Nothing -> if ((mode o2) == AutoInsert)
                          then return (addRelations o2 [(relName, (RelationDecl relName "" [] Nothing Nothing True))])
                          else hasError("Insertion of relation type: " ++ relName 
                                        ++ " doesn't exist in the Ontology.\n")
             Just((RelationDecl name defText typeList origNameAndPackage relImpMode inserted)) -> 
               let newType = RelationTypeDecl source target cardOpt super packagePath importMode -- Hier anfgen
                   newRel = (RelationDecl name defText (typeList ++ [newType]) origNameAndPackage relImpMode inserted) 
               in  case super of
                       Nothing -> return (addRelations o2 [(name, newRel)])
                       Just(superR) -> 
                         if (Map.member superR (relations onto))
                            then return (addRelations o2 [(name, newRel)])
                            else case (mode onto) of
                                    AutoInsert -> 
                                       let rel2 = (superR, (RelationDecl superR "" [] Nothing Nothing True))
                                       in return(addRelations o2 ((name,newRel):(rel2:[]))) 
                                    _  -> hasError("Insertion of relation: " 
                                                    ++ name ++ " -> Superrelation " 
                                                    ++ superR ++ " not defined in Ontology.\n")
     o4 <- addEdge o3 (classGraph o3) relName source target 
     return o4
  where
    addClasses o cList = 
                 MMiSSOntology {name = name o, 
	  		        classes = addListToMap (classes o) cList,
			        objects = objects o,
			        relations = relations o,
			        objectLinks = objectLinks o,
                                defines = defines o,
			        mode = mode o,
                                classGraph = foldl addClassNodeWithoutDecl (classGraph o) cList ,
                                relationGraph = relationGraph onto}

    addRelations o rList = 
                 MMiSSOntology {name = name o, 
	  		        classes = classes o,
			        objects = objects o,
			        relations = addListToMap (relations o) rList,
			        objectLinks = objectLinks o,
                                defines = defines o,
			        mode = mode o, 
                                classGraph = classGraph o,
                                relationGraph = relationGraph onto} 

    lookupClass o className =
       case Map.lookup className (classes o) of
         Nothing -> if ((mode o) == AutoInsert)
                      then return (addClasses o [(className, (ClassDecl className "" [] [] True Nothing Nothing (Just(LocalImp))))])
                      else hasError("Insertion of relation type: Class " ++ className 
                                        ++ " doesn't exist in the Ontology.\n")
         Just((ClassDecl cn defT sup typeList ai classType package importMode)) ->
           if (cn == source)
             then let mayTypeDecl = (find ((relName ==) . fst) typeList)
                      newClassList = case mayTypeDecl of
                                       Just((_, clist)) -> clist ++ [target]
                                       Nothing -> [target]
                      newTypeList = (deleteBy isEqualTypelist (relName, []) typeList) ++ [(relName, newClassList)]
                  in return (addClasses o [(className, (ClassDecl cn defT sup newTypeList ai classType package importMode))])
             else  return o

    addEdge onto g rel source target = 
      case findLNode g source of
        Nothing -> return(onto)
        Just(snode) -> case findLNode g target of
                         Nothing -> return(onto)
                         Just(tnode) -> 
                            let newg = insEdge (snode, tnode, rel) g
                            in return (MMiSSOntology {name = name onto,
                                                      classes = classes onto,
                                                      objects = objects onto,
			                              relations = relations onto,
			                              objectLinks = objectLinks onto,
                                                      defines = defines onto,
			                              mode = mode onto,
                                                      classGraph = newg,
                                                      relationGraph = relationGraph onto} )


isEqualTypelist :: (RelName, [ClassName]) -> (RelName, [ClassName]) -> Bool
isEqualTypelist (r1, _) (r2, _) = r1 == r2

{-- insert Object --}
insertObject :: MMiSSOntology -> ObjectName -> DefaultText -> ClassName 
             -> (Maybe (ClassName, PackagePath)) -> (Maybe ImportMode) -> WithError (MMiSSOntology)

insertObject onto objectName defText className package importMode =
  do o1 <- if (Map.member objectName (objects onto))
             then hasError("Insertion of object: " ++ objectName ++ " already exists.")
             else return onto 
     o2 <- lookupClass o1 className
     return (MMiSSOntology {name = name onto,
                            classes = classes o2,
                            objects = Map.insert objectName 
                                                 (ObjectDecl objectName defText className package importMode)
                                                 (objects onto) ,
			    relations = relations onto,
			    objectLinks = objectLinks onto,
                            defines = defines onto,
			    mode = mode onto,
                            classGraph = addObjectToGraph objectName className (classGraph onto),
                            relationGraph = relationGraph onto} )
  where
    addClasses o cList = 
                 MMiSSOntology {name = name o, 
	  		        classes = addListToMap (classes o) cList,
			        objects = objects o,
			        relations = relations o,
			        objectLinks = objectLinks o,
                                defines = defines o,
			        mode = mode o,
                                classGraph = foldl addClassNodeWithoutDecl (classGraph onto) cList,
                                relationGraph = relationGraph onto}
    lookupClass o className =
       case Map.lookup className (classes o) of
         Nothing -> if ((mode o) == AutoInsert)
                      then return (addClasses o [(className, (ClassDecl className "" [] [] True Nothing Nothing (Just(GlobalImp))))])
                      else hasError("Insertion of object: " ++ objectName ++ " -> Class " ++ className 
                                        ++ " doesn't exist in the Ontology.\n")
         Just(_) -> return o

    addObjectToGraph name className g = 
       case (findLNode g name) of
         Nothing -> let n = head (newNodes 1 g)
                        newG = (insNode (n, (("_" ++ name ++ "_"), className, OntoObject)) g)
                    in newG
         Just(node) -> g


insertLink :: MMiSSOntology -> ObjectName -> ObjectName -> RelName -> Maybe PackagePath -> Maybe ImportMode 
              -> WithError(MMiSSOntology)

insertLink onto source target relName packagePath importMode =
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
             Nothing -> hasError("Insertion of object link: Relation " ++ relName 
                                        ++ " doesn't exist in the Ontology.\n")
     return (MMiSSOntology {name = name o3,
                            classes = classes o3,
                            objects = objects o3,
			    relations = relations o3,
			    objectLinks = (objectLinks o3) ++ [(ObjectLink source target relName packagePath importMode)],
                            defines = defines o3,
			    mode = mode o3,
                            classGraph = addObjectLinkToGraph source target relName (classGraph onto),
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
    checkClass :: String -> ClassDecl -> [String] -> [String]
    checkClass className (ClassDecl _ _ _ _ inserted _ _ _) l =
      if inserted
        then (l ++ ["Class " ++ className ++ " is not properly defined."])
        else l
    checkRel :: String -> RelationDecl -> [String] -> [String]
    checkRel relName (RelationDecl _ _ _ _ _ inserted) l =
      if inserted
        then (l ++ ["Relation " ++ relName ++ " is not properly defined."])
        else l


getPureClassGraph :: Gr (String,String,OntoObjectType) String -> Gr (String,String,OntoObjectType) String
-- getPureClassGraph g = efilter (\(_,_,edgeType) -> edgeType == "isa") g
getPureClassGraph g = 
  let classNodeList = map (\(nid,_) -> nid) (getTypedNodes g OntoClass)
  in nfilter (`elem` classNodeList) g


nfilter :: DynGraph gr => (Node -> Bool) -> gr a b -> gr a b 
nfilter f = ufold cfilter empty
            where cfilter (p,v,l,s) g = if (f v) 
                                          then (p',v,l,s') & g
                                          else g
                   where p' = filter (\(b,u)->f u) p
                         s' = filter (\(b,w)->f w) s


getTypedNodes :: Gr (String,String,OntoObjectType) String -> OntoObjectType 
                 -> [LNode (String, String, OntoObjectType)]
getTypedNodes g t = 
  map labNode' (gsel (\(_,_,(_,_,objType),_) -> objType == t) g)



exportSpaceTree :: MMiSSOntology -> String
exportSpaceTree onto =
  let subclassGraph = elfilter (== "isa") (getPureClassGraph (classGraph onto))
      topClasses = filter (\(nid,label) -> 
                             if ((filter filterISA (lsuc subclassGraph nid)) == [])
                               then True
                               else False) 
                       (labNodes subclassGraph)
      reversedSubClassGraph = gmap (\(p,v,l,s)->
                                      let newp = map (\(_,n)->("hasSubClass",n)) s
                                          news = map (\(_,n)->("hasSubClass",n)) p
                                      in (newp,v,l,news))
                                    subclassGraph      
      classesStr = foldl (writeClassNode reversedSubClassGraph) "" topClasses     
  in
    "<node>\nRoot\n" ++ classesStr ++ "</node>"

  where
    filterISA :: (Node,String) -> Bool
    filterISA (_,"isa") = True
    filterISA _ = False

    writeClassNode g inStr (nid,(className,_,_)) =
      let thisClassStr = "<node>\n" ++ className ++ "\n" 
          successors = mapMaybe (\(node) -> case (lab g node) of
                                               Just(l) -> Just((node,l))
                                               Nothing -> Nothing 
                                ) 
                                (suc g nid)
          rest = foldl (writeClassNode g) "" (successors)
      in inStr ++ thisClassStr ++ rest ++ "</node>\n" 


exportLatexIndex :: MMiSSOntology -> String
exportLatexIndex onto =
  let subclassGraph = elfilter (== "isa") (getPureClassGraph (classGraph onto))
      topClasses = filter (\(nid,label) -> 
                             if ((filter filterISA (lsuc subclassGraph nid)) == [])
                               then True
                               else False) 
                       (labNodes subclassGraph)
      reversedSubClassGraph = gmap (\(p,v,l,s)->
                                      let newp = map (\(_,n)->("hasSubClass",n)) s
                                          news = map (\(_,n)->("hasSubClass",n)) p
                                      in (newp,v,l,news))
                                    subclassGraph      

      topClasses' = mapMaybe labelToClass
                             topClasses
      classesStr = foldl (writeClassNode reversedSubClassGraph "") "" topClasses'     
      relationsStr = foldl writeRelationName "" (Map.elems (relations(onto)))

      objectsStr = foldl writeObject "" (Map.elems (objects(onto)))

  in
    "\\DispRelationSection{}\n\n" ++ relationsStr ++ "\n\n\\DispClassSection{}\n\n" 
       ++ classesStr ++ "\n\n" ++ "\\DispObjectSection{}\n\n" ++ objectsStr ++ "\n"

  where
    labelToClass :: (Node,(String,String,OntoObjectType)) -> Maybe (ClassDecl, Node)
    labelToClass (nid,(label,_,_)) =
       case Map.lookup label (classes onto) of  
          Nothing -> Nothing
          Just(c) -> Just((c,nid))
                             
    filterISA :: (Node,String) -> Bool
    filterISA (_,"isa") = True
    filterISA _ = False

    writeClassNode g spaceStr inStr (c@(ClassDecl classname defaultText superclasslist relTypes _ _ _ _),nid) =
      let thisClassStr = writeClass spaceStr c 
          successors :: [(ClassDecl, Node)]
          successors = mapMaybe labelToClass (mapMaybe (\(node) -> case (lab g node) of
                                                                       Just(l) -> Just((node,l))
                                                                       Nothing -> Nothing 
                                                       ) 
                                                       (suc g nid)
                                             )
          rest = foldl (writeClassNode g (spaceStr ++ "\\DispIndent")) "" (successors)
      in inStr ++ thisClassStr ++ rest 

    writeClass spaceStr (ClassDecl classname defaultText superclasslist relTypes _ _ _ _) = 
      let superclassstr = case superclasslist of
                             [] -> "{}"
                             (first:rest) -> "{" ++ first ++ "}"
          classCmd = "\\DispClassName{" ++ classname ++ "}{" ++ defaultText ++ "}\\\\\n"
          relationsForClass = foldl (writeRelType (spaceStr ++ "\\DispIndent{}") classname) "" relTypes
      in spaceStr ++ classCmd ++ relationsForClass 

    writeObject inStr (ObjectDecl objectname defaultText classname _ _) =
      inStr ++ "\\DispObjectName{" ++ objectname ++ "}{" ++ classname ++ "}\\\\\n"

    writeObjectLinks inStr (ObjectLink name1 name2 relname _ _) =
      inStr ++ "\\Relate{" ++ relname ++ "}{" ++ name1 ++ "}{" ++ name2 ++ "}" ++ "\n"

    writeRelType spaceStr classname inStr (relName, classList) =
      case Map.lookup  relName (relations onto) of
        Nothing -> inStr ++ "\n"
        Just(rel) -> 
          let relationCmds = foldl (writeRelationCmd spaceStr classname relName) "" (nub classList)
          in inStr ++ relationCmds

    writeRelationCmd spaceStr classname relName inStr targetClass =
      let s1 = "\\DispRelation{}"
          s2 = "\\DispRelationNameAtClass{" ++ relName ++ "}"
          s4 = "\\DispRelationTarget{" ++ targetClass ++ "}"
      in inStr ++ spaceStr ++ s1 ++ s2 ++ s4 ++ "\\\\\n"

    writeRelationName inStr (RelationDecl relName relText _ _ _ _) =
      inStr ++ "\\DispRelationName{" ++ relName ++ "}{" ++ relText ++ "}\\\\\n"



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
writeOWLLink inStr (ObjectLink object1 object2 relName _ _) =
 let start = "<rdf:Description rdf:about=\"#" ++ object1 ++ "\">\n"
     propStr = "<" ++ relName ++ " rdf:resource=\"#" ++ object2 ++ "\"/>\n"
     end = "</rdf:Description>\n"
 in inStr ++ start ++ propStr ++ end


writeOWLObject :: String -> ObjectDecl -> String
writeOWLObject inStr (ObjectDecl name defText instanceOf _ _) =
 let start = "<rdf:Description" ++ " rdf:about=\"#" ++ name ++ "\">\n"
     defTextStr = "<MPhrase>" ++ (latexToEntity defText) ++ "</MPhrase>\n"
     classStr = "<rdf:type>\n  <owl:Class rdf:about=\"#" ++ instanceOf ++ "\"/>\n</rdf:type>"
     end = "</rdf:Description>"
 in inStr ++ start ++ defTextStr ++ classStr ++ end


writeOWLClass :: String -> ClassDecl -> String

writeOWLClass inStr (ClassDecl name defText super relTypes _ _ _ _) =
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
                        "      <owl:Class rdf:about=\"#" ++ (head classList) ++ "\"/>\n" ++ 
			"    </owl:allValuesFrom>\n" 
	     onPropStr = "    <owl:onProperty>\n" 
			  ++ "      <owl:ObjectProperty rdf:about=\"#" ++ relName ++ "\"/>\n"
			  ++"    </owl:onProperty>\n" 
	     end = "  </owl:Restriction>\n</rdfs:subClassOf>\n"
	  in inStr ++ start ++ onPropStr ++ classStr ++ end
    _ -> let start = "<rdfs:subClassOf>\n  <owl:Restriction>\n    <owl:onProperty>\n" ++
                     "        <owl:ObjectProperty rdf:about=\"#" ++ relName ++ "\"/>\n" ++ 
                     "    </owl:onProperty>\n" ++
                     "    <owl:allValuesFrom>\n" ++
                     "     <owl:Class>\n" ++
                     "        <owl:unionOf rdf:parseType=\"Collection\">\n"
             restrictions = foldl writeSingleClassRestriction "" classList
             end = "</owl:unionOf>\n</owl:Class>\n</owl:allValuesFrom>\n</owl:Restriction>\n</rdfs:subClassOf>\n"
         in inStr ++ start ++ restrictions ++ end

writeSingleClassRestriction :: String -> ClassName -> String
writeSingleClassRestriction inStr className 
  = inStr ++ "<owl:Class rdf:about=\"#" ++ className ++  "\"/>\n"



writeOWLRelation :: String -> RelationDecl -> String

writeOWLRelation inStr (RelationDecl relName relText _ _ _ _) =
 let start = "<owl:ObjectProperty rdf:ID=\"" ++ relName ++ "\">\n"
     defText = "  <MPhrase>" ++ relText ++ "</MPhrase>\n"
     end = "</owl:ObjectProperty>\n"
   in inStr ++ start ++ defText ++ end


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


latexToEntityList :: [(String, String)]
latexToEntityList = [("<", "&#38;#60;"), (">", "&#62;"), ("&", "&#38;#38;")]
                    ++ [("'", "&#39;"), ("\"", "&#34;")]



latexToEntity :: String -> String
latexToEntity inStr = foldl (applyTranslation "") inStr latexToEntityList

applyTranslation :: String -> String -> (String, String) -> String
applyTranslation outStr inStr (search, replaceStr) =
   if lenInStr < lenSearch 
     then outStr ++ inStr
     else if (isPrefixOf search inStr)
            then applyTranslation (outStr ++ replaceStr) (drop lenSearch inStr)  (search, replaceStr)
            else applyTranslation (outStr ++ (take 1 inStr)) (drop 1 inStr)  (search, replaceStr)
   where
   lenInStr = genericLength inStr
   lenSearch = genericLength search   


findLNode :: Gr (String, String, OntoObjectType) String -> String -> Maybe Node
findLNode gr label = case (gsel (\(p,v,(l, _, _),s) -> l == label) gr) of
                      [] -> Nothing
                      conList -> Just(node' (head conList))               


addListToMap :: (Map.Map String a) -> [(String, a)] -> (Map.Map String a) 
addListToMap m l =
      foldl insToMap m l
  where 
    insToMap :: (Map.Map String a) -> (String, a) -> (Map.Map String a)
    insToMap m (s,c) = Map.insert s c m


-- Insert a class-node into the graph. The ClassDecl doesn't have to be considered, because
-- classes added here have no Superclass (they are inserted in AutoInsert-Mode). 
addClassNodeWithoutDecl :: Gr (String, String, OntoObjectType) String -> (String, ClassDecl) 
                           -> Gr (String, String, OntoObjectType) String
addClassNodeWithoutDecl g (cn, _) = 
  case findLNode g cn of
    Just(_) -> g
    Nothing -> 
      let node = head (newNodes 1 g)
      in  insNode (node, (cn, "", OntoClass)) g


graphvizNodeAtts :: MMiSSOntology -> (String, String, OntoObjectType) -> String
graphvizNodeAtts o (cname, _, t) = 
  if (t == OntoObject) 
    then "label = \"" ++ cname ++ "\", URL=\"" ++ url ++  "\", color = \"yellow\", shape = \"box\", style = \"filled\", fontname=\"Helvetica\""
    else "label=<<TABLE BORDER=\"1\" CELLBORDER=\"0\" BGCOLOR=\"lightcyan\">"
	 ++ "  <TR><TD><FONT FACE=\"Helvetica\" POINT-SIZE=\"12.0\">" ++ phrase ++ "</FONT></TD></TR>"
	 ++ "  <TR><TD><FONT FACE=\"Helvetica\" POINT-SIZE=\"8.0\">" ++ cname ++ "</FONT></TD></TR></TABLE>>,"
         ++ "  shape = \"plaintext\", URL=\"" ++ url ++ "\""
  where
    phrase = case Map.lookup cname (classes o) of
                Nothing -> ""
                (Just(ClassDecl _ p _ _ _ _ _ _)) -> p
    url = (name o) ++ ".pdf#" ++ cname


graphvizEdgeAtts :: MMiSSOntology -> String -> String
graphvizEdgeAtts _ str = 
  case str of
    "isa" -> "dir = \"back\", arrowtail = \"empty\", arrowsize = 1.5, style = \"bold\", fontname=\"Helvetica\", fontsize=10.0"
    "instanceOf" -> "style = \"dashed\", arrowsize = 1.5, style = \"bold\", fontname=\"Helvetica\", fontsize=10.0"
    otherwise ->"label = \" " ++ str ++ "\", dir = \"back\", arrowsize = 1.5, style = \"bold\", fontname=\"Helvetica\", fontsize=12.0"


---------------------------------------------------------------------------
-- Diverse Instanzen für die MMiSSOntology-Datenstrukturen
---------------------------------------------------------------------------


instance Monad m => HasBinary MMiSSOntologyFlat m where
   writeBin = mapWrite ReadShow
   readBin = mapRead (\ (ReadShow x) -> x)

--instance Show (String, String, OntoObjectType) where
--  show (name,_,t) = show name

instance Eq (Gr (String, String, OntoObjectType) String) where
  (==) = mapEq
          (\(g) -> (labNodes g, labEdges g))

instance Eq (Gr String String) where
  (==) = mapEq
          (\(g) -> (labNodes g, labEdges g))

--instance Show (Gr a b) where
--  show g = show (labNodes g, labEdges g)

--instance (Read a, Read b) => Read (Gr a b) where
--  readsPrec 0 t = let (nodes, edges) = read t
--                  in [(mkGraph nodes edges, "")]

instance (Ord k, Read k, Read e) => Read (Map.Map k e) where
    readPrec = do elements <- set (readPair readPrec readPrec)
                  return $ Map.fromList elements

-- ^ @(readPrec p1 p2)@ parses a pair of things with the syntax @a:=b@
--  where @a@ is parsed by @p1@,
--    and @b@ is parsed by @p2@
readPair :: ReadPrec a -> ReadPrec b -> ReadPrec (a,b)
readPair reada readb =
    do a <- reset reada
       L.Symbol ":=" <- lexP
       b <- reset readb
       return (a,b) 

set :: ReadPrec a -> ReadPrec [a]
-- ^ @(set p)@ parses a list of things parsed by @p@,
-- using the curly-braces syntax.
set readx =
    parens
    ( do L.Punc "{" <- lexP
         (setRest False +++ setNext)
    )
 where
  setRest started =
    do L.Punc c <- lexP
       case c of
         "}"           -> return []
         "," | started -> setNext
         _             -> pfail

  setNext =
    do x  <- reset readx
       xs <- setRest True
       return (x:xs) 

