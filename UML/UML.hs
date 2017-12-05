{- |
Description :  Data structure for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  glauer@iws.cs.ovgu.de
Stability   :  experimental

Structure used by ClassDiagramParser.hs
-}

-- |This module contains the general data structure for UML Class Diagrams.

module UML.UML where
import qualified Common.Id
import qualified Data.Map         as Map
import           Data.Maybe
import           Prelude          hiding (Enum)
import 		 Data.Data 	  hiding (DataType)
import           UML.StateMachine

data Model = ClassModel CM
                | SM StateMachine deriving Show

-- |A UML Class Model 
data CM = CM {
        cmName               :: String,
        cmClasses            :: (Map.Map Id Class), 
        cmAssociations       :: (Map.Map Id Association),
        cmInterfaces         :: (Map.Map Id Interface),
        cmPackageMerges      :: [Id],
        cmEnums              :: Map.Map Id UML.UML.Enum,
        cmAssociationClasses :: (Map.Map Id  AssociationClass),
        cmSignals            :: (Map.Map Id Signal),
        cmPackages           :: [Package]} deriving Show

-- ^These mappings are still necessary. You will need them, e.g. to get 
-- super classes by their id. (subject to change - someday - maybe)

instance Common.Id.GetRange CM where
  getRange _ = Common.Id.nullRange
  rangeSpan _ = []

data ClassEntity = CL Class 
                    | AC AssociationClass
                    | EN UML.UML.Enum
		    | DT UML.UML.DataType deriving (Ord, Show)

instance Eq ClassEntity where
    (==) x1 x2 = (showClassEntityName x1) == (showClassEntityName x2)

data Package = Package {
        packageName               :: String,
        classes                   :: (Map.Map Id Class),
        associations              :: (Map.Map Id Association),
        interfaces                :: (Map.Map Id Interface),
        packageMerges             :: [Id],
        packageEnums              :: Map.Map Id UML.UML.Enum,
        packageAssociationClasses :: (Map.Map Id  AssociationClass),
        signals                   :: (Map.Map Id Signal),
        packagePackages           :: [Package]} deriving (Eq, Ord, Show)

-- These do not work very well, yet.
--    -> AssociationClasses can contain classes but not 
--       other AssociationClass

data AssociationClass = AssociationClass {
        acClass :: Class,
        acAsso  :: Association} deriving (Eq, Ord, Show)


data Class = Class {
        super     :: [ClassEntity],
        className :: String,
        attr      :: [Attribute],
        proc      :: [Procedure]} deriving (Eq, Ord, Show)

data DataType = DataType {
        dtsuper :: [ClassEntity],
	      dtName  :: String,
	      dtattr  :: [Attribute],
        dtproc  :: [Procedure] } deriving (Eq, Ord, Show)

data Attribute = Attribute {
        attrName       :: String,
        attrType       :: Type,
        attrUpperValue :: String,
        attrLowerValue :: String,
        attrVisibility :: String} deriving (Eq, Ord)

instance Show Attribute where
    show attri = (attrName attri) ++ ":" ++ ((show . attrType) attri) ++ "[" 
                    ++ (attrLowerValue attri) ++ ", " 
                    ++ (attrUpperValue attri) ++ "]"

data Procedure = Procedure {
        procName        :: String,
        procPara        :: [Attribute],
        procReturnType  :: Maybe Type,
        procPackImports :: [Id],
        procElemImports :: [Id],
        procVisibility  :: String} deriving (Eq, Ord, Show)


data Enum = Enum {
        enumName     :: String,
        enumLiterals :: [Literal]} deriving (Eq, Ord, Show)

data Literal = Literal { literalName :: String,
            literalOwner             :: UML.UML.Enum}  deriving (Eq, Ord)

instance Show Literal where
    show lit = literalName lit



data Association = Association {
        ends     :: [End],
        assoName :: String} deriving (Eq, Ord, Show)

data EndType = Composition | Aggregation | Normal deriving (Eq, Ord, Show)

-- The XMI-Standard ignores ends that are compositions or aggregations but adds
-- attributes to the corresponding class. Leads to edges having only one end, 
-- which is quite inconvenient.
-- Thus in this DS above mentioned attributes are ignored and the corresponding
-- (special) edges recreated. These edges are marked by the non-normal EndTypes.

data End = End {
        endTarget :: ClassEntity,
        label     :: Label,
        endName   :: Maybe String,
        endType   :: EndType} deriving (Eq, Ord)

showClassEntityName :: ClassEntity -> String
showClassEntityName (CL x) = className x
showClassEntityName (AC x) = className (acClass x)
showClassEntityName (EN x) = enumName x
showClassEntityName (DT x) = dtName x
instance Show End where
    show end = case endTarget end of
            CL cl -> "End " ++ (fromMaybe "" (endName end)) ++ "(" 
                            ++ ((show . endType) end) ++ "): " ++ (className cl)
                            ++ (show (label end))
            AC ac -> "End " ++ (fromMaybe "" (endName end)) ++ "(" 
                            ++ ((show . endType) end) ++ "): " 
                            ++ (className (acClass ac))   
                            ++ (show (label end))
            EN x -> "End "  ++ (fromMaybe "" (endName end)) 
                            ++ "(" ++ ((show . endType) end) ++ "): " 
                            ++ (show x) ++ (show (label end))

data Interface = Interface {
        interfaceName :: String} deriving (Eq, Ord, Show)

data Label = Label {
        upperValue :: String,
        lowerValue :: String} deriving (Eq, Ord)

instance Show Label where
    show l = "[" ++ (lowerValue l) ++ ", " ++ (upperValue l) ++ "]"

data Signal = Signal {
        signalName :: String} deriving (Eq, Ord, Show)

type Id = String
data UMLType = CE ClassEntity | UMLString | UMLInteger | UMLBool 
                | UMLUnlimitedNatural | UMLReal | UMLSequence Type 
                | UMLSet Type | UMLOrderedSet Type | UMLBag Type 
                | Other String deriving (Show, Eq, Ord)  
                -- The "Other" types are somewhat cryptic in XMI. 
                -- They are left as-is - who knows who needs this. 
                -- Note that they might contain class ids

data Type = Type {  
    umltype    :: UMLType,
    typeUnique  :: Bool,
    typeOrdered :: Bool} deriving (Eq, Ord)

instance Show Type where
    show t = show (umltype t)

compositionEnds :: Association -> (End, End)
compositionEnds ass = (corigin, ctarget)
        where
            corigin = head $ filter isComposedEnd $ ends ass
            ctarget = case (filter (not . (corigin ==)) (ends ass)) of
                        (x : _) -> x
                        [] -> error $ show $ ends ass

isComposedEnd :: End -> Bool
isComposedEnd en = (endType en) == Composition

isComposition :: Association -> Bool
isComposition as = any isComposedEnd (ends as)

umlTypeString :: UMLType -> String
umlTypeString (CE c) = showClassEntityName c
umlTypeString (UMLString) = "buml:String"
umlTypeString (UMLInteger) = "buml:Integer"
umlTypeString (UMLBool) = "buml:Bool"
umlTypeString (UMLUnlimitedNatural) = "buml:NaturalNumber"
umlTypeString (UMLReal) = "buml:Real"
umlTypeString _ = ""

defaultType :: ClassEntity -> Type
defaultType ce = Type {umltype = CE ce, typeOrdered = False, typeUnique = True}
