{- |
Description :  Data structure for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  martin.glauer@st.ovgu.de
Stability   :  experimental

Structure used by ClassDiagramParser.hs
-}

module UML.UML where
import qualified Data.Map as Map
import Data.Maybe
import UML.StateMachine

data Model = ClassModel CM
                | StateMachine [Entity] [Transition]
		| StateMachineR Region deriving Show

data CM = CM {
        cmName :: String,
        cmClasses :: (Map.Map Id Class), -- These mappings are still necessary. You will need them, e.g. to get super classes by their id. (subject to change - someday)
        cmAssociations :: (Map.Map Id Association),
        cmInterfaces :: (Map.Map Id Interface),
        cmPackageMerges :: [Id],
	cmEnums :: Map.Map Id UML.UML.Enum,
	cmAssociationClasses :: (Map.Map Id  AssociationClass),
        cmSignals :: (Map.Map Id Signal),
	cmPackages:: [Package]} deriving Show

data ClassEntity = CL Class | AC AssociationClass | EN UML.UML.Enum deriving Show

instance Eq ClassEntity where
	(==) x1 x2 = (showClassEntityName x1) == (showClassEntityName x2)

data Package = Package {
        packageName :: String,
        classes :: (Map.Map Id Class),
        associations :: (Map.Map Id Association),
        interfaces :: (Map.Map Id Interface),
        packageMerges :: [Id],
	packageEnums :: Map.Map Id UML.UML.Enum,
	packageAssociationClasses :: (Map.Map Id  AssociationClass),
        signals :: (Map.Map Id Signal),
	packagePackages :: [Package]} deriving Show

--These do not work very well, yet.
--	-> AssociationClasses can target classes but not other other AssociationClass  (ToDo)

data AssociationClass = AssociationClass {
        acClass :: Class,
        acAsso :: Association} deriving Show


data Class = Class {
        super :: [ClassEntity],
        className :: String,
        attr :: [Attribute],
        proc :: [Procedure]
} deriving Show

data Attribute = Attribute {
        attrName :: String,
        attrType :: Type,
        attrUpperValue :: String,
        attrLowerValue :: String,
        attrVisibility :: String
}

instance Show Attribute where 
	show attr = (attrName attr) ++ ":" ++ ((show.attrType) attr) ++ "[" ++ (attrLowerValue attr) ++ ", " ++ (attrUpperValue attr) ++ "]" 

data Procedure = Procedure {
        procName :: String,
        procPara :: [Attribute],
        procReturnType :: Maybe Type,
        procPackImports :: [Id],
        procElemImports :: [Id],
        procVisibility :: String
} deriving Show


data Enum = Enum{
		enumName :: String,
		enumLiterals :: [Literal]} deriving Show

data Literal = Literal{ literalName:: String,
			literalOwner :: UML.UML.Enum} 

instance Show Literal where
	show lit = literalName lit

data Association = Association {
        ends :: [End],
	assoName :: String
} deriving Show

data EndType = Composition | Aggregation | Normal deriving (Show,Eq)

-- The XMI-Standard ignores ends that are compositions or aggregations but adds attributes to the corresponding class. Leads to edges having only one end, which is quite inconvenient.
--	Thus in this DS above mentioned attributes are ignored and the corresponding (special) edges recreated. These edges are marked by the non-normal EndTypes.
data End = End {
endTarget :: ClassEntity,
label :: Label,
endName :: Maybe String,
endType :: EndType
} deriving Eq

showClassEntityName :: ClassEntity -> String
showClassEntityName (CL x) = className x
showClassEntityName (AC x) = className (acClass x)
showClassEntityName (EN x) = enumName x
instance Show End where
	show end = case endTarget end of 
			CL cl -> "End " ++ (fromMaybe "" (endName end)) ++"("++ ((show.endType) end) ++ "): " ++ (className cl) ++ (show (label end))
			AC ac -> "End " ++ (fromMaybe "" (endName end)) ++"("++ ((show.endType) end) ++ "): " ++ (className (acClass ac))   ++ (show (label end))

data Interface = Interface {
interfaceName :: String
} deriving Show

data Label = Label {upperValue :: String,
lowerValue :: String}  deriving Eq

instance Show Label where
	show l = "[" ++ (lowerValue l) ++ ", " ++ (upperValue l) ++ "]"

data Signal = Signal {
        sigSuper :: [ClassEntity],
        signalName :: String,
        sigAttr :: [Attribute],
        sigProc :: [Procedure]
} deriving Show

type Id = String
data UMLType = CE ClassEntity | UMLString | UMLInteger | UMLBool | UMLUnlimitedNatural | UMLReal | UMLSequence Type | UMLSet Type | UMLOrderedSet Type | UMLBag Type | Other String deriving Show  --These types are somewhat cryptic in XMI. They are left as-is - who knows who needs this. Note that they might contain class ids

data Type = Type{
	umltype::UMLType,
	typeUnique::Bool,
	typeOrdered::Bool}

instance Show Type where
	show t = show (umltype t)
