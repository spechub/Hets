{- |
Description :  Data structure for UML Class Diagrams
Copyright   :  (c) Martin Glauer

Maintainer  :  martin.glauer@st.ovgu.de
Stability   :  experimental

Structure used by ClassDiagramParser.hs
-}

module UML where
import qualified Data.Map as Map
import StateMachine
data Model = ClassModel CM
                | StateMachine [Entity] [Transition]
		| StateMachineR Region deriving Show

data CM = CM {
        cmName :: String,
        cmClasses :: (Map.Map Id Class), -- These mappings are still necessary. You will need them, e.g. to get super classes by their id. (subject to change - someday)
        cmAssociations :: (Map.Map Id Association),
        cmInterfaces :: (Map.Map Id Interface),
        cmPackageMerges :: [Id],
	cmAssociationClasses :: (Map.Map Id  AssociationClass),
        cmSignals :: (Map.Map Id Signal),
	cmPackages:: [Package]} deriving Show

data ClassEntity = CL Class | AC AssociationClass deriving Show

data Package = Package {
        packageName :: String,
        classes :: (Map.Map Id Class),
        associations :: (Map.Map Id Association),
        interfaces :: (Map.Map Id Interface),
        packageMerges :: [Id],
	packageAssociationClasses :: (Map.Map Id  AssociationClass),
        signals :: (Map.Map Id Signal),
	packagePackages :: [Package]} deriving Show

--These do not work very well, yet.
--	-> AssociationClasses can target classes but not other other AssociationClass  (ToDo)

data AssociationClass = AssociationClass {
        acClass :: Class,
        acAsso :: Association} deriving Show


data Class = Class {
        super :: [Id],
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
	show attr = (attrName attr) ++ ":" ++ (attrType attr) ++ "[" ++ (attrLowerValue attr) ++ ", " ++ (attrUpperValue attr) ++ "]" 

data Procedure = Procedure {
        procName :: String,
        procPara :: [(String, Type)],
        procReturnType :: Maybe Type,
        procPackImports :: [Id],
        procElemImports :: [Id],
        procVisibility :: String
} deriving Show

data Association = Association {
        ends :: [End]
} deriving Show

data EndType = Composition | Aggregation | Normal deriving Show

-- The XMI-Standard ignores ends that are compositions or aggregations but adds attributes to the corresponding class. Leads to edges having only one end, which is quite inconvenient.
--	Thus in this DS above mentioned attributes are ignored and the corresponding (special) edges recreated. These edges are marked by the non-normal EndTypes.
data End = End {
endTarget :: ClassEntity,
label :: Label,
endType :: EndType
}

instance Show End where
	show end = case endTarget end of 
			CL cl -> "End("++ ((show.endType) end) ++ "): " ++ (className cl) ++ (show (label end))
			AC ac -> "End("++ ((show.endType) end) ++ "): " ++ (className (acClass ac))   ++ (show (label end))

data Interface = Interface {
interfaceName :: String
} deriving Show

data Label = Label {upperValue :: String,
lowerValue :: String} 

instance Show Label where
	show l = "[" ++ (lowerValue l) ++ ", " ++ (upperValue l) ++ "]"

data Signal = Signal {
        sigSuper :: [Id],
        signalName :: String,
        sigAttr :: [Attribute],
        sigProc :: [Procedure]
} deriving Show

type Id = String
type Type = String  --These types are somewhat cryptic in XMI. They are left as-is - who knows who needs this. Note that they might contain class ids
