module UML where
import qualified Data.Map as Map

data Model = 	ClassModel [Package]
		|StateMachine (Map.Map Id State) [Transition] (Map.Map Id PseudoState)
		|Err String deriving Show

data Package = Package{
	packageName::String,
	classes::(Map.Map Id Class), 
	associations::[Association], 
	interfaces::(Map.Map Id Interface),
	packageMerges::[Id]} deriving Show

data Class = Class {	
	super::[Id],
	className::String,
	attr::[Attribute],
	proc::[Procedure]
} deriving Show

data Attribute = Attribute{
	attrName::String,
	attrType::Type	
} deriving Show

data Procedure = Procedure{
	procName::String,
	procPara::[(String,Type)],
	procReturnType::Maybe Type,
	procPackImports::[Id],
	procElemImports::[Id]
} deriving Show

data Association = Association{
	ends::[End]
} deriving Show

data End = End{
endTarget :: Id,
label::Label
} deriving Show

data Interface=Interface{
interfaceName::String
} deriving Show

type Id = String
type Type = String

data Label = Label{upperValue::String,
lowerValue::String} deriving Show


--begin:StateMachines

data Region = Region{
	states::[State],
	transitions::[Transition],
	pseudoStates::[PseudoState]}deriving Show

data PseudoState = PseudoState{
pseudoStateName::String,
pseudoStateType::String
}deriving Show

data State=State{
	region::Maybe Region,
	stateName::String
}deriving Show

data Transition = Transition{
	source::String,
	target::String,
	trigger::Trigger,
	guard::Maybe Guard,
	event::Maybe Event}deriving Show

type Trigger = String
type Guard = String
type Event = String
