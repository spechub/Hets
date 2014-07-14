module StateMachineParser where
import qualified Data.Map as Map
import System.IO
import Text.XML.Light
import UML
import Utils
import XMINames
import Data.Maybe

processRegion :: Element -> Maybe Region
processRegion el = Nothing -- Just Region{states=[], transitions=[]}

processPseudoState :: Element -> (Id, PseudoState)
processPseudoState el = (fromMaybe "" (findAttr attrIdName el), PseudoState {pseudoStateName = fromMaybe "" (findAttr nameName el), pseudoStateType = fromMaybe "" (findAttr (sName "kind") el)})

processState :: Element -> (Id, State)
processState el = (fromMaybe "" (findAttr attrIdName el), State { stateName = fromMaybe "" (findAttr nameName el),
                                region = processRegion (head (findChildren smRegionName el))})

processTransition :: Element -> Transition
processTransition el = Transition {source = fromMaybe "" (findAttr (sName "source") el), target = fromMaybe "" (findAttr (sName "target") el), trigger = "", guard = Nothing, event = Nothing}

parseTransitions :: [Element] -> [Transition]
parseTransitions [] = []
parseTransitions (el : lis) = ((processTransition el) : (parseTransitions lis))

parsePseudoStates :: [Element] -> [(Id, PseudoState)]
parsePseudoStates [] = []
parsePseudoStates (el : lis) = case (findAttr typeName el) of
                Nothing -> parsePseudoStates lis
                Just "uml:Pseudostate" -> ((processPseudoState el) : (parsePseudoStates lis))
                Just _ -> parsePseudoStates lis

parseStates :: [Element] -> [(Id, State)]
parseStates [] = []
parseStates (el : lis) =
        case (findAttr typeName el) of
                Nothing -> parseStates lis
                Just "uml:State" -> ((processState el) : (parseStates lis))
                Just _ -> parseStates lis

parseStateMachine :: Element -> Model
parseStateMachine el = StateMachine (Map.fromList (parseStates (findChildren smSubvertexName (head (findChildren smRegionName el))))) (parseTransitions (findChildren (sName "transition") (head (findChildren smRegionName el)))) (Map.fromList (parsePseudoStates (findChildren smSubvertexName (head (findChildren smRegionName el)))))
