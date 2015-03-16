module UML.StateMachineParser where
import qualified Data.Map as Map
import System.IO
import Text.XML.Light
import UML.UML
import UML.Utils
import UML.XMINames
import Data.Maybe
import UML.StateMachine 

processRegion :: Element -> (Region,[(String,Entity)])
processRegion el = (Region {states=ent, transitions=trans}, emap)
	where (ent, trans,emap) = readEverything el

--processRegionMap :: Element ->  [(String, Entity)]
--processRegionMap el = readMap el


mergeEAnnotations :: Element -> Maybe String -> [Element]
mergeEAnnotations el st = case st of 
			Nothing -> foldl (++) [] (map elChildren annots)
			Just s -> foldl (++) [] (map (\x -> (findChildren (sName s) x)) annots)
			where annots = (findChildren (sName "eAnnotations" ) el)

processPseudoState :: Element -> (Entity,[(String,Entity)])
processPseudoState el = (ps, [(id,ps)])
			where 	id = fromMaybe "" (findAttr attrIdName el)
				ps = case (findAttr (sName "kind") el) of 
					Just "exitPoint" -> ExitState (fromMaybe "" (findAttr nameName el))
					Just "fork" -> Fork
					Just "join" -> Join
					Just "choice" -> Choice
					Just "junction" -> Junction
					Just "deepHistory" -> DeepHistory
					Just "shallowHistory" -> ShallowHistory
					Nothing -> InitialState (fromMaybe "" (findAttr nameName el)) 
					_ -> error ("No kind: " ++ (fromMaybe "ERROR" (findAttr nameName el)))

--processState :: Element -> Entity
--processState el =  fromJust $ Map.lookup (fromJust(findAttr nameName el)) eMap
--	where 	regs = (map processRegion  (findChildren smRegionName el))
--		p = (fromMaybe "" (findAttr attrIdName el), State (fromMaybe "" )  regs)

processState :: Element -> (Entity,[(String, Entity)])
processState el =  (snd p,p:regMap)
	where 	regMap = foldl (++) [] (map (snd.processRegion) regNames)
		regNames = (findChildren smRegionName el)
		p = (fromMaybe "" (findAttr attrIdName el), State (fromMaybe "" (findAttr nameName el)) (map (fst.processRegion) regNames))

processTransition :: Element -> Transition
processTransition el = Transition {source = (fromJust (findAttr (sName "source") el)), target = (fromJust (findAttr (sName "target") el)), trigger = tr, guard = gu, effect = ef}
	where 	tr = case trCand of 
			[] -> Nothing 
			_ -> findAttr (sName "value") $ head (findChildren (sName "defaultValue") (head trCand))
		ef = case (findChildren (sName "effect") el) of
			[] -> Nothing
			efs -> findAttr (sName "redefinedBehavior") (head efs)
		trCand = case (elChildren el) of
				[] -> [] 
				_ -> (filter (\x -> ((Just "ReceivedEvent") == (findAttr (sName "name") x))) (mergeEAnnotations el (Just "contents")))

		gu = case (findAttr (sName "guard") el) of 
			Nothing -> Nothing -- (show el)
			Just id ->  case findChildren (sName "specification" ) rules of 
					[] -> Just $ show el
					_ -> findAttr (sName "value") $ head (findChildren (sName "specification" ) rules)
					where 	rules = (head (filter (\x -> ((Just id) == findAttr attrIdName x))  ruleCands))
					      	ruleCands =  (findChildren (sName "ownedRule" ) el)--foldl (++) [] (map (\x -> (findChildren (sName "ownedRule" ) x)) annots)
						--annots = (findChildren (sName "eAnnotations" ) el) 
		


parseTransitions :: [Element] -> [Transition]
parseTransitions [] = []
parseTransitions (el : lis) = ((processTransition el) : (parseTransitions lis))


parseStates :: [Element] -> ([Entity],[(String,Entity)])
parseStates [] = ([],[])
parseStates (el : lis) =
        case (findAttr typeName el) of
                Nothing -> (ent,emap)
                Just "uml:State" -> ((fst (processState el)):ent, (snd (processState el)) ++ emap) 
		Just "uml:Pseudostate" -> ((fst (processPseudoState el)):ent, (snd (processPseudoState el)) ++ emap)
                Just _ -> (ent, emap)
	where (ent, emap) = (parseStates lis)


--readMap :: Element -> [(String, Entity)]
--readMap el = foldl (++) [] (map processStateMap (findChildren smSubvertexName el))

readEverything :: Element -> ([Entity],[Transition],[(String,Entity)])
readEverything el = (ent, trans, emap) 
	where 	(ent,emap) = parseStates (findChildren smSubvertexName el)
		trans = parseTransitions (findChildren (sName "transition") el)

parseStateMachine :: Element -> Model
parseStateMachine el = case ent of 
			[] -> StateMachineR (fst ((processRegion  (head (findChildren smRegionName el)))))
			_ -> StateMachine ent trans 
			
	--eMap = Map.fromList (readMap (head (findChildren smRegionName el)))
	where (ent, trans,eMap) = readEverything el
