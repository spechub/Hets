module UML.StateMachineParser where
import           Data.Maybe
import           Text.XML.Light
import           UML.StateMachine
import           UML.UML
import           UML.XMINames



processRegion :: Maybe String -> Element -> (Region, [(String, Entity)])
processRegion xmiv el = (Region {states = ent, transitions = trans}, emap)
    where (ent, trans, emap) = readEverything xmiv el

--processRegionMap :: Element ->  [(String, Entity)]
--processRegionMap el = readMap el


mergeEAnnotations :: Element -> Maybe String -> [Element]
mergeEAnnotations el st = case st of
            Nothing -> foldl (++) [] (map elChildren annots)
            Just s -> foldl (++) [] (map (\ x -> (findChildren (sName s) x)) annots)
            where annots = (findChildren (sName "eAnnotations" ) el)

processPseudoState :: Maybe String -> Element -> (Entity, [(String, Entity)])
processPseudoState xmiv el = (ent, [(id1, ent)])
            where
                ent = Entity id1 name et
                id1 = fromMaybe "" (findAttr (attrIdName xmiv) el)
                name = (fromMaybe "" (findAttr nameName el))
                et = case (findAttr (sName "kind") el) of
                    Just "exitPoint" -> ExitState  
                    Just "fork" -> Fork 
                    Just "join" -> Join 
                    Just "choice" -> Choice 
                    Just "junction" -> Junction 
                    Just "deepHistory" -> DeepHistory 
                    Just "shallowHistory" -> ShallowHistory 
                    Nothing -> InitialState 
                    Just x -> error ("State kind not known: " ++ (show x))

--processState :: Element -> Entity
--processState el =  fromJust $ Map.lookup (fromJust(findAttr nameName el)) eMap
--    where     regs = (map processRegion  (findChildren smRegionName el))
--        p = (fromMaybe "" (findAttr attrIdName el), State (fromMaybe "" )  regs)

processState :: Maybe String -> Element -> (Entity, [(String, Entity)])
processState xmiv el =  (snd p, p : regMap)
    where
        regMap = foldl (++) [] (map (snd . (processRegion xmiv)) regNames)
        id = fromJust (findAttr (attrIdName xmiv) el)
        regNames = (findChildren smRegionName el)
        p = (id,Entity  id (fromMaybe "" (findAttr nameName el)) $ State (map (fst . (processRegion xmiv)) regNames))

processTransition :: Maybe String -> Element -> Transition
processTransition xmiv el = Transition {source = (fromJust (findAttr (sName "source") el)), target = (fromJust (findAttr (sName "target") el)), trigger = tr, guard = gu, effect = ef}
    where
        tr = case trCand of
            [] -> Nothing
            _ -> findAttr (sName "value") $ head (findChildren (sName "defaultValue") (head trCand))
        ef = case (findChildren (sName "effect") el) of
            [] -> Nothing
            efs -> findAttr (sName "redefinedBehavior") (head efs)
        trCand = case (elChildren el) of
                [] -> []
                _ -> (filter (\ x -> ((Just "ReceivedEvent") == (findAttr (sName "name") x))) (mergeEAnnotations el (Just "contents")))

        gu = case (findAttr (sName "guard") el) of
            Nothing -> Nothing -- (show el)
            Just id1 ->  case findChildren (sName "specification" ) rules of
                    [] -> Just $ show el
                    _ -> findAttr (sName "value") $ head (findChildren (sName "specification" ) rules)
                    where     rules = (head (filter (\ x -> ((Just id1) == findAttr (attrIdName xmiv) x))  ruleCands))
                              ruleCands =  (findChildren (sName "ownedRule" ) el) --foldl (++) [] (map (\x -> (findChildren (sName "ownedRule" ) x)) annots)
                        --annots = (findChildren (sName "eAnnotations" ) el)



parseTransitions :: Maybe String -> [Element] -> [Transition]
parseTransitions _ [] = []
parseTransitions xmiv (el : lis) = ((processTransition xmiv el) : (parseTransitions xmiv lis))


parseStates :: Maybe String -> [Element] -> ([Entity], [(String, Entity)])
parseStates _ [] = ([], [])
parseStates xmiv (el : lis) =
        case (findAttr (typeName xmiv) el) of
                Nothing -> (ent, emap)
                Just "uml:State" -> ((fst (processState xmiv el)) : ent, (snd (processState xmiv el)) ++ emap)
                Just "uml:Pseudostate" -> ((fst (processPseudoState xmiv el)) : ent, (snd (processPseudoState xmiv el)) ++ emap)
                Just "uml:FinalState" -> (fs : ent, (id,fs) : emap)
                                            where   id = fromJust (findAttr (attrIdName xmiv) el)
                                                    fs = Entity id (fromMaybe "" (findAttr nameName el)) FinalState
                Just _ -> (ent, emap)
    where (ent, emap) = (parseStates xmiv lis)


--readMap :: Element -> [(String, Entity)]
--readMap el = foldl (++) [] (map processStateMap (findChildren smSubvertexName el))

readEverything :: Maybe String -> Element -> ([Entity], [Transition], [(String, Entity)])
readEverything xmiv el = (ent, trans, emap)
    where
        (ent, emap) = parseStates xmiv (findChildren smSubvertexName el)
        trans = parseTransitions xmiv (findChildren (sName "transition") el)

parseStateMachine :: Maybe String -> Element -> StateMachine
parseStateMachine xmiv  el = case ent of
            -- [] -> StateMachineR (fst ((processRegion xmiv  (head (findChildren smRegionName el)))))
            _ -> StateMachine{regions = regs }
                    where regs = case fst $ processState xmiv el of 
                            Entity id name (State regs0) ->  regs0
                            _ -> []
    where (ent, trans, _) = readEverything xmiv el
