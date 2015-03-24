module UML.StateMachineParser where
import Text.XML.Light
import UML.UML
import UML.XMINames
import Data.Maybe
import UML.StateMachine 

processRegion :: Maybe String -> Element -> (Region,[(String,Entity)])
processRegion xmiv el = (Region {states=ent, transitions=trans}, emap)
    where (ent, trans,emap) = readEverything xmiv el

--processRegionMap :: Element ->  [(String, Entity)]
--processRegionMap el = readMap el


mergeEAnnotations :: Element -> Maybe String -> [Element]
mergeEAnnotations el st = case st of 
            Nothing -> foldl (++) [] (map elChildren annots)
            Just s -> foldl (++) [] (map (\x -> (findChildren (sName s) x)) annots)
            where annots = (findChildren (sName "eAnnotations" ) el)

processPseudoState :: Maybe String -> Element -> (Entity,[(String,Entity)])
processPseudoState xmiv el = (ps, [(id1,ps)])
            where     
                id1 = fromMaybe "" (findAttr (attrIdName xmiv) el)
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
--    where     regs = (map processRegion  (findChildren smRegionName el))
--        p = (fromMaybe "" (findAttr attrIdName el), State (fromMaybe "" )  regs)

processState :: Maybe String -> Element -> (Entity,[(String, Entity)])
processState xmiv el =  (snd p,p:regMap)
    where     
        regMap = foldl (++) [] (map (snd.(processRegion xmiv)) regNames)
        regNames = (findChildren smRegionName el)
        p = (fromMaybe "" (findAttr (attrIdName xmiv) el), State (fromMaybe "" (findAttr nameName el)) (map (fst.(processRegion xmiv)) regNames))

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
                _ -> (filter (\x -> ((Just "ReceivedEvent") == (findAttr (sName "name") x))) (mergeEAnnotations el (Just "contents")))

        gu = case (findAttr (sName "guard") el) of 
            Nothing -> Nothing -- (show el)
            Just id1 ->  case findChildren (sName "specification" ) rules of 
                    [] -> Just $ show el
                    _ -> findAttr (sName "value") $ head (findChildren (sName "specification" ) rules)
                    where     rules = (head (filter (\x -> ((Just id1) == findAttr (attrIdName xmiv) x))  ruleCands))
                              ruleCands =  (findChildren (sName "ownedRule" ) el)--foldl (++) [] (map (\x -> (findChildren (sName "ownedRule" ) x)) annots)
                        --annots = (findChildren (sName "eAnnotations" ) el) 
        


parseTransitions :: Maybe String -> [Element] -> [Transition]
parseTransitions _ [] = []
parseTransitions xmiv (el : lis) = ((processTransition xmiv el) : (parseTransitions xmiv lis))


parseStates :: Maybe String -> [Element] -> ([Entity],[(String,Entity)])
parseStates _ [] = ([],[])
parseStates xmiv (el : lis) =
        case (findAttr (typeName xmiv) el) of
                Nothing -> (ent,emap)
                Just "uml:State" -> ((fst (processState xmiv el)):ent, (snd (processState xmiv el)) ++ emap) 
                Just "uml:Pseudostate" -> ((fst (processPseudoState xmiv el)):ent, (snd (processPseudoState xmiv el)) ++ emap)
                Just _ -> (ent, emap)
    where (ent, emap) = (parseStates xmiv lis)


--readMap :: Element -> [(String, Entity)]
--readMap el = foldl (++) [] (map processStateMap (findChildren smSubvertexName el))

readEverything :: Maybe String -> Element -> ([Entity],[Transition],[(String,Entity)])
readEverything xmiv el = (ent, trans, emap) 
    where     
        (ent,emap) = parseStates xmiv (findChildren smSubvertexName el)
        trans = parseTransitions xmiv (findChildren (sName "transition") el)

parseStateMachine :: Maybe String -> Element -> Model
parseStateMachine xmiv  el = case ent of 
            [] -> StateMachineR (fst ((processRegion xmiv  (head (findChildren smRegionName el)))))
            _ -> StateMachine ent trans 
            
    --eMap = Map.fromList (readMap (head (findChildren smRegionName el)))
    where (ent, trans,_) = readEverything xmiv el
