import qualified Data.List as List
import qualified Data.Set as Set

type Node = Char
type Action = Char

data Edge = Edge 
    { leftNode :: Node
    , action :: Action
    , rightNode :: Node 
    } deriving (Show,Eq,Ord)

data LTS = LTS
    { nodeList :: [Node]
    , edgeList :: [Edge]
    , actionList :: [Action]
    } deriving (Show, Eq, Ord)
                 
data LogOp = AndOp
           | OrOp
           | ImpliesOp
             deriving (Show, Eq, Ord)

data ModOp = BoxOp
           | DiamondOp
             deriving (Show, Eq, Ord)

data HML = Top 
         | Bot 
         | Neg HML 
         | Bin LogOp HML HML 
         | Modal ModOp HML Action 
           deriving (Show, Eq, Ord)

satisfy :: LTS -> HML -> [(Node, ([(Node, HML, Bool)], Bool))]
satisfy lts f = case nodeList lts of
    []     -> []
    n : nt -> (n, hml lts f n) : satisfy lts { nodeList = nt } f

hml :: LTS -> HML -> Node -> ([(Node, HML, Bool)], Bool)
hml lts f n = ltshml lts f n $ edgeList lts

ltshml :: LTS -> HML -> Node -> [Edge] -> ([(Node, HML, Bool)], Bool)
ltshml lts f n ed1 = case f of
    Bot                 -> ([(n, Bot, False)], False)
    Top                 -> ([(n, Top, True)], True)
    Neg g               -> case ltshml lts g n ed1 of
        (l, b) -> ((n, Neg g, not b) : l, not b)
    Bin AndOp g h       -> case ltshml lts g n ed1 of
        (l, True)  ->  case ltshml lts h n ed1 of
            (k, True)  -> ((n, Bin AndOp g h, True) : l ++ k, True) 
            (k, False) -> ((n, Bin AndOp g h, False) : l ++ k, False)
        (l, False) -> ((n, Bin AndOp g h, False) : l, False) 
    Bin OrOp g h        -> case ltshml lts g n ed1 of
        (l, True)  -> ((n, Bin OrOp g h, True) : l, True)
        (l, False) -> case ltshml lts h n ed1 of
            (k, True)  -> ((n, Bin OrOp g h, True) : l ++ k, True) 
            (k, False) -> ((n, Bin OrOp g h, False) : l ++ k, False)
    Bin ImpliesOp g h   -> case ltshml lts g n ed1 of
        (l, True)  ->  case ltshml lts h n ed1 of
            (k, True)  -> ((n, Bin ImpliesOp g h, True) : l ++ k, True) 
            (k, False) -> ((n, Bin ImpliesOp g h, False) : l ++ k, False)
        (l, False) -> ((n, Bin ImpliesOp g h, True) : l, True) 
    Modal BoxOp g a     -> case ed1 of
        []         -> ([(n, Modal BoxOp g a, True)], True)
        ed : et ->
            if (leftNode ed) == n then
                if (action ed) == a then
                    case ltshml lts g (rightNode ed) (edgeList lts) of
                        (l, True)  -> case ltshml lts (Modal BoxOp g a)
                                                 n et of
                            (k, True)  -> (List.nub
                                 ((n, Modal BoxOp g a, True) : l ++ k), True) 
                            (k, False) -> (List.nub
                                 ((n, Modal BoxOp g a, False) : l ++ k), False)
                        (l, False) -> (List.nub
                                 ((n, Modal BoxOp g a, False) : l), False)
                else ltshml lts (Modal BoxOp g a) n et
            else ltshml lts (Modal BoxOp g a) n et
    Modal DiamondOp g a -> case ed1 of
        []         -> ([(n, Modal DiamondOp g a, False)], False)
        ed : et ->
            if (leftNode ed) == n then
                if (action ed) == a then
                    case ltshml lts g (rightNode ed) (edgeList lts) of
                        (l,True)  -> (List.nub
                            ((n, Modal DiamondOp g a, True) : l), True)
                        (l,False) -> case ltshml lts (Modal DiamondOp g a)
                                                 n et of
                            (k,True)  -> (List.nub
                             ((n, Modal DiamondOp g a, True) : l ++ k), True) 
                            (k,False) -> (List.nub
                             ((n, Modal DiamondOp g a, False) : l ++ k), False)
                else ltshml lts (Modal DiamondOp g a) n et
            else ltshml lts (Modal DiamondOp g a) n et

simulations :: LTS -> LTS -> [((Node,Node), [(Node,Node)])] 
simulations lts1 lts2 = sims lts1 lts2 (nodeList lts1) (nodeList lts2)

sims :: LTS -> LTS -> [Node] -> [Node] -> [((Node,Node),[(Node,Node)])] 
sims lts1 lts2 nd1 nd2 = case nd1 of
    []     -> []
    n : nt -> case nd2 of
        []     -> sims lts1 lts2 nt (nodeList lts2)
        m : mt -> if simulates lts1 lts2 n m then
                  ((n, m), simulation lts1 lts2 n m) : sims lts1 lts2 nd1 mt
                  else sims lts1 lts2 nd1 mt

simulation :: LTS -> LTS -> Node -> Node -> [(Node,Node)] 
simulation lts1 lts2 n m = fst $ sim lts1 lts2 n m
                                     (edgeList lts1) (edgeList lts2) []

simulates :: LTS -> LTS -> Node -> Node -> Bool 
simulates lts1 lts2 n m = snd $ sim lts1 lts2 n m
                                    (edgeList lts1) (edgeList lts2) []


sim ::  LTS -> LTS -> Node -> Node -> [Edge] -> [Edge] -> [(Node,Node)] ->
                                                      ([(Node,Node)],Bool) 
sim lts1 lts2 n m ed1 ed2 l = if elem (n, m) l then (l, True) else
    case ed1 of
    []       -> (List.nub ((n, m) : l), True)
    ed : e1t ->
        if (leftNode ed) == n then
            case ed2 of
                []       -> ([], False)
                ee : e2t ->
                    if (leftNode ee) == m then 
                        if (action ed) == (action ee) then
                            case sim lts1 lts2 (rightNode ed) (rightNode ee)
                                     (edgeList lts1) (edgeList lts2)
                                     (List.nub ((n, m) : l)) of
                                (k, True)  -> case sim lts1 lts2 n m 
                                                      e1t (edgeList lts2) l of
                                    (o, True)  -> (List.nub (k ++ o), True)
                                    (_, False) -> ([], False)
                                (_, False) -> sim lts1 lts2 n m ed1 e2t l
                        else (sim lts1 lts2 n m ed1 e2t l)
                    else (sim lts1 lts2 n m ed1 e2t l)                     
        else sim lts1 lts2 n m e1t (edgeList lts2) l
