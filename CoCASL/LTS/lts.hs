{- |
Module      :  $Header$
Copyright   :  (c) Daniel Hausmann, Uni Bremen 2004
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  hausmann@informatik.uni-bremen.de
Stability   :  provisional
Portability :  portable

Functions which allow to compute
- satisfaction of a Hennessy-Milner-Logic formula for a LTS
- simulations and bisimulations between two LTSs.

-}


import qualified Data.List as List

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

equal :: [(Node, Node)] -> [(Node, Node)] -> Bool
equal l1 l2 = case l1 of
              []         -> case l2 of
                  []    -> True
                  _ : _ -> False
              (n, m) : l1t -> if elem (n, m) l2
                  then equal l1t (List.delete (n, m) l2)
                  else False

-- functions for hml-formulas

satisfy :: LTS -> HML -> [(Node, ([(Node, HML, Bool)], Bool))]
satisfy lts f = case nodeList lts of
    []     -> []
    n : nt -> (n, ltshml lts f n $ edgeList lts) :
              satisfy lts { nodeList = nt } f

ltshml :: LTS -> HML -> Node -> [Edge] -> ([(Node, HML, Bool)], Bool)
ltshml lts f n ed1 = case f of
    Bot          -> ([(n, Bot, False)], False)
    Top          -> ([(n, Top, True)], True)
    Neg g        -> case ltshml lts g n ed1 of
        (l, b1) -> ((n, Neg g, not b1) : l, not b1)
    Bin op g h   -> case ltshml lts g n ed1 of
        (l,b1) -> case ltshml lts h n ed1 of
            (k,b2) -> case op of
                AndOp     -> ((n, f, b1 && b2) : l ++ k, b1 && b2)
                OrOp      -> ((n, f, b1 || b2) : l ++ k, b1 || b2)
                ImpliesOp -> ((n, f, (not b1) || b2) : l ++ k, (not b1) || b2)
    Modal op g a -> case ed1 of
        []         -> case op of
            BoxOp     -> ([(n, f, True)], True)
            DiamondOp -> ([(n, f, False)], False)
        ed : et ->
            if (leftNode ed) == n then
                if (action ed) == a then
                    case ltshml lts g (rightNode ed) (edgeList lts) of
                        (l, b1)  -> case ltshml lts f n et of
                            (k, b2)  -> case op of
                              BoxOp     -> if b1 then
                                (List.nub((n, f, b2) : l ++ k), b2)
                                else (List.nub((n, f, False) : l), False)
                              DiamondOp -> if b1 then
                                (List.nub((n, f, True) : l), True)
                                else (List.nub((n, f, b2) : l ++ k), b2)
                else ltshml lts f n et
            else ltshml lts f n et


-- functions for bisimulations

bisimulations :: LTS -> LTS -> [((Node, Node), [(Node, Node)])]
bisimulations lts1 lts2 = bisims lts1 lts2 $ simulations lts1 lts2

bisims :: LTS -> LTS -> [((Node, Node), [(Node, Node)])] ->
                                         [((Node, Node), [(Node, Node)])]
bisims lts1 lts2 l = case l of
                         []            -> []
                         ((n,m),ls):lt -> if bisimulates lts1 lts2 n m
                              then ((n,m),ls) : bisims lts1 lts2 lt
                              else bisims lts1 lts2 lt

bisimulation :: LTS -> LTS -> Node -> Node -> [(Node, Node)]
bisimulation lts1 lts2 n m = if bisimulates lts1 lts2 n m
                             then simulation lts1 lts2 n m
                             else []

bisimulates :: LTS -> LTS -> Node -> Node -> Bool
bisimulates lts1 lts2 n m = (simulates lts1 lts2 n m) &&
                            equal (simulation lts2 lts1 m n)
                            (map (\(p,q)->(q,p)) (simulation lts1 lts2 n m))


-- functions for simulations

simulations :: LTS -> LTS -> [((Node, Node), [(Node, Node)])]
simulations lts1 lts2 = sims lts1 lts2 (nodeList lts1) (nodeList lts2)

sims :: LTS -> LTS -> [Node] -> [Node] -> [((Node, Node), [(Node, Node)])]
sims lts1 lts2 nd1 nd2 = case nd1 of
    []     -> []
    n : nt -> case nd2 of
        []     -> sims lts1 lts2 nt (nodeList lts2)
        m : mt -> if simulates lts1 lts2 n m then
                  ((n, m), simulation lts1 lts2 n m) : sims lts1 lts2 nd1 mt
                  else sims lts1 lts2 nd1 mt

simulation :: LTS -> LTS -> Node -> Node -> [(Node, Node)]
simulation lts1 lts2 n m = fst $ sim lts1 lts2 n m
                                     (edgeList lts1) (edgeList lts2) []

simulates :: LTS -> LTS -> Node -> Node -> Bool
simulates lts1 lts2 n m = snd $ sim lts1 lts2 n m
                                    (edgeList lts1) (edgeList lts2) []


sim ::  LTS -> LTS -> Node -> Node -> [Edge] -> [Edge] -> [(Node, Node)] ->
                                                      ([(Node, Node)], Bool)
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
                        else sim lts1 lts2 n m ed1 e2t l
                    else sim lts1 lts2 n m ed1 e2t l
        else sim lts1 lts2 n m e1t (edgeList lts2) l
