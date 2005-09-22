import Data.List

type Node = Char
type Action = Char
type Edge = (Node,Action,Node)
type LTS = ([Node],[Edge],[Action])

data HML = Top | Bot | Neg HML | And HML HML | Or HML HML | Implies HML HML | Box HML Action | Diamond HML Action deriving (Show,Eq,Ord)


satisfy :: LTS -> HML -> [(Node,[(Node,HML,Bool)],Bool)]
satisfy (n1,e1,a1) f = case n1 of
                       []   -> []
                       n:nt -> case hml (n1,e1,a1) f n of
                               (l,True)  -> (n,l,True):satisfy (nt,e1,a1) f 
                               (l,False) -> (n,l,False):satisfy (nt,e1,a1) f

hml :: LTS -> HML -> Node  -> ([(Node,HML,Bool)],Bool)
hml (n1,e1,a1) f n = ltshml (n1,e1,a1) f n e1

ltshml :: LTS -> HML -> Node -> [Edge] -> ([(Node,HML,Bool)],Bool)
ltshml (n1,e1,a1) f n ed1 = case f of
                            Bot         -> ([(n,Bot,False)],False)
                            Top         -> ([(n,Top,True)],True)
                            Neg g       -> case ltshml (n1,e1,a1) g n ed1 of
                                           (l,True)  -> ((n,Neg g,False):l,False)
                                           (l,False) -> ((n,Neg g,True):l,True)
                            And g h     -> case ltshml (n1,e1,a1) g n ed1 of
                                           (l,True)  ->  case ltshml (n1,e1,a1) h n ed1 of
                                                         (k,True)  -> ((n,And g h,True):l++k,True) 
                                                         (k,False) -> ((n,And g h,False):l++k,False)
                                           (l,False) -> ((n,And g h,False):l,False) 
                            Or g h      -> case ltshml (n1,e1,a1) g n ed1 of
                                           (l,True)  -> ((n,Or g h,True):l,True)
                                           (l,False) -> case ltshml (n1,e1,a1) h n ed1 of
                                                         (k,True)  -> ((n,Or g h,True):l++k,True) 
                                                         (k,False) -> ((n,Or g h,False):l++k,False)                           
                            Implies g h -> case ltshml (n1,e1,a1) g n ed1 of
                                           (l,True)  ->  case ltshml (n1,e1,a1) h n ed1 of
                                                         (k,True)  -> ((n,Implies g h,True):l++k,True) 
                                                         (k,False) -> ((n,Implies g h,False):l++k,False)
                                           (l,False) -> ((n,Implies g h,True):l,True) 
                            Box g a     -> case ed1 of
                                           []         -> ([(n,Box g a, True)],True)
                                           (p,b,q):et -> if p==n then
                                                                 if b==a then
                                                                         case ltshml (n1,e1,a1) g q e1 of
                                                                         (l,True)  -> case ltshml (n1,e1,a1) (Box g a) n et of
                                                                                      (k,True)  -> (nub((n,Box g a,True):l++k),True) 
                                                                                      (k,False) -> (nub((n,Box g a,False):l++k),False)
                                                                         (l,False) -> (nub((n,Box g a,False):l),False)
                                                                 else ltshml (n1,e1,a1) (Box g a) n et
                                                         else ltshml (n1,e1,a1) (Box g a) n et
                            Diamond g a -> case ed1 of
                                           []         -> ([(n,Diamond g a, False)],False)
                                           (p,b,q):et -> if p==n then
                                                                 if b==a then
                                                                         case ltshml (n1,e1,a1) g q e1 of
                                                                         (l,True)  -> (nub((n,Diamond g a,True):l),True)
                                                                         (l,False) -> case ltshml (n1,e1,a1) (Diamond g a) n et of
                                                                                      (k,True)  -> (nub((n,Diamond g a,True):l++k),True) 
                                                                                      (k,False) -> (nub((n,Diamond g a,False):l++k),False)
                                                                 else ltshml (n1,e1,a1) (Diamond g a) n et
                                                         else ltshml (n1,e1,a1) (Diamond g a) n et


simulations :: LTS -> LTS -> [((Node,Node),[(Node,Node)])] 
simulations (n1,e1,a1) (n2,e2,a2) = sims (n1,e1,a1) (n2,e2,a2) n1 n2

sims :: LTS -> LTS -> [Node] -> [Node] -> [((Node,Node),[(Node,Node)])] 
sims (n1,e1,a1) (n2,e2,a2) nd1 nd2 = case nd1 of
                                            []   -> []
                                            n:nt -> case nd2 of
                                                    []   -> sims (n1,e1,a1) (n2,e2,a2) nt n2
                                                    m:mt -> case simulates (n1,e1,a1) (n2,e2,a2) n m of
                                                          True  -> ((n,m),simulation (n1,e1,a1) (n2,e2,a2) n m):sims (n1,e1,a1) (n2,e2,a2) nd1 mt
                                                          False -> sims (n1,e1,a1) (n2,e2,a2) nd1 mt

simulation :: LTS -> LTS -> Node -> Node -> [(Node,Node)] 
simulation (n1,e1,a1) (n2,e2,a2) n m = case sim (n1,e1,a1) (n2,e2,a2) n m e1 e2 [] of
                                        (l,True)  -> l
                                        (l,False) -> l 

simulates :: LTS -> LTS -> Node -> Node -> Bool 
simulates (n1,e1,a1) (n2,e2,a2) n m = case sim (n1,e1,a1) (n2,e2,a2) n m e1 e2 [] of
                                      (l,True)  -> True
                                      (l,False) -> False

sim ::  LTS -> LTS -> Node -> Node -> [Edge] -> [Edge] -> [(Node,Node)] -> ([(Node,Node)],Bool) 
sim (n1,e1,a1) (n2,e2,a2) n m ed1 ed2 l = if elem (n,m) l then (l,True) else
                                          case ed1 of
                                          []          -> (nub ((n,m):l),True)
                                          (p,a,q):e1t -> if p==n then
                                                                 case ed2 of
                                                                 []          -> ([],False)
                                                                 (r,b,s):e2t -> if r==m then 
                                                                                        if a==b then
                                                                                            case sim (n1,e1,a1) (n2,e2,a2) q s e1 e2 (nub ((n,m):l)) of
                                                                                            (k,True)  -> case sim (n1,e1,a1) (n2,e2,a2) n m e1t e2 l of
                                                                                                         (o,True)  -> (nub (k++o),True)
                                                                                                         (o,False) -> ([],False)
                                                                                            (k,False) -> sim (n1,e1,a1) (n2,e2,a2) n m ed1 e2t l
                                                                                        else (sim (n1,e1,a1) (n2,e2,a2) n m ed1 e2t l)
                                                                                else (sim (n1,e1,a1) (n2,e2,a2) n m ed1 e2t l)                     
                                                         else sim (n1,e1,a1) (n2,e2,a2) n m e1t e2 l