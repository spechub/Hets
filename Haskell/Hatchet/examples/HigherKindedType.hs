-- the trick is the higher kinded arguments 
-- in the type Rose

data Pair a = Pair a a 

data Rose a b = NilRose | NodeRose a (b (Rose a b))

-- mirror :: Rose Int [] -> Rose Int [] 
mirror (NodeRose x roses)
   = NodeRose x (reverse roses)

size1 NilRose = 0
size1 (NodeRose x roses) = 1 + (sum $ map size1 roses)

size2 NilRose = 0 
size2 (NodeRose x (Just y)) = 1 + size2 y

size3 NilRose = 0
size3 (NodeRose x (Pair rose1 rose2)) = 1 + (size3 rose1) + (size3 rose2)
