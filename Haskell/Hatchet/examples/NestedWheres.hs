-- NestedWheres.hs
-- output cannot be displayed

main = ((mapMyId [("point1",(inc,2))]), (mapMyId [('a',(1,double)),('b',(3,inc))]))
       where
       mapMyId :: [(c,(a,b))] -> [(c,(a,b))]
       mapMyId []     = []
       mapMyId (w:ws) = (scramble ( myId ( scramble ( myId w) ))) : (mapMyId ws) 
                        where
                        scramble :: (c, (b,a)) -> (b, (c,a))
                        scramble w = (fst (snd w), (fst w, snd (snd w)))
                        myId :: (c, (b,a)) -> (c, (b,a))
                        myId x = (first x, (first $ second x, second $ second x))
                                 where
                                 first :: (a,b) -> a
                                 first (x,y) = x
                                 second :: (a,b) -> b
                                 second (x,y) = y

inc x    = x + 1
double x = x + x       
