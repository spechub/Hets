-- NestedTuples.hs
-- Output: (T 3 Empty Empty,("a",True),T (T "b" Empty Empty) Empty Empty)

data Btree a = Empty | T a (Btree a) (Btree a)
               deriving Show

main :: (Btree Int, (String, Bool), Btree (Btree String))
main = (T 3 Empty Empty,("a",True),T (T "b" Empty Empty) Empty Empty)
