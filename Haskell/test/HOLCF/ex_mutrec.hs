

data Form a b = Square a b | Rectangle a b 

data LColor a = Blue a | Red a | Multi (CList a)
data CList a  = Trans | CCons (LColor a) (CList a)

data MyList a  = MyNil | MyCons a (MyList a)

myEqual        :: Eq a => a -> a -> Bool
myEqual x y    =   if x == y then True else False

fibon :: Int -> Int
fibon n = if n == 0 then 1 else if n == 1 then 1 
    else (fibon (n - 1)) + (fibon (n - 2))

mRecFun1 :: Int ->  Int
mRecFun1 n = 
 if n == 0 then 0 else 
   if n == 1 then 2 else 
     (mRecFun1 (n - 1)) + (mRecFun2 (n - 2))     

mRecFun2 :: Int ->  Int
mRecFun2 n = 
 if n == 0 then 0 else 
   if n == 1 then 0 else 
     (mRecFun1 (n - 1)) + (mRecFun2 (n - 1))     

hasColor :: Eq a => a -> a -> LColor (Form a a)
hasColor x y = 
  if (myEqual x y) then Red ((\z -> Square x z) x) else Blue (Rectangle x y) 

