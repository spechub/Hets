
myEqual :: Eq a => a -> a -> Bool
myEqual x y = if x == y then True else False

foon :: Bool -> Bool -> Bool -> Bool
foon a b c = let
 testName1 = myEqual a b
 testName2 = myEqual b c
 in
 testName1 && testName2
