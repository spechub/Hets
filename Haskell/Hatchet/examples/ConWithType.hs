-- ConWithType.hs
-- Output: 3

data Weird a b =  Funny (a -> b)

data Woo a = W | N a

--fun :: Weird a b -> a -> b

fun = \w -> \x -> case w of
                  Funny f -> f x





-- main :: Int
main = fun (Funny inc) 2


inc :: Int -> Int
inc = \x -> x + 1
