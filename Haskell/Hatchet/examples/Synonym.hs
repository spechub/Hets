-- Synonym.hs
-- Output: ("hello",[([2],'a')],["hello"])

type Stack a = [a]

type Triple = (String, Stack (Stack Int, Char), [String])

weird :: Triple -> Triple
weird (a,b,c) = (id a, id b, id c)

peek :: Stack a -> Maybe a
peek [] = Nothing 
peek (s:_) = Just s

push :: a -> Stack a -> Stack a
push x stack = x:stack

pop :: Stack a -> Stack a
pop [] = []
pop (_:ss) = ss

main :: Triple
main = weird ("hello", [(pop (push 1 (push 2 [])),'a')], foo (push (push 2 []) []))

foo :: Stack (Stack Int) -> Stack String 
foo _ = push "hello" []
