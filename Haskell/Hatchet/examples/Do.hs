-- Do.hs

main = io "hello"

io s
  = do
      let
        k = reverse s
      s <- getLine
      let
        q = (k ++ s)
      putStr q
      putStr "foo"

boo = do
       id $ putStrLn "end"
       print True 
       print $ id ("fred" ++ show "wally") 
       let newGameState1 = map id [] 
       boo 

