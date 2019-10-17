module Common.Counter where
import Data.IORef

data Counter = Counter { x :: IORef Int}

makeCounter :: Int -> IO Counter        
makeCounter i = do iref <- newIORef i   
                   return (Counter iref)

incCounter :: Int -> Counter -> IO ()            
incCounter i (Counter c) = do modifyIORef c (+ i)

showCounter :: Counter -> IO Int               
showCounter (Counter c) = do c' <- readIORef c
                             return c' 
