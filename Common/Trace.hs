module Common.Trace where

import Debug.Trace

strace :: Show a => String -> a -> a
strace s x = trace (s++": "++show x) x
