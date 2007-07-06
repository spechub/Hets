module Perm where

perms xs = [x : ps | (x,ys) <- selections xs, ps <- perms ys]
selections []     = []
selections (x:xs) = (x,xs) : [(y,x:ys) | (y,ys) <- selections xs]
