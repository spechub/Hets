{- |
Module      :  $Header$
Description :  utility functions that can't be found in the libraries
Copyright   :  (c) Klaus Luettich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Utility functions that can't be found in the libraries
               but should be shared across Hets.
-}

module Common.Utils
  ( isSingleton
  , replace
  , hasMany
  , number
  , combine
  , trim
  , trimLeft
  , trimRight
  , nubOrd
  , nubOrdOn
  , readMaybe
  , mapAccumLM
  , composeMap
  , keepMins
  , splitOn
  , basename
  , dirname
  , fileparse
  , stripDir
  , stripSuffix
  , getEnvSave
  , getEnvDef
  , filterMapWithList
  , timeoutCommand
  ) where

import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.Exit
import System.IO
import System.Environment
import System.Process

import Control.Monad
import Control.Concurrent

-- | replace first (non-empty) sublist with second one in third argument list
replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace sl r = case sl of
  [] -> error "Common.Utils.replace: empty list"
  _ -> concat . unfoldr (\ l -> case l of
    [] -> Nothing
    hd : tl -> Just $ case stripPrefix sl l of
      Nothing -> ([hd], tl)
      Just rt -> (r, rt))

-- | add indices to a list starting from one
number :: [a] -> [(a, Int)]
number = flip zip [1 ..]

-- | /O(1)/ test if the set's size is one
isSingleton :: Set.Set a -> Bool
isSingleton s = Set.size s == 1

-- | /O(1)/ test if the set's size is greater one
hasMany :: Set.Set a -> Bool
hasMany s = Set.size s > 1

-- | Transform a list [l1,l2, ... ln] to (in sloppy notation)
-- [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
-- (this is just sequence!)
combine :: [[a]] -> [[a]]
combine = sequence
-- see http://www.haskell.org/pipermail/haskell-cafe/2009-November/069490.html

-- | trims a string both on left and right hand side
trim :: String -> String
trim = trimRight . trimLeft

-- | trims a string only on the left side
trimLeft :: String -> String
trimLeft = dropWhile isSpace

-- | trims a string only on the right side
trimRight :: String -> String
trimRight = reverse . trimLeft . reverse

{- | The 'nubWith' function accepts as an argument a \"stop list\" update
function and an initial stop list. The stop list is a set of list elements
that 'nubWith' uses as a filter to remove duplicate elements.  The stop list
is normally initially empty.  The stop list update function is given a list
element a and the current stop list b, and returns 'Nothing' if the element is
already in the stop list, else 'Just' b', where b' is a new stop list updated
to contain a. -}
nubWith :: (a -> b -> Maybe b) -> b -> [a] -> [a]
nubWith f s es = case es of
  [] -> []
  e : rs -> case f e s of
       Just s' -> e : nubWith f s' rs
       Nothing -> nubWith f s rs

nubOrd :: Ord a => [a] -> [a]
nubOrd = nubOrdOn id

nubOrdOn :: Ord b => (a -> b) -> [a] -> [a]
nubOrdOn g = let f a s = let e = g a in
                   if Set.member e s then Nothing else Just (Set.insert e s)
  in nubWith f Set.empty

readMaybe :: Read a => String -> Maybe a
readMaybe s = case filter (all isSpace . snd) $ reads s of
  [(a, _)] -> Just a
  _ -> Nothing

-- | generalization of mapAccumL to monads
mapAccumLM :: Monad m
           => (acc -> x -> m (acc, y)) -- Function of elt of input list
                                     -- and accumulator, returning new
                                     -- accumulator and elt of result list
           -> acc           -- Initial accumulator
           -> [x]           -- Input list
           -> m (acc, [y])          -- Final accumulator and result list
mapAccumLM f s l = case l of
  [] -> return (s, [])
  x : xs -> do
    (s', y) <- f s x
    (s'', ys) <- mapAccumLM f s' xs
    return (s'', y : ys)

-- | composition of arbitrary maps
composeMap :: Ord a => Map.Map a b -> Map.Map a a -> Map.Map a a -> Map.Map a a
composeMap s m1 m2 = if Map.null m2 then m1 else Map.intersection
  (Map.foldWithKey ( \ i j ->
    let k = Map.findWithDefault j j m2 in
    if i == k then Map.delete i else Map.insert i k) m2 m1) s

-- | keep only minimal elements
keepMins :: (a -> a -> Bool) -> [a] -> [a]
keepMins lt l = case l of
    [] -> []
    x : r -> let s = filter (not . lt x) r
                 m = keepMins lt s
              in if any (`lt` x) s then m
                 else x : m

{- |
  A function inspired by the perl function split. A list is splitted
  on a seperator element in smaller non-empty lists.
  The seperator element is dropped from the resulting list.
-}
splitOn :: Eq a => a -- ^ seperator
        -> [a] -- ^ list to split
        -> [[a]]
splitOn x xs = let (l, r) = break (== x) xs in
    (if null l then [] else [l]) ++ (if null r then [] else splitOn x $ tail r)

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It removes the directory part of a filepath.
-}
basename :: FilePath -> FilePath
basename = snd . stripDir

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It gives the directory part of a filepath.
-}
dirname :: FilePath -> FilePath
dirname = fst . stripDir

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It splits a filepath into the basename, the
  directory and gives the suffix that matched from the list of
  suffixes. If a suffix matched it is removed from the basename.
-}
fileparse :: [String] -- ^ list of suffixes
          -> FilePath
          -> (FilePath, FilePath, Maybe String)
          -- ^ (basename,directory,matched suffix)
fileparse sufs fp = let (path, base) = stripDir fp
                        (base', suf) = stripSuffix sufs base
                    in (base', path, suf)

stripDir :: FilePath -> (FilePath, FilePath)
stripDir =
    (\ (x, y) -> (if null y then "./" else reverse y, reverse x))
    . break (== '/') . reverse

stripSuffix :: [String] -> FilePath -> (FilePath, Maybe String)
stripSuffix suf fp = case filter isJust $ map (stripSuf fp) suf of
                       Just (x, s) : _ -> (x, Just s)
                       _ -> (fp, Nothing)
    where stripSuf f s | s `isSuffixOf` f =
                           Just (take (length f - length s) f, s)
                       | otherwise = Nothing

{- | filter a map according to a given list of keys (it dosen't hurt
   if a key is not present in the map) -}
filterMapWithList :: Ord k => [k] -> Map.Map k e -> Map.Map k e
filterMapWithList = filterMapWithSet . Set.fromList

{- | filter a map according to a given set of keys (it dosen't hurt if
   a key is not present in the map) -}
filterMapWithSet :: Ord k => Set.Set k -> Map.Map k e -> Map.Map k e
filterMapWithSet s = Map.filterWithKey (\ k _ -> Set.member k s)

{- | get, parse and check an environment variable; provide the default
  value, only if the envionment variable is not set or the
  parse-check-function returns a Left value -}
getEnvSave :: a -- ^ default value
           -> String -- ^ name of environment variable
           -> (String -> Maybe a) -- ^ parse and check value of variable;
                         -- for every b the default value is returned
           -> IO a
getEnvSave defValue envVar readFun =
    liftM (maybe defValue (fromMaybe defValue . readFun)
           . lookup envVar) getEnvironment

-- | get environment variable
getEnvDef :: String -- ^ environment variable
          -> String -- ^  default value
          -> IO String
getEnvDef envVar defValue = getEnvSave defValue envVar Just

-- | runs a command with timeout
timeoutCommand :: Int -> String -> IO (Maybe ExitCode, Handle, Handle)
timeoutCommand time cmd = do
  wait <- newEmptyMVar
  (_, outh, errh, proch) <- runInteractiveCommand cmd
  tid1 <- forkIO $ do
    exit <- waitForProcess proch
    putMVar wait $ Just exit
  tid2 <- forkIO $ do
    threadDelay $ time * 1000000
    putMVar wait Nothing
    terminateProcess proch
  res <- takeMVar wait
  killThread (if isJust res then tid2 else tid1) `catch` print
  return (res, outh, errh)
