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
  ( joinWith
  , nubOrd
  , readMaybe
  , mapAccumLM
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
  , composeMap
  ) where

import Data.Char
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import System.Environment
import System.IO.Error
import Control.Monad

import qualified Control.Exception as Exception

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

nubOrd :: Ord e => [e] -> [e]
nubOrd = let f e s = if Set.member e s then Nothing else Just (Set.insert e s)
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
composeMap :: (Monad m, Ord a, Ord b, Ord c, Show b) =>
                Map.Map a b -> Map.Map b c -> m (Map.Map a c)
composeMap in1 in2 = foldM (\ m1 (x,y)  -> case Map.lookup y in2 of
   Nothing -> fail ("Item " ++ (show y) ++ " not found in target map")
   Just z  -> return $ Map.insert x z m1) Map.empty $ Map.toList in1

-- | keep only minimal elements
keepMins :: (a -> a -> Bool) -> [a] -> [a]
keepMins lt l = case l of
    [] -> []
    x : r -> let s = filter ( \ y -> not (lt x y)) r
                 m = keepMins lt s
              in if any ( \ y -> lt y x) s then m
                 else x : m

{- |
  A function inspired by perls join function. It joins a list of
  lists of elements by seperating them with a seperator element.
-}
joinWith :: a -- ^ seperator element
         -> [[a]] -- ^ list of lists of elements
         -> [a]
joinWith sep = concat . intersperse [sep]

{- |
  A function inspired by the perl function split. A list is splitted
  on a seperator element in smaller non-empty lists.
  The seperator element is dropped from the resulting list.
-}
splitOn :: Eq a => a -- ^ seperator
        -> [a] -- ^ list to split
        -> [[a]]
splitOn x xs = let (l, r) = break (==x) xs in
    (if null l then [] else [l]) ++ (if null r then [] else splitOn x $ tail r)

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It removes the directory part of a filepath.
-}
basename :: FilePath -> FilePath
basename fp = (\(_path,basen) -> basen) (stripDir fp)

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It gives the directory part of a filepath.
-}
dirname :: FilePath -> FilePath
dirname fp = (\(path,_basen) -> path) (stripDir fp)

{- |
  A function inspired by a perl function from the standard perl-module
  File::Basename. It splits a filepath into the basename, the
  directory and gives the suffix that matched from the list of
  suffixes. If a suffix matched it is removed from the basename.
-}
fileparse :: [String] -- ^ list of suffixes
          -> FilePath
          -> (FilePath,FilePath,Maybe String)
          -- ^ (basename,directory,matched suffix)
fileparse sufs fp = let (path,base) = stripDir fp
                        (base',suf) = stripSuffix sufs base
                    in (base',path,suf)

stripDir :: FilePath -> (FilePath,FilePath)
stripDir fp =
    (\(x,y) -> (if not (null y) then reverse y else "./", reverse x))
    (break (== '/') (reverse fp))

stripSuffix :: [String] -> FilePath -> (FilePath,Maybe String)
stripSuffix suf fp = case filter justs $ map (stripSuf fp) suf of
                     ((Just (x,s)):_)  -> (x,Just s)
                     _                 -> (fp, Nothing)
    where stripSuf f s | s `isSuffixOf` f =
                           Just (take (length f - length s) f, s)
                       | otherwise = Nothing
          justs (Nothing) = False
          justs (Just _)  = True

{- | filter a map according to a given list of keys (it dosen't hurt
   if a key is not present in the map) -}
filterMapWithList :: Ord k => [k] -> Map.Map k e -> Map.Map k e
filterMapWithList l = filterMapWithSet sl
    where sl = Set.fromList l

{- | filter a map according to a given set of keys (it dosen't hurt if
   a key is not present in the map) -}
filterMapWithSet :: Ord k => Set.Set k -> Map.Map k e -> Map.Map k e
filterMapWithSet s = Map.filterWithKey selected
    where selected k _ = Set.member k s

{- | get, parse and check an environment variable; provide the default
  value, only if the envionment variable is not set or the
  parse-check-function returns a Left value -}
getEnvSave :: a -- ^ default value
           -> String -- ^ name of environment variable
           -> (String -> Maybe a) -- ^ parse and check value of variable;
                         -- for every b the default value is returned
           -> IO a
getEnvSave defValue envVar readFun = Exception.catch
  (getEnv envVar >>= return . maybe defValue id . readFun)
  $ \ e -> case e of
             Exception.IOException ie ->
                 if isDoesNotExistError ie -- == NoSuchThing
                 then return defValue else Exception.throwIO e
             _ -> Exception.throwIO e

-- | get environment variable
getEnvDef :: String -- ^ environment variable
          -> String -- ^  default value
          -> IO String
getEnvDef envVar defValue = getEnvSave defValue envVar Just
