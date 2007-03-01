{- |
Module      :  $Header$
Description :  utility functions that can't be found in the libraries
Copyright   :  (c) Klaus Lüttich, Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  luettich@tzi.de
Stability   :  provisional
Portability :  portable

Utility functions that can't be found in the libraries
               but should be shared across Hets.
-}

module Common.Utils
        ( joinWith
        , splitOn
        , basename
        , dirname
        , fileparse
        , stripDir
        , stripSuffix
        , safeContext
        , getEnvSave
        , filterMapWithList
        ) where

import Data.List
import Data.Graph.Inductive.Graph

import qualified Data.Map as Map
import qualified Data.Set as Set

import System.Environment
import System.IO.Error

import qualified Control.Exception as Exception

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

-- safe context for graphs
safeContext :: (Show a, Show b,Graph gr) => String -> gr a b -> Node
            -> Context a b
safeContext err g v =
  case match v g of
    (Nothing,_) -> error (err++": Match Exception, Node: "++show v++
                          " not present in graph with nodes:\n"++
                          show (nodes g)++"\nand edges:\n"++show (edges g))
    (Just c,_)  -> c

{- |
   filter a map according to a given list of keys (it dosen't hurt if a key is not present in the map)
-}
filterMapWithList :: Ord k => [k] -> Map.Map k e -> Map.Map k e
filterMapWithList l = filterMapWithSet sl
    where sl = Set.fromList l

{- |
   filter a map according to a given set of keys (it dosen't hurt if a key is not present in the map)
-}
filterMapWithSet :: Ord k => Set.Set k -> Map.Map k e -> Map.Map k e
filterMapWithSet s = Map.filterWithKey selected
    where selected k _ = Set.member k s

{- | get, parse and check an environment variable; provide the default
  value, only if the envionment variable is not set or the
  parse-check-function returns a Left value
-}
getEnvSave :: a -- ^ default value
           -> String -- ^ name of environment variable
           -> (String -> Either b a) -- ^ parse and check value of variable;
                         -- for every b the default value is returned
           -> IO a
getEnvSave defValue envVar readFun = do
   is <- Exception.catch (getEnv envVar >>= (return . Right))
               (\e -> case e of
                      Exception.IOException ie ->
                          if isDoesNotExistError ie -- == NoSuchThing
                          then return $ Left defValue
                          else Exception.throwIO e
                      _ -> Exception.throwIO e)
   return (either id (\s -> (either (const defValue) id (readFun s))) is)
