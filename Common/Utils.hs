{-| 
   
 > HetCATS/Utils.hs
 > $Id$
 > Authors: Klaus Lüttich
 > Year:    2002

   Useful functions that can't be found in the libraries.
   But should shared across HetCATS.

   Todo:
     - Add your own functions.
-}

module Common.Utils where

import Data.List

import Common.AS_Annotation

{- | 
  A function inspired by perls join function. It joins a list of
  lists of elements by seperating them with a seperator element. 
-} 
joinWith :: a -- ^ seperator element
	 -> [[a]] -- ^ list of lists of elements
	 -> [a]  
joinWith sep = concat . intersperse (sep:[])

{- |
  A function inspired by the perl function split. A list is splitted
  on a seperator element in smaller lists. The seperator element is
  dropped from the resulting list.
-}
splitOn :: Eq a => a -- ^ seperator
	-> [a] -- ^ list to split
	-> [[a]]
splitOn sep = (\(f,r) -> f : case r of 
	                     [] -> []
			     _  -> (splitOn sep $ tail r)
	      ) . break ((==) sep)

{-|
  A function inspired by a perl function from the standard perl-module
  File::Basename. It removes the directory part of a filepath.
-}
basename :: FilePath -> FilePath
basename fp = (\(path,basen) -> basen) (stripDir fp)

{-|
  A function inspired by a perl function from the standard perl-module
  File::Basename. It gives the directory part of a filepath.
-}
dirname :: FilePath -> FilePath
dirname fp = (\(path,basen) -> path) (stripDir fp)

{-| 
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
stripDir fp = (\(x,y) -> (reverse y, reverse x)) (break (== '/') (reverse fp))

stripSuffix :: [String] -> FilePath -> (FilePath,Maybe String)
stripSuffix suf fp = case filter justs $ map (stripSuf fp) suf of
		     []      -> (fp, Nothing)
		     ((Just (x,s)):_)  -> (x,Just s)
    where stripSuf f s | s `isSuffixOf` f = Just (stripOf s f, s) 
		       | otherwise = Nothing
	  justs (Nothing) = False
	  justs (Just _)  = True

stripOf :: (Show a, Eq a) => [a] -> [a] -> [a]
stripOf suf inp = reverse $ stripOf' (reverse suf) (reverse inp)
    where stripOf' []     i  = i
	  stripOf' (x:xs) [] = error $ 
			       concat ["suffix is longer than input string\n"
				      ,"input was: ", show suf, " ",show inp ]
	  stripOf' (x:xs) (y:ys) | x == y    = stripOf' xs ys
				 | otherwise = 
				     error $ concat ["suffix don't match input"
						    ," at "
						    ,show $ reverse (x:xs)
						    ," ",show $ reverse (y:ys)]

-- stripOf suf = reverse . drop (length suf) . reverse

-- |
-- like the chomp from Perl
-- but this chomp removes trailing newlines AND trailing spaces if any 
chomp :: String -> String
chomp = reverse . chomp' . reverse 
    where chomp' [] = []
	  chomp' xs@(x:xs') | x == '\n' || x == ' ' = chomp' xs'
			    | otherwise = xs

-- IgnoreMaybe datatype
-- extension to Maybe for use in computations over recursive types
-- that need a "don't care" result
--
-- RealJust a means result a was computed
-- RealNothing means computation failed
-- IgnoreNothing means the rest of the computation should not be
--               influenced by this result
--
data IgnoreMaybe a = RealJust a
                   | RealNothing
                   | IgnoreNothing

-- drop IgnoreNothing from a list to get Maybe list
--
dropIgnore :: [IgnoreMaybe a] -> [Maybe a]
dropIgnore []                = []
dropIgnore ((RealJust x):t)  = (Just x):(dropIgnore t)
dropIgnore (RealNothing:t)   = Nothing:(dropIgnore t)
dropIgnore (IgnoreNothing:t) = dropIgnore t

-- convert from Maybe to IgnoreMaybe
--
toIgnore :: Maybe a -> IgnoreMaybe a
toIgnore (Just x) = RealJust x
toIgnore _        = RealNothing

-- convert from IgnoreMaybe to Maybe
-- IgnoreNothing is propagated (wrt to the meaning given above) to Nothing
--
toMaybe :: IgnoreMaybe a -> Maybe a
toMaybe (RealJust x) = Just x
toMaybe _            = Nothing

-- map over IgnoreMaybe taking (Maybe a -> b) function
--
mapIgnore :: (Maybe a -> b) -> [IgnoreMaybe a] -> [b]
mapIgnore f [] = []
mapIgnore f (IgnoreNothing:t) = mapIgnore f t
mapIgnore f (h:t) = (f $ toMaybe h):(mapIgnore f t)

-- map over IgnoreMaybe taking (a -> b) function
--
mapIgnoreMaybe :: (a -> b) -> [IgnoreMaybe a] -> [b]
mapIgnoreMaybe f [] = []
mapIgnoreMaybe f (RealJust x:t) = (f x):(mapIgnoreMaybe f t)
mapIgnoreMaybe f (h:t) = mapIgnoreMaybe f t

-- add element to list as if it were a set
--  addition is to the front if element wasn't already in the list, in which
--  case the list is not modified
--
setAddOne :: Eq a => [a] -> a -> [a]
setAddOne set x = if (x `elem` set) then set else (x:set)

-- concat two lists as if they were sets
-- adds each element from the second list using setAddOne
--
setAdd :: Eq a => [a] -> [a] -> [a]
setAdd set add = foldl setAddOne set add

-- find out whether all the elements of a list occur only once
--
allUnique :: Eq a => [a] -> Bool
allUnique [] = False
allUnique [h] = True
allUnique (h:t) = ([ x | x<-t, x == h ]==[]) && allUnique t

-- compute members of a list occuring more than once
--
notUnique :: Eq a => [a] -> [a]
notUnique [] = []
notUnique (h:t) = let
                    diff = [ x | x<-t, x/=h ]
                    rest = notUnique diff
                  in
                    case (h `elem` t) of True ->  h : rest
                                         False -> rest
