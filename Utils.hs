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

module Utils where

import List

import AS_Annotation
import PrettyPrint

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
