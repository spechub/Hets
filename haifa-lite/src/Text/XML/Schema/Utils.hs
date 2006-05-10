{-# OPTIONS -fglasgow-exts -fallow-undecidable-instances -fallow-overlapping-instances #-}
----------------------------------------------------------------------------
-- |
-- Module      :  Text.XML.Schema.Utils
-- Copyright   :  (c) Simon Foster 2005
-- License     :  GPL version 2 (see COPYING)
-- 
-- Maintainer  :  aca01sdf@shef.ac.uk
-- Stability   :  experimental
-- Portability :  non-portable (ghc >= 6 only)
--
-- A set of helper utilities for mapping XML-Schema.
--
-- @This file is part of HAIFA.@
--
-- @HAIFA is free software; you can redistribute it and\/or modify it under the terms of the 
-- GNU General Public License as published by the Free Software Foundation; either version 2 
-- of the License, or (at your option) any later version.@
--
-- @HAIFA is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY; without 
-- even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.@
--
-- @You should have received a copy of the GNU General Public License along with HAIFA; if not, 
-- write to the Free Software Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA@
----------------------------------------------------------------------------
module Text.XML.Schema.Utils where

import Network.URI
import Text.XML.HXT.Parser
import Data.List
import Control.Monad
import Data.Char
import Data.Maybe
import System.Process
import System.IO
import Text.Regex
import System.Directory

-- | A simple True False Branch function for writing simpler if/then/else.
(?) :: Bool -> (a,a) -> a
(?) True  (x,_) = x
(?) False (_,x) = x


qnameToModule :: QName -> String
qnameToModule q = concat $ intersperse "." $ (fromMaybe [] $ liftM backwardURI $ parseURIReference (namespaceUri q)) ++ [toHaskellName $ localPart q]

uriToModule :: URI -> String
uriToModule u = concat $ intersperse "." $ backwardURI u

backwardURI :: URI -> [String]
backwardURI u = let ip = if (isPrefixOf "www." (authority u)) then drop 4 (authority u) else authority u in
            map toHaskellName
            ((reverse $ delimit ip '.') ++ (delimit (map (\x -> (x=='/') ? ('.', x)) (path u)) '.'))
    where
        fc (h:t) = if (h `elem` ['0'..'9']) then ('N':h:t) else (h:t)

toHaskellName :: String -> String
toHaskellName (h:t) = map (\x -> if (x=='-') then '_' else x) $ if (h `elem` ['0'..'9']) then ('N':h:t) else (toUpper h:t)

-- | Delimit a list by some item.
delimit            :: Eq a => [a] -> a -> [[a]]
delimit s x        =  case dropWhile ((==) x) s of
                      [] -> []
                      s' -> w : delimit s'' x
                            where (w, s'') = break ((==) x) s'


findModuleRegex = mkRegex "Could not find module"

canResolveModule :: FilePath -> String -> IO Bool
canResolveModule ghc n = do (inp,out,err,pid) <- runInteractiveProcess ghc ["-e", "putStrLn \"yes\"", n] Nothing Nothing
			    s <- hGetContents out
			    x <- hGetContents err
			    if (isJust $ matchRegex findModuleRegex s) 
			       then return False
			       else return True

createURIPath :: FilePath -> URI -> IO ()
createURIPath p u = do
                        let ul = backwardURI u
                        doDirLoop p ul
    where                    
    doDirLoop _ [] = return ()
    doDirLoop p (h:t) = do d <- doesDirectoryExist (p ++ "/" ++ h)
			   if d then return () else createDirectory (p ++ "/" ++ h)
			   doDirLoop (p ++ "/" ++ h) t
