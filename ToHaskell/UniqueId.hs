{- |
Module      :  $Header$
Copyright   :  (c) Uni Bremen 2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   Creating and searching unique identifier.
-}


module ToHaskell.UniqueId (
       -- * Creating unique identifiers
         distinctOpIds
       , newName
       -- * Searching for an identifier
       , findUniqueId
       )where

import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import Common.Id
import qualified Common.Lib.Map as Map hiding (map)

-- | Generates distinct names for overloaded function identifiers.
distinctOpIds :: Int -> [(Id, OpInfos)] -> [(Id, OpInfo)]
distinctOpIds _ [] = []
distinctOpIds n ((i,OpInfos info) : idInfoList) = 
    case info of
    [] -> distinctOpIds 2 idInfoList
    [hd] -> (i, hd) : distinctOpIds 2 idInfoList
    hd : tl -> (newName i n, hd) : 
	     distinctOpIds (n + 1) ((i, OpInfos tl) : idInfoList)

-- | Adds a number to the name of an identifier.
newName :: Id -> Int -> Id
newName (Id tlist idlist poslist) n = 
  let newTok = (Token ('0' : show n) nullPos) 
  in (Id (tlist ++ [newTok]) idlist poslist)

-- | Searches for the real name of an overloaded identifier.
findUniqueId :: UninstOpId -> TypeScheme -> TypeMap -> Assumps -> Maybe Id
findUniqueId uid ts tm as = 
    let OpInfos l = Map.findWithDefault (OpInfos []) uid as
	fit :: Int -> [TypeScheme] -> Maybe Id
	fit n tl = 
	    case tl of
		   [] -> Nothing
		   ty:rt -> if isUnifiable tm 0 ts ty then 
			    Just $ if null rt then uid else newName uid n
			    else fit (n + 1) rt
    in fit 2 $ map opType l
       

