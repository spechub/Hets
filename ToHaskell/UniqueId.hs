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
       , canUnify
       , findSimilarId
       , isSimilarId
       , areSimilarTokens
       )where

import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import Common.Id
import qualified Common.Lib.Map as Map hiding (map)

-- | Generates distinct names for overloaded function identifiers.
distinctOpIds :: [(Id,OpInfos)] -> [(Id, OpInfos)]
distinctOpIds [] = []
distinctOpIds ((i,OpInfos info):(idInfoList)) = 
  let len = length info in
  if len == 0 then
     distinctOpIds idInfoList
  else 
     if len == 1 then
        ((i,OpInfos info):(distinctOpIds (idInfoList)))
     else -- if len > 1
        ((newName i len,OpInfos $ [head info]):
         (distinctOpIds((i, OpInfos $ tail info):(idInfoList))))


-- | Adds a number to the name of an identifier.
newName :: Id -> Int -> Id
newName (Id tlist idlist poslist) len = 
  let newTok = (Token (show len) nullPos) 
  in (Id (tlist ++ [newTok]) idlist poslist)

-- | Searches for the new name of a renamed identifier.
--   Uses 'canUnify' and 'findSimilarId'.
findUniqueId :: UninstOpId -> TypeScheme -> TypeMap -> Assumps -> Maybe Id
findUniqueId uid ts tm as = 
    let fittingAs = Map.filter (canUnify tm ts) as 
    in if Map.size fittingAs == 1 then
         -- gut, eine Uebereinstimmung
          Just $ head $ Map.keys $ fittingAs
       else
          if Map.size fittingAs > 1 then
          --falls mehr als ein passendes TypeScheme gefunden wurde
          --kann auf "Ähnlichkeit" mit der Id getestet werden
            Just $ findSimilarId uid  (Map.keys  fittingAs)
	  else Nothing

-- | Searches in the list of identifier for an entry that differs only in 
--   the last token of the token list.
--   Uses 'isSimilarId'.
findSimilarId :: Id -> [Id] -> Id
findSimilarId i ilist = 
  let filtered = filter (== i) ilist
  in if filtered == [] then
       head $ filter (isSimilarId i) ilist
     else head filtered

-- | Two identifiers are similar if the second is maximum one token longer
--   and if they match in all other respects.
isSimilarId :: Id -> Id -> Bool
isSimilarId (Id tlist1 idlist1 _) (Id tlist2 idlist2 _) =
  idlist1 == idlist2 && areSimilarTokens tlist1 tlist2

-- | Two lists of token are similar if the second one is maximum one entry
--   longer and if they match in all other respects.
areSimilarTokens :: [Token] -> [Token] -> Bool
areSimilarTokens [] [] = True
areSimilarTokens (_t:_ts) [] = False
areSimilarTokens [] (_t:ts) = length ts == 0
areSimilarTokens (t1:ts1) (t2:ts2) = 
   t1 == t2 && areSimilarTokens ts1 ts2

-- | Tests wether a typescheme can be unified with any other typescheme 
--   of the TypeMap.
--   Uses 'HasCASL.Unify.isUnifiable'.
canUnify :: TypeMap -> TypeScheme -> OpInfos -> Bool
canUnify tm ts (OpInfos infos) = 
    or $ map (isUnifiable tm 0 ts) (map opType infos)