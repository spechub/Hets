module ToHaskell.UniqueId where

import HasCASL.As
import HasCASL.Le
import HasCASL.Unify
import Common.Id
import qualified Common.Lib.Map as Map hiding (map)

-- Funktion, die evtl. überladenen Operationen eindeutige Namen gibt
-- | Generates distinct names for overloaded function identifiers.
distinctOpIds :: [(Id,OpInfos)] -> [(DistinctOpId, OpInfos)]
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


-- Durchnummerierung von überladenen Funktionsnamen
-- | Adds a number to the name of an identifier.
newName :: Id -> Int -> Id
newName (Id tlist idlist poslist) len = 
  let newTok = (Token (show len) nullPos) 
  in (Id (tlist ++ [newTok]) idlist poslist)


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

findSimilarId :: Id -> [Id] -> Id
findSimilarId i ilist = 
  let filtered = filter (== i) ilist
  in if filtered == [] then
       head $ filter (isSimilarId i) ilist
     else head filtered

isSimilarId :: Id -> Id -> Bool
isSimilarId (Id tlist1 idlist1 _) (Id tlist2 idlist2 _) =
  idlist1 == idlist2 && areSimilarTokens tlist1 tlist2

areSimilarTokens :: [Token] -> [Token] -> Bool
areSimilarTokens [] [] = True
areSimilarTokens (_t:_ts) [] = False
areSimilarTokens [] (_t:ts) = length ts == 0
areSimilarTokens (t1:ts1) (t2:ts2) = 
   t1 == t2 && areSimilarTokens ts1 ts2


canUnify :: TypeMap -> TypeScheme -> OpInfos -> Bool
canUnify tm ts (OpInfos infos) = 
    or $ map (isUnifiable tm 0 ts) (map opType infos)
