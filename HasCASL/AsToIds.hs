{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  maeder@tzi.de
Stability   :  experimental
Portability :  portable 

extract ids from As for mixfix analysis
-}

module HasCASL.AsToIds where

import HasCASL.As
import Common.Id
import Common.AS_Annotation
import qualified Common.Lib.Set as Set

type Ids = Set.Set Id

unite :: [Ids] -> Ids
unite = Set.unions

idsOfBasicSpec :: BasicSpec -> Ids 
idsOfBasicSpec (BasicSpec l) = unite $ map (idsOfBasicItem . item) l 

idsOfBasicItem :: BasicItem -> Ids 
idsOfBasicItem (SigItems i) = idsOfSigItems i
idsOfBasicItem (ClassItems _ l _ ) = unite $ map (idsOfClassItem . item) l
idsOfBasicItem (GenItems l _) = unite $ map (idsOfSigItems . item) l
idsOfBasicItem (Internal l _) = unite $ map (idsOfBasicItem . item) l
idsOfBasicItem _ = Set.empty

idsOfClassItem :: ClassItem -> Ids
idsOfClassItem (ClassItem _ l _) = unite $ map (idsOfBasicItem . item) l

idsOfSigItems :: SigItems -> Ids
idsOfSigItems (TypeItems _ _ _) = Set.empty
idsOfSigItems (OpItems b l _) = unite $ map (idsOfOpItem b . item) l

idsOfOpItem :: OpBrand -> OpItem -> Ids
idsOfOpItem b (OpDecl os _ _ _) = 
    let ois = Set.fromList $ map ( \ (OpId i _ _) -> i) os  
        in case b of 
                  Pred -> ois
                  _ -> Set.empty
idsOfOpItem b (OpDefn (OpId i _ _) _ _ _ _ _) =
        case b of 
                  Pred -> (Set.singleton i)
                  _ -> Set.empty
