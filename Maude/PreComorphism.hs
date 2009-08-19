

module Maude.PreComorphism where

import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Maude.Sign as MSign
import qualified Maude.Sentence as MSentence
import qualified Maude.Morphism as MMorphism

import qualified CASL.Sign as CSign
import qualified CASL.Morphism as CMorphism

import Common.Id
import Common.Result
import Common.AS_Annotation
import qualified Common.Lib.Rel as Rel

mapMorphism :: MMorphism.Morphism -> Result (CMorphism.Morphism () () ())
mapMorphism _ = Result [] Nothing

mapSentence :: MSign.Sign -> MSentence.Sentence -> Result sentence2
mapSentence _ _ = Result [] Nothing

mapTheory :: (MSign.Sign, [Named MSentence.Sentence]) 
              -> Result (CSign.CASLSign, [Named sentence2])
mapTheory (sg, _) = Result [] $ Just (msign2csign sg, [])

msign2csign :: MSign.Sign -> CSign.CASLSign
msign2csign msign = csign { CSign.sortSet = cs,
                            CSign.predMap = rp }
   where csign = CSign.emptySign ()
         mk = arrangeKinds (MSign.sorts msign) (MSign.subsorts msign)
         cs = kindsFromMap mk
         ks = kindPredicates mk
         rp = rewPredicates ks cs

-- mapOps :: Map.Map Id Id -> MSign.OpMap -> CSign.OpMap
-- mapOps m = Map.foldWithKey 

-- | generate the predicates
rewPredicates :: Map.Map Id (Set.Set CSign.PredType) -> Set.Set Id
                 -> Map.Map Id (Set.Set CSign.PredType)
rewPredicates m = Set.fold rewPredicate m

rewPredicate :: Id -> Map.Map Id (Set.Set CSign.PredType)
                -> Map.Map Id (Set.Set CSign.PredType)
rewPredicate kind m = Map.insertWith (Set.union) kind ar m
   where ar = Set.singleton $ CSign.PredType [kind, kind]

-- | create the predicates that assign sorts to each term
kindPredicates :: Map.Map Id Id -> Map.Map Id (Set.Set CSign.PredType)
kindPredicates = Map.foldWithKey kindPredicate Map.empty

-- | create the predicates that assign the current sort to the
-- corresponding terms
kindPredicate :: Id -> Id -> Map.Map Id (Set.Set CSign.PredType)
                 -> Map.Map Id (Set.Set CSign.PredType)
kindPredicate sort kind mis = Map.insertWith (Set.union) sort ar mis
   where ar = Set.singleton $ CSign.PredType [kind]

-- | extract the kinds from the map of id's
kindsFromMap :: Map.Map Id Id -> Set.Set Id
kindsFromMap = Map.fold Set.insert Set.empty

-- | return a map where each sort is mapped to its kind, both of them
-- already converted to Id
arrangeKinds :: MSign.SortSet -> MSign.SubsortRel -> Map.Map Id Id
arrangeKinds ss r = arrangeKindsList (Set.toList ss) r Map.empty

arrangeKindsList :: [Token] -> MSign.SubsortRel -> Map.Map Id Id -> Map.Map Id Id
arrangeKindsList [] _ _ = Map.empty
arrangeKindsList l@(s : _) r m = arrangeKindsList not_rel r m'
      where top = getTop s r
            tc = Rel.transClosure r
            (rel, not_rel) = sameKindList s tc l
            f = \ x y z -> Map.insert (token2id y) (token2id x) z
            m' = foldr (f top) m rel

sameKindList :: Token -> MSign.SubsortRel -> [Token] -> ([Token],[Token])
sameKindList _ _ [] = ([], [])
sameKindList t r (t' : ts) = if MSign.sameKind t t' r
                       then (t' : hold, not_hold)
                       else (hold, t' : not_hold)
      where (hold, not_hold) = sameKindList t r ts

-- | transform the set of Maude sorts in a set of CASL sorts, including
-- only one sort for each kind.
sortsTranslation :: MSign.SortSet -> MSign.SubsortRel -> Set.Set Id
sortsTranslation ss r = sortsTranslationList (Set.toList ss) r

-- | transform a list representing the Maude sorts in a set of CASL sorts,
-- including only one sort for each kind.
sortsTranslationList :: [Token] -> MSign.SubsortRel -> Set.Set Id
sortsTranslationList [] _ = Set.empty
sortsTranslationList (s : ss) r = Set.insert (token2id top) res
      where top = getTop s r
            ss' = deleteRelated ss top r
            res = sortsTranslation ss' r

-- | return a maximal element from the sort relation 
getTop :: Token -> MSign.SubsortRel -> Token
getTop tok r = case succs of
           [] -> tok
           (tok' : _) -> getTop tok' r
      where succs = Set.toList $ Rel.succs r tok

-- | delete from the list of sorts those in the same kind that the parameter
deleteRelated :: [Token] -> Token -> MSign.SubsortRel -> MSign.SortSet
deleteRelated ss tok r = foldr (f tok tc) Set.empty ss
      where tc = Rel.transClosure r
            f = \ sort trC x y -> if MSign.sameKind sort x trC
                                  then y
                                  else Set.insert x y

-- | build an Id from a token with the function mkId
token2id :: Token -> Id
token2id t = mkId [t]