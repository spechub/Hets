{- |
Module      :  $Header$
Description :  Signatures for Maude
Copyright   :  (c) Martin Kuehl, Uni Bremen 2008
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  mkhl@informatik.uni-bremen.de
Stability   :  experimental
Portability :  portable

Definition of signatures for Maude.
-}
{-
  Ref.

  ...
-}

module Maude.Sign where

import Maude.AS_Maude
import Maude.Meta
import Maude.Symbol
import Maude.Sentence
import Maude.Printing
import Maude.Util

import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (fromJust)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Foldable as Fold

import Common.Id (mkSimpleId)
import Common.Lib.Rel (Rel)
import qualified Common.Lib.Rel as Rel
import qualified Common.Doc as Doc
import Common.DocUtils (Pretty(..))


type SortSet = Set Qid
type SubsortRel = Rel Qid
type OpDecl = ([Qid], Qid, [Attr])
type OpDeclSet = Set OpDecl
type OpMap = Map Qid OpDeclSet
type Sentences = Set Sentence

data Sign = Sign {
        sorts :: SortSet,
        subsorts :: SubsortRel,
        ops :: OpMap,
        sentences :: Sentences
    } deriving (Show, Ord, Eq)


instance Pretty Sign where
  pretty sign = Doc.text $ "\n" ++ (printSign (sorts sign) (subsorts sign) (ops sign))
                           ++ Set.fold f "" (sentences sign)
           where f = \ x y -> case x of
                  Equation eq -> printEq eq ++ y
                  Membership mb -> printMb mb ++ y
                  Rule rl -> printRl rl ++ y


instance HasSorts Sign where
    getSorts = sorts
    mapSorts mp sign = sign {
        sorts = mapSorts mp (sorts sign),
        subsorts = mapSorts mp (subsorts sign)
    }

instance HasOps Sign where
    getOps = Map.keysSet . ops
    mapOps mp sign = sign {
        ops = Map.foldWithKey (map'op mp) Map.empty (ops sign)
    }


-- | extract the Signature of a Module
fromSpec :: Module -> Sign
fromSpec (Module _ _ stmts) = let
        insert stmt = case stmt of
            SortStmnt sort -> insertSort sort
            SubsortStmnt sub -> insertSubsort sub
            OpStmnt op -> insertOp op
            EqStmnt eq -> insertEq eq
            MbStmnt mb -> insertMb mb
            RlStmnt rl -> insertRl rl
            _ -> id
    in foldr insert empty stmts

-- | extract the Set of all Qids from a Signature
symbols :: Sign -> SymbolSet
symbols sign = Set.unions [ sorts2symbols $ sorts sign,
                            ops2symbols $ ops sign,
                            labels2symbols $ sentences sign ]

sorts2symbols :: Set Qid -> SymbolSet
sorts2symbols = Set.map Sort

ops2symbols :: OpMap -> SymbolSet
ops2symbols = const Set.empty

labels2symbols :: Sentences -> SymbolSet
labels2symbols = let
        insert sent = case sent of
            Equation _ -> id
            Membership _ -> id
            Rule rl -> if not $ labeled rl
                then id
                else Set.insert $ symbolLabel rl
    in Set.fold insert Set.empty

-- | the empty Signature
empty :: Sign
empty = Sign {
    sorts = Set.empty,
    subsorts = Rel.empty,
    ops = Map.empty,
    sentences = Set.empty
}

-- | the union of two Signatures
union :: Sign -> Sign -> Sign
union sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.union sorts,
        subsorts = apply Rel.union subsorts,
        ops = apply Map.union ops,
        sentences = apply Set.union sentences
    }

-- | the intersection of two Signatures
intersection :: Sign -> Sign -> Sign
intersection sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
    in Sign {
        sorts = apply Set.intersection sorts,
        subsorts = apply Rel.intersection subsorts,
        ops = apply Map.intersection ops,
        sentences = apply Set.intersection sentences
    }

-- | insert a Sort into a Signature
insertSort :: Sort -> Sign -> Sign
insertSort sort sign = sign {sorts = ins'sort sort (sorts sign)}

-- | insert a Subsort declaration into a Signature
insertSubsort :: SubsortDecl -> Sign -> Sign
insertSubsort decl sign = sign {subsorts = ins'subsort decl (subsorts sign)}

-- | insert an Operator name into a Signature
insertOpName :: OpId -> Sign -> Sign
insertOpName name sign = sign {ops = ins'opName name (ops sign)}

-- | insert an Operator declaration into a Signature
insertOp :: Operator -> Sign -> Sign
insertOp op sign = sign {ops = ins'op op (ops sign)}

-- | insert an Equation declaration into a Signature
insertEq :: Equation -> Sign -> Sign
insertEq eq sign = sign {sentences = Set.insert (Equation eq) (sentences sign)}

-- | insert a Membership declaration into a Signature
insertMb :: Membership -> Sign -> Sign
insertMb mb sign = sign {sentences = Set.insert (Membership mb) (sentences sign)}

-- | insert a Rule declaration into a Signature if it is labeled
insertRl :: Rule -> Sign -> Sign
insertRl rl sign = if not $ labeled rl
    then sign
    else sign {sentences = Set.insert (Rule rl) (sentences sign)}

-- | check that a Signature is legal
isLegal :: Sign -> Bool
isLegal sign = let
        isLegalSort sort = Set.member sort (sorts sign)
        isLegalOp (dom, cod, _) = all isLegalSort dom && isLegalSort cod
        legal'subsorts = Fold.all isLegalSort $ Rel.nodes (subsorts sign)
        legal'ops = Fold.all (Fold.all isLegalOp) (ops sign)
    in all id [legal'subsorts, legal'ops]

-- | check that a Signature is a subsignature of another Signature
isSubsign :: Sign -> Sign -> Bool
isSubsign sig1 sig2 = let
        apply func items = func (items sig1) (items sig2)
        sorts'included = apply Set.isSubsetOf sorts
        subsorts'included = apply Rel.isSubrelOf subsorts
        ops'included = apply Map.isSubmapOf ops
    in all id [sorts'included, subsorts'included, ops'included]

-- | check that a Signature can include a Sentence
includesSentence :: Sign -> Sentence -> Bool
includesSentence sign sen = let
        ops'subset   = Set.isSubsetOf (getOps sen)   (getOps sign)
        sorts'subset = Set.isSubsetOf (getSorts sen) (getSorts sign)
    in all id [sorts'subset, ops'subset]

-- | simplification of sentences (leave out qualifications)
-- TODO: Add real implementation of simplification
simplifySentence :: Sign -> Sentence -> Sentence
simplifySentence _ = id

-- | rename the given sort
renameListSort :: [(Qid, Qid)] -> Sign -> Sign
renameListSort rnms sg = foldr f sg rnms
              where f (x, y) = renameSort x y

-- | rename the given sort
renameSort :: Qid -> Qid -> Sign -> Sign
renameSort from to sign = Sign sorts' subsorts' ops' sens'
              where sorts' = ren'sort'sortset from to $ sorts sign
                    subsorts' = ren'sort'subsortrel from to $ subsorts sign
                    ops' = ren'sort'op_map from to $ ops sign
                    sens' = ren'sort'sentences from to $ sentences sign

-- | rename the given op
renameOp :: Qid -> Qid -> [Attr] -> Sign -> Sign
renameOp from to ats sign = sign {ops = ops'}
              where ops' = ren'op'op_map from to ats $ ops sign

-- | rename the op with the given profile
renameOpProfile :: Qid -> [Qid] -> Qid -> [Attr] -> Sign -> Sign
renameOpProfile from ar to ats sg = case Map.member from (ops sg) of
                 False -> sg
                 True -> 
                    let ssr = Rel.transClosure $ subsorts sg
                        ods = fromJust $ Map.lookup from (ops sg)
                        (ods1, ods2) = Set.partition (\ (x, _, _) -> allSameKind ar x ssr) ods
                        ods1' = ren'op'set from to ats ods1
                        new_ops1 = if ods2 == Set.empty 
                                   then Map.delete from (ops sg)
                                   else Map.insert from ods2 (ops sg)
                        new_ops2 = if ods1 == Set.empty
                                   then new_ops1
                                   else Map.insertWith (Set.union) to ods1' new_ops1
                    in sg {ops = new_ops2}

allSameKind :: [Qid] -> [Qid] -> Rel Qid -> Bool
allSameKind (q1 : qs1) (q2 : qs2) r = sameKind q1 q2 r && allSameKind qs1 qs2 r
allSameKind [] [] _ = True
allSameKind _ _ _ = False

sameKind :: Qid -> Qid -> Rel Qid -> Bool
sameKind q1 q2 r = nk1 == nk2 || Rel.member nk1 nk2 r || Rel.member nk2 nk1 r
           where nk1 = kind2sort (show q1)
                 nk2 = kind2sort (show q2)

kind2sort :: String -> Qid
kind2sort ('`' : '[' : s) = mkSimpleId $ dropClosing s
kind2sort s = mkSimpleId $ s

dropClosing :: String -> String
dropClosing ('`' : ']' : []) = []
dropClosing (c : ss) = c : dropClosing ss
dropClosing _ = ""

--- Helper functions for inserting Signature members into their respective collections.

-- insert a Sort into a Set of Sorts
ins'sort :: Sort -> SortSet -> SortSet
ins'sort = Set.insert . getName

-- insert a Subsort declaration into a Subsort Relationship
ins'subsort :: SubsortDecl -> SubsortRel -> SubsortRel
ins'subsort (Subsort sub super) = Rel.insert (getName sub) (getName super)

-- insert an Operator name into an Operator Map
ins'opName :: OpId -> OpMap -> OpMap
ins'opName op = Map.insert (getName op) Set.empty

-- insert an Operator declaration into an Operator Map
ins'op :: Operator -> OpMap -> OpMap
ins'op (Op op dom cod as) opmap = let
        name = getName op
        old'ops = Map.findWithDefault Set.empty name opmap
        new'ops = Set.insert (map getName dom, getName cod, as) old'ops
    in Map.insert name new'ops opmap

-- map and insert an OperatorMap key-value pair
map'op :: Map Qid Qid -> Qid -> OpDeclSet -> OpMap -> OpMap
map'op mp op decls = Map.insert (mapAsFunction mp op) decls

-- | rename a sort in a sortset
ren'sort'sortset :: Qid -> Qid -> SortSet -> SortSet 
ren'sort'sortset from to = Set.insert to . Set.delete from

-- | rename a sort in a subsort relation
ren'sort'subsortrel :: Qid -> Qid -> SubsortRel -> SubsortRel 
ren'sort'subsortrel from to ssr = Rel.fromList ssr''
                where ssr' = Rel.toList ssr
                      ssr'' = map (ren'pair from to) ssr'

-- | aux function that renames pair
ren'pair :: Qid -> Qid -> (Qid, Qid) -> (Qid, Qid)
ren'pair from to (s1, s2) = if from == s1
                            then (to, s2)
                            else if from == s2
                                 then (s1, to)
                                 else (s1, s2)

-- | rename a sort in an operator map
ren'sort'op_map :: Qid -> Qid -> OpMap -> OpMap
ren'sort'op_map from to = Map.map (ren'sort'ops from to)

-- | rename a sort in a set of operator declarations
ren'sort'ops :: Qid -> Qid -> OpDeclSet -> OpDeclSet
ren'sort'ops from to = Set.map $ ren'op from to

-- | aux function to rename operator declarations
ren'op :: Qid -> Qid -> OpDecl -> OpDecl
ren'op from to (ar, coar, ats) = (ar', coar', ats')
             where ar' = map (\ x -> if x == from then to else x) ar
                   coar' = if from == coar
                           then to
                           else coar
                   ats' = renameSortAttrs from to ats

-- | rename a sort in an attribute set. This renaming only affects to
-- identity attributes.
renameSortAttrs :: Qid -> Qid -> [Attr] -> [Attr]
renameSortAttrs from to = map (renameSortAttr from to)

-- | rename a sort in an attribute. This renaming only affects to
-- identity attributes.
renameSortAttr :: Qid -> Qid -> Attr -> Attr
renameSortAttr from to attr = case attr of
         Id t -> Id $ renameSortTerm from to t
         LeftId t -> LeftId $ renameSortTerm from to t
         RightId t -> RightId $ renameSortTerm from to t
         _ -> attr

-- | rename a sort in a term
renameSortTerm :: Qid -> Qid -> Term -> Term
renameSortTerm from to (Const q ty) = Const q $ renameSortType from to ty
renameSortTerm from to (Var q ty) = Var q $ renameSortType from to ty
renameSortTerm from to (Apply q ts ty) = Apply q (map (renameSortTerm from to) ts)
                                                 (renameSortType from to ty)

-- | rename a sort in a type. This renaming does not affect kinds
renameSortType :: Qid -> Qid -> Type -> Type
renameSortType from to (TypeSort s) = TypeSort $ SortId sid'
       where SortId sid = s
             sid' = if (sid == from)
                   then to
                   else sid
renameSortType _ _ ty = ty

-- | rename a sort in the sentences.
ren'sort'sentences :: Qid -> Qid -> Sentences -> Sentences
ren'sort'sentences from to = Set.map (ren'sort'sentence from to)

-- | rename a sort in a sentence.
ren'sort'sentence :: Qid -> Qid -> Sentence -> Sentence
ren'sort'sentence from to (Equation eq) = Equation $ Eq lhs' rhs' cond' ats
               where Eq lhs rhs cond ats = eq
                     lhs' = renameSortTerm from to lhs
                     rhs' = renameSortTerm from to rhs
                     cond' = renameSortConditions from to cond
ren'sort'sentence from to (Membership mb) = Membership $ Mb lhs' s' cond' ats
               where Mb lhs s cond ats = mb
                     lhs' = renameSortTerm from to lhs
                     SortId sid = s
                     s' = if (sid == from)
                          then SortId to
                          else s
                     cond' = renameSortConditions from to cond
ren'sort'sentence from to (Rule rl) = Rule $ Rl lhs' rhs' cond' ats
               where Rl lhs rhs cond ats = rl
                     lhs' = renameSortTerm from to lhs
                     rhs' = renameSortTerm from to rhs
                     cond' = renameSortConditions from to cond

-- | rename a sort in a list of conditions
renameSortConditions :: Qid -> Qid -> [Condition] -> [Condition]
renameSortConditions from to = map (renameSortCondition from to)

-- | rename a sort in a condition
renameSortCondition :: Qid -> Qid -> Condition -> Condition
renameSortCondition from to (EqCond t1 t2) = EqCond t1' t2'
               where t1' = renameSortTerm from to t1
                     t2' = renameSortTerm from to t2
renameSortCondition from to (MatchCond t1 t2) = MatchCond t1' t2'
               where t1' = renameSortTerm from to t1
                     t2' = renameSortTerm from to t2
renameSortCondition from to (MbCond t s) = MbCond t' s'
               where t' = renameSortTerm from to t
                     SortId sid = s
                     s' = if (sid == from)
                          then SortId to
                          else s
renameSortCondition from to (RwCond t1 t2) = RwCond t1' t2'
               where t1' = renameSortTerm from to t1
                     t2' = renameSortTerm from to t2

-- | rename an operator without profile in an operator map
ren'op'op_map :: Qid -> Qid -> [Attr] -> OpMap -> OpMap
ren'op'op_map from to ats = Map.fromList . map f . Map.toList
               where f = \ (x,y) -> if x == from 
                                    then (to, ren'op'set from to ats y)
                                    else (x,y)

-- | rename the attributes in the operator declaration set
ren'op'set :: Qid -> Qid -> [Attr] -> OpDeclSet -> OpDeclSet
ren'op'set from to ats ods = Set.map f ods
               where f = \ (x, y, z) -> let
                              z' = ren'op'ident'ats from to z
                              in (x, y, ren'op'ats ats z')


-- | rename an operator in an attribute set. This renaming only affects to
-- identity attributes.
ren'op'ident'ats :: Qid -> Qid -> [Attr] -> [Attr]
ren'op'ident'ats from to = map (ren'op'ident'at from to)

-- | rename a sort in an attribute. This renaming only affects to
-- identity attributes.
ren'op'ident'at :: Qid -> Qid -> Attr -> Attr
ren'op'ident'at from to attr = case attr of
         Id t -> Id $ ren'op'term from to t
         LeftId t -> LeftId $ ren'op'term from to t
         RightId t -> RightId $ ren'op'term from to t
         _ -> attr

-- | rename a sort in a term
ren'op'term :: Qid -> Qid -> Term -> Term
ren'op'term from to (Const q ty) = Const q' ty
         where q' = if q == from then to else q
ren'op'term from to (Var q ty) = Var q' ty
         where q' = if q == from then to else q
ren'op'term from to (Apply q ts ty) = Apply q' (map (ren'op'term from to) ts)
                                           (renameSortType from to ty)
         where q' = if q == from then to else q

-- | rename the attributes in an attribute set
ren'op'ats :: [Attr] -> [Attr] -> [Attr]
ren'op'ats [] curr_ats = curr_ats
ren'op'ats (at : ats) curr_ats = ren'op'ats ats $ ren'op'at at curr_ats

-- | rename an attribute in an attribute set
ren'op'at :: Attr -> [Attr] -> [Attr]
ren'op'at rn@(Prec i) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Prec _ -> Prec i
                             at -> at
ren'op'at rn@(Gather qs) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Gather _ -> Gather qs
                             at -> at
ren'op'at rn@(Format qs) (a : ats) = a' : ren'op'at rn ats
               where a' = case a of
                             Format _ -> Format qs
                             at -> at
ren'op'at _ _ = []

-- | check if a rule has label
labeled :: Rule -> Bool
labeled = not . Set.null . getLabels

-- | return the label of the rule as a symbol.
symbolLabel :: Rule -> Symbol
symbolLabel = Lab . head . Set.elems . getLabels
