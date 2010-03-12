{- |
Module      :  $Header$
Description :  substitution of terms
Copyright   :  (c) Ewaryst Schulz, DFKI Bremen 2010
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  ewaryst.schulz@dfki.de
Stability   :  experimental
Portability :  portable

substitution and let-reduction of terms
-}

module HasCASL.Subst where

--import qualified Data.Graph.Analysis.Algorithms.Common() as DGAAC

import HasCASL.As
import HasCASL.AsUtils
import HasCASL.FoldTerm
import HasCASL.Le

import Common.Id
import Common.Lib.State

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List as List
import Data.Maybe


------------------------- Subst type -------------------------

-- | The constants for which terms can be substituted
data SubstConst = SConst Id TypeScheme
                  deriving (Eq, Ord, Show)

type SubstType = Id

-- | Type for the SubstRules.
--   The status entry signals if the use of this substitution will trigger
--   a failure or not. This mechanism is used to detect if variable capturing
--   will occur.
data SRule a = Blocked a | Ready a deriving Show


newtype Subst =
    Subst ( Map.Map SubstConst (SRule Term) -- | the const->term mapping
          , Map.Map SubstType (SRule Type) -- | the const->type mapping
                                           -- | if a constant c occurs in the term t of a
          --   const-term mapping (c',t) then c' is entered in the
          --   by this mapping corresponding set s: (c, insert c' s)
          , Map.Map SubstConst (Set.Set SubstConst)) deriving Show

eps :: Subst
eps = Subst (Map.empty, Map.empty, Map.empty)

size :: Subst -> Int
size (Subst (m,t,_)) = Map.size m + Map.size t

isBlocked :: SRule a -> Bool
isBlocked (Ready _) = False
isBlocked _ = True

ruleContent :: SRule a -> a
ruleContent (Ready x) = x
ruleContent (Blocked x) = x

blockRule :: SRule a -> SRule a
blockRule (Ready x) = Blocked x
blockRule x = x

-- | Mark all mappings to terms which contain a var from the given scope
--   as blocked.
inScope :: [SubstConst] -> Subst -> Subst
inScope scs (Subst (m,t,br)) =
    let
        -- constants to block
        cb = Set.unions $ Map.elems $ Map.filterWithKey (\ k _ -> elem k scs) br
        -- map after removal of the blocked constants
        nbr = Map.filter (not . Set.null)
              $ Map.map (flip Set.difference $ Set.fromList scs) br
        -- blockfunction
        blf c v = if Set.member c cb then blockRule v else v
    in Subst (Map.mapWithKey blf m, t, nbr)




mkSConst :: Id -> TypeScheme -> SubstConst
mkSConst = SConst
mkSVar :: Id -> Type -> SubstConst
mkSVar n = SConst n . simpleTypeScheme

mkSRule :: a -> SRule a
mkSRule = Ready

toSConst :: Term -> Maybe SubstConst
toSConst (QualVar vd) = Just $ toSC vd
toSConst (QualOp _ n ts _ _ _) = Just $ toSC (n, ts)
toSConst _ = Nothing


substFromEqs :: [(Term, Term)] -> Subst
substFromEqs eqs =
  let f sb (t1,t2) = case toSConst t1 of
                       Nothing -> sb
                       Just sc -> addTerm sb sc t2
  in foldl f eps eqs

substFromTermMap :: [(SubstConst, Term)] -> Subst
substFromTermMap tmap = foldl (\sb -> uncurry $ addTerm sb) eps tmap


termEmpty :: Subst -> Bool
termEmpty (Subst (m,_,_)) = Map.null m
typeEmpty :: Subst -> Bool
typeEmpty (Subst (_,m,_)) = Map.null m


lookupTerm :: Subst -> SubstConst -> Maybe (SRule Term)
lookupTerm (Subst (m,_,_)) k = Map.lookup k m

lookupType :: Subst -> SubstType -> Maybe (SRule Type)
lookupType (Subst (_,t,_)) k = Map.lookup k t

addTerm :: Subst -> SubstConst -> Term -> Subst
addTerm (Subst (m,t,br)) k v =
    let nm = Map.insert k (mkSRule v) m
        f x = (toSC x, Set.singleton k)
        g x = (fromJust $ toSConst x, Set.singleton k)
        s = Set.map f (freeVars v) `Set.union` Set.map g (opsInTerm v)
        nbr = Map.fromList $ Set.toList s
    in Subst (nm, t, Map.unionWith Set.union br nbr)

removeTerm :: Subst -> SubstConst -> Subst
removeTerm (Subst (m,t,br)) k =
    Subst ( Map.delete k m, t
          , Map.filter (not . Set.null) $ Map.map (Set.delete k) br)
                 
addType :: Subst -> SubstType -> Type -> Subst
addType (Subst (m,t,br)) k v = Subst (m, Map.insert k (mkSRule v) t,br)

removeType :: Subst -> SubstType -> Subst
removeType (Subst (m,t,br)) k = Subst (m, Map.delete k t,br)
                 


class LookupSubst a b where
    lookupS :: Subst -> a -> Maybe (SRule b)

class SCLike a where
    toSC :: a -> SubstConst

class STLike a where
    toST :: a -> SubstType

class Substable a where
    subst :: Subst -> a -> a

---- instances



instance LookupSubst Term Term where
    lookupS s x = case toSConst x of
                    Just sc -> lookupTerm s sc
                    _ -> Nothing

instance SCLike a => LookupSubst a Term where
    lookupS s x = lookupTerm s $ toSC x

instance STLike a => LookupSubst a Type where
    lookupS s x = lookupType s $ toST x


instance SCLike SubstConst where
    toSC = id

instance SCLike VarDecl where
    toSC (VarDecl n typ _ _) = mkSVar n typ

instance SCLike (Id, OpInfo) where
    toSC (n, inf) = mkSConst n $ opType inf

instance SCLike (PolyId, TypeScheme) where
    toSC (PolyId n _ _, typs) = mkSConst n typs

instance SCLike (Id, TypeScheme) where
    toSC (n, typs) = mkSConst n typs

instance STLike TypeArg where
    toST = typevarId


---- class functions

addC :: SCLike a => Subst -> a -> Term -> Subst
addC s k v = addTerm s (toSC k) v
removeC :: SCLike a => Subst -> a -> Subst
removeC s k = removeTerm s (toSC k)
removeListC :: SCLike a => Subst -> [a] -> Subst
removeListC s l = foldl removeC s l

addT :: STLike a => Subst -> a -> Type -> Subst
addT s k v = addType s (toST k) v
removeT :: STLike a => Subst -> a -> Subst
removeT s k = removeType s (toST k)
removeListT :: STLike a => Subst -> [a] -> Subst
removeListT s l = foldl removeT s l


lookupContent :: LookupSubst a b => Subst -> a -> Maybe b
lookupContent s k = fmap ruleContent $ lookupS s k

---- other functions
typevarId :: TypeArg -> Id
typevarId (TypeArg n _ _ _ _ _ _)= n


------------------------- Substitution -------------------------

{-

* VARIABLE CAPTURING

examples: 

for let reduction:
forall x:A. let y:A = x in exists x:A. x = y 

   or let expanded

for beta reduction
forall x:A. ( \y:A . exists x:A. x = y ) x

The obvious solution is variable renaming of the bound vars by
the inner binder, here, e.g., exists x:A -> exists x':A .
Another solution is signaling an error in the subst function,
whenever a substitution will cause variable capturing.

We implement the second solution.

-}


substWithDefault :: (LookupSubst a b, Show a) => Subst -> b -> a -> b
substWithDefault s dfault x =
    case lookupS s x of
      Nothing -> dfault
      Just mp -> if isBlocked mp then error $ "substWithDefault: Rule for "
                 ++ show x ++ " is blocked!"
                 else ruleContent mp

instance Substable Type where
    subst _ t = t

instance Substable Term where
    subst s t
      | termEmpty s = t
      | otherwise =
          case t of
          qv@(QualVar v) -> substWithDefault s qv v
          qo@(QualOp _ n typ _ _ _) -> substWithDefault s qo (n,typ)
          ApplTerm t1 t2 rg -> ApplTerm (subst s t1) (subst s t2) rg
          TupleTerm l rg -> TupleTerm (map (subst s) l) rg
          TypedTerm term tq typ rg ->
              TypedTerm (subst s term) tq (subst s typ) rg
          p@(AsPattern _ _ _) -> p
          QuantifiedTerm q vars term rg ->
              let (vds, tvs) = splitVars vars
                  scs = map toSC vds
                  s' = inScope scs $ removeListT (removeListC s scs) tvs
              in QuantifiedTerm q vars (subst s' term) rg
          LambdaTerm varPatts p term rg ->
              let bvars = map toSC 
                          $ Set.toList $ Set.unions $ map freeVars varPatts
                  s' = inScope bvars $ removeListC s bvars
              in LambdaTerm varPatts p (subst s' term) rg
          LetTerm lb eqs term rg -> 
              let (eqs', s') = substLetEqs s eqs
              in LetTerm lb eqs' (subst s' term) rg
          CaseTerm term eqs rg ->
              CaseTerm (subst s term) (substCaseEqs s eqs) rg
          _ -> t


substLetEqs :: Subst -> [ProgEq] -> ([ProgEq], Subst)
substLetEqs s eqs = runState (mapM substLetEq eqs) s

substLetEq :: ProgEq -> State Subst ProgEq
substLetEq (ProgEq lh rh rg) = do
  s <- get
  let scs = map toSC (Set.toList $ freeVars lh)
            ++ mapMaybe toSConst (Set.toList $ opsInTerm lh)
  -- IMPORTANT REMARK:
  -- The ops contain also constructors which are used to form patterns.
  -- These constructors shouldn't be substituted at all, so it should
  -- be no problem if we remove them from the substitution.
  put $ inScope scs $ removeListC s scs
  return (ProgEq lh (subst s rh) rg)


substCaseEqs :: Subst -> [ProgEq] -> [ProgEq]
substCaseEqs s = map $ substCaseEq s

substCaseEq :: Subst -> ProgEq -> ProgEq
substCaseEq s (ProgEq lh rh rg) =
    let bvars = map toSC $ Set.toList $ freeVars lh
    in ProgEq lh (subst (inScope bvars $ removeListC s bvars) rh) rg


----------------------- Substitution for let reduction -----------------------

-- | substitutes the symbols, bound by progeqs, in the term
substEqs :: Term -> [ProgEq] -> ReductionResult Term
-- evil hack to use the reduction type as it is also for building
-- the substitution. This leads to the fact that a successful reduction
-- will be given a notreduced flag!
-- TODO: remove this evil hack
substEqs t eqs = toReduced $ (\x -> subst x t) <$> redFold substFromEq eps eqs
--substEqs t eqs = error $ (show t) ++ "\n\n\n"
--                 ++ let redd = redFold substFromEq eps eqs
--                    in (show $ getResult redd) ++ (show $ getResultType redd)
--substEqs t eqs = (\x -> error $ show x) <$> redFold substFromEq eps eqs


substFromEq :: Subst -> ProgEq -> ReductionResult Subst
substFromEq s (ProgEq lh rh _) =
    case toSConst lh of
      -- NotReduced plays the role of continue, so use it here!
      Just sc -> NotReduced $ addTerm s sc $ subst s rh
      Nothing -> CannotReduce HasPatternsOrFunctions "substFromEq" s


------------------------- Reduction -------------------------

data ReductionFailure = HasPatternsOrFunctions | HasCycles deriving Show

-- | Codes for explaining the success of a reduction.
--   * reduced is a stop-flag and signals success
--   * notreduced is a continue-flag
--   * cannotreduce is a stop-flag and signals failure
data ReductionResult a = Reduced a | NotReduced a
                       | CannotReduce ReductionFailure String a

instance Functor ReductionResult where
    fmap f rr = case rr of
                  Reduced a -> Reduced $ f a
                  NotReduced a -> NotReduced $ f a
                  CannotReduce rf s a -> CannotReduce rf s $ f a

-- | Usually defined in Data.Functor, but not importable here
(<$) :: Functor f => a -> f b -> f a
(<$) = fmap . const

infixl 4 <$>

-- | An infix synonym for 'fmap'.
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) = fmap


toReduced :: ReductionResult a -> ReductionResult a
toReduced rr = case rr of
                  NotReduced a -> Reduced a
                  _ -> rr



-- | intended to unpack the result or to give an error if CannotReduce
getResult :: ReductionResult a -> a
getResult rr = case rr of
                 Reduced a -> a
                 NotReduced a -> a
                 CannotReduce rf s _ ->
                     error $ "Cannot reduce because " ++ show rf ++ ", " ++ s


getResultType :: ReductionResult a -> String
getResultType rr = case rr of
                     Reduced a -> "Reduced"
                     NotReduced a -> "NotReduced"
                     CannotReduce rf s _ -> "CannotReduce: " ++ show rf
                                            ++ ", " ++ s


-- generic functions for the reduction-datatype

redList :: (a -> ReductionResult a) -> [a] -> ReductionResult [a]
redList _ [] = NotReduced []
redList f tl@(t:l) = case f t of
                        NotReduced _ -> (t:) <$> redList f l
                        Reduced x -> Reduced (x:l)
                        x -> const tl <$> x


redFold :: (a -> b -> ReductionResult a) -> a -> [b] -> ReductionResult a
redFold _ s [] = NotReduced s
redFold f x (t:l) = case f x t of
                      NotReduced y -> redFold f y l
                      y -> y

-- | Reduces until the result is NotReduced.
redUntil :: (a -> ReductionResult a) -> a -> a
redUntil f a = case f a of
                 NotReduced x -> x
                 Reduced x -> redUntil f x
                 x -> getResult x

---- let-reduction
redLetList :: [Term] -> ReductionResult [Term]
redLetList  = redList redLet

redLetProg :: ([ProgEq], Term) -> ReductionResult ([ProgEq], Term)
redLetProg (eqs, t) =
    let -- build a list from the input structure
        res = redLetList $ map (\ (ProgEq _ rh _) -> rh) eqs ++ [t]
        -- function to recombine the result structure from the list
        recomb tl = (zipWith rhsRepl eqs tl, last tl)
        -- needed for recomb
        rhsRepl (ProgEq lh _ rg) x = (ProgEq lh x rg)
    in fmap recomb res



-- this function is a nice example where the usage of an abstract functor
-- makes the implementation cleaner

-- | reduce the topleft-most occurence of a let-expression if possible
-- , i.e, if the let doesn't contain function-definitions nor patterns
redLet :: Term -> ReductionResult Term
redLet t =
    case t of
      -- LetTerm LetBrand [ProgEq] Term Range
      LetTerm _ eqs term _ -> substEqs term eqs
      ApplTerm t1 t2 rg -> 
          (\ [r1,r2] -> ApplTerm r1 r2 rg) <$> redLetList [t1,t2]
      TupleTerm l rg -> (\x -> TupleTerm x rg) <$> redLetList l
      TypedTerm term tq typ rg -> (\x -> TypedTerm x tq typ rg) <$> redLet term
      QuantifiedTerm q vars term rg ->
          (\x -> QuantifiedTerm q vars x rg) <$> redLet term
      LambdaTerm vars p term rg ->
          (\x -> LambdaTerm vars p x rg) <$> redLet term
      CaseTerm term eqs rg ->
          (\ (xeqs, xt) -> CaseTerm xt xeqs rg) <$> redLetProg (eqs, term)
      _ -> NotReduced t


letReduceOnce :: Term -> Term
letReduceOnce = getResult . redLet

letReduce :: Term -> Term
letReduce = redUntil redLet

---- beta-reduction
-- TODO!

