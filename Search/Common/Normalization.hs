{-
todo:
- minimal scope
-}

{- |
Module      :  $Header$
Description :  Formula Normalization
Copyright   :  (c) Immanuel Normann, Uni Bremen 2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  inormann@jacobs-university.de
Stability   :  provisional
Portability :  portable
-}
module Search.Common.Normalization where

import Data.List
import Search.Utils.List
import Search.Common.Data
import Control.Monad.State
 -- nur für den Abschnitt indexing nötig, sollte vielleicht in eine Extradatai ausgelagert werden:
import qualified Data.Set as Set
import qualified Data.Map as Map
import Search.Common.BooleanRing (brForm)
import Search.Common.ACINormalization


data ScopeLabel a = Scope Int a deriving (Eq,Ord)
type MaxScope = Int
type ScopeId = Int
type ActualScope = Int

instance (Show a) => Show (ScopeLabel a) where
    show (Scope n a) = show a ++ show n

{- +++++++++++++++++++++++ check well formedness +++++++++++++++++++++++ -}

checkWellFormedness ::(Show c,Show v,Eq c,Eq v,Ord v) => Formula (Constant c) v -> Formula (Constant c) v
checkWellFormedness (Var v fs) = Var v fs
checkWellFormedness (Const c fs) =
    let passWithArrity n = if (length fs) == n
                           then Const c (map checkWellFormedness fs)
                           else error (show (Const c fs) ++
                                       " has " ++ show (length fs) ++
                                       " arguments, but it is only defined for " ++
                                       show n ++ " arguments")
    in case c of TrueAtom -> passWithArrity 0
                 Not -> passWithArrity 1
                 Imp -> passWithArrity 2
                 Eqv -> passWithArrity 2
                 Xor -> passWithArrity 2
                 _ -> Const c (map checkWellFormedness fs)
checkWellFormedness (Binder q vars f) = Binder q vars (checkWellFormedness f)

{- +++++++++++++++++++++++ remove true and false atoms +++++++++++++++++++++++ -}

true :: Formula (Constant c) v
true = Const TrueAtom []
false :: Formula (Constant c) v
false = Const FalseAtom []

elemTrueFalse :: (Eq c,Eq v,Ord v) => Formula (Constant c) v -> Formula (Constant c) v
elemTrueFalse (Var v fs) = (Var v fs)



elemTrueFalse (Const Not [f]) =
    case (elemTrueFalse f)
    of (Const TrueAtom []) -> false
       (Const FalseAtom []) -> true
       f' -> Const Not [f']

elemTrueFalse (Const Imp fs) = 
    case map elemTrueFalse fs
    of [Const TrueAtom [],f] -> f
       [Const FalseAtom [],_] -> true
       [_,Const TrueAtom []] -> true
       [f,Const FalseAtom []] -> Const Not [f]
       fs' -> Const Imp fs'

elemTrueFalse (Const Eqv fs) = 
    case map elemTrueFalse fs
    of [Const TrueAtom [],f] -> f
       [Const FalseAtom [],f] -> Const Not [f]
       [f,Const TrueAtom []] -> f
       [f,Const FalseAtom []] -> Const Not [f]
       fs' -> Const Eqv fs'

elemTrueFalse (Const Xor fs) = 
    case map elemTrueFalse fs
    of [Const TrueAtom [],f] -> Const Not [f]
       [Const FalseAtom [],f] -> f
       [f,Const TrueAtom []] -> Const Not [f]
       [f,Const FalseAtom []] -> f
       fs' -> Const Xor fs'

elemTrueFalse (Const Or fs) =
    let fs' = map elemTrueFalse fs
    in if elem true fs'
       then true
       else case filter (/=false) fs'
            of [] -> false -- i.e. every component of fs was false so (Const Or fs) is false
               [f] -> f  -- Or with a single argument f is interpreted as f itself!!
               ffs -> (Const Or ffs)

elemTrueFalse (Const And fs) =
    let fs' = map elemTrueFalse fs
    in if elem false fs'
       then false
       else case filter (/=true) fs'
            of [] -> true -- i.e. every component of fs was false so (Const Or fs) is false
               [f] -> f  -- And with a single argument f is interpreted as f itself!!
               ffs -> (Const And ffs)

elemTrueFalse (Const c fs) = Const c (map elemTrueFalse fs) -- iff c is true, false or a logic dependent constant

elemTrueFalse (Binder c vars f) = 
    case (elemTrueFalse f)
    of (Const TrueAtom []) -> true
       (Const FalseAtom []) -> false
       f' -> (Binder c vars f')

{- +++++++++++++++++++++++ annotateScope +++++++++++++++++++++++ -}

-- todo: remove vars from binding occurence which do not occur also in the body of a binding expression
-- e.g. (all (a,b) (f a)) -> (all (a) (f a))

annotateScope :: (Eq v,Ord v) => Formula c v -> Formula c (ScopeLabel v)
annotateScope f = fst $ state (0,[])
    where (State state) = annotateScopeST f

annotateScopeST :: (Eq v,Ord v) => Formula c v -> State (MaxScope,[(ScopeId,[v])]) (Formula c (ScopeLabel v))
annotateScopeST (Const c ts) =
    do nts <- mapM annotateScopeST ts
       return (Const c nts)
annotateScopeST (Var v ts) =
    do (ms,sl) <- get
       nts <- mapM annotateScopeST ts
       return (Var  (mkScopeLabel (ms,sl) v) nts)
annotateScopeST (Binder c vars body) =
    do (ms,sl) <- get
       let newMs = ms + 1
	   newVars = (map (Scope newMs) vars)
	   newSl = (newMs,vars):sl
	   in do put (newMs,newSl)
		 newBody <- (annotateScopeST body)
		 (newMs6,_) <- get
		 put (newMs6,sl)
		 return (Binder c newVars newBody)

mkScopeLabel :: (Eq a) => (MaxScope,[(ScopeId,[a])]) -> a -> ScopeLabel a
mkScopeLabel (_,sl) a = Scope (getActualScope a sl) a

getActualScope :: (Eq var) => var -> [(ScopeId,[var])] -> ActualScope
getActualScope _ [] = 0
getActualScope var ((scopeId,vars):rest) =
    if (elem var vars) then scopeId  else getActualScope var rest

{-
*Normalization> annotateScope f1
Const "and" [Var (Scope 0 "a") [],Binder "forall" [Scope 1 "a"] (Var (Scope 1 "a") []),Var (Scope 0 "a") [],Binder "forall" [Scope 2 "a"] (Var (Scope 2 "a") [])]
*Normalization> annotateScope f2
Const "and" [Var (Scope 0 "a") [],Binder "forall" [Scope 1 "a"] (Binder "forall" [Scope 2 "a"] (Var (Scope 2 "a") [])),Var (Scope 0 "a") [],Binder "forall" [Scope 3 "a"] (Var (Scope 3 "a") [])]
*Normalization> annotateScope f3
Const "and" [Var (Scope 0 "a") [],Binder "forall" [Scope 1 "a",Scope 1 "b"] (Binder "forall" [Scope 2 "a",Scope 2 "fun"] (Var (Scope 2 "fun") [Var (Scope 2 "a") [],Var (Scope 1 "b") []])),Var (Scope 0 "a") [],Binder "forall" [Scope 3 "a"] (Var (Scope 3 "a") [])]
-}

{- +++++++++++++++++++++++ prenex +++++++++++++++++++++++ -}

prenex :: Formula (Constant c) v -> Formula (Constant c) v
prenex = moveLeftAllSome . pushInwardsNot . elemImpEqvXor

elemImpEqvXor :: Formula (Constant c) v -> Formula (Constant c) v
elemImpEqvXor (Binder b vars body) = Binder b vars (elemImpEqvXor body)
elemImpEqvXor (Const Imp [a,b]) = Const Or [Const Not [elemImpEqvXor a],elemImpEqvXor b]
elemImpEqvXor (Const Eqv [a,b]) = Const And [Const Or [Const Not [elemImpEqvXor a], (elemImpEqvXor b)],
			       Const Or [Const Not [elemImpEqvXor b], (elemImpEqvXor a)]]
elemImpEqvXor (Const Xor [a,b]) = Const Or [Const And [Const Not [elemImpEqvXor a], (elemImpEqvXor b)],
			      Const And [Const Not [elemImpEqvXor b], (elemImpEqvXor a)]]
elemImpEqvXor (Const Not [a]) = Const Not [elemImpEqvXor a]
elemImpEqvXor (Const c fs) = Const c (map elemImpEqvXor fs)
elemImpEqvXor (Var v fs) = Var v fs -- no recursive call here, because logical constants can't occur in fs!

{- | 'pushInwardsNot' pushes "not" inwards
-}

pushInwardsNot :: Formula (Constant c) v -> Formula (Constant c) v
pushInwardsNot (Const Not [Const Not [f]]) = pushInwardsNot f
pushInwardsNot (Const Not [f]) =
    let insertNot x = pushInwardsNot (Const Not [x])
	in case f 
	   of (Binder All vars body) -> Binder Some vars (insertNot body)
	      (Binder Some vars body) -> Binder All vars (insertNot body)
	      (Binder c vars body) -> error ("undefined binder ") -- ++ show c)
	      (Const And fs) -> Const Or (map insertNot fs)
	      (Const Or fs) -> Const And (map insertNot fs)
	      (Const c fs) -> (Const Not [Const c (map pushInwardsNot fs)]) -- better error for c = Imp, Eqv, Xor?
	      (Var c fs) -> Const Not [Var c fs]
pushInwardsNot (Const c fs) = Const c (map pushInwardsNot fs)
pushInwardsNot (Var c fs) = Var c fs -- no recursive call here, because logical constants can't occur in fs!
pushInwardsNot (Binder c vars body) = Binder c vars (pushInwardsNot body)

{- | 'moveLeftAllSome' moves all quantifiers outwards yielding the prenexform
-}

moveLeftAllSome :: Formula (Constant c) v -> Formula (Constant c) v  -- todo: check this! Does it really work how it should?
moveLeftAllSome (Binder b vs f) = Binder b vs (moveLeftAllSome f)
moveLeftAllSome (Const c fs) = (exQ (Const c (collectF fs')) fs')
    where fs' = map moveLeftAllSome fs
          exQ :: Formula (Constant c) v -> [Formula (Constant c) v] -> Formula (Constant c) v
	  exQ f ((Binder b vars body):rest) = Binder b vars (exQ f (body:rest))
	  exQ f (_:rest) = exQ f rest
	  exQ f [] = f
	  collectF :: [Formula (Constant c) v] -> [Formula (Constant c) v]
	  collectF ((Binder _ _ body):rest) = (collectF [body]) ++ (collectF rest)
	  collectF (h:rest) = h:(collectF rest)
	  collectF [] = []
moveLeftAllSome (Var c fs) = Var c fs -- no recursive call here, because quantifiers can't occur in fs!


{- +++++++++++++++++++++++ cnf +++++++++++++++++++++++ -}

cnf :: (Eq c) => Formula (Constant c) v -> Formula (Constant c) v
cnf (Binder b vs body) = Binder b vs (cnf body)
cnf f = cnfBody f

cnfBody :: (Eq c) => Formula (Constant c) v -> Formula (Constant c) v
cnfBody (Var v ts) = (Var v ts)
cnfBody (Const TrueAtom _) = (Const TrueAtom [])
cnfBody (Const FalseAtom _) = (Const FalseAtom [])
cnfBody t = case (termType t)
        of CNF -> t
           OrAndTree -> cnfBody (Const And (distOr t))
           OtherTree -> cnfBody $ makeOrAndTree $ cnfChildren t
               where cnfChildren (Const c ts) = (Const c (map cnfBody ts))
                     cnfChildren f = f
{-
           OtherTree -> cnfBody $ makeOrAndTree t
-}

{- | 'makeOrAndTree' assumes as input an and-or-tree formula.
It returns a flattened and-or-tree meaning each child of an and (or) node
is either an or (and) node or a literal
-}

makeOrAndTree :: (Eq c) => Formula (Constant c) v -> Formula (Constant c) v
makeOrAndTree (Const And ts) = (Const And (ands ++ others))
    where (ands',others) = partition (equalsConstant And) ts
          ands = stripOff ands'
makeOrAndTree (Const Or ts) = (Const Or (ands ++ ors ++ nots))
    where (ands,others) = partition (equalsConstant And) ts
          (ors',nots) = partition (equalsConstant Or) others
          ors = stripOff ors'
makeOrAndTree f = f          

stripOff :: [Formula (Constant c) v] -> [Formula (Constant c) v]
stripOff ((Const _ fs1):fs2) = fs1 ++ (stripOff fs2)
stripOff (f:fs2) = f:(stripOff fs2)
stripOff [] = []

equalsConstant :: (Eq c) => (Constant c) -> Formula (Constant c) v -> Bool
equalsConstant c (Const a _) = c == a
equalsConstant _ _ = False

isAtom :: Formula (Constant c) v -> Bool
isAtom (Var _ _) = True
isAtom (Const Equal _) = True
isAtom (Const (LogicDependent _) _) = True  -- todo: Is this true??
isAtom _ = False

isLiteral :: Formula (Constant c) v -> Bool
isLiteral (Const Not [f]) = isAtom f
isLiteral f = isAtom f

isClause :: Formula (Constant c) v -> Bool
isClause (Const Or ts) = all isLiteral ts
isClause t = isLiteral t

isCNF :: Formula (Constant c) v -> Bool
isCNF (Const And ts) = all isClause ts
isCNF t = isClause t

distOr :: Formula (Constant c) v -> [Formula (Constant c) v]
distOr (Const Or ((Const And (f:fs1)):fs2)) = 
    (Const Or (f:fs2)):(distOr (Const Or ((Const And fs1):fs2)))
distOr (Const Or ((Const And []):_)) = []
distOr f = [f]

data TermType = CNF | OrAndTree | OtherTree deriving Show

termType :: Formula (Constant c) v -> TermType
termType (Const Or ((Const And _):_)) = OrAndTree
termType t = if (isCNF t) then CNF else OtherTree

{- +++++++++++++++++++++++ aci normalization +++++++++++++++++++++++ -}

aciFormula (Binder q vars f) = Binder q vars (aciFormula f)
aciFormula prop = aciProp prop -- prop must not contain binder expr as subterms!

-- returns an error if prop has a binder expr as subterm
aciProp prop = (npropToProp symbList) $ ntermToNprop (replace symbList term)
    where term = propToTerm prop
          (symbList:_) = aciMorphism term

formulaToTerm (Binder _ _ f) = formulaToTerm f
formulaToTerm f = propToTerm f
propToTerm (Const And fs) = Sequence [Symbol (C And),ACI (Set.fromList (map propToTerm fs))]
propToTerm (Const Or fs) = Sequence [Symbol (C Or),ACI (Set.fromList (map propToTerm fs))]
propToTerm (Const Equal fs) = Sequence [Symbol (C Equal),ACI (Set.fromList (map propToTerm fs))] -- und weitere
propToTerm (Const c []) = Symbol (C c)
propToTerm (Const c fs) = Sequence (Symbol (C c): (map propToTerm fs))
propToTerm (Var v []) = Symbol (V v)
propToTerm (Var v fs) = Sequence (Symbol (V v): (map propToTerm fs))

data NTerm = N Int [NTerm] deriving (Eq,Ord,Show)

ntermToNprop (Number n) = N n []
ntermToNprop (Sequence [Number n,ACI ts]) = N n (map ntermToNprop (Set.toList ts))
ntermToNprop (Sequence (Number n:ts)) = N n (map ntermToNprop ts)
ntermToNprop t = error ("ntermToNprop can't handle " ++ show t)

npropToProp symbList (N n nts) = 
    case (symbList!!n)
    of (C c) -> Const c (map (npropToProp symbList) nts)
       (V v) -> Var v (map (npropToProp symbList) nts)



{- +++++++++++++++++++++++ merge binding +++++++++++++++++++++++ -}

mergeBinding ::  Eq c => Formula c v ->  Formula c v
mergeBinding (Binder c1 vs1 (Binder c2 vs2 body)) = 
    if c1 == c2 then mergeBinding (Binder c1 (vs1 ++ vs2) body)
    else Binder c1 vs1 (Binder c2 vs2 (mergeBinding body))
mergeBinding (Binder c vs body) = Binder c vs (mergeBinding body)
mergeBinding (Const c fs) = Const c (map mergeBinding fs)
mergeBinding (Var v fs) = Var v fs  -- no recursive call here, because binders can't occur in fs!


{- +++++++++++++++++++++++ sort bindings +++++++++++++++++++++++ -}

sortBinding :: (Ord v) => Formula c v -> Formula c v
sortBinding (Binder c vs body) = Binder c (sort vs) (sortBinding body)
sortBinding (Const c fs) = Const c (map sortBinding fs)
sortBinding (Var v fs) = Var v fs

{- +++++++++++++++++++++++ alphaNormalize +++++++++++++++++++++++ -}

data IntVar v = SVar v | NVar Int

instance Show sv => Show (IntVar sv) where
    show (SVar v) = show v
    show (NVar n) = show n

alphaNormalize :: (Eq v,Ord v) => Formula c (ScopeLabel v) -> (Formula c Int,[v],[ScopeLabel v])
alphaNormalize f = (nf,reverse freeVars,boundVars)
    where (nf,(freeVars,boundVars)) = state ([],[])
          (State state) = alphaNormalizeST f

alphaNormalizeST :: (Eq v,Ord v) => Formula c (ScopeLabel v) -> State ([v],[ScopeLabel v]) (Formula c Int)
alphaNormalizeST (Const c ts) =
    do nts <- mapM alphaNormalizeST ts
       return (Const c nts)
alphaNormalizeST (Var v ts) =
    do num <- separateSymbols v
       nts <- mapM alphaNormalizeST ts
       return (Var num nts)
alphaNormalizeST (Binder c vars body) =
    do nbody <- alphaNormalizeST body
       nvars <- mapM separateSymbols vars
       return (Binder c nvars nbody)

--data FBVar v = FreeVar v | BoundVar v deriving (Eq,Ord,Show)

separateSymbols :: (Eq s,Ord s) => (ScopeLabel s) -> State ([s],[ScopeLabel s]) Int
separateSymbols symbol =
    case symbol
	 of (Scope 0 v) -> do (freeVars,boundVars) <- get
                              put (v:freeVars,boundVars)
                              return 0
	    (Scope _ _) -> do (freeVars,boundVars) <- get
			      let (newBoundVars,int) = updateListAndGetIndex symbol boundVars
				  in do put (freeVars,newBoundVars)
					return (int+1)

{-
*Normalization> alphaNormalize $ annotateScope f1
((and 0 (all (1) 1) 0 (all (2) 2)),([a,a],[a1,a2]))
*Normalization> alphaNormalize $ annotateScope f2
((and 0 (all (2) (all (1) 1)) 0 (all (3) 3)),([a,a],[a2,a1,a3]))
*Normalization> alphaNormalize $ annotateScope f3
((and 0 (all (4 3) (all (2 1) (1 2 3))) 0 (all (5) 5)),([a,a],[f2,a2,b1,a1,a3]))
-}

--normalize :: (Eq v,Ord v,Ord c) => Formula (Constant c) v -> (Formula (Constant c) Int,[v],[ScopeLabel v])
--normalize :: (Show c, Show v,Eq v,Ord v,Ord c) => Formula (Constant c) v -> (Skeleton c,[v],String)
normalize f = if (countNodes f > 100) -- && (maxACI f > 8)
	      then getSkeletonParams ((weakNormalize f),"weak")
	      else getSkeletonParams ((strongNormalize f),"strong")
    where getSkeletonParams ((sceleton,paramaters,_),info) = (sortBinding sceleton,paramaters,info)
	  weakNormalize = alphaNormalize . mergeBinding . elemTrueFalse . prenex . annotateScope
	  strongNormalize = alphaNormalize . mergeBinding . maybeAciFormula . cnf . elemTrueFalse . prenex . annotateScope
	  maybeAciFormula f = if (maxACI f < 8) then (aciFormula f) else f

countNodes (Var _ fs) = 1 + (sum (map countNodes fs))
countNodes (Const _ fs) = 1 + (sum (map countNodes fs))
countNodes (Binder _ vars f) = 1 + (length vars) + (countNodes f)

maxOfArgs :: [Formula (Constant c) v] -> Int
maxOfArgs fs = if null fs then 0 else (maximum (map maxACI fs))
maxACI :: Formula (Constant c) v -> Int
maxACI (Const Or fs) = max (length fs) (maxOfArgs fs)
maxACI (Const And fs) = max (length fs) (maxOfArgs fs)
maxACI (Var _ fs) = (maxOfArgs fs)
maxACI (Const _ fs) = (maxOfArgs fs)
maxACI (Binder _ _ f) = (maxACI f)



{- +++++++++++++++++++++++ Linearisierung abstrakter Formeln +++++++++++++++++++++++ -}
--data Formula c v = Const c [Formula c v] | Var v [Formula c v] | Binder c [v] (Formula c v)

type Link = String -- vorlauefig: hier sollen die zugehoerigen Formelparameter der abstrakten Formel abgelegt werden, sowie ein pointer zu der Theorie und der konkreten Formel darin.
type ArityMap c v = Map.Map Int (SymbolMap c v)
data SymbolMap c v = Branch (Map.Map (SymbolNode c v) (ArityMap c v))
                   | Leaf (Map.Map (SymbolNode c v) Link) deriving (Show,Ord,Eq)
data SymbolNode c v = C c | V v deriving (Show,Ord,Eq)
type AF c = Formula (Constant c) Int
type TreeOfLAF c v = Map.Map Int (SymbolMap c v)

