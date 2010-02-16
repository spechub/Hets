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

import HasCASL.As
import HasCASL.FoldTerm
import HasCASL.AsUtils
import HasCASL.PrintAs
import HasCASL.Le
import HasCASL.Logic_HasCASL

import Common.Id
import Common.DocUtils
import Common.Result
import Common.ExtSign
import Common.AS_Annotation

import Static.GTheory
import Static.DevGraph

import Logic.Coerce
import Logic.Prover

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List as List
import Data.Maybe


                   


------------------------- Subst type -------------------------

data SubstConst = SConst Id TypeScheme | SVar Id Type deriving (Eq, Ord)
type SubstType = Id

type Subst = (Map.Map SubstConst Term, Map.Map SubstType Type)

eps :: Subst
eps = (Map.empty, Map.empty)


lookupTerm :: Subst -> SubstConst -> Maybe Term
lookupTerm (m,_) k = Map.lookup k m

lookupType :: Subst -> SubstType -> Maybe Type
lookupType (_,t) k = Map.lookup k t

addTerm :: Subst -> SubstConst -> Term -> Subst
addTerm (m,t) k v = (Map.insert k v m, t)

removeTerm :: Subst -> SubstConst -> Subst
removeTerm (m,t) k = (Map.delete k m, t)
                 
addType :: Subst -> SubstType -> Type -> Subst
addType (m,t) k v = (m, Map.insert k v t)

removeType :: Subst -> SubstType -> Subst
removeType (m,t) k = (m, Map.delete k t)
                 


class LookupSubst a b where
    lookupS :: Subst -> a -> Maybe b

class SCLike a where
    toSC :: a -> SubstConst

class STLike a where
    toST :: a -> SubstType

class Substable a where
    subst :: Subst -> a -> a

---- instances



instance SCLike a => LookupSubst a Term where
    lookupS s x = lookupTerm s $ toSC x

instance STLike a => LookupSubst a Type where
    lookupS s x = lookupType s $ toST x


instance SCLike VarDecl where
    toSC (VarDecl n typ _ _) = SVar n typ

instance SCLike (Id, OpInfo) where
    toSC (n, inf) = SConst n $ opType inf

instance SCLike (PolyId, TypeScheme) where
    toSC (PolyId n _ _, typs) = SConst n typs

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


---- other functions
typevarId :: TypeArg -> Id
typevarId (TypeArg n _ _ _ _ _ _)= n

removeGVD :: Subst -> GenVarDecl -> Subst
removeGVD s gvd =
    case gvd of
      GenVarDecl vd -> removeC s vd
      GenTypeVarDecl t -> removeT s t

removeListGVD :: Subst -> [GenVarDecl] -> Subst
removeListGVD s l = foldl removeGVD s l


------------------------- Substitution -------------------------

substWithDefault :: LookupSubst a b => Subst -> b -> a -> b
substWithDefault s dfault x =
    case lookupS s x of Nothing -> dfault
                        Just t -> t


instance Substable Type where
    subst s t = t

instance Substable Term where
    subst s@(m,_) t
      | Map.null m = t
      | otherwise =
          case t of
          -- QualVar VarDecl
          -- pos "(", "var", ":", ")"
          qv@(QualVar v) -> substWithDefault s qv v
          -- QualOp OpBrand PolyId TypeScheme [Type] InstKind Range
          -- pos "(", "op", ":", ")"
          qo@(QualOp _ n typ _ _ _) -> substWithDefault s qo (n,typ)
          -- ApplTerm Term Term Range  -- analysed
          -- pos?
          ApplTerm t1 t2 rg -> ApplTerm (subst s t1) (subst s t2) rg
          -- TupleTerm [Term] Range    -- special application
          -- pos "(", ","s, ")"
          TupleTerm l rg -> TupleTerm (map (subst s) l) rg
          -- TypedTerm Term TypeQual Type Range
          -- pos ":", "as" or "in"
          TypedTerm term tq typ rg ->
              TypedTerm (subst s term) tq (subst s typ) rg
          -- AsPattern VarDecl Term Range
          -- pos "@"
          -- patterns are terms constructed by the first six variants
          p@(AsPattern _ _ _) -> p
          -- QuantifiedTerm Quantifier [GenVarDecl] Term Range
          -- pos quantifier, ";"s, dot
          -- only "forall" may have a TypeVarDecl
          QuantifiedTerm q vars term rg ->
              let s' = removeListGVD s vars
              in QuantifiedTerm q vars (subst s' term) rg
          
{-
          -- LambdaTerm [Term] Partiality Term Range
          -- pos "\", dot (plus "!")
          LambdaTerm vars p term rg ->
          -- CaseTerm Term [ProgEq] Range
          -- pos "case", "of", "|"s
          CaseTerm term eqs rg ->
          -- LetTerm LetBrand [ProgEq] Term Range
          LetTerm lb eqs term rg -> 
-}
          _ -> t


------------------------- Play around output -------------------------

showHasCASLSig :: DGNodeLab -> Result ()
showHasCASLSig dgn = do
   case dgn_theory dgn of
    G_theory lid (ExtSign sign _) _ sens _ ->
        do
          csign <- coercePlainSign lid HasCASL "" sign
          csens <- coerceSens lid HasCASL "" $ toNamedList sens
          test1 csign csens
          hint () ("\n"++show lid ++"\n") nullRange
          return ()

showL :: [String]->String
showL l =  unlines $ intersperse "" l

test1 :: Env -> [Named Sentence] -> Result ()
test1 e s = do
  hint () ("\n"
           ++ "ops:\n" ++ (showL $ map toSimpOp (flattenOpMap $ assumps e)) ++"\n\n"
           ++ "sens:\n" ++ (showL $ map toSimpNSen s) ++"\n\n"
          ) nullRange
  return ()

------------------------- SIMPLE OUTPUT FOR Ops -------------------------

flattenSetMap :: Map.Map a (Set.Set b) -> [(a,b)]
flattenSetMap m = Map.foldWithKey f [] m where
    f k v l = map (\x -> (k,x)) (Set.toList v) ++ l


flattenOpMap :: Assumps -> [(Id,OpInfo)]
flattenOpMap = flattenSetMap

toSimpOp :: (Id,OpInfo) -> String
toSimpOp (n, inf) = show n
                    ++ ": " ++ toSimpTypS (opType inf)
                    ++ case opDefn inf of 
                         Definition _ t -> " = " ++ toSimp t
                         _ -> ""

------------------------- SIMPLE OUTPUT FOR Types -------------------------


toSimpTypS :: TypeScheme -> String
toSimpTypS (TypeScheme a t _) =
    case a of [] -> toSimpTyp t
              _ -> toSimpBind "!" (map toSimpTypArg a) $ toSimpTyp t

toSimpTypArg :: TypeArg -> String
toSimpTypArg (TypeArg n _ _ _ _ _ _) = show n

toSimpTyp :: Type -> String
toSimpTyp = show . pretty

------------------------- SIMPLE OUTPUT FOR Terms/Sentences -------------------------

toSimpNSen :: Named Sentence -> String
toSimpNSen x = concat [senAttr x, ": ", toSimpSen $ sentence x]

toSimpSen :: Sentence -> String
toSimpSen (Formula t) = toSimp t
toSimpSen _ = "unsupported!"

toSimp :: Term -> String
toSimp = foldTerm toSimpRec

toSimpVar s = s
toSimpSym s = s ++ "@"
toSimpApp s a = toSimpParens "()" " " [s, a]
toSimpBind q vars b = toSimpParens "[]" " " [q, toSimpParens "() ." ", " vars, b]
toSimpParens b sep l = concat $ [b!!0] : intersperse sep l ++ [tail b]
toSimpProgEq x y = concat [x,"=",y]

toSimpQuant Universal = "!"
toSimpQuant Existential = "?"
toSimpQuant Unique = "?!"

toSimpGVDs l = map toSimpGVD l
toSimpVD (VarDecl i t _ _) = show i ++ ":" ++ toSimpTyp t
toSimpGVD (GenVarDecl v) = toSimpVD v
toSimpGVD (GenTypeVarDecl v) = toSimpTypArg v

toSimpRec :: FoldRec String String
toSimpRec = FoldRec
    { -- Term VarDecl
      foldQualVar = \_ (VarDecl v _ _ _) -> toSimpVar $ show v
      -- Term OpBrand PolyId TypeScheme [Type] InstKind Range
    , foldQualOp = \_ _ (PolyId i _ _) t _ _ _ -> (toSimpSym $ show i)++":"++toSimpTypS t
    -- Term a a Range
    , foldApplTerm = \ (ApplTerm _ o2 _) y z _ -> toSimpApp y z
    -- Term [a] Range
    , foldTupleTerm = \_ l _ -> toSimpParens "<>" ", " l
    -- Term a TypeQual Type Range
    , foldTypedTerm = \_ z _ _ _ -> z
    -- Term Quantifier [GenVarDecl] a Range
    , foldQuantifiedTerm =
        \_ q vars z _ -> toSimpBind (toSimpQuant q) (toSimpGVDs vars) z
    -- Term [a] Partiality a Range
    , foldLambdaTerm = \_ vars _ b _ -> toSimpBind "lam" vars b
    -- Term VarDecl a Range
    , foldAsPattern = \_ _ _ _ -> failInTermRec "AsPattern"
    -- Term a [b] Range
    , foldCaseTerm = \_ _ _ _ -> failInTermRec "CaseTerm"
    -- Term LetBrand [b] a Range
    , foldLetTerm = \_ _ eql b _ -> toSimpBind "let" eql b
    -- ProgEq a a Range
    , foldProgEq = \_ x y _ -> toSimpProgEq x y
    -- Term Id [Type] [a] Range
    , foldResolvedMixTerm = \_ _ _ _ _ -> failInTermRec "ResolvedMixTerm"
    -- Term Token
    , foldTermToken = \_ _ -> failInTermRec "TermToken"
    -- TermTypeQual Type Range
    , foldMixTypeTerm = \_ _ _ _ -> failInTermRec "MixTypeTerm"
    -- Term [a]
    , foldMixfixTerm = \_ _ -> failInTermRec "MixfixTerm"
    -- Term BracketKind [a] Range
    , foldBracketTerm = \_ _ _ _ -> failInTermRec "BracketTerm"
    }

failInTermRec :: String -> a
failInTermRec x = error $ "Occurence of " ++ x ++ " in toSimpRec!"


------------------------- SIMPLE OUTPUT FOR Types -------------------------

