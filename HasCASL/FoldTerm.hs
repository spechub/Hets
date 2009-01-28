{- |
Module      :  $Header$
Description :  fold functions for terms and program equations
Copyright   :  (c) Christian Maeder and Uni Bremen 2005
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

folding terms
-}

module HasCASL.FoldTerm where

import HasCASL.As
import Common.Id
import qualified Data.Set as Set

data FoldRec a b = FoldRec
    { foldQualVar :: Term -> VarDecl -> a
    , foldQualOp :: Term -> OpBrand -> PolyId -> TypeScheme -> [Type]
        -> InstKind -> Range -> a
    , foldApplTerm :: Term -> a -> a -> Range -> a
    , foldTupleTerm :: Term -> [a] -> Range -> a
    , foldTypedTerm :: Term -> a -> TypeQual -> Type -> Range -> a
    , foldAsPattern :: Term -> VarDecl -> a -> Range -> a
    , foldQuantifiedTerm
        :: Term -> Quantifier -> [GenVarDecl] -> a -> Range -> a
    , foldLambdaTerm :: Term -> [a] -> Partiality -> a -> Range -> a
    , foldCaseTerm :: Term -> a -> [b] -> Range -> a
    , foldLetTerm :: Term -> LetBrand -> [b] -> a -> Range -> a
    , foldResolvedMixTerm :: Term -> Id -> [Type] -> [a] -> Range -> a
    , foldTermToken :: Term -> Token -> a
    , foldMixTypeTerm  :: Term ->TypeQual -> Type -> Range -> a
    , foldMixfixTerm :: Term -> [a] -> a
    , foldBracketTerm :: Term -> BracketKind -> [a] -> Range -> a
    , foldProgEq :: ProgEq -> a -> a -> Range -> b
    }

type MapRec = FoldRec Term ProgEq

mapRec :: MapRec
mapRec = FoldRec
    { foldQualVar = \ _ -> QualVar
    , foldQualOp = \ _ -> QualOp
    , foldApplTerm = \ _ -> ApplTerm
    , foldTupleTerm = \ _ -> TupleTerm
    , foldTypedTerm = \ _ -> TypedTerm
    , foldAsPattern = \ _ -> AsPattern
    , foldQuantifiedTerm = \ _ -> QuantifiedTerm
    , foldLambdaTerm = \ _ -> LambdaTerm
    , foldCaseTerm = \ _ -> CaseTerm
    , foldLetTerm = \ _ -> LetTerm
    , foldResolvedMixTerm = \ _ -> ResolvedMixTerm
    , foldTermToken = \ _ -> TermToken
    , foldMixTypeTerm = \ _ -> MixTypeTerm
    , foldMixfixTerm = \ _ -> MixfixTerm
    , foldBracketTerm = \ _ -> BracketTerm
    , foldProgEq = \ _ -> ProgEq
    }

foldTerm :: FoldRec a b -> Term -> a
foldTerm r t = case t of
   QualVar vd -> foldQualVar r t vd
   QualOp b i sc tys k qs -> foldQualOp r t b i sc tys k qs
   ApplTerm t1 t2 ps ->
       foldApplTerm r t (foldTerm r t1) (foldTerm r t2) ps
   TupleTerm ts ps -> foldTupleTerm r t (map (foldTerm r) ts) ps
   TypedTerm te q ty ps -> foldTypedTerm r t (foldTerm r te) q ty ps
   QuantifiedTerm q vs te ps ->
       foldQuantifiedTerm r t q vs (foldTerm r te) ps
   LambdaTerm ps p te qs ->
       foldLambdaTerm r t (map (foldTerm r) ps) p (foldTerm r te) qs
   CaseTerm te es ps ->
       foldCaseTerm r t (foldTerm r te) (map (foldEq r) es) ps
   LetTerm b es te ps ->
       foldLetTerm r t b (map (foldEq r) es) (foldTerm r te) ps
   AsPattern vd pa ps -> foldAsPattern r t vd (foldTerm r pa) ps
   TermToken tok -> foldTermToken r t tok
   MixfixTerm ts -> foldMixfixTerm r t $ map (foldTerm r) ts
   BracketTerm b ts ps -> foldBracketTerm r t b (map (foldTerm r) ts) ps
   MixTypeTerm q ty ps -> foldMixTypeTerm r t q ty ps
   ResolvedMixTerm i tys ts ps ->
       foldResolvedMixTerm r t i tys (map (foldTerm r) ts) ps

foldEq :: FoldRec a b -> ProgEq -> b
foldEq r e@(ProgEq p t q) = foldProgEq r e (foldTerm r p) (foldTerm r t) q

getAllTypes :: Term -> [Type]
getAllTypes = foldTerm FoldRec
    { foldQualVar = \ _ (VarDecl _ t _ _) -> [t]
    , foldQualOp = \ _ _ _ _ ts _ _ -> ts
    , foldApplTerm = \ _ t1 t2 _ -> t1 ++ t2
    , foldTupleTerm = \ _ tts _ -> concat tts
    , foldTypedTerm = \ _ ts _ t _ -> t : ts
    , foldAsPattern = \ _ (VarDecl _ t _ _) ts _ -> t : ts
    , foldQuantifiedTerm = \ _ _ gvs ts _ -> ts ++ concatMap
         ( \ gv -> case gv of
                     GenVarDecl (VarDecl _ t _ _) -> [t]
                     _ -> []) gvs
    , foldLambdaTerm = \ _ _ _ ts _ -> ts
    , foldCaseTerm = \ _ ts tts _ -> concat $ ts : tts
    , foldLetTerm = \ _ _ tts ts _ -> concat $ ts : tts
    , foldResolvedMixTerm = \ _ _ ts tts _ -> ts ++ concat tts
    , foldTermToken = \ _ _ -> []
    , foldMixTypeTerm = \ _ _ _ _ -> []
    , foldMixfixTerm = \ _ tts -> concat tts
    , foldBracketTerm = \ _ _ tts _ -> concat tts
    , foldProgEq = \ _ ps ts _ -> ps ++ ts
    }

freeVars :: Term -> Set.Set VarDecl
freeVars = foldTerm FoldRec
    { foldQualVar = \ _ t -> Set.singleton t
    , foldQualOp = \ _ _ _ _ _ _ _ -> Set.empty
    , foldApplTerm = \ _ t1 t2 _ -> Set.union t1 t2
    , foldTupleTerm = \ _ tts _ -> Set.unions tts
    , foldTypedTerm = \ _ ts _ _ _ -> ts
    , foldAsPattern = \ _ t ts _ -> Set.insert t ts
    , foldQuantifiedTerm = \ _ _ gvs ts _ -> Set.difference ts $
         foldr ( \ gv -> case gv of
           GenVarDecl t -> Set.insert t
           _ -> id) Set.empty gvs
    , foldLambdaTerm = \ _ pats _ ts _ -> Set.difference ts $ Set.unions pats
    , foldCaseTerm = \ _ ts tts _ -> Set.difference
          (Set.unions $ ts : map snd tts) $ Set.unions $ map fst tts
    , foldLetTerm = \ _ _ tts ts _ -> Set.difference
          (Set.unions $ ts : map snd tts) $ Set.unions $ map fst tts
    , foldResolvedMixTerm = \ _ _ _ tts _ -> Set.unions tts
    , foldTermToken = \ _ _ -> Set.empty
    , foldMixTypeTerm = \ _ _ _ _ -> Set.empty
    , foldMixfixTerm = \ _ tts -> Set.unions tts
    , foldBracketTerm = \ _ _ tts _ -> Set.unions tts
    , foldProgEq = \ _ ps ts _ -> (ps, ts)
    }
