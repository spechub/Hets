{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  experimental
Portability :  portable 

   extract ids from As for mixfix analysis
-}

module HasCASL.AsToIds where

import HasCASL.As
import Common.Id
import Common.AS_Annotation
import qualified Common.Lib.Set as Set

data Ids = Ids { predIds :: Set.Set Id
	       , otherIds :: Set.Set Id } deriving (Show, Eq)

unite :: [Ids] -> Ids
unite l = Ids (Set.unions $ map predIds l) $ Set.unions $ map otherIds l

idsOfBasicSpec :: BasicSpec -> Ids 
idsOfBasicSpec (BasicSpec l) = unite $ map (idsOfBasicItem . item) l 

emptyIds :: Ids
emptyIds = Ids Set.empty Set.empty

toIds :: [Set.Set Id] -> Ids
toIds is = Ids Set.empty $ Set.unions is

idsOfBasicItem :: BasicItem -> Ids 
idsOfBasicItem (SigItems i) = idsOfSigItems i
idsOfBasicItem (ClassItems _ l _ ) = unite $ map (idsOfClassItem . item) l
idsOfBasicItem (GenVarItems l _) = toIds $ map idsOfGenVarDecl l
idsOfBasicItem (ProgItems l _) = toIds $ map (idsOfProgEq . item) l
idsOfBasicItem (FreeDatatype l _) = toIds $ map (idsOfDatatype . item) l
idsOfBasicItem (GenItems l _) = unite $ map (idsOfSigItems . item) l
idsOfBasicItem (AxiomItems decls fs _) = 
    toIds (map idsOfGenVarDecl decls 
	      ++ map (idsOfTerm . item) fs)
idsOfBasicItem (Internal l _) = unite $ map (idsOfBasicItem . item) l

idsOfClassItem :: ClassItem -> Ids
idsOfClassItem (ClassItem _ l _) = unite $ map (idsOfBasicItem . item) l

idsOfSigItems :: SigItems -> Ids
idsOfSigItems (TypeItems _ l _) = toIds $ map (idsOfTypeItem . item) l
idsOfSigItems (OpItems b l _) = unite $ map (idsOfOpItem b . item) l

idsOfTypeItem :: TypeItem -> Set.Set Id
idsOfTypeItem (SubtypeDefn _ vs _ t _) = 
    Set.union (idsOfVars vs) $ idsOfTerm $ item t
idsOfTypeItem (Datatype d) = idsOfDatatype d 
idsOfTypeItem _ = Set.empty

idsOfVars :: Vars -> Set.Set Id
idsOfVars (Var v) = Set.single v
idsOfVars (VarTuple vs _) = Set.unions $ map idsOfVars vs

idsOfOpItem :: OpBrand -> OpItem -> Ids
idsOfOpItem b (OpDecl os _ as _) = 
    let ois = Set.fromList $ map ( \ (OpId i _ _) -> i) os  
	ais = Set.unions $ map idsOfAttr as
	in case b of 
		  Pred -> Ids ois ais
		  _ -> toIds [ois, ais]
idsOfOpItem b (OpDefn (OpId i _ _) vs _ _ t _) =
    let vis = Set.unions $ map (Set.unions . map idsOfVarDecl) vs 
	tis = Set.union vis $ idsOfTerm t
	in case b of 
		  Pred -> Ids (Set.single i) tis 
		  _ -> toIds [Set.insert i tis]

idsOfAttr :: OpAttr -> Set.Set Id
idsOfAttr (BinOpAttr _ _) = Set.empty
idsOfAttr (UnitOpAttr t _) = idsOfTerm t

idsOfVarDecl :: VarDecl -> Set.Set Id
idsOfVarDecl (VarDecl v _ _ _) = Set.single v

idsOfGenVarDecl :: GenVarDecl -> Set.Set Id
idsOfGenVarDecl (GenVarDecl v) = idsOfVarDecl v
idsOfGenVarDecl (GenTypeVarDecl _ ) = Set.empty

idsOfDatatype :: DatatypeDecl -> Set.Set Id
idsOfDatatype (DatatypeDecl _ _ as _ _) = 
    Set.unions $ map (idsOfAlternative . item) as  

idsOfAlternative :: Alternative -> Set.Set Id
idsOfAlternative (Constructor c cs _ _) =
    Set.insert c $ Set.unions $ map (Set.unions . map idsOfComponent) cs 
idsOfAlternative (Subtype _ _) = Set.empty

idsOfComponent :: Component -> Set.Set Id
idsOfComponent (Selector s _ _ _ _) = Set.single s
idsOfComponent (NoSelector _) = Set.empty

idsOfProgEq :: ProgEq -> Set.Set Id
idsOfProgEq (ProgEq p t _) = 
    Set.union (idsOfPattern p) $ idsOfTerm t

idsOfTerm :: Term -> Set.Set Id
idsOfTerm (TypedTerm t _ _ _) = idsOfTerm t
idsOfTerm (QuantifiedTerm _ vs t _) = 
    Set.union (idsOfTerm t) $ Set.unions $ map idsOfGenVarDecl vs
idsOfTerm (LambdaTerm ps _ t _) = 
    Set.union (idsOfTerm t) $ Set.unions $ map idsOfPattern ps
idsOfTerm (CaseTerm t es _) = 
    Set.union (idsOfTerm t) $ Set.unions $ map idsOfProgEq es
idsOfTerm (LetTerm _ es t _) = 
    Set.union (idsOfTerm t) $ Set.unions $ map idsOfProgEq es
idsOfTerm (MixfixTerm ts) = Set.unions $ map idsOfTerm ts
idsOfTerm (BracketTerm _ ts _) = Set.unions $ map idsOfTerm ts
idsOfTerm _ = Set.empty

idsOfPattern :: Pattern -> Set.Set Id
idsOfPattern (PatternVar v) = idsOfVarDecl v
idsOfPattern (TypedPattern p _ _) = idsOfPattern p
idsOfPattern (AsPattern p1 p2 _) = 
    Set.union (idsOfPattern p1) $ idsOfPattern p2
idsOfPattern (PatternToken t) = Set.single $ simpleIdToId t
idsOfPattern (BracketPattern _ ps _) = Set.unions $ map idsOfPattern ps
idsOfPattern (MixfixPattern ps) = Set.unions $ map idsOfPattern ps
idsOfPattern _ = Set.empty
