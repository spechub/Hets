
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2004
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

CASL signature
    
-}

module CASL.Sign where

import CASL.AS_Basic_CASL
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty
import Common.Lib.State
import CASL.Print_AS_Basic
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.Result
import Common.AS_Annotation
import Common.AnnoState

-- a dummy datatype for the LogicGraph and for identifying the right
-- instances
data CASL = CASL deriving (Show)


data FunKind = Total | Partial deriving (Show, Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SORT], opRes :: SORT} 
	      deriving (Show, Eq, Ord)

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

class (Show lid, AParsable b, AParsable s, AParsable f, PrettyPrint e,
      Eq f, Eq e) => 
      Analyzable lid b s f e | lid -> b, lid -> s, lid -> f, lid -> e where
      analyzeExtBasicItems :: lid -> b -> (Maybe e) -> (Maybe e)
      analyzeExtSigItems :: lid -> s -> (Maybe e) -> (Maybe e)
      analyzeExtFormula :: lid -> f -> f

data Analyzable lid b s f e =>
     Sign lid b s f e = Sign { sortSet :: Set.Set SORT
	       , sortRel :: Rel.Rel SORT	 
               , opMap :: Map.Map Id (Set.Set OpType)
	       , assocOps :: Map.Map Id (Set.Set OpType)
	       , predMap :: Map.Map Id (Set.Set PredType)
               , varMap :: Map.Map SIMPLE_ID (Set.Set SORT)
	       , sentences :: [Named (FORMULA f)]	 
	       , envDiags :: [Diagnosis]
               , extendedInfo :: Maybe e
	       } deriving (Show)

-- specific types for CASL logic
type CASLSign = Sign CASL () () () ()
type CASLFORMULA = FORMULA ()

-- better ignore assoc flags for equality
instance Analyzable lid b s f e => Eq (Sign lid b s f e) where
    e1 == e2 = 
	sortSet e1 == sortSet e1 &&
	sortRel e1 == sortRel e2 &&
	opMap e1 == opMap e2 &&
	predMap e1 == predMap e2 &&
        extendedInfo e1 == extendedInfo e2

emptySign :: Analyzable lid b s f e => Sign lid b s f e
emptySign = Sign { sortSet = Set.empty
	       , sortRel = Rel.empty
	       , opMap = Map.empty
	       , assocOps = Map.empty
	       , predMap = Map.empty
	       , varMap = Map.empty
	       , sentences = []
	       , envDiags = []
               , extendedInfo = Nothing }

subsortsOf :: Analyzable lid b s f e => 
              SORT -> Sign lid b s f e -> Set.Set SORT
subsortsOf s e =
  Set.insert s $
    Map.foldWithKey addSubs (Set.empty) (Rel.toMap $ sortRel e)
  where addSubs sub supers =
         if s `Set.member` supers 
            then Set.insert sub
            else id

supersortsOf :: Analyzable lid b s f e => SORT -> Sign lid b s f e -> Set.Set SORT
supersortsOf s e =
  case Map.lookup s $ Rel.toMap $ sortRel e of
    Nothing -> Set.single s
    Just supers -> Set.insert s supers

toOP_TYPE :: OpType -> OP_TYPE
toOP_TYPE OpType { opArgs = args, opRes = res, opKind = k } =
    (case k of 
     Total -> Total_op_type 
     Partial -> Partial_op_type) args res []

toPRED_TYPE :: PredType -> PRED_TYPE
toPRED_TYPE PredType { predArgs = args } = Pred_type args []

toOpType :: OP_TYPE -> OpType
toOpType (Total_op_type args r _) = OpType Total args r
toOpType (Partial_op_type args r _) = OpType Partial args r

toPredType :: PRED_TYPE -> PredType
toPredType (Pred_type args _) = PredType args

instance PrettyPrint OpType where
  printText0 ga ot = printText0 ga $ toOP_TYPE ot

instance PrettyPrint PredType where
  printText0 ga pt = printText0 ga $ toPRED_TYPE pt

instance Analyzable lid b s f e => PrettyPrint (Sign lid b s f e) where
    printText0 ga s = 
	ptext "sorts" <+> commaT_text ga (Set.toList $ sortSet s) 
	$$ 
        (if Rel.isEmpty (sortRel s) then empty
            else ptext "sorts" <+> 
             (vcat $ map printRel $ Map.toList $ Rel.toMap $ sortRel s))
	$$ 
	vcat (map (\ (i, t) -> 
		   ptext "op" <+>
		   printText0 ga i <+> colon <>
		   printText0 ga t) 
	      $ concatMap (\ (o, ts) ->
			  map ( \ ty -> (o, ty) ) $ Set.toList ts)
	       $ Map.toList $ opMap s)
	$$ 
	vcat (map (\ (i, t) -> 
		   ptext "pred" <+>
		   printText0 ga i <+> colon <+>
		   printText0 ga (toPRED_TYPE t)) 
	     $ concatMap (\ (o, ts) ->
			  map ( \ ty -> (o, ty) ) $ Set.toList ts)
	     $ Map.toList $ predMap s)
     where printRel (subs, supersorts) =
             printText0 ga subs <+> ptext "<" <+> printSet ga supersorts

-- working with Sign

diffSig :: Analyzable lid b s f e => Sign lid b s f e -> Sign lid b s f e -> Sign lid b s f e
diffSig a b = 
    a { sortSet = sortSet a `Set.difference` sortSet b
      , sortRel = Rel.transClosure $ Rel.fromSet $ Set.difference
	(Rel.toSet $ sortRel a) $ Rel.toSet $ sortRel b
      , opMap = opMap a `diffMapSet` opMap b
      , assocOps = assocOps a `diffMapSet` assocOps b	
      , predMap = predMap a `diffMapSet` predMap b	
      }
  -- transClosure needed:  {a < b < c} - {a < c; b} 
  -- is not transitive!

diffMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) 
	   -> Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
diffMapSet =
    Map.differenceWith ( \ s t -> let d = Set.difference s t in
			 if Set.isEmpty d then Nothing 
			 else Just d )

addSig :: Analyzable lid b s f e => Sign lid b s f e -> Sign lid b s f e -> Sign lid b s f e
addSig a b = 
    a { sortSet = sortSet a `Set.union` sortSet b
      , sortRel = Rel.transClosure $ Rel.fromSet $ Set.union
	(Rel.toSet $ sortRel a) $ Rel.toSet $ sortRel b
      , opMap = remPartOpsM $ Map.unionWith Set.union (opMap a) $ opMap b
      , assocOps = Map.unionWith Set.union (assocOps a) $ assocOps b
      , predMap = Map.unionWith Set.union (predMap a) $ predMap b	
      }

isEmptySig :: Analyzable lid b s f e => Sign lid b s f e -> Bool 
isEmptySig s = 
    Set.isEmpty (sortSet s) && 
    Rel.isEmpty (sortRel s) && 
    Map.isEmpty (opMap s) &&
    Map.isEmpty (predMap s)

isSubSig :: Analyzable lid b s f e => Sign lid b s f e -> Sign lid b s f e -> Bool
isSubSig sub super = isEmptySig $ diffSig sub 
                      (super 
		       { opMap = addPartOpsM $ opMap super })

partOps :: Set.Set OpType -> Set.Set OpType
partOps s = Set.fromDistinctAscList $ map ( \ t -> t { opKind = Partial } ) 
	 $ Set.toList $ Set.filter ((==Total) . opKind) s

remPartOps :: Set.Set OpType -> Set.Set OpType 
remPartOps s = s Set.\\ partOps s

remPartOpsM :: Ord a => Map.Map a (Set.Set OpType) 
	    -> Map.Map a (Set.Set OpType) 
remPartOpsM = Map.map remPartOps

addPartOps :: Set.Set OpType -> Set.Set OpType 
addPartOps s = Set.union s $ partOps s

addPartOpsM :: Ord a => Map.Map a (Set.Set OpType) 
	    -> Map.Map a (Set.Set OpType) 
addPartOpsM = Map.map addPartOps

addDiags :: Analyzable lid b s f e => [Diagnosis] -> State (Sign lid b s f e) ()
addDiags ds = 
    do e <- get
       put e { envDiags = ds ++ envDiags e }

addSort :: Analyzable lid b s f e => SORT -> State (Sign lid b s f e) ()
addSort s = 
    do e <- get
       let m = sortSet e
       if Set.member s m then 
	  addDiags [mkDiag Hint "redeclared sort" s] 
	  else put e { sortSet = Set.insert s m }

checkSort :: Analyzable lid b s f e => SORT -> State (Sign lid b s f e) ()
checkSort s = 
    do m <- gets sortSet
       addDiags $ if Set.member s m then [] else 
		    [mkDiag Error "unknown sort" s]

addSubsort :: Analyzable lid b s f e => SORT -> SORT -> State (Sign lid b s f e) ()
addSubsort super sub = 
    do e <- get
       mapM_ checkSort [super, sub] 
       put e { sortRel = Rel.insert sub super $ sortRel e }

closeSubsortRel :: Analyzable lid b s f e => State (Sign lid b s f e) ()
closeSubsortRel= 
    do e <- get
       put e { sortRel = Rel.transClosure $ sortRel e }

addVars :: Analyzable lid b s f e => VAR_DECL -> State (Sign lid b s f e) ()
addVars (Var_decl vs s _) = mapM_ (addVar s) vs

addVar :: Analyzable lid b s f e => 
          SORT -> SIMPLE_ID -> State (Sign lid b s f e) ()
addVar s v = 
    do e <- get
       let m = varMap e
           l = Map.findWithDefault Set.empty v m
       if Set.member s l then 
	  addDiags [mkDiag Hint "redeclared var" v] 
	  else put e { varMap = Map.insert v (Set.insert s l) m }

