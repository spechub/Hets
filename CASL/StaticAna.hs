
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
apply mixfix resolution to all terms and formulae in basic items 

- collect signature

-}

module CASL.StaticAna where

import CASL.AS_Basic_CASL
import CASL.MixfixParser
import Common.Lib.State
import Common.PrettyPrint
import Common.PPUtils
import Common.Lib.Pretty
import CASL.Print_AS_Basic
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Named
import Common.Result
import Data.Maybe

-- * data types for the environment 

data FunKind = Total | Partial deriving (Show, Eq, Ord)

-- constants have empty argument lists 
data OpType = OpType {opKind :: FunKind, opArgs :: [SORT], opRes :: SORT} 
	      deriving (Show, Eq, Ord)

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

data Env = Env { sortSet :: Set.Set SORT
	       , sortRel :: Rel.Rel SORT	 
               , opMap :: Map.Map Id (Set.Set OpType)
	       , predMap :: Map.Map Id (Set.Set PredType)
               , varMap :: Map.Map SIMPLE_ID (Set.Set SORT)
	       , sentences :: [Named FORMULA]	 
	       , envDiags :: [Diagnosis]
	       } deriving (Show, Eq)

emptyEnv :: Env
emptyEnv = Env { sortSet = Set.empty
	       , sortRel = Rel.empty
	       , opMap = Map.empty
	       , predMap = Map.empty
	       , varMap = Map.empty
	       , sentences = []
	       , envDiags = [] }

addSort :: SORT -> State Env ()
addSort s = 
    do e <- get
       let m = sortSet e
       put e { sortSet = Set.insert s m }
       addDiags $ if Set.member s m then [mkDiag Hint "known sort" s] else []

checkSort :: SORT -> State Env ()
checkSort s = 
    do m <- gets sortSet
       addDiags $ if Set.member s m then [] else 
		    [mkDiag Error "unknown sort" s]

addSubsort :: SORT -> SORT -> State Env ()
addSubsort super sub = 
    do e <- get
       mapM_ checkSort [super, sub] 
       put e { sortRel = Rel.insert sub super $ sortRel e }

addVars :: VAR_DECL -> State Env ()
addVars (Var_decl vs s _) = mapM_ (addVar s) vs

addVar :: SORT -> SIMPLE_ID -> State Env ()
addVar s v = 
    do e <- get
       let m = varMap e
           l = Map.findWithDefault Set.empty v m
       put e { varMap = Map.insert v (s `Set.insert` l) m }
       addDiags $ if s `Set.member` l then 
		    [mkDiag Hint "known var" v] else []

addOp :: OpType -> Id -> State Env ()
addOp ty i = 
    do mapM_ checkSort (opRes ty : opArgs ty)
       e <- get
       let m = opMap e
           l = Map.findWithDefault Set.empty i m
       put e { opMap = Map.insert i (ty `Set.insert` l) m }
       addDiags $ if ty `Set.member` l then 
		    [mkDiag Hint "known op" i] else []

addPred :: PredType -> Id -> State Env ()
addPred ty i = 
    do mapM_ checkSort $ predArgs ty
       e <- get
       let m = predMap e
           l = Map.findWithDefault Set.empty i m
       put e { predMap = Map.insert i (ty `Set.insert` l) m }
       addDiags $ if ty `Set.member` l then 
		    [mkDiag Hint "known pred" i] else []

allOpIds :: Env -> Set.Set Id
allOpIds = Set.fromList . Map.keys . opMap 

formulaIds :: Env -> Set.Set Id
formulaIds e = 
    Set.fromList (map simpleIdToId $ Map.keys $ varMap e) 
	   `Set.union` allOpIds e

allPredIds :: Env -> Set.Set Id
allPredIds = Set.fromList . Map.keys . predMap 

addDiags :: [Diagnosis] -> State Env ()
addDiags ds = 
    do e <- get
       put e { envDiags = ds ++ envDiags e }

addSentences :: [Named FORMULA] -> State Env ()
addSentences ds = 
    do e <- get
       put e { sentences = ds ++ sentences e }

mapAnM :: (Monad m) => (a -> m b) -> [Annoted a] -> m [Annoted b]
mapAnM f al = 
    do il <- mapM (f . item) al
       return $ zipWith ( \ a i -> a { item = i }) al il
		
-- * traversing all data types of the abstract syntax

ana_BASIC_SPEC :: GlobalAnnos -> BASIC_SPEC -> State Env BASIC_SPEC
ana_BASIC_SPEC ga (Basic_spec al) = fmap Basic_spec $
			       mapAnM (ana_BASIC_ITEMS ga) al

-- looseness of a datatype
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord)

ana_BASIC_ITEMS :: GlobalAnnos -> BASIC_ITEMS -> State Env BASIC_ITEMS
ana_BASIC_ITEMS ga bi = 
    case bi of 
    Sig_items sis -> fmap Sig_items $ ana_SIG_ITEMS ga Loose sis 
    Free_datatype al _ -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_DATATYPE_DECL Free) al 
	   return bi
    Sort_gen al ps ->
	do ul <- mapAnM (ana_SIG_ITEMS ga Generated) al 
	   return $ Sort_gen ul ps
    Var_items il _ -> 
	do mapM_ addVars il
	   return bi
    Local_var_axioms il afs ps -> 
	do e <- get -- save
	   mapM_ addVars il
	   ops <- gets formulaIds
	   put e -- restore 
	   preds <- gets allPredIds
	   let rfs = map (resolveFormula ga ops preds . item) afs 
	       ds = concatMap diags rfs
	       arfs = zipWith ( \ a m -> case maybeResult m of 
				Nothing -> Nothing
				Just f -> Just a { item = f }) afs rfs
	       ufs = mapMaybe id arfs
	       fufs = map ( \ a -> a { item = Quantification Universal il 
				     (item a) ps } ) ufs
	       sens = map ( \ a -> NamedSen (getRLabel a) $ item a) fufs
           addDiags ds
           addSentences sens			    
           return $ Local_var_axioms il ufs ps
    Axiom_items afs ps -> 		    
	do ops <- gets formulaIds
	   preds <- gets allPredIds
	   let rfs = map (resolveFormula ga ops preds . item) afs 
	       ds = concatMap diags rfs
	       arfs = zipWith ( \ a m -> case maybeResult m of 
				Nothing -> Nothing
				Just f -> Just a { item = f }) afs rfs
	       ufs = mapMaybe id arfs
	       sens = map ( \ a -> NamedSen (getRLabel a) $ item a) ufs
           addDiags ds
           addSentences sens			    
           return $ Axiom_items ufs ps

ana_SIG_ITEMS :: GlobalAnnos -> GenKind -> SIG_ITEMS -> State Env SIG_ITEMS
ana_SIG_ITEMS ga gk si = 
    case si of 
    Sort_items al ps -> 
	do ul <- mapAnM (ana_SORT_ITEM ga) al 
	   return $ Sort_items ul ps
    Op_items al ps -> 
	do ul <- mapAnM (ana_OP_ITEM ga) al 
	   return $ Op_items ul ps
    Pred_items al ps -> 
	do ul <- mapAnM (ana_PRED_ITEM ga) al 
	   return $ Pred_items ul ps
    Datatype_items al _ -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
	   mapAnM (ana_DATATYPE_DECL gk) al 
	   return si

ana_SORT_ITEM :: GlobalAnnos -> SORT_ITEM -> State Env SORT_ITEM
ana_SORT_ITEM ga si = 
    case si of 
    Sort_decl il _ ->
	do mapM_ addSort il
	   return si
    Subsort_decl il i _ -> 
	do mapM_ addSort (i:il)
	   mapM_ (addSubsort i) il
	   return si
    Subsort_defn sub v super af ps -> 
	do addSort sub
           ops <- gets allOpIds 
	   preds <- gets allPredIds
           let Result ds mf = resolveFormula ga 
			      (Set.insert (simpleIdToId v) ops) preds $ item af
           addDiags ds 
	   addSubsort super sub
	   return $ case mf of 
	            Nothing -> Subsort_decl [sub] super ps
		    Just f -> Subsort_defn sub v super af { item = f } ps
    Iso_decl il _ ->
	do mapM_ addSort il
	   mapM_ ( \ i -> mapM_ (addSubsort i) il) il
	   return si

ana_OP_ITEM :: GlobalAnnos -> OP_ITEM -> State Env OP_ITEM
ana_OP_ITEM ga oi = 
    case oi of 
    Op_decl ops ty il ps -> 
	do mapM_ (addOp $ toOpType ty) ops
	   ul <- mapM (ana_OP_ATTR ga) il
	   return $ Op_decl ops ty (mapMaybe id ul) ps
    Op_defn i par at ps -> 
	do let ty = headToType par
           addOp (toOpType ty) i
	   ops <- gets allOpIds
	   preds <- gets allPredIds 
	   let vars = headToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveMixfix ga allOps preds False $ item at
	   addDiags ds
	   return $ case mt of 
	            Nothing -> Op_decl [i] ty [] ps
		    Just t -> Op_defn i par at { item = t } ps
    where 
    toOpType :: OP_TYPE -> OpType
    toOpType (Total_op_type args r _) = OpType Total args r
    toOpType (Partial_op_type args r _) = OpType Partial args r
    headToType :: OP_HEAD -> OP_TYPE
    headToType (Total_op_head args r ps) = 
	Total_op_type (sortsOfArgs args) r ps
    headToType (Partial_op_head args r ps) = 
	Partial_op_type (sortsOfArgs args) r ps
    headToVars :: OP_HEAD -> [VAR]
    headToVars h = 
	let as = case h of 
		 Total_op_head args _ _ -> args
		 Partial_op_head args _ _ -> args
	    in concatMap ( \ (Arg_decl v _ _) -> v) as 

sortsOfArgs :: [ARG_DECL] -> [SORT]
sortsOfArgs = map ( \ (Arg_decl _ s _) -> s)

ana_OP_ATTR :: GlobalAnnos -> OP_ATTR -> State Env (Maybe OP_ATTR)
ana_OP_ATTR ga oa = 
    case oa of 
    Unit_op_attr t ->
	do ops <- gets allOpIds
	   preds <- gets allPredIds 
	   let Result ds mt = resolveMixfix ga ops preds False t
	   addDiags ds
	   return $ fmap Unit_op_attr mt
    _ -> return $ Just oa

ana_PRED_ITEM :: GlobalAnnos -> PRED_ITEM -> State Env PRED_ITEM
ana_PRED_ITEM ga p = 
    case p of 
    Pred_decl preds ty _ -> 
	do mapM (addPred $ toPredType ty) preds
	   return p
    Pred_defn i par at ps ->
	do let ty = predHeadToType par
           addPred (toPredType ty) i
	   ops <- gets allOpIds
	   preds <- gets allPredIds 
	   let vars = predHeadToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveFormula ga allOps preds $ item at
	   addDiags ds
	   return $ case mt of 
	            Nothing -> Pred_decl [i] ty ps
		    Just t -> Pred_defn i par at { item = t } ps
    where 
    toPredType :: PRED_TYPE -> PredType
    toPredType (Pred_type args _) = PredType args
    predHeadToType :: PRED_HEAD -> PRED_TYPE
    predHeadToType (Pred_head args ps) = 
	Pred_type (sortsOfArgs args) ps
    predHeadToVars :: PRED_HEAD -> [VAR]
    predHeadToVars (Pred_head args _) = 
	concatMap ( \ (Arg_decl v _ _) -> v) args 

ana_DATATYPE_DECL :: GenKind -> DATATYPE_DECL -> State Env ()
ana_DATATYPE_DECL _gk (Datatype_decl s al _) = 
-- GenKind currently unused 
    do mapAnM (ana_ALTERNATIVE s) al
       return ()

ana_ALTERNATIVE :: SORT -> ALTERNATIVE -> State Env ()
ana_ALTERNATIVE s c = 
    case c of 
    Total_construct i il _ -> 
	do ul <- mapM (ana_COMPONENTS s) il
	   let ty = OpType Total (concatMap compSort il) s
           addOp ty i
    Partial_construct i il _ -> 
	do ul <- mapM (ana_COMPONENTS s) il
	   let ty = OpType Partial (concatMap compSort il) s
           addOp ty i
    Subsorts ss _ ->
	do mapM_ (addSubsort s) ss
    where compSort :: COMPONENTS -> [SORT]
	  compSort (Total_select l cs _) = map (const cs) l
	  compSort (Partial_select l cs _) = map (const cs) l
	  compSort (Sort cs) = [cs]
 
ana_COMPONENTS :: SORT -> COMPONENTS -> State Env ()
ana_COMPONENTS s c = 
    case c of 
    Total_select is cs _ ->
	do let ty = OpType Total [s] cs
	   mapM_ (addOp ty) is
    Partial_select is cs _ ->
	do let ty = OpType Partial [s] cs
	   mapM_ (addOp ty) is
    _ -> return ()

-- wrap it all up for a logic

type Sign = Env  -- ignoring vars, sentences and diags

type Sentence = FORMULA

emptySign :: Sign
emptySign = emptyEnv 

basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos)
                 -> Result (BASIC_SPEC,Sign,Sign,[Named Sentence])

basicAnalysis (bs, inSig, ga) = 
    let (bs', accSig) = runState (ana_BASIC_SPEC ga bs) inSig
	ds = envDiags accSig
	sents = sentences accSig
	cleanSig = accSig { envDiags = [], sentences = [], varMap = Map.empty }
	in Result ds $ Just (bs',cleanSig `diffSig` inSig, cleanSig, sents) 

diffSig :: Sign -> Sign -> Sign
diffSig a b = 
    a { sortSet = sortSet a `Set.difference` sortSet b
      , sortRel = fromSet $ Set.difference
	(toSet $ sortRel a) $ toSet $ sortRel b
      , opMap = opMap a `diffMapSet` opMap b	
      , predMap = predMap a `diffMapSet` predMap b	
      }

diffMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) 
	   -> Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
diffMapSet =
    Map.differenceWith ( \ s t -> let d = Set.difference s t in
			 if Set.isEmpty d then Nothing 
			 else Just d )

toSet :: (Ord a) => Rel.Rel a -> Set.Set (a, a)
toSet = Set.fromList . Rel.toList

fromSet :: (Ord a) => Set.Set (a, a) -> Rel.Rel a
fromSet = Rel.fromList . Set.toList 

addSig :: Sign -> Sign -> Sign
addSig a b = 
    a { sortSet = sortSet a `Set.union` sortSet b
      , sortRel = fromSet $ Set.union
	(toSet $ sortRel a) $ toSet $ sortRel b
      , opMap = Map.unionWith Set.union (opMap a) $ opMap b	
      , predMap = Map.unionWith Set.union (predMap a) $ predMap b	
      }

isEmptySig :: Sign -> Bool 
isEmptySig s = 
    Set.isEmpty (sortSet s) && 
    Rel.isEmpty (sortRel s) && 
    Map.isEmpty (opMap s) &&
    Map.isEmpty (predMap s)

isSubSig :: Sign -> Sign -> Bool
isSubSig sub super = isEmptySig $ diffSig sub super

toOP_TYPE :: OpType -> OP_TYPE
toOP_TYPE OpType { opArgs = args, opRes = res, opKind = k } =
    (case k of 
     Total -> Total_op_type 
     Partial -> Partial_op_type) args res []

toPRED_TYPE :: PredType -> PRED_TYPE
toPRED_TYPE PredType { predArgs = args } = Pred_type args []

instance PrettyPrint Sign where
    printText0 ga s = 
	ptext "sorts" <+> commaT_text ga (Set.toList $ sortSet s) 
	$$ 
	vcat (map (\ (i, t) -> 
		   ptext "op" <+>
		   printText0 ga i <+> colon <>
		   printText0 ga (toOP_TYPE t)) 
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
		   
