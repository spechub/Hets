
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  All rights reserved.

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable
    
apply mixfix resolution to all terms and formulae in basic items 

-}


module CASL.StaticAna where

import CASL.AS_Basic_CASL
import CASL.MixfixParser
import Common.Lib.State
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

data SortInfo = SortInfo deriving (Show, Eq)

data OpInfo = OpInfo { opType :: OP_TYPE } deriving (Show, Eq)

data PredInfo = PredInfo { predType :: PRED_TYPE } deriving (Show, Eq)

data Env = Env { sortMap :: Map.Map SORT SortInfo
	       , sortRel :: Rel.Rel SORT	 
               , opMap :: Map.Map Id [OpInfo]
	       , predMap :: Map.Map Id [PredInfo]
               , varMap :: Map.Map SIMPLE_ID (Set.Set SORT)
	       , sentences :: [Named FORMULA]	 
               , globalAnnos :: GlobalAnnos
	       , envDiags :: [Diagnosis]
	       } deriving (Show)

emptyEnv :: Env
emptyEnv = Env { sortMap = Map.empty
	       , sortRel = Rel.empty
	       , opMap = Map.empty
	       , predMap = Map.empty
	       , varMap = Map.empty
	       , sentences = []
	       , globalAnnos = emptyGlobalAnnos
	       , envDiags = [] }

addSort :: SORT -> State Env ()
addSort s = 
    do e <- get
       put e { sortMap = Map.insert s SortInfo $ sortMap e }

addSuperSort :: SORT -> SORT -> State Env ()
addSuperSort super sub = 
    do e <- get
       put e { sortRel = Rel.insert sub super $ sortRel e }

addOp :: OP_TYPE -> Id -> State Env ()
addOp ty i = 
    do e <- get
       put e { opMap = Map.insert i [OpInfo ty] $ opMap e }

addPred :: PRED_TYPE -> Id -> State Env ()
addPred ty i = 
    do e <- get
       put e { predMap = Map.insert i [PredInfo ty] $ predMap e }

allOpIds :: Env -> Set.Set Id
allOpIds = Set.fromList . Map.keys . opMap 

formulaIds :: Env -> Set.Set Id
formulaIds e = 
    Set.fromList ((map simpleIdToId $ Map.keys $ varMap e) ++
       Map.keys (opMap e))

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

maBASIC_SPEC :: BASIC_SPEC -> State Env BASIC_SPEC
maBASIC_SPEC (Basic_spec al) = fmap Basic_spec $
			       mapAnM maBASIC_ITEMS al

maBASIC_ITEMS :: BASIC_ITEMS -> State Env BASIC_ITEMS
maBASIC_ITEMS bi = 
    case bi of 
    Sig_items sis -> fmap Sig_items $ maSIG_ITEMS sis 
    Free_datatype al ps -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           maSORT_ITEM $ Sort_decl sorts ps
           ul <- mapAnM maDATATYPE_DECL al 
	   return $ Free_datatype ul ps
    Sort_gen al ps ->
	do ul <- mapAnM maSIG_ITEMS al 
	   return $ Sort_gen ul ps
    v@(Var_items il _) -> 
	do mapM_ addVars il
	   return v
    Local_var_axioms il afs ps -> 
	do e <- get -- save
	   mapM_ addVars il
	   ops <- gets formulaIds
	   put e -- restore 
	   preds <- gets allPredIds
           ga <- gets globalAnnos
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
           ga <- gets globalAnnos
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

maSIG_ITEMS :: SIG_ITEMS -> State Env SIG_ITEMS
maSIG_ITEMS si = 
    case si of 
    Sort_items al ps -> 
	do ul <- mapAnM maSORT_ITEM al 
	   return $ Sort_items ul ps
    Op_items al ps -> 
	do ul <- mapAnM maOP_ITEM al 
	   return $ Op_items ul ps
    Pred_items al ps -> 
	do ul <- mapAnM maPRED_ITEM al 
	   return $ Pred_items ul ps
    Datatype_items al ps -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           maSORT_ITEM $ Sort_decl sorts ps
	   ul <- mapAnM maDATATYPE_DECL al 
	   return $ Datatype_items ul ps

maSORT_ITEM :: SORT_ITEM -> State Env SORT_ITEM
maSORT_ITEM si = 
    case si of 
    s@(Sort_decl il _) ->
	do mapM_ addSort il
	   return s
    s@(Subsort_decl il i _) -> 
	do mapM_ addSort (i:il)
	   mapM_ (addSuperSort i) il
	   return s
    Subsort_defn sub v super af ps -> 
	do addSort sub
           ops <- gets allOpIds 
	   preds <- gets allPredIds
	   ga <- gets globalAnnos
           let Result ds mf = resolveFormula ga 
			      (Set.insert (simpleIdToId v) ops) preds $ item af
	       uf = case mf of 
			    Nothing -> af 
			    Just f -> af { item = f }
           addDiags ds 
	   addSuperSort super sub
	   return $ Subsort_defn sub v super uf ps
    s@(Iso_decl il _) ->
	do mapM_ addSort il
	   mapM_ ( \ i -> mapM_ (addSuperSort i) il) il
	   return s

maOP_ITEM :: OP_ITEM -> State Env OP_ITEM
maOP_ITEM oi = 
    case oi of 
    Op_decl ops ty il ps -> 
	do mapM_ (addOp ty) ops
	   ul <- mapM maOP_ATTR il
	   return $ Op_decl ops ty ul ps
    Op_defn i par at ps -> 
	do addOp (headToType par) i
	   ops <- gets allOpIds
	   preds <- gets allPredIds 
	   ga <- gets globalAnnos 
	   let vars = headToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveMixfix ga allOps preds False $ item at
	       ut = case mt of 
		    Nothing -> at
		    Just t -> at { item = t }
	   addDiags ds
	   return $ Op_defn i par ut ps
    where 
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

maOP_ATTR :: OP_ATTR -> State Env OP_ATTR
maOP_ATTR oa = 
    case oa of 
    Unit_op_attr t ->
	do ops <- gets allOpIds
	   preds <- gets allPredIds 
	   ga <- gets globalAnnos 
	   let Result ds mt = resolveMixfix ga ops preds False t
	       ut = case mt of 
			 Nothing -> t
			 Just r -> r
	   addDiags ds
	   return $ Unit_op_attr ut
    _ -> return oa

maPRED_ITEM :: PRED_ITEM -> State Env PRED_ITEM
maPRED_ITEM p = 
    case p of 
    Pred_decl preds ty _ -> 
	do mapM (addPred ty) preds
	   return p
    Pred_defn i par at ps -> 
	do addPred (predHeadToType par) i
	   ops <- gets allOpIds
	   preds <- gets allPredIds 
	   ga <- gets globalAnnos 
	   let vars = predHeadToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveFormula ga allOps preds $ item at
	       ut = case mt of 
		    Nothing -> at
		    Just t -> at { item = t }
	   addDiags ds
	   return $ Pred_defn i par ut ps
    where 
    predHeadToType :: PRED_HEAD -> PRED_TYPE
    predHeadToType (Pred_head args ps) = 
	Pred_type (sortsOfArgs args) ps
    predHeadToVars :: PRED_HEAD -> [VAR]
    predHeadToVars (Pred_head args _) = 
	concatMap ( \ (Arg_decl v _ _) -> v) args 


maDATATYPE_DECL :: DATATYPE_DECL -> State Env DATATYPE_DECL
maDATATYPE_DECL dd = return dd

addVars :: VAR_DECL -> State Env ()
addVars (Var_decl vs s _) = 
    do e <- get
       put e { varMap = foldr ( \ v m -> Map.insert v (Set.single s) m)
	       (varMap e) vs }
