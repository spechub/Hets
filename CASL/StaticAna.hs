
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

CASL static analysis for basic specifications
    
-}

module CASL.StaticAna where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.MixfixParser
import CASL.Overload
import Common.Lib.State
import Common.PrettyPrint
import Common.Lib.Pretty
import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Lib.Rel as Rel
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Named
import Common.Result
import Data.Maybe

checkPlaces :: [SORT] -> Id -> [Diagnosis]
checkPlaces args i = 
    if let n = placeCount i in n == 0 || n == length args then []
	   else [mkDiag Error "wrong number of places" i]

addOp :: OpType -> Id -> State Sign ()
addOp ty i = 
    do mapM_ checkSort (opRes ty : opArgs ty)
       e <- get
       let m = opMap e
           l = Map.findWithDefault Set.empty i m
	   check = addDiags $ checkPlaces (opArgs ty) i
	   store = do put e { opMap = Map.insert i (Set.insert ty l) m }
       if Set.member ty l then 
	     addDiags [mkDiag Hint "redeclared op" i] 
          else case opKind ty of 
	  Partial -> if Set.member ty {opKind = Total} l then
		     addDiags [mkDiag Warning "partially redeclared" i] 
		     else store >> check
	  Total -> do store
		      if Set.member ty {opKind = Partial} l then
			 addDiags [mkDiag Hint "redeclared as total" i] 
			 else check

addAssocOp :: OpType -> Id -> State Sign ()
addAssocOp ty i = do
       e <- get
       let m = assocOps e
	   pty = ty { opKind = Partial } -- ignore FunKind
           l = Map.findWithDefault Set.empty i m
       put e { assocOps = Map.insert i (Set.insert pty l) m }

addPred :: PredType -> Id -> State Sign ()
addPred ty i = 
    do mapM_ checkSort $ predArgs ty
       e <- get
       let m = predMap e
           l = Map.findWithDefault Set.empty i m
       if Set.member ty l then 
	  addDiags [mkDiag Hint "redeclared pred" i] 
	  else do put e { predMap = Map.insert i (Set.insert ty l) m }
		  addDiags $ checkPlaces (predArgs ty) i

allOpIds :: State Sign (Set.Set Id)
allOpIds = do 
    e <- get
    return $ Set.fromDistinctAscList $ Map.keys $ opMap e 

addAssocs :: GlobalAnnos -> State Sign GlobalAnnos
addAssocs ga = do 
    e <- get
    return ga { assoc_annos =  
		foldr ( \ i m -> case Map.lookup i m of
			Nothing -> Map.insert i ALeft m
			_ -> m ) (assoc_annos ga) (Map.keys $ assocOps e) } 

formulaIds :: State Sign (Set.Set Id)
formulaIds = do
    e <- get
    ops <- allOpIds
    return (Set.fromDistinctAscList (map simpleIdToId $ Map.keys $ varMap e) 
	       `Set.union` ops)

allPredIds :: State Sign (Set.Set Id)
allPredIds = do
    e <- get
    return $ Set.fromDistinctAscList $ Map.keys $ predMap e

addSentences :: [Named FORMULA] -> State Sign ()
addSentences ds = 
    do e <- get
       put e { sentences = ds ++ sentences e }

-- * traversing all data types of the abstract syntax

ana_BASIC_SPEC :: GlobalAnnos -> BASIC_SPEC -> State Sign BASIC_SPEC
ana_BASIC_SPEC ga (Basic_spec al) = fmap Basic_spec $
			       mapAnM (ana_BASIC_ITEMS ga) al

-- looseness of a datatype
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord)

ana_BASIC_ITEMS :: GlobalAnnos -> BASIC_ITEMS -> State Sign BASIC_ITEMS
ana_BASIC_ITEMS ga bi = 
    case bi of 
    Sig_items sis -> fmap Sig_items $ ana_SIG_ITEMS ga Loose sis 
    Free_datatype al _ -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_DATATYPE_DECL Free) al 
           closeSubsortRel 
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
	   ops <- formulaIds
	   put e -- restore 
	   preds <- allPredIds
	   newGa <- addAssocs ga
	   let rfs = map (resolveFormula newGa ops preds . item) afs 
	       ds = concatMap diags rfs
	       arfs = zipWith ( \ a m -> case maybeResult m of 
				Nothing -> Nothing
				Just f -> Just a { item = f }) afs rfs
	       ufs = catMaybes arfs
	       fufs = map ( \ a -> a { item = Quantification Universal il 
				     (item a) ps } ) ufs
	       sens = map ( \ a -> NamedSen (getRLabel a) $ item a) fufs
           addDiags ds
           addSentences sens			    
           return $ Local_var_axioms il ufs ps
    Axiom_items afs ps -> 		    
	do ops <- formulaIds
	   preds <- allPredIds
	   newGa <- addAssocs ga
	   let rfs = map (resolveFormula newGa ops preds . item) afs 
	       ds = concatMap diags rfs
	       arfs = zipWith ( \ a m -> case maybeResult m of 
				Nothing -> Nothing
				Just f -> Just a { item = f }) afs rfs
	       ufs = catMaybes arfs
	       sens = map ( \ a -> NamedSen (getRLabel a) $ item a) ufs
           addDiags ds
           addSentences sens			    
           return $ Axiom_items ufs ps

ana_SIG_ITEMS :: GlobalAnnos -> GenKind -> SIG_ITEMS -> State Sign SIG_ITEMS
ana_SIG_ITEMS ga gk si = 
    case si of 
    Sort_items al ps -> 
	do ul <- mapAnM (ana_SORT_ITEM ga) al 
           closeSubsortRel
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
           closeSubsortRel
	   return si

ana_SORT_ITEM :: GlobalAnnos -> SORT_ITEM -> State Sign SORT_ITEM
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
	do ops <- allOpIds 
	   preds <- allPredIds
	   newGa <- addAssocs ga
           let Result ds mf = resolveFormula newGa
			      (Set.insert (simpleIdToId v) ops) preds $ item af
           addDiags ds 
	   addSort sub
           addSubsort super sub
	   return $ case mf of 
	            Nothing -> Subsort_decl [sub] super ps
		    Just f -> Subsort_defn sub v super af { item = f } ps
    Iso_decl il _ ->
	do mapM_ addSort il
	   mapM_ ( \ i -> mapM_ (addSubsort i) il) il
	   return si

toOpType :: OP_TYPE -> OpType
toOpType (Total_op_type args r _) = OpType Total args r
toOpType (Partial_op_type args r _) = OpType Partial args r

ana_OP_ITEM :: GlobalAnnos -> OP_ITEM -> State Sign OP_ITEM
ana_OP_ITEM ga oi = 
    case oi of 
    Op_decl ops ty il ps -> 
	do mapM_ (addOp $ toOpType ty) ops
	   ul <- mapM (ana_OP_ATTR ga) il
	   if Assoc_op_attr `elem` il then
	      mapM_ (addAssocOp $ toOpType ty) ops
	      else return ()
	   return $ Op_decl ops ty (catMaybes ul) ps
    Op_defn i par at ps -> 
	do let ty = headToType par
           addOp (toOpType ty) i
	   ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
 	   let vars = headToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveMixfix newGa allOps preds False $ item at
	   addDiags ds
	   return $ case mt of 
	            Nothing -> Op_decl [i] ty [] ps
		    Just t -> Op_defn i par at { item = t } ps
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
sortsOfArgs = concatMap ( \ (Arg_decl l s _) -> map (const s) l)

ana_OP_ATTR :: GlobalAnnos -> OP_ATTR -> State Sign (Maybe OP_ATTR)
ana_OP_ATTR ga oa = 
    case oa of 
    Unit_op_attr t ->
	do ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
	   let Result ds mt = resolveMixfix newGa ops preds False t
	   addDiags ds
	   return $ fmap Unit_op_attr mt
    _ -> return $ Just oa

toPredType :: PRED_TYPE -> PredType
toPredType (Pred_type args _) = PredType args

ana_PRED_ITEM :: GlobalAnnos -> PRED_ITEM -> State Sign PRED_ITEM
ana_PRED_ITEM ga p = 
    case p of 
    Pred_decl preds ty _ -> 
	do mapM (addPred $ toPredType ty) preds
	   return p
    Pred_defn i par at ps ->
	do let ty = predHeadToType par
           addPred (toPredType ty) i
	   ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
	   let vars = predHeadToVars par
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveFormula newGa allOps preds $ item at
	   addDiags ds
	   return $ case mt of 
	            Nothing -> Pred_decl [i] ty ps
		    Just t -> Pred_defn i par at { item = t } ps
    where 
    predHeadToType :: PRED_HEAD -> PRED_TYPE
    predHeadToType (Pred_head args ps) = 
	Pred_type (sortsOfArgs args) ps
    predHeadToVars :: PRED_HEAD -> [VAR]
    predHeadToVars (Pred_head args _) = 
	concatMap ( \ (Arg_decl v _ _) -> v) args 

-- full function type of a selector (result sort is component sort)
data Component = Component { compId :: Id, compType :: OpType }
		 deriving (Show)

instance Eq Component where
    Component i1 t1 == Component i2 t2 = 
	(i1, opArgs t1, opRes t1) == (i2, opArgs t2, opRes t2)

instance Ord Component where
    Component i1 t1 <=  Component i2 t2 = 
	(i1, opArgs t1, opRes t1) <= (i2, opArgs t2, opRes t2)

instance PrettyPrint Component where
    printText0 ga (Component i ty) =
	printText0 ga i <+> colon <> printText0 ga ty

instance PosItem Component where
    get_pos = Just . posOfId . compId

-- full function type of constructor (result sort is the data type)
data Alternative = Construct Id OpType [Component]
		   deriving (Show, Eq) 

ana_DATATYPE_DECL :: GenKind -> DATATYPE_DECL -> State Sign ()
ana_DATATYPE_DECL _gk (Datatype_decl s al _) = 
-- GenKind currently unused 
    do ul <- mapM (ana_ALTERNATIVE s . item) al
       let constr = catMaybes ul
       if null constr then return ()
	  else do addDiags $ checkUniqueness $ map fst constr
		  let totalSels = Set.unions $ map snd constr
		      wrongConstr = filter ((totalSels /=) . snd) constr
		  addDiags $ map ( \ (c, _) -> mkDiag Error 
		      ("total selectors '" ++ showSepList (showString ",")
		       showPretty (Set.toList totalSels) 
		       "'\n\tmust appear in alternative") c) wrongConstr

ana_ALTERNATIVE :: SORT -> ALTERNATIVE 
		-> State Sign (Maybe (Component, Set.Set Component))
ana_ALTERNATIVE s c = 
    case c of 
    Subsorts ss _ ->
	do mapM_ (addSubsort s) ss
	   return Nothing
    _ -> do let (part, i, il) = case c of 
			     Total_construct a l _ -> (Total, a, l)
			     Partial_construct a l _ -> (Partial, a, l)
			     _ -> error "ana_ALTERNATIVE"
		ty = OpType part (concatMap compSort il) s
	    addOp ty i
	    ul <- mapM (ana_COMPONENTS s) il
            let ts = concatMap fst ul
            addDiags $ checkUniqueness (ts ++ concatMap snd ul)
	    return $ Just (Component i ty, Set.fromList ts) 
    where compSort :: COMPONENTS -> [SORT]
	  compSort (Total_select l cs _) = map (const cs) l
	  compSort (Partial_select l cs _) = map (const cs) l
	  compSort (Sort cs) = [cs]
 
ana_COMPONENTS :: SORT -> COMPONENTS -> State Sign ([Component], [Component])
ana_COMPONENTS s c = 
    case c of 
    Sort _ -> return ([], [])
    _ -> do let (part, is, cs) = case c of 
				 Total_select as bs _ -> (Total, as, bs) 
				 Partial_select as bs _ -> (Partial, as, bs) 
				 _ -> error "ana_COMPONENTS"
		ty = OpType part [s] cs
		ts = map ( \ i -> Component i ty) is
	    mapM_ (addOp ty) is
	    return $ case part of 
			       Total -> (ts, [])
			       Partial -> ([], ts)

-- wrap it all up for a logic

basicAnalysis :: (BASIC_SPEC, Sign, GlobalAnnos)
                 -> Result (BASIC_SPEC, Sign, Sign, [Named FORMULA])

basicAnalysis (bs, inSig, ga) = do 
    let (newBs, accSig) = runState (ana_BASIC_SPEC ga bs) inSig
	ds = envDiags accSig
	sents = sentences accSig
	cleanSig = accSig { envDiags = [], sentences = [], varMap = Map.empty }
	diff = diffSig cleanSig inSig
	remPartOpsS s = s { opMap = remPartOpsM $ opMap s }
    --checked_sents <- return sents
    checked_sents <- overloadResolution accSig sents
    Result ds (Just ()) -- insert diags
    return ( newBs
	   , remPartOpsS diff
	   , remPartOpsS cleanSig
	   , checked_sents ) 

