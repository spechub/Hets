
{- |
Module      :  $Header$
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2003
Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

Maintainer  :  hets@tzi.de
Stability   :  provisional
Portability :  portable

CASL static analysis for basic specifications
Follows Chaps. III:2 and III:3 of the CASL Reference Manual.
    
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
import Common.Id
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Result
import Data.Maybe
import Data.List

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
    Free_datatype al ps -> 
	do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_DATATYPE_DECL Free) al 
	   toSortGenAx ps $ getDataGenSig al
           closeSubsortRel 
	   return bi
    Sort_gen al ps ->
	do ul <- mapAnM (ana_SIG_ITEMS ga Generated) al 
	   let gs = map (getGenSig . item) ul
	   toSortGenAx ps (Set.unions $ map fst gs, Set.unions $ map snd gs)
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

toSortGenAx :: [Pos] -> (Set.Set Id, Set.Set Component) -> State Sign ()
toSortGenAx ps (sorts, ops) = do
    let s = Set.toList sorts
        f =  Sort_gen_ax s $
			   map ( \ c ->  Qual_op_name (compId c)  
				 (toOP_TYPE $ compType c) []) $ Set.toList ops
    if null s then 
       addDiags[Diag Error "missing generated sort" (headPos ps)]
       else return ()
    addSentences [NamedSen ("ga_generated_" ++ 
 			 showSepList (showString "_") showId s "") f]

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

getGenSig :: SIG_ITEMS -> (Set.Set Id, Set.Set Component)
getGenSig si = case si of 
    Sort_items al _ -> (Set.unions (map (getSorts . item) al), Set.empty)
    Op_items al _ -> (Set.empty, Set.unions (map (getOps . item) al))
    Pred_items _ _ -> (Set.empty, Set.empty)
    Datatype_items dl _ -> getDataGenSig dl

getDataGenSig :: [Annoted DATATYPE_DECL] -> (Set.Set Id, Set.Set Component)
getDataGenSig dl = 
    let alts = map (( \ (Datatype_decl s al _) -> (s, al)) . item) dl
	sorts = map fst alts
	cs = concatMap ( \ (s, al) -> map (( \ a -> 
	      let (i, ty, _) = getConsType s a
	      in Component i ty)) 
		       $ filter ( \ a ->
				  case a of 
				  Subsorts _ _ -> False
				  _ -> True)
		       $ map item al) alts
	in (Set.fromList sorts, Set.fromList cs)

getSorts :: SORT_ITEM -> Set.Set Id
getSorts si = 
    case si of 
    Sort_decl il _ -> Set.fromList il
    Subsort_decl il i _ -> Set.fromList (i:il)
    Subsort_defn sub _ _ _ _ -> Set.single sub
    Iso_decl il _ -> Set.fromList il

getOps :: OP_ITEM -> Set.Set Component
getOps oi = case oi of 
    Op_decl is ty _ _ -> 
	Set.fromList $ map ( \ i -> Component i $ toOpType ty) is
    Op_defn i par _ _ -> Set.single $ Component i $ toOpType $ headToType par

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
    headToVars :: OP_HEAD -> [VAR]
    headToVars h = 
	let as = case h of 
		 Total_op_head args _ _ -> args
		 Partial_op_head args _ _ -> args
	    in concatMap ( \ (Arg_decl v _ _) -> v) as 

headToType :: OP_HEAD -> OP_TYPE
headToType (Total_op_head args r ps) = 
	Total_op_type (sortsOfArgs args) r ps
headToType (Partial_op_head args r ps) = 
	Partial_op_type (sortsOfArgs args) r ps

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

-- | return list of constructors 
ana_DATATYPE_DECL :: GenKind -> DATATYPE_DECL -> State Sign [Component]
ana_DATATYPE_DECL _gk (Datatype_decl s al _) = 
-- GenKind currently unused 
    do ul <- mapM (ana_ALTERNATIVE s . item) al
       let constr = catMaybes ul
           cs = map fst constr		    
       if null constr then return ()
	  else do addDiags $ checkUniqueness cs
		  let totalSels = Set.unions $ map snd constr
		      wrongConstr = filter ((totalSels /=) . snd) constr
		  addDiags $ map ( \ (c, _) -> mkDiag Error 
		      ("total selectors '" ++ showSepList (showString ",")
		       showPretty (Set.toList totalSels) 
		       "'\n\tmust appear in alternative") c) wrongConstr
       return cs


getConsType :: SORT -> ALTERNATIVE -> (Id, OpType, [COMPONENTS])
getConsType s c = 
    let (part, i, il) = case c of 
			Subsorts _ _ ->  error "getConsType"
			Total_construct a l _ -> (Total, a, l)
			Partial_construct a l _ -> (Partial, a, l)
	in (i, OpType part (concatMap 
			    (map (opRes . snd) . getCompType s) il) s, il)

getCompType :: SORT -> COMPONENTS -> [(Maybe Id, OpType)]
getCompType s (Total_select l cs _) = 
    map (\ i -> (Just i, OpType Total [s] cs)) l
getCompType s (Partial_select l cs _) = 
    map (\ i -> (Just i, OpType Partial [s] cs)) l
getCompType s (Sort cs) = [(Nothing, OpType Partial [s] cs)]

genSelVars :: Int -> [(Maybe Id, OpType)] -> [VAR_DECL]
genSelVars _ [] = []
genSelVars n ((_, ty):rs)  = 
    Var_decl [mkSelVar n] (opRes ty) [] : genSelVars (n+1) rs

mkSelVar :: Int -> Token
mkSelVar n = mkSimpleId ("X" ++ show n)

makeSelForms :: [VAR_DECL] -> TERM 
	     -> Int -> [(Maybe Id, OpType)] -> [Named FORMULA]
makeSelForms _ _ _ [] = []
makeSelForms vs t n ((mi, ty):rs) =
    (case mi of 
	    Nothing -> []
	    Just i -> [NamedSen ("ga_selector_" ++ showId i "")
	             $ Quantification Universal vs 
		      (Strong_equation 
		       (Application (Qual_op_name i (toOP_TYPE ty) []) [t] [])
		       (Qual_var (mkSelVar n) (opRes ty) []) []) []]
    )  ++ makeSelForms vs t (n+1) rs


selForms :: (Id, OpType, [COMPONENTS]) -> [Named FORMULA]
selForms (i, ty, il) =
    let cs = concatMap (getCompType $ opRes ty) il
	vs = genSelVars 1 cs
	t = Application (Qual_op_name i (toOP_TYPE ty) [])
	    (map ( \ (Var_decl v s _) -> Qual_var (head v) s []) vs) []
    in makeSelForms vs t 1 cs 
 
-- | return the constructor and the set of total selectors 
ana_ALTERNATIVE :: SORT -> ALTERNATIVE 
		-> State Sign (Maybe (Component, Set.Set Component))
ana_ALTERNATIVE s c = 
    case c of 
    Subsorts ss _ ->
	do mapM_ (addSubsort s) ss
	   return Nothing
    _ -> do let cons@(i, ty, il) = getConsType s c
	    addOp ty i
	    ul <- mapM (ana_COMPONENTS s) il
            let ts = concatMap fst ul
            addDiags $ checkUniqueness (ts ++ concatMap snd ul)
	    addSentences $ selForms cons
	    return $ Just (Component i ty, Set.fromList ts) 

 
-- | return total and partial selectors
ana_COMPONENTS :: SORT -> COMPONENTS -> State Sign ([Component], [Component])
ana_COMPONENTS s c = do
    let cs = getCompType s c
    sels <- mapM ( \ (mi, ty) -> 
	    case mi of 
	    Nothing -> return Nothing
	    Just i -> do addOp ty i
		         return $ Just $ Component i ty) cs 
    return $ partition ((==Total) . opKind . compType) $ catMaybes sels 

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

