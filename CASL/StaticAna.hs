
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

mkForall :: [VAR_DECL] -> FORMULA -> [Pos] -> FORMULA
mkForall vl f ps = if null vl then f else 
		   Quantification Universal vl f ps

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
	       fufs = map ( \ a -> a { item = mkForall il 
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
	do ul <- mapM (ana_SORT_ITEM ga) al 
           closeSubsortRel
	   return $ Sort_items ul ps
    Op_items al ps -> 
	do ul <- mapM (ana_OP_ITEM ga) al 
	   return $ Op_items ul ps
    Pred_items al ps -> 
	do ul <- mapM (ana_PRED_ITEM ga) al 
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

ana_SORT_ITEM :: GlobalAnnos -> Annoted SORT_ITEM 
	      -> State Sign (Annoted SORT_ITEM)
ana_SORT_ITEM ga asi =
    case item asi of 
    Sort_decl il _ ->
	do mapM_ addSort il
	   return asi
    Subsort_decl il i _ -> 
	do mapM_ addSort (i:il)
	   mapM_ (addSubsort i) il
	   return asi
    Subsort_defn sub v super af ps -> 
	do ops <- allOpIds 
	   preds <- allPredIds
	   newGa <- addAssocs ga
           let Result ds mf = resolveFormula newGa
			      (Set.insert (simpleIdToId v) ops) preds $ item af
	       lb = getRLabel af
	       lab = if null lb then getRLabel asi else lb
           addDiags ds 
	   addSort sub
           addSubsort super sub
	   case mf of 
	     Nothing -> return asi { item = Subsort_decl [sub] super ps}
	     Just f -> do 
	       let p = [posOfId sub]
		   pv = [tokPos v]
	       addSentences[NamedSen lab $
			     mkForall [Var_decl [v] super pv] 
			     (Equivalence 
			      (Membership (Qual_var v super pv) sub p)
			      f p) p]
	       return asi { item = Subsort_defn sub v super af { item = f } ps}
    Iso_decl il _ ->
	do mapM_ addSort il
	   mapM_ ( \ i -> mapM_ (addSubsort i) il) il
	   return asi

ana_OP_ITEM :: GlobalAnnos -> Annoted OP_ITEM -> State Sign (Annoted OP_ITEM)
ana_OP_ITEM ga aoi = 
    case item aoi of 
    Op_decl ops ty il ps -> 
	do let oty = toOpType ty
           mapM_ (addOp oty) ops
	   ul <- mapM (ana_OP_ATTR ga oty ops) il
	   if Assoc_op_attr `elem` il then
	      mapM_ (addAssocOp oty) ops
	      else return ()
	   return aoi {item = Op_decl ops ty (catMaybes ul) ps}
    Op_defn i par at ps -> 
	do let ty = headToType par
	       lb = getRLabel at
	       lab = if null lb then getRLabel aoi else lb
	       args = case par of 
		      Total_op_head as _ _ -> as
		      Partial_op_head as _ _ -> as
	       vs = map (\ (Arg_decl v s qs) -> (Var_decl v s qs)) args
	       arg = concatMap ( \ (Var_decl v s qs) ->
				 map ( \ j -> Qual_var j s qs) v) vs
           addOp (toOpType ty) i
	   ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
 	   let vars =  concatMap ( \ (Arg_decl v _ _) -> v) args
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveMixfix newGa allOps preds False $ item at
	   addDiags ds
	   case mt of 
	     Nothing -> return aoi { item = Op_decl [i] ty [] ps }
	     Just t -> do let p = [posOfId i]
		          addSentences [NamedSen lab $
			     mkForall vs 
			     (Strong_equation 
			      (Application (Qual_op_name i ty p) arg ps)
			      t p) ps]
			  return aoi {item = Op_defn i par at { item = t } ps }

headToType :: OP_HEAD -> OP_TYPE
headToType (Total_op_head args r ps) = 
	Total_op_type (sortsOfArgs args) r ps
headToType (Partial_op_head args r ps) = 
	Partial_op_type (sortsOfArgs args) r ps

sortsOfArgs :: [ARG_DECL] -> [SORT]
sortsOfArgs = concatMap ( \ (Arg_decl l s _) -> map (const s) l)

ana_OP_ATTR :: GlobalAnnos -> OpType -> [Id] -> OP_ATTR 
	    -> State Sign (Maybe OP_ATTR)
ana_OP_ATTR ga ty ois oa = 
    let sty = toOP_TYPE ty
	rty = opRes ty 
	q = [posOfId rty] in
    case oa of 
    Unit_op_attr t ->
	do ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
	   let Result ds mt = resolveMixfix newGa ops preds False t
	   addDiags ds
	   case mt of 
	     Nothing -> return Nothing
	     Just e -> do 
               addSentences $ map (makeUnit True e ty) ois
               addSentences $ map (makeUnit False e ty) ois
	       return $ Just $ Unit_op_attr e
    Assoc_op_attr -> do
      let ns = map mkSimpleId ["x", "y", "z"]
	  vs = map ( \ v -> Var_decl [v] rty q) ns
	  [v1, v2, v3] = map ( \ v -> Qual_var v rty q) ns
	  makeAssoc i = let p = [posOfId i] 
			    qi = Qual_op_name i sty p in 
	    NamedSen ("ga_assoc_" ++ showId i "") $
	    mkForall vs
	    (Strong_equation 
	     (Application qi [v1, Application qi [v2, v3] p] p)
	     (Application qi [Application qi [v1, v2] p, v3] p) p) p
      addSentences $ map makeAssoc ois
      return $ Just oa
    Comm_op_attr -> do 
      let ns = map mkSimpleId ["x", "y"]
	  atys = opArgs ty 
	  vs = zipWith ( \ v t -> Var_decl [v] t (map posOfId atys) ) ns atys
	  args = map toQualVar vs
	  makeComm i = let p = [posOfId i]
			   qi = Qual_op_name i sty p in
	    NamedSen ("ga_comm_" ++ showId i "") $
	    mkForall vs
	    (Strong_equation  
	     (Application qi args p)
	     (Application qi (reverse args) p) p) p
      case atys of 
         [_,_] -> addSentences $ map makeComm ois
	 _ -> addDiags [Diag Error "expecting two arguments for commutativity" 
		       $ posOfId rty]
      return $ Just oa
    Idem_op_attr -> do 
      let v = mkSimpleId "x"
	  vd = Var_decl [v] rty q
	  qv = toQualVar vd
	  makeIdem i = let p = [posOfId i] in 
	    NamedSen ("ga_idem_" ++ showId i "") $
	    mkForall [vd]
	    (Strong_equation  
	     (Application (Qual_op_name i sty p) [qv, qv] p)
	     qv p) p
      addSentences $ map makeIdem ois
      return $ Just oa

makeUnit :: Bool -> TERM -> OpType -> Id -> Named FORMULA
makeUnit b t ty i =
    let lab = "ga_" ++ (if b then "right" else "left") ++ "_unit_"
	      ++ showId i ""
	v = mkSimpleId "x"
	vty = opRes ty
	q = [posOfId vty]
	p = [posOfId i]
	qv = Qual_var v vty q
	args = [qv, t] 
	rargs = if b then args else reverse args
    in NamedSen lab $ mkForall [Var_decl [v] vty q]
		     (Strong_equation 
		      (Application (Qual_op_name i (toOP_TYPE ty) p) rargs p)
		      qv p) p

ana_PRED_ITEM :: GlobalAnnos -> Annoted PRED_ITEM 
	      -> State Sign (Annoted PRED_ITEM)
ana_PRED_ITEM ga ap = 
    case item ap of 
    Pred_decl preds ty _ -> 
	do mapM (addPred $ toPredType ty) preds
	   return ap
    Pred_defn i par at ps ->
	do let Pred_head args rs = par
	       lb = getRLabel at
	       lab = if null lb then getRLabel ap else lb
	       ty = Pred_type (sortsOfArgs args) rs
	       vs = map (\ (Arg_decl v s qs) -> (Var_decl v s qs)) args
	       arg = concatMap ( \ (Var_decl v s qs) ->
				 map ( \ j -> Qual_var j s qs) v) vs
           addPred (toPredType ty) i
	   ops <- allOpIds
	   preds <- allPredIds 
	   newGa <- addAssocs ga
	   let vars = concatMap ( \ (Arg_decl v _ _) -> v) args 
	       allOps = foldr ( \ v s -> Set.insert (simpleIdToId v) s) 
			ops vars 
	       Result ds mt = resolveFormula newGa allOps preds $ item at
	   addDiags ds
	   case mt of 
	     Nothing -> return ap {item = Pred_decl [i] ty ps}
	     Just t -> do 
	       let p = [posOfId i]
               addSentences [NamedSen lab $
			     mkForall vs 
			     (Equivalence (Predication (Qual_pred_name i ty p)
					   arg p) t p) p]
	       return ap {item = Pred_defn i par at { item = t } ps}

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
ana_DATATYPE_DECL gk (Datatype_decl s al _) = 
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
       case gk of 
         Free -> do 
	   let allts = map item al
	       (alts, subs) = partition ( \ a -> case a of 
			       Subsorts _ _ -> False
			       _ -> True) allts
	       sbs = concatMap ( \ (Subsorts ss _) -> ss) subs
	       comps = map (getConsType s) alts
	       ttrips = map (( \ (a, vs, t, ses) -> (a, vs, t, catSels ses))
			       . selForms1 "X" ) comps 
	       sels = concatMap ( \ (_, _, _, ses) -> ses) ttrips
	   addSentences $ map makeInjective 
			    $ filter ( \ (_, _, ces) -> not $ null ces) 
			      comps
	   addSentences $ concatMap ( \ as -> map (makeDisjToSort as) sbs)
			comps 
	   addSentences $ makeDisjoint comps 
	   addSentences $ catMaybes $ concatMap 
			     ( \ ses -> 
			       map (makeUndefForm ses) ttrips) sels
	 _ -> return ()
       return cs

makeDisjToSort :: (Id, OpType, [COMPONENTS]) -> SORT -> Named FORMULA
makeDisjToSort a s = 
    let (c, v, t, _) = selForms1 "X" a 
	p = [posOfId s] in
	NamedSen ("ga_disjoint_" ++ showId c "_sort_" ++ showId s "") $
	mkForall v (Negation (Membership t s p) p) p

makeInjective :: (Id, OpType, [COMPONENTS]) -> Named FORMULA
makeInjective a = 
    let (c, v1, t1, _) = selForms1 "X" a
	(_, v2, t2, _) = selForms1 "Y" a
	p = [posOfId c]
    in NamedSen ("ga_injective_" ++ showId c "") $
       mkForall (v1 ++ v2) 
       (Equivalence (Strong_equation t1 t2 p)
	(let ces = zipWith ( \ w1 w2 -> Strong_equation 
			     (toQualVar w1) (toQualVar w2) p) v1 v2
	 in if isSingle ces then head ces else Conjunction ces p)
	p) p

makeDisjoint :: [(Id, OpType, [COMPONENTS])] -> [Named FORMULA]
makeDisjoint [] = []
makeDisjoint (a:as) = map (makeDisj a) as ++ makeDisjoint as
makeDisj :: (Id, OpType, [COMPONENTS]) -> (Id, OpType, [COMPONENTS])
	    -> Named FORMULA
makeDisj a1 a2 = 
    let (c1, v1, t1, _) = selForms1 "X" a1
	(c2, v2, t2, _) = selForms1 "Y" a2
	p = [posOfId c1, posOfId c2]
    in NamedSen ("ga_disjoint_" ++ showId c1 "_" ++ showId c2 "") $
       mkForall (v1 ++ v2) 
       (Negation (Strong_equation t1 t2 p) p) p

catSels :: [(Maybe Id, OpType)] -> [(Id, OpType)]
catSels =  map ( \ (m, t) -> (fromJust m, t)) . 
		 filter ( \ (m, _) -> isJust m)

makeUndefForm :: (Id, OpType) -> (Id, [VAR_DECL], TERM, [(Id, OpType)])
	      -> Maybe (Named FORMULA)
makeUndefForm (s, ty) (i, vs, t, sels) = 
    let p = [posOfId s] in
    if any ( \ (se, ts) -> s == se && opRes ts == opRes ty ) sels
    then Nothing else
       Just $ NamedSen ("ga_selector_undef_" ++ showId s "_" 
			++ showId i "") $
              mkForall vs 
	      (Negation 
	       (Definedness
		(Application (Qual_op_name s (toOP_TYPE ty) p) [t] p)
		p) p) p

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

genSelVars :: String -> Int -> [(Maybe Id, OpType)] -> [VAR_DECL]
genSelVars _ _ [] = []
genSelVars str n ((_, ty):rs)  = 
    Var_decl [mkSelVar str n] (opRes ty) [] : genSelVars str (n+1) rs

mkSelVar :: String -> Int -> Token
mkSelVar str n = mkSimpleId (str ++ show n)

makeSelForms :: Int -> (Id, [VAR_DECL], TERM, [(Maybe Id, OpType)])
	     -> [Named FORMULA]
makeSelForms _ (_, _, _, []) = []
makeSelForms n (i, vs, t, (mi, ty):rs) =
    (case mi of 
	    Nothing -> []
	    Just j -> let p = [posOfId j] 
                          rty = opRes ty
                          q = [posOfId rty] in 
              [NamedSen ("ga_selector_" ++ showId j "")
	             $ mkForall vs 
		      (Strong_equation 
		       (Application (Qual_op_name j (toOP_TYPE ty) p) [t] p)
		       (Qual_var (mkSelVar "X" n) rty q) p) p]
    )  ++ makeSelForms (n+1) (i, vs, t, rs)

selForms1 :: String -> (Id, OpType, [COMPONENTS]) 
	  -> (Id, [VAR_DECL], TERM, [(Maybe Id, OpType)])
selForms1 str (i, ty, il) =
    let cs = concatMap (getCompType $ opRes ty) il
	vs = genSelVars str 1 cs 
    in (i, vs, Application (Qual_op_name i (toOP_TYPE ty) [])
	    (map toQualVar vs) [], cs)

toQualVar :: VAR_DECL -> TERM
toQualVar (Var_decl v s ps) = 
    if isSingle v then Qual_var (head v) s ps else error "toQualVar"

selForms :: (Id, OpType, [COMPONENTS]) -> [Named FORMULA]
selForms = makeSelForms 1 . selForms1 "X"
 
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
	ds = reverse $ envDiags accSig
	sents = reverse $ sentences accSig
	cleanSig = accSig { envDiags = [], sentences = [], varMap = Map.empty }
	diff = diffSig cleanSig inSig
	remPartOpsS s = s { opMap = remPartOpsM $ opMap s }
    --checked_sents <- return sents
    checked_sents <- overloadResolution accSig sents
    Result ds (Just ()) -- insert diags
    return ( newBs
	   , remPartOpsS diff
	   , remPartOpsS cleanSig
	   , reverse checked_sents ) 

