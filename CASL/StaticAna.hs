
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

{- todo: correct implementation of variables
         (shadowing instead of overloading)
-}

module CASL.StaticAna where

import CASL.AS_Basic_CASL
import CASL.Sign
import CASL.MixfixParser
import CASL.Overload
import CASL.Inject
import CASL.Quantification
import CASL.Utils
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

import Control.Exception (assert)

checkPlaces :: [SORT] -> Id -> [Diagnosis]
checkPlaces args i = 
    if let n = placeCount i in n == 0 || n == length args then []
           else [mkDiag Error "wrong number of places" i]

addOp :: OpType -> Id -> State (Sign f e) ()
addOp ty i = 
    do checkSorts (opRes ty : opArgs ty)
       e <- get
       let m = opMap e
           l = Map.findWithDefault Set.empty i m
           check = addDiags $ checkPlaces (opArgs ty) i
           store = do put e { opMap = addOpTo i ty m }
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

addAssocOp :: OpType -> Id -> State (Sign f e) ()
addAssocOp ty i = do
       e <- get
       put e { assocOps = addOpTo i ty $ assocOps e }

updateExtInfo :: (e -> Result e) -> State (Sign f e) ()
updateExtInfo upd = do
    s <- get
    let re = upd $ extendedInfo s
    case maybeResult re of
         Nothing -> return ()
         Just e -> put s { extendedInfo = e }
    addDiags $ diags re

addOpTo :: Id -> OpType -> OpMap -> OpMap 
addOpTo k v m = 
    let l = Map.findWithDefault Set.empty k m
        n = Map.insert k (Set.insert v l) m   
    in case opKind v of
     Total -> let vp =  v { opKind = Partial } in 
              if Set.member vp l then
              Map.insert k (Set.insert v $ Set.delete vp l) m
              else n
     _ -> if Set.member v { opKind = Total } l then m
          else n

addPred :: PredType -> Id -> State (Sign f e) ()
addPred ty i = 
    do checkSorts $ predArgs ty
       e <- get
       let m = predMap e
           l = Map.findWithDefault Set.empty i m
       if Set.member ty l then 
          addDiags [mkDiag Hint "redeclared pred" i] 
          else do put e { predMap = Map.setInsert i ty m }
                  addDiags $ checkPlaces (predArgs ty) i

allOpIds :: Sign f e -> Set.Set Id
allOpIds = Set.fromDistinctAscList . Map.keys . opMap

addAssocs :: GlobalAnnos -> Sign f e -> GlobalAnnos
addAssocs ga e =
    ga { assoc_annos =  
                foldr ( \ i m -> case Map.lookup i m of
                        Nothing -> Map.insert i ALeft m
                        _ -> m ) (assoc_annos ga) (Map.keys $ assocOps e) } 

formulaIds :: Sign f e -> Set.Set Id
formulaIds e = let ops = allOpIds e in
    Set.fromDistinctAscList (map simpleIdToId $ Map.keys $ varMap e) 
               `Set.union` ops

allPredIds :: Sign f e -> Set.Set Id
allPredIds = Set.fromDistinctAscList . Map.keys . predMap

addSentences :: [Named (FORMULA f)] -> State (Sign f e) ()
addSentences ds = 
    do e <- get
       put e { sentences = reverse ds ++ sentences e }

-- * traversing all data types of the abstract syntax

ana_BASIC_SPEC :: Resolver f => Min f e 
               -> Ana b f e -> Ana s f e -> GlobalAnnos
               -> BASIC_SPEC b s f -> State (Sign f e) (BASIC_SPEC b s f)
ana_BASIC_SPEC mef ab as ga (Basic_spec al) = fmap Basic_spec $
      mapAnM (ana_BASIC_ITEMS mef ab as ga) al

-- looseness of a datatype
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord)

mkForall :: [VAR_DECL] -> FORMULA f -> [Pos] -> FORMULA f
mkForall vl f ps = if null vl then f else 
                   Quantification Universal vl f ps

ana_BASIC_ITEMS :: Resolver f => Min f e  
                -> Ana b f e -> Ana s f e -> GlobalAnnos 
                -> BASIC_ITEMS b s f -> State (Sign f e) (BASIC_ITEMS b s f)
ana_BASIC_ITEMS mef ab as ga bi = 
    case bi of 
    Sig_items sis -> fmap Sig_items $ 
                     ana_SIG_ITEMS mef as ga Loose sis 
    Free_datatype al ps -> 
        do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_DATATYPE_DECL Free) al 
           toSortGenAx ps True $ getDataGenSig al
           closeSubsortRel 
           return bi
    Sort_gen al ps ->
        do (gs,ul) <- ana_Generated mef as ga al
           toSortGenAx ps False 
                (Set.unions $ map fst gs, Set.unions $ map snd gs)
           return $ Sort_gen ul ps
    Var_items il _ -> 
        do mapM_ addVars il
           return bi
    Local_var_axioms il afs ps -> 
        do e <- get -- save
           mapM_ addVars il
           vds <- gets envDiags
           sign <- get
           put e { envDiags = vds } -- restore with shadowing warnings 
           let preds = allPredIds sign
               ops = formulaIds sign
               newGa = addAssocs ga sign
               (es, resFs, anaFs) = foldr ( \ f (dss, ress, anas) -> 
                      let Result ds m = anaForm mef newGa ops preds sign 
                                        $ item f
                      in case m of
                         Nothing -> (ds ++ dss, ress, anas)
                         Just (resF, anaF) -> 
                             (ds ++ dss, f {item = resF} : ress, 
                                 f {item = anaF} : anas))
                     ([], [], []) afs
               fufs = map (mapAn (\ f -> let 
                                 vs = map ( \ (v, s) -> 
                                            Var_decl [v] s ps)
                                      $ Set.toList $ freeVars f 
                                 in stripQuant $ mkForall (vs ++ il) f ps)) 
                      anaFs 
               sens = map ( \ a -> NamedSen (getRLabel a) $ item a) fufs
           addDiags es
           addSentences sens                        
           return $ Local_var_axioms il resFs ps
    Axiom_items afs ps ->                   
        do sign <- get
           ops <- gets formulaIds
           preds <- gets allPredIds
           newGa <- gets $ addAssocs ga
           let (es, resFs, anaFs) = foldr ( \ f (dss, ress, anas) -> 
                      let Result ds m = anaForm mef newGa ops preds sign 
                                        $ item f
                      in case m of
                         Nothing -> (ds ++ dss, ress, anas)
                         Just (resF, anaF) -> 
                             (ds ++ dss, f {item = resF} : ress, 
                                 f {item = anaF} : anas))
                     ([], [], []) afs
               fufs = map (mapAn (\ f -> let
                                 vs = map ( \ (v, s) -> 
                                            Var_decl [v] s ps)
                                      $ Set.toList $ freeVars f 
                                 in stripQuant $ mkForall vs f ps)) anaFs
               sens = map ( \ a -> NamedSen (getRLabel a) $ item a) fufs
           addDiags es
           addSentences sens                        
           return $ Axiom_items resFs ps
    Ext_BASIC_ITEMS b -> fmap Ext_BASIC_ITEMS $ ab ga b

mapAn :: (a -> b) -> Annoted a -> Annoted b
mapAn f an = replaceAnnoted (f $ item an) an

toSortGenAx :: [Pos] -> Bool ->
               (Set.Set Id, Set.Set Component) -> State (Sign f e) ()
toSortGenAx ps isFree (sorts, ops) = do
    let sortList = Set.toList sorts
        opSyms = map ( \ c ->  Qual_op_name (compId c)  
                      (toOP_TYPE $ compType c) []) $ Set.toList ops
        resType _ (Op_name _) = False
        resType s (Qual_op_name _ t _) = res_OP_TYPE t ==s
        getIndex s = maybe (-1) id $ findIndex (==s) sortList
        addIndices (Op_name _) = 
          error "CASL/StaticAna: Internal error in function addIndices"
        addIndices os@(Qual_op_name _ t _) = 
            (os,map getIndex $ args_OP_TYPE t)
        collectOps s = 
          Constraint s (map addIndices $ filter (resType s) opSyms) s
        constrs = map collectOps sortList
        f =  Sort_gen_ax constrs isFree
    if null sortList then 
       addDiags[Diag Error "missing generated sort" (headPos ps)]
       else return ()
    addSentences [NamedSen ("ga_generated_" ++ 
                         showSepList (showString "_") showId sortList "") f]

ana_SIG_ITEMS :: Resolver f => Min f e  
                -> Ana s f e -> GlobalAnnos -> GenKind 
                -> SIG_ITEMS s f -> State (Sign f e) (SIG_ITEMS s f)
ana_SIG_ITEMS mef as ga gk si = 
    case si of 
    Sort_items al ps -> 
        do ul <- mapM (ana_SORT_ITEM mef ga) al 
           closeSubsortRel
           return $ Sort_items ul ps
    Op_items al ps -> 
        do ul <- mapM (ana_OP_ITEM mef ga) al 
           return $ Op_items ul ps
    Pred_items al ps -> 
        do ul <- mapM (ana_PRED_ITEM mef ga) al 
           return $ Pred_items ul ps
    Datatype_items al _ -> 
        do let sorts = map (( \ (Datatype_decl s _ _) -> s) . item) al
           mapM_ addSort sorts
           mapAnM (ana_DATATYPE_DECL gk) al 
           closeSubsortRel
           return si
    Ext_SIG_ITEMS s -> fmap Ext_SIG_ITEMS $ as ga s

-- helper
ana_Generated :: Resolver f => Min f e 
              -> Ana s f e -> GlobalAnnos -> [Annoted (SIG_ITEMS s f)]     
              -> State (Sign f e) 
                 ([(Set.Set Id, Set.Set Component)],[Annoted (SIG_ITEMS s f)])
ana_Generated mef as ga  al = do
   ul <- mapAnM (ana_SIG_ITEMS mef as ga Generated) al
   return (map (getGenSig . item) ul, ul)
   
getGenSig :: SIG_ITEMS s f -> (Set.Set Id, Set.Set Component)
getGenSig si = case si of 
      Sort_items al _ -> (Set.unions (map (getSorts . item) al), Set.empty)
      Op_items al _ -> (Set.empty, Set.unions (map (getOps . item) al))
      Datatype_items dl _ -> getDataGenSig dl
      _ -> (Set.empty, Set.empty)

getDataGenSig :: [Annoted DATATYPE_DECL] -> (Set.Set Id, Set.Set Component)
getDataGenSig dl = 
    let alts = map (( \ (Datatype_decl s al _) -> (s, al)) . item) dl
        sorts = map fst alts
        mkComponent (i, ty, _) = Component i ty
        cs = concatMap ( \ (s, al) -> concatMap (( \ a -> 
              map mkComponent (getConsType s a)))
                       $ map item al) alts
        in (Set.fromList sorts, Set.fromList cs)

getSorts :: SORT_ITEM f -> Set.Set Id
getSorts si = 
    case si of 
    Sort_decl il _ -> Set.fromList il
    Subsort_decl il i _ -> Set.fromList (i:il)
    Subsort_defn sub _ _ _ _ -> Set.single sub
    Iso_decl il _ -> Set.fromList il

getOps :: OP_ITEM f -> Set.Set Component
getOps oi = case oi of 
    Op_decl is ty _ _ -> 
        Set.fromList $ map ( \ i -> Component i $ toOpType ty) is
    Op_defn i par _ _ -> Set.single $ Component i $ toOpType $ headToType par

ana_SORT_ITEM :: Resolver f => Min f e 
              -> GlobalAnnos -> Annoted (SORT_ITEM  f) 
              -> State (Sign f e) (Annoted (SORT_ITEM f))
ana_SORT_ITEM mef ga asi =
    case item asi of 
    Sort_decl il _ ->
        do mapM_ addSort il
           return asi
    Subsort_decl il i _ -> 
        do mapM_ addSort (i:il)
           mapM_ (addSubsort i) il
           return asi
    Subsort_defn sub v super af ps -> 
        do e <- get -- save
           put e { varMap = Map.empty }
           addVars (Var_decl [v] super ps) 
           sign <- get
           ops <- gets formulaIds 
           preds <- gets allPredIds
           newGa <- gets $ addAssocs ga
           put e -- restore 
           let Result ds mf = anaForm mef newGa ops preds sign $ item af
               lb = getRLabel af
               lab = if null lb then getRLabel asi else lb
           addDiags ds 
           addSort sub
           addSubsort super sub
           case mf of 
             Nothing -> return asi { item = Subsort_decl [sub] super ps}
             Just (resF, anaF) -> do 
               let p = [posOfId sub]
                   pv = [tokPos v]
               addSentences[NamedSen lab $
                             mkForall [Var_decl [v] super pv] 
                             (Equivalence 
                              (Membership (Qual_var v super pv) sub p)
                              anaF p) p]
               return asi { item = Subsort_defn sub v super 
                                   af { item = resF } ps}
    Iso_decl il _ ->
        do mapM_ addSort il
           mapM_ ( \ i -> mapM_ (addSubsort i) il) il
           return asi

ana_OP_ITEM :: Resolver f => Min f e -> GlobalAnnos -> Annoted (OP_ITEM f) 
            -> State (Sign f e) (Annoted (OP_ITEM f))
ana_OP_ITEM mef ga aoi = 
    case item aoi of 
    Op_decl ops ty il ps -> 
        do let oty = toOpType ty
           mapM_ (addOp oty) ops
           ul <- mapM (ana_OP_ATTR mef ga oty ops) il
           if null $ filter ( \ i -> case i of 
                                   Assoc_op_attr -> True
                                   _ -> False) il 
              then return ()
              else mapM_ (addAssocOp oty) ops
           return aoi {item = Op_decl ops ty (catMaybes ul) ps}
    Op_defn i ohd at ps -> 
        do let ty = headToType ohd
               lb = getRLabel at
               lab = if null lb then getRLabel aoi else lb
               args = case ohd of 
                      Op_head _ as _ _ -> as
               vs = map (\ (Arg_decl v s qs) -> (Var_decl v s qs)) args
               arg = concatMap ( \ (Var_decl v s qs) ->
                                 map ( \ j -> Qual_var j s qs) v) vs
           addOp (toOpType ty) i
           e <- get -- save
           put e { varMap = Map.empty }
           mapM_ addVars vs
           sign <- get
           ops <- gets formulaIds
           preds <- gets allPredIds 
           newGa <- gets $ addAssocs ga
           put e -- restore
           let Result ds mt = anaTerm mef newGa ops preds sign 
                              (res_OP_TYPE ty) ps $ item at
           addDiags ds
           case mt of 
             Nothing -> return aoi { item = Op_decl [i] ty [] ps }
             Just (resT, anaT) -> do 
                 let p = [posOfId i]
                 addSentences [NamedSen lab $ mkForall vs 
                     (Strong_equation 
                      (Application (Qual_op_name i ty p) arg ps)
                      anaT p) ps]
                 return aoi {item = Op_defn i ohd at { item = resT } ps }

headToType :: OP_HEAD -> OP_TYPE
headToType (Op_head k args r ps) = Op_type k (sortsOfArgs args) r ps

sortsOfArgs :: [ARG_DECL] -> [SORT]
sortsOfArgs = concatMap ( \ (Arg_decl l s _) -> map (const s) l)

ana_OP_ATTR :: Resolver f => Min f e -> GlobalAnnos 
            -> OpType -> [Id] -> (OP_ATTR f)
            -> State (Sign f e) (Maybe (OP_ATTR f))
ana_OP_ATTR mef ga ty ois oa = 
    let sty = toOP_TYPE ty
        rty = opRes ty 
        q = [posOfId rty] in
    case oa of 
    Unit_op_attr t ->
        do sign <- get
           ops <- gets allOpIds
           preds <- gets allPredIds 
           newGa <- gets $ addAssocs ga
           let Result ds mt = anaTerm mef newGa ops preds sign rty q t
           addDiags ds
           case mt of 
             Nothing -> return Nothing
             Just (resT, anaT)  -> do 
               addSentences $ map (makeUnit True anaT ty) ois
               addSentences $ map (makeUnit False anaT ty) ois
               return $ Just $ Unit_op_attr resT
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

makeUnit :: Bool -> TERM f -> OpType -> Id -> Named (FORMULA f)
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

ana_PRED_ITEM :: Resolver f => Min f e 
              -> GlobalAnnos -> Annoted (PRED_ITEM f)
              -> State (Sign f e) (Annoted (PRED_ITEM f))
ana_PRED_ITEM mef ga ap = 
    case item ap of 
    Pred_decl preds ty _ -> 
        do mapM (addPred $ toPredType ty) preds
           return ap
    Pred_defn i phd@(Pred_head args rs) at ps ->
        do let lb = getRLabel at
               lab = if null lb then getRLabel ap else lb
               ty = Pred_type (sortsOfArgs args) rs
               vs = map (\ (Arg_decl v s qs) -> (Var_decl v s qs)) args
               arg = concatMap ( \ (Var_decl v s qs) ->
                                 map ( \ j -> Qual_var j s qs) v) vs
           addPred (toPredType ty) i
           e <- get -- save
           put e { varMap = Map.empty }
           mapM_ addVars vs          
           sign <- get
           ops <- gets formulaIds
           preds <- gets allPredIds 
           newGa <- gets $ addAssocs ga
           put e -- restore
           let Result ds mt = anaForm mef newGa ops preds sign $ item at
           addDiags ds
           case mt of 
             Nothing -> return ap {item = Pred_decl [i] ty ps}
             Just (resF, anaF) -> do 
               let p = [posOfId i]
               addSentences [NamedSen lab $
                             mkForall vs 
                             (Equivalence (Predication (Qual_pred_name i ty p)
                                           arg p) anaF p) p]
               return ap {item = Pred_defn i phd at { item = resF } ps}

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
ana_DATATYPE_DECL :: GenKind -> DATATYPE_DECL -> State (Sign f e) [Component]
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
                       "'\n  must appear in alternative") c) wrongConstr
       case gk of 
         Free -> do 
           let allts = map item al
               (alts, subs) = partition ( \ a -> case a of 
                               Subsorts _ _ -> False
                               _ -> True) allts
               sbs = concatMap ( \ (Subsorts ss _) -> ss) subs
               comps = concatMap (getConsType s) alts
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

makeDisjToSort :: (Id, OpType, [COMPONENTS]) -> SORT -> Named (FORMULA f)
makeDisjToSort a s = 
    let (c, v, t, _) = selForms1 "X" a 
        p = [posOfId s] in
        NamedSen ("ga_disjoint_" ++ showId c "_sort_" ++ showId s "") $
        mkForall v (Negation (Membership t s p) p) p

makeInjective :: (Id, OpType, [COMPONENTS]) -> Named (FORMULA f)
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

makeDisjoint :: [(Id, OpType, [COMPONENTS])] -> [Named (FORMULA f)]
makeDisjoint [] = []
makeDisjoint (a:as) = map (makeDisj a) as ++ makeDisjoint as
makeDisj :: (Id, OpType, [COMPONENTS]) 
                           -> (Id, OpType, [COMPONENTS])
                           -> Named (FORMULA f)
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

makeUndefForm :: (Id, OpType) -> (Id, [VAR_DECL], TERM f, [(Id, OpType)])
              -> Maybe (Named (FORMULA f))
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

getConsType :: SORT -> ALTERNATIVE -> [(Id, OpType, [COMPONENTS])]
getConsType s c = 
    let getConsTypeAux (part, i, il) = 
          (i, OpType part (concatMap 
                            (map (opRes . snd) . getCompType s) il) s, il)
     in case c of 
        Subsorts srts _ ->  
             [(injName, OpType Total [s1] s,[Sort s1]) | s1<-srts]
        Alt_construct k a l _ -> [getConsTypeAux (k, a, l)]

getCompType :: SORT -> COMPONENTS -> [(Maybe Id, OpType)]
getCompType s (Cons_select k l cs _) = 
    map (\ i -> (Just i, OpType k [s] cs)) l
getCompType s (Sort cs) = [(Nothing, OpType Partial [s] cs)]

genSelVars :: String -> Int -> [(Maybe Id, OpType)] -> [VAR_DECL]
genSelVars _ _ [] = []
genSelVars str n ((_, ty):rs)  = 
    Var_decl [mkSelVar str n] (opRes ty) [] : genSelVars str (n+1) rs

mkSelVar :: String -> Int -> Token
mkSelVar str n = mkSimpleId (str ++ show n)

makeSelForms :: Int -> (Id, [VAR_DECL], TERM f, [(Maybe Id, OpType)])
             -> [Named (FORMULA f)]
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
          -> (Id, [VAR_DECL], TERM f, [(Maybe Id, OpType)])
selForms1 str (i, ty, il) =
    let cs = concatMap (getCompType $ opRes ty) il
        vs = genSelVars str 1 cs 
    in (i, vs, Application (Qual_op_name i (toOP_TYPE ty) [])
            (map toQualVar vs) [], cs)

toQualVar :: VAR_DECL -> TERM f
toQualVar (Var_decl v s ps) = 
    if isSingle v then Qual_var (head v) s ps else error "toQualVar"

selForms :: (Id, OpType, [COMPONENTS]) -> [Named (FORMULA f)]
selForms = makeSelForms 1 . selForms1 "X"
 
-- | return the constructor and the set of total selectors 
ana_ALTERNATIVE :: SORT -> ALTERNATIVE 
                -> State (Sign f e) (Maybe (Component, Set.Set Component))
ana_ALTERNATIVE s c = 
    case c of 
    Subsorts ss _ ->
        do mapM_ (addSubsort s) ss
           return Nothing
    _ -> do let [cons@(i, ty, il)] = getConsType s c
            addOp ty i
            ul <- mapM (ana_COMPONENTS s) il
            let ts = concatMap fst ul
            addDiags $ checkUniqueness (ts ++ concatMap snd ul)
            addSentences $ selForms cons
            return $ Just (Component i ty, Set.fromList ts) 

 
-- | return total and partial selectors
ana_COMPONENTS :: SORT -> COMPONENTS 
               -> State (Sign f e) ([Component], [Component])
ana_COMPONENTS s c = do
    let cs = getCompType s c
    sels <- mapM ( \ (mi, ty) -> 
            case mi of 
            Nothing -> return Nothing
            Just i -> do addOp ty i
                         return $ Just $ Component i ty) cs 
    return $ partition ((==Total) . opKind . compType) $ catMaybes sels 

-- | utility
resultToState :: (a -> Result a) -> a -> State (Sign f e) a
resultToState f a = do 
    let r =  f a 
    addDiags $ diags r
    case maybeResult r of
        Nothing -> return a
        Just b -> return b

-- wrap it all up for a logic

type Ana b f e = GlobalAnnos -> b -> State (Sign f e) b

class PrettyPrint f => Resolver f where
   putParen :: f -> f -- ^ put parenthesis around mixfix terms
   mixResolve :: MixResolve f -- ^ resolve mixfix terms 
   checkMix :: (f -> Bool) -- ^ check if a formula extension has been 
                             -- analysed completely by mixfix resolution
   putInj :: f -> f -- ^ insert injections 

anaForm :: Resolver f => Min f e -> GlobalAnnos -> Set.Set Id -> Set.Set Id 
        -> Sign f e -> (FORMULA f) -> Result (FORMULA f, FORMULA f)
anaForm mef ga ops preds sign f = do 
    resF <- resolveFormula putParen mixResolve ga ops preds f
    anaF <- minExpFORMULA mef ga sign 
         $ assert (noMixfixF checkMix resF) resF
    return (resF, injFormula putInj anaF)

anaTerm :: Resolver f => Min f e -> GlobalAnnos -> Set.Set Id -> Set.Set Id 
        -> Sign f e -> SORT -> [Pos] -> (TERM f) -> Result (TERM f, TERM f)
anaTerm mef ga ops preds sign srt pos t = do 
    resT <- resolveMixfix putParen mixResolve ga ops preds t
    anaT <- oneExpTerm mef ga sign 
         $ assert (noMixfixT checkMix resT) $ Sorted_term resT srt pos
    return (resT, injTerm putInj anaT)

basicAnalysis :: Resolver f
              => Min f e -- ^ type analysis of f
              -> Ana b f e  -- ^ static analysis of basic item b
              -> Ana s f e  -- ^ static analysis of signature item s  
              -> (e -> e -> e) -- ^ difference of signature extension e
              -> (BASIC_SPEC b s f, Sign f e, GlobalAnnos)
         -> Result (BASIC_SPEC b s f, Sign f e, Sign f e, [Named (FORMULA f)])
basicAnalysis mef anab anas dif (bs, inSig, ga) = 
    let (newBs, accSig) = runState (ana_BASIC_SPEC mef anab anas ga bs) 
                          inSig
        ds = reverse $ envDiags accSig
        sents = reverse $ sentences accSig
        cleanSig = accSig { envDiags = [], sentences = [], varMap = Map.empty }
        diff = diffSig cleanSig inSig 
            { extendedInfo = dif (extendedInfo accSig) $ extendedInfo inSig }
    in Result ds $ Just (newBs, diff, cleanSig, sents) 

basicCASLAnalysis :: (BASIC_SPEC () () (), Sign () (), GlobalAnnos)
                  -> Result (BASIC_SPEC () () (), Sign () (), 
                             Sign () (), [Named (FORMULA ())])
basicCASLAnalysis = 
    basicAnalysis (const $ const return) (const return) (const return) const

instance Resolver () where
    putParen = id
    mixResolve = const $ const return
    checkMix = const True
    putInj = id
