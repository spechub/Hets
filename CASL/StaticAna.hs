{- |
Module      :  ./CASL/StaticAna.hs
Description :  CASL static analysis for basic specifications
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL static analysis for basic specifications

Follows Chaps. III:2 and III:3 of the CASL Reference Manual.

The static analysis takes an abstract syntax tree of a basic specification
and outputs a signature and a set of formulas, while checking that
- all sorts used in operation and predicate declarations have been declared
- all sorts, operation and predicate symbols used in formulas have
  been declared
- formulas type-check
The formulas are returned with fully-qualified variables, operation
and predicate symbols.

The static analysis functions are parameterized with functions for
treating CASL extensions, that is, additional basic items, signature
items and formulas.
-}

module CASL.StaticAna where

import CASL.AS_Basic_CASL
import CASL.MixfixParser
import CASL.Overload
import CASL.Quantification
import CASL.Sign
import CASL.ToDoc

import Common.AS_Annotation
import Common.Doc
import Common.DocUtils
import Common.ExtSign
import Common.GlobalAnnotations
import Common.Id
import Common.Keywords
import Common.Lib.State
import Common.Result
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import Control.Monad

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List

import Logic.SemConstr

import Debug.Trace

checkPlaces :: [SORT] -> Id -> [Diagnosis]
checkPlaces args i = let n = placeCount i in
    [mkDiag Error "wrong number of places" i | n > 0 && n /= length args ]

checkWithVars :: String -> Map.Map SIMPLE_ID a -> Id -> [Diagnosis]
checkWithVars s m i@(Id ts _ _) = if isSimpleId i then
    case Map.lookup (head ts) m of
    Nothing -> []
    Just _ -> alsoWarning s varS i
    else []

addOp :: Annoted a -> OpType -> Id -> State (Sign f e) ()
addOp a ty i =
    do checkSorts (opRes ty : opArgs ty)
       e <- get
       let m = opMap e
           l = MapSet.lookup i m
           ds = checkWithOtherMap opS predS (predMap e) i
                ++ checkWithVars opS (varMap e) i
           check = addDiags $
                   (if Set.member ty l then [mkDiag Hint "redeclared op" i]
                    else checkPlaces (opArgs ty) i ++ checkNamePrefix i)
                   ++ ds
           store = put e { opMap = addOpTo i ty m }
           pTy = mkPartial ty
       case opKind ty of
          Partial -> if Set.member (mkTotal ty) l then
                     addDiags $ mkDiag Warning "partially redeclared" i : ds
                     else store >> check
          Total -> if Set.member pTy l then do
                         put e { opMap = MapSet.insert i ty
                                   $ MapSet.delete i pTy m }
                         addDiags $ mkDiag Hint "redeclared as total" i : ds
                   else store >> check
       addAnnoSet a $ Symbol i $ OpAsItemType ty

addAssocOp :: OpType -> Id -> State (Sign f e) ()
addAssocOp ty i = do
       e <- get
       put e { assocOps = addOpTo i ty $ assocOps e
             , globAnnos = updAssocMap (addAssocId i) $ globAnnos e
             }

updateExtInfo :: (e -> Result e) -> State (Sign f e) ()
updateExtInfo upd = do
    s <- get
    let re = upd $ extendedInfo s
    case maybeResult re of
         Nothing -> return ()
         Just e -> put s { extendedInfo = e }
    addDiags $ diags re

addPred :: Annoted a -> PredType -> Id -> State (Sign f e) ()
addPred a ty i =
    do checkSorts $ predArgs ty
       e <- get
       let m = predMap e
           l = MapSet.lookup i m
           ds = checkWithOtherMap predS opS (opMap e) i
                ++ checkWithVars predS (varMap e) i
       if Set.member ty l then
          addDiags $ mkDiag Hint "redeclared pred" i : ds
          else do
            put e { predMap = MapSet.insert i ty m }
            addDiags $ checkPlaces (predArgs ty) i ++ checkNamePrefix i ++ ds
       addAnnoSet a $ Symbol i $ PredAsItemType ty

nonConsts :: OpMap -> Set.Set Id
nonConsts = MapSet.keysSet . MapSet.filter (not . null . opArgs)

opMapConsts :: OpMap -> Set.Set Id
opMapConsts = MapSet.keysSet . MapSet.filter (null . opArgs)

allOpIds :: Sign f e -> Set.Set Id
allOpIds = nonConsts . opMap

allConstIds :: Sign f e -> Set.Set Id
allConstIds = opMapConsts . opMap

addAssocs :: Sign f e -> GlobalAnnos -> GlobalAnnos
addAssocs e =
  updAssocMap (\ m -> Set.fold addAssocId m $ MapSet.keysSet $ assocOps e)

updAssocMap :: (AssocMap -> AssocMap) -> GlobalAnnos -> GlobalAnnos
updAssocMap f ga = ga { assoc_annos = f $ assoc_annos ga }

addAssocId :: Id -> AssocMap -> AssocMap
addAssocId i m = case Map.lookup i m of
                   Nothing -> Map.insert i ALeft m
                   _ -> m

formulaIds :: Sign f e -> Set.Set Id
formulaIds e = let ops = allOpIds e in
    Set.fromDistinctAscList (map simpleIdToId $ Map.keys $ varMap e)
               `Set.union` ops

allPredIds :: Sign f e -> Set.Set Id
allPredIds = MapSet.keysSet . predMap

addSentences :: [Named (FORMULA f)] -> State (Sign f e) ()
addSentences ds =
    do e <- get
       put e { sentences = reverse ds ++ sentences e }

-- * traversing all data types of the abstract syntax

ana_BASIC_SPEC :: (FormExtension f, TermExtension f) => Min f e
               -> Ana b b s f e -> Ana s b s f e -> Mix b s f e
               -> BASIC_SPEC b s f -> State (Sign f e) (BASIC_SPEC b s f)
ana_BASIC_SPEC mef ab anas mix (Basic_spec al) = fmap Basic_spec $
      mapAnM (ana_BASIC_ITEMS mef ab anas mix) al

-- looseness of a datatype
data GenKind = Free | Generated | Loose deriving (Show, Eq, Ord)

unionGenAx :: [GenAx] -> GenAx
unionGenAx = foldr (\ (s1, r1, f1) (s2, r2, f2) ->
                        (Set.union s1 s2,
                         Rel.union r1 r2,
                         Set.union f1 f2)) emptyGenAx

anaVarForms :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> [VAR_DECL] -> [Annoted (FORMULA f)] -> Range
  -> State (Sign f e) [Annoted (FORMULA f)]
anaVarForms mef mix vs fs r = do
   (resFs, fufs) <- anaLocalVarForms (anaForm mef mix) vs fs r
   addSentences $ map makeNamedSen fufs
   return resFs

anaLocalVarForms :: TermExtension f
  => (Sign f e -> FORMULA f -> Result (FORMULA f, FORMULA f))
  -> [VAR_DECL] -> [Annoted (FORMULA f)] -> Range
  -> State (Sign f e) ([Annoted (FORMULA f)], [Annoted (FORMULA f)])
anaLocalVarForms anaFrm il afs ps = do
           e <- get -- save
           mapM_ addVars il
           vds <- gets envDiags
           sign <- get
           unless (null il) $ put e { envDiags = vds }
           -- restore with shadowing warnings
           let (es, resFs, anaFs) = foldr (\ f (dss, ress, ranas) ->
                      let Result ds m = anaFrm sign $ item f
                      in case m of
                         Nothing -> (ds ++ dss, ress, ranas)
                         Just (resF, anaF) ->
                             (ds ++ dss, f {item = resF} : ress,
                                 f {item = anaF} : ranas))
                     ([], [], []) afs
               fufs = map (mapAn (\ f -> quantFreeVars sign
                            (mkForallRange il f ps) ps))
                      anaFs
           addDiags es
           return (resFs, fufs)

anaDatatypeDecls :: GenKind -> SortsKind -> [Annoted DATATYPE_DECL]
  -> State (Sign f e) ()
anaDatatypeDecls gk sk al = do
           let ts = map (\ i -> case item i of
                        Datatype_decl s _ _ -> (i, s)) al
           addDiags . map (\ l -> case l of
              _ : t : _ -> mkDiag (if gk == Loose then Warning else Error)
               "duplicate type name in mutually recursive type definition" t
              _ -> error "anaDatatypeDecls")
               . filter ((> 1) . length) . group . sort $ map snd ts
           mapM_ (uncurry $ addSort sk) ts
           mapAnM (ana_DATATYPE_DECL gk) al
           closeSubsortRel

ana_BASIC_ITEMS :: (FormExtension f, TermExtension f)
  => Min f e -> Ana b b s f e -> Ana s b s f e -> Mix b s f e
    -> BASIC_ITEMS b s f -> State (Sign f e) (BASIC_ITEMS b s f)
ana_BASIC_ITEMS mef ab anas mix bi =
    case bi of
    Sig_items sis -> fmap Sig_items $
                     ana_SIG_ITEMS mef anas mix Loose sis
    Free_datatype sk al ps -> do
           anaDatatypeDecls Free sk al
           toSortGenAx ps True $ getDataGenSig al
           return bi
    Sort_gen al ps -> do
           (gs, ul) <- ana_Generated mef anas mix al
           toSortGenAx ps False $ unionGenAx gs
           return $ Sort_gen ul ps
    Var_items il _ -> do
           mapM_ addVars il
           return bi
    Local_var_axioms il afs ps -> do
        resFs <- anaVarForms mef mix il afs ps
        return $ Local_var_axioms il resFs ps
    Axiom_items afs ps -> do
        resFs <- anaVarForms mef mix [] afs ps
        return $ Axiom_items resFs ps
    Ext_BASIC_ITEMS b -> fmap Ext_BASIC_ITEMS $ ab mix b

mapAn :: (a -> b) -> Annoted a -> Annoted b
mapAn f an = replaceAnnoted (f $ item an) an

type GenAx = (Set.Set SORT, Rel.Rel SORT, Set.Set Component)

emptyGenAx :: GenAx
emptyGenAx = (Set.empty, Rel.empty, Set.empty)

toSortGenAx :: Range -> Bool -> GenAx -> State (Sign f e) ()
toSortGenAx ps isFree (sorts, rel, ops) = do
    let sortList = Set.toList sorts
        opSyms = map (\ c -> let ide = compId c in Qual_op_name ide
                      (toOP_TYPE $ compType c) $ posOfId ide) $ Set.toList ops
        injSyms = map (\ (s, t) -> let p = posOfId s in
                        Qual_op_name (mkUniqueInjName s t)
                        (Op_type Total [s] t p) p) $ Rel.toList
                  $ Rel.irreflex rel
        allSyms = opSyms ++ injSyms
        resType (Op_name _) = error "CASL.StaticAna.resType"
        resType (Qual_op_name _ t _) = res_OP_TYPE t
        argTypes (Op_name _) = error "CASL.StaticAna.argTypes"
        argTypes (Qual_op_name _ t _) = args_OP_TYPE t
        getIndex l s = fromMaybe (-1) $ elemIndex s l
        addIndices l os =
            (os, map (getIndex l) $ argTypes os)
        collectOps s = (s, filter ((== s) . resType) allSyms)
        constrs0 = map collectOps sortList
        dRel = Rel.depSort . Rel.transClosure $ foldr (\ (s, os) r ->
               Set.fold (`Rel.insertDiffPair` s) (Rel.insertKey s r)
               $ Set.unions
               $ map (Set.intersection sorts . Set.fromList . argTypes) os)
               Rel.empty constrs0
        m2 = Map.fromList constrs0
        mkConstr ss =
            let sl = Set.toList ss in
            toSortGenNamed
            (mkSort_gen_ax
            (map (\ s -> Constraint s
                   (map (addIndices sl)
                    $ Map.findWithDefault (error "CASL.StaticAna.mkConstr")
                    s m2) s) sl) isFree) sl
        resList = Set.fromList $ map resType allSyms
        noConsList = Set.difference sorts resList
        voidOps = Set.difference resList sorts
        sens = map mkConstr dRel
    when (null sortList)
      $ addDiags [Diag Error "missing generated sort" ps]
    unless (Set.null noConsList)
      $ addDiags [mkDiag Warning "generated sorts without constructor"
          noConsList]
    unless (Set.null voidOps)
      $ addDiags [mkDiag Warning "non-generated sorts as constructor result"
                  voidOps]
    when (length dRel > 1)
      $ addDiags [mkDiag Warning "splittable groups of generated sorts" dRel]
    addSentences sens

ana_SIG_ITEMS :: (FormExtension f, TermExtension f)
  => Min f e -> Ana s b s f e -> Mix b s f e -> GenKind -> SIG_ITEMS s f
    -> State (Sign f e) (SIG_ITEMS s f)
ana_SIG_ITEMS mef anas mix gk si =
    case si of
    Sort_items sk al ps ->
        do ul <- mapM (ana_SORT_ITEM mef mix sk) al
           closeSubsortRel
           return $ Sort_items sk ul ps
    Op_items al ps ->
        do ul <- mapM (ana_OP_ITEM mef mix) al
           return $ Op_items ul ps
    Pred_items al ps ->
        do ul <- mapM (ana_PRED_ITEM mef mix) al
           return $ Pred_items ul ps
    Datatype_items sk al _ ->
        do anaDatatypeDecls gk sk al
           return si
    Ext_SIG_ITEMS s -> fmap Ext_SIG_ITEMS $ anas mix s

-- helper
ana_Generated :: (FormExtension f, TermExtension f)
  => Min f e -> Ana s b s f e -> Mix b s f e -> [Annoted (SIG_ITEMS s f)]
    -> State (Sign f e) ([GenAx], [Annoted (SIG_ITEMS s f)])
ana_Generated mef anas mix al = do
   ul <- mapAnM (ana_SIG_ITEMS mef anas mix Generated) al
   return (map (getGenSig . item) ul, ul)

getGenSig :: SIG_ITEMS s f -> GenAx
getGenSig si = case si of
      Sort_items _ al _ -> unionGenAx $ map (getGenSorts . item) al
      Op_items al _ -> (Set.empty, Rel.empty,
                           Set.unions (map (getOps . item) al))
      Datatype_items _ dl _ -> getDataGenSig dl
      _ -> emptyGenAx

isConsAlt :: ALTERNATIVE -> Bool
isConsAlt a = case a of
  Subsorts _ _ -> False
  _ -> True

getDataGenSig :: [Annoted DATATYPE_DECL] -> GenAx
getDataGenSig dl =
    let alts = concatMap ((\ (Datatype_decl s al _) ->
                          map (\ a -> (s, item a)) al) . item) dl
        sorts = map fst alts
        (realAlts, subs) = partition (isConsAlt . snd) alts
        cs = map (\ (s, a) ->
               let (i, ty, _) = getConsType s a
               in Component i ty) realAlts
        rel = foldr (\ (t, a) r ->
                  foldr (`Rel.insertDiffPair` t)
                  r $ getAltSubsorts a)
               Rel.empty subs
        in (Set.fromList sorts, rel, Set.fromList cs)

getGenSorts :: SORT_ITEM f -> GenAx
getGenSorts si = let
  (sorts, rel) = case si of
    Sort_decl il _ -> (Set.fromList il, Rel.empty)
    Subsort_decl il i _ ->
      (Set.fromList (i : il), foldr (`Rel.insertDiffPair` i) Rel.empty il)
    Subsort_defn sub _ super _ _ ->
      (Set.singleton sub, Rel.insertDiffPair sub super Rel.empty)
    Iso_decl il _ -> (Set.fromList il,
      foldr (\ s r -> foldr (Rel.insertDiffPair s) r il) Rel.empty il)
    in (sorts, rel, Set.empty)

getOps :: OP_ITEM f -> Set.Set Component
getOps oi = case oi of
    Op_decl is ty _ _ ->
        Set.fromList $ map (flip Component $ toOpType ty) is
    Op_defn i par _ _ -> maybe Set.empty
        (Set.singleton . Component i . toOpType) $ headToType par

ana_SORT_ITEM :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> SortsKind -> Annoted (SORT_ITEM f)
    -> State (Sign f e) (Annoted (SORT_ITEM f))
ana_SORT_ITEM mef mix sk asi =
    case item asi of
    Sort_decl il _ ->
        do mapM_ (addSort sk asi) il
           return asi
    Subsort_decl il i _ ->
        do mapM_ (addSort sk asi) (i : il)
           mapM_ (addSubsort i) il
           return asi
    Subsort_defn sub v super af ps ->
        do e <- get -- save
           put e { varMap = Map.empty }
           addVars (Var_decl [v] super ps)
           sign <- get
           put e -- restore
           let Result ds mf = anaForm mef mix sign $ item af
               lb = getRLabel af
               lab = if null lb then getRLabel asi else lb
           addDiags ds
           addSort sk asi sub
           addSubsort super sub
           case mf of
             Nothing -> return asi { item = Subsort_decl [sub] super ps}
             Just (resF, anaF) -> do
               let p = posOfId sub
                   pv = tokPos v
               addSentences [(makeNamed lab $
                              mkForallRange [Var_decl [v] super pv]
                              (Relation
                               (Membership (Qual_var v super pv) sub p)
                               Equivalence anaF p) p) {
                              isAxiom = notImplied af }]
               return asi { item = Subsort_defn sub v super
                                   af { item = resF } ps}
    Iso_decl il _ ->
        do mapM_ (addSort sk asi) il
           case il of
               [] -> return ()
               _ : tl -> mapM_ (uncurry $ addSubsortOrIso False)
                         $ zip tl il
           return asi

putVarsInEmptyMap :: [VAR_DECL] -> State (Sign f e) (Sign f e)
putVarsInEmptyMap vs = do
           e <- get -- save
           put e { varMap = Map.empty }
           mapM_ addVars vs
           sign <- get
           put e -- restore
           return sign

ana_OP_ITEM :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> Annoted (OP_ITEM f)
    -> State (Sign f e) (Annoted (OP_ITEM f))
ana_OP_ITEM mef mix aoi =
    case item aoi of
    Op_decl ops ty il ps ->
        do let oty = toOpType ty
               ni = notImplied aoi
           mapM_ (addOp aoi oty) ops
           ul <- mapM (ana_OP_ATTR mef mix oty ni ops) il
           when (any (\ a -> case a of
                  Assoc_op_attr -> True
                  _ -> False) il) $ do
              mapM_ (addAssocOp oty) ops
              when (any (\ a -> case a of
                  Comm_op_attr -> True
                  _ -> False) il)
                   $ addSentences $ map (addLeftComm oty ni) ops
           return aoi {item = Op_decl ops ty (catMaybes ul) ps}
    Op_defn i ohd@(Op_head k vs _ _) at ps ->
        do let mty = headToType ohd
               lb = getRLabel at
               lab = if null lb then getRLabel aoi else lb
               arg = concatMap (\ (Var_decl v s qs) ->
                                 map (\ j -> Qual_var j s qs) v) vs
           maybe (return ()) (\ ty -> addOp aoi (toOpType ty) i) mty
           sign <- putVarsInEmptyMap vs
           let Result ds mt = anaTerm mef mix sign
                 (fmap res_OP_TYPE mty) ps $ item at
           addDiags ds
           case mt of
             Nothing -> return $ maybe aoi
               (\ ty -> aoi { item = Op_decl [i] ty [] ps }) mty
             Just (resT, anaT) -> do
                 let p = posOfId i
                     tvs = freeTermVars sign anaT
                     ty = headToTypeM (Op_type k (sortsOfArgs vs)
                                       (sortOfTerm anaT) ps) id ohd
                 maybe (addOp aoi (toOpType ty) i) (const $ return ()) mty
                 addDiags $ warnUnusedVars " local " sign tvs
                 addSentences [(makeNamed lab $ mkForallRange vs
                     (Equation
                      (Application (Qual_op_name i ty p) arg ps)
                      Strong anaT p) ps) {
                       isAxiom = notImplied at, isDef = True }]
                 return aoi {item = Op_defn i ohd at { item = resT } ps }

headToTypeM :: a -> (OP_TYPE -> a) -> OP_HEAD -> a
headToTypeM def f (Op_head k args mr ps) = maybe def
  (\ r -> f $ Op_type k (sortsOfArgs args) r ps) mr

headToType :: OP_HEAD -> Maybe OP_TYPE
headToType = headToTypeM Nothing Just

sortsOfArgs :: [VAR_DECL] -> [SORT]
sortsOfArgs = concatMap (\ (Var_decl l s _) -> map (const s) l)

threeVars :: SORT -> ([VAR_DECL], [TERM f])
threeVars rty =
      let q = posOfId rty
          ns = map mkSimpleId ["x", "y", "z"]
          vs = map (\ v -> Var_decl [v] rty q) ns
      in (vs, map toQualVar vs)

-- see Isabelle/doc/ref.pdf 10.6 Permutative rewrite rules (p. 137)
addLeftComm :: OpType -> Bool -> Id -> Named (FORMULA f)
addLeftComm ty ni i =
  let sty = toOP_TYPE ty
      rty = opRes ty
      (vs, [v1, v2, v3]) = threeVars rty
      p = posOfId i
      qi = Qual_op_name i sty p
  in (makeNamed ("ga_left_comm_" ++ showId i "") $
             mkForallRange vs
             (Equation
              (Application qi [v1, Application qi [v2, v3] p] p) Strong
              (Application qi [v2, Application qi [v1, v3] p] p) p) p)
            { isAxiom = ni }

ana_OP_ATTR :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> OpType -> Bool -> [Id] -> OP_ATTR f
    -> State (Sign f e) (Maybe (OP_ATTR f))
ana_OP_ATTR mef mix ty ni ois oa = do
  let sty = toOP_TYPE ty
      rty = opRes ty
      atys = opArgs ty
      q = posOfId rty
      tds = case atys of
         [t1, t2] | t1 == t2 -> case oa of
              Comm_op_attr -> []
              _ -> [ Diag Error "result sort must be equal to argument sorts" q
                   | t1 /= rty ]
         _ -> [Diag Error "expecting two arguments of equal sort" q]
  addDiags tds
  case oa of
    Unit_op_attr t -> do
           sign <- get
           let Result ds mt = anaTerm mef mix
                              sign { varMap = Map.empty } (Just rty) q t
           addDiags ds
           case mt of
             Nothing -> return Nothing
             Just (resT, anaT) -> do
               when (null tds) $ do
                 addSentences $ map (makeUnit True anaT ty ni) ois
                 addSentences $ map (makeUnit False anaT ty ni) ois
               return $ Just $ Unit_op_attr resT
    Assoc_op_attr -> do
      let (vs, [v1, v2, v3]) = threeVars rty
          makeAssoc i = let p = posOfId i
                            qi = Qual_op_name i sty p in
            (makeNamed ("ga_assoc_" ++ showId i "") $
             mkForallRange vs
             (Equation
              (Application qi [Application qi [v1, v2] p, v3] p) Strong
              (Application qi [v1, Application qi [v2, v3] p] p) p) p)
            { isAxiom = ni }
      when (null tds) . addSentences $ map makeAssoc ois
      return $ Just oa
    Comm_op_attr -> do
      let ns = map mkSimpleId ["x", "y"]
          vs = zipWith (\ v t -> Var_decl [v] t
                         $ concatMapRange posOfId atys) ns atys
          args = map toQualVar vs
          makeComm i = let p = posOfId i
                           qi = Qual_op_name i sty p in
            (makeNamed ("ga_comm_" ++ showId i "") $
             mkForallRange vs
             (Equation (Application qi args p) Strong
              (Application qi (reverse args) p) p) p) {
             isAxiom = ni }
      when (null tds) . addSentences $ map makeComm ois
      return $ Just oa
    Idem_op_attr -> do
      let v = mkSimpleId "x"
          vd = Var_decl [v] rty q
          qv = toQualVar vd
          makeIdem i = let p = posOfId i in
           (makeNamed ("ga_idem_" ++ showId i "") $
            mkForallRange [vd]
            (Equation
             (Application (Qual_op_name i sty p) [qv, qv] p)
             Strong qv p) p) { isAxiom = ni }
      when (null tds) . addSentences $ map makeIdem ois
      return $ Just oa

-- first bool for left and right, second one for no implied annotation
makeUnit :: Bool -> TERM f -> OpType -> Bool -> Id -> Named (FORMULA f)
makeUnit b t ty ni i =
    let lab = "ga_" ++ (if b then "right" else "left") ++ "_unit_"
              ++ showId i ""
        v = mkSimpleId "x"
        vty = opRes ty
        q = posOfId vty
        p = posOfId i
        qv = Qual_var v vty q
        args = [qv, t]
        rargs = if b then args else reverse args
    in (makeNamed lab $ mkForallRange [Var_decl [v] vty q]
                     (Equation
                      (Application (Qual_op_name i (toOP_TYPE ty) p) rargs p)
                      Strong qv p) p) {isAxiom = ni }

ana_PRED_ITEM :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> Annoted (PRED_ITEM f)
    -> State (Sign f e) (Annoted (PRED_ITEM f))
ana_PRED_ITEM mef mix apr = case item apr of
    Pred_decl preds ty _ -> do
      mapM_ (addPred apr $ toPredType ty) preds
      return apr
    Pred_defn i phd@(Pred_head vs rs) at ps -> do
           let lb = getRLabel at
               lab = if null lb then getRLabel apr else lb
               ty = Pred_type (sortsOfArgs vs) rs
               arg = concatMap (\ (Var_decl v s qs) ->
                                 map (\ j -> Qual_var j s qs) v) vs
           addPred apr (toPredType ty) i
           sign <- putVarsInEmptyMap vs
           let Result ds mt = anaForm mef mix sign $ item at
           addDiags ds
           case mt of
             Nothing -> return apr {item = Pred_decl [i] ty ps}
             Just (resF, anaF) -> do
               let p = posOfId i
               addSentences [(makeNamed lab $
                              mkForallRange vs
                              (Relation (Predication (Qual_pred_name i ty p)
                                            arg p) Equivalence anaF p) p) {
                              isDef = True }]
               return apr {item = Pred_defn i phd at { item = resF } ps}

-- full function type of a selector (result sort is component sort)
data Component = Component { compId :: Id, compType :: OpType } deriving Show

instance Eq Component where
    Component i1 t1 == Component i2 t2 =
        (i1, opArgs t1, opRes t1) == (i2, opArgs t2, opRes t2)

instance Ord Component where
    Component i1 t1 <= Component i2 t2 =
        (i1, opArgs t1, opRes t1) <= (i2, opArgs t2, opRes t2)

instance Pretty Component where
    pretty (Component i ty) =
        pretty i <+> colon <> pretty ty

instance GetRange Component where
    getRange = getRange . compId

-- | return list of constructors
ana_DATATYPE_DECL :: GenKind -> DATATYPE_DECL -> State (Sign f e) [Component]
ana_DATATYPE_DECL gk (Datatype_decl s al _) =
    do ul <- mapM (ana_ALTERNATIVE s) al
       let constr = catMaybes ul
           cs = map fst constr
       unless (null constr) $ do
                  addDiags $ checkUniqueness cs
                  let totalSels = Set.unions $ map snd constr
                      wrongConstr = filter ((totalSels /=) . snd) constr
                  addDiags $ map (\ (c, _) -> mkDiag Warning
                      ("total selectors '" ++ showSepList (showString ", ")
                       showDoc (Set.toList totalSels)
                       "'\n  should be in alternative") c) wrongConstr
       case gk of
         Free -> do
           let allts = map item al
               (alts, subs) = partition isConsAlt allts
               sbs = concatMap getAltSubsorts subs
               comps = map (getConsType s) alts
               ttrips = map ((\ (a, vs, t, ses) -> (a, vs, t, catSels ses))
                               . selForms1 "X" ) comps
               sels = concatMap (\ (_, _, _, ses) -> ses) ttrips
           addDiags $ foldr (\ a ds -> case a of
             Alt_construct p i _ _ | p == Partial ->
               mkDiag Error
               "illegal free partial constructor" i : ds
             _ -> ds) [] allts
           addSentences $ map makeInjective
                            $ filter (\ (_, _, ces) -> not $ null ces)
                              comps
           addSentences $ makeDisjSubsorts s sbs
           addSentences $ concatMap (\ c -> map (makeDisjToSort c) sbs)
                        comps
           addSentences $ makeDisjoint comps
           addSentences $ catMaybes $ concatMap
                             (\ ses ->
                               map (makeUndefForm ses) ttrips) sels
         _ -> return ()
       return cs

makeDisjSubsorts :: SORT -> [SORT] -> [Named (FORMULA f)]
makeDisjSubsorts d subs = case subs of
    [] -> []
    s : rs -> map (makeDisjSubsort s) rs ++ makeDisjSubsorts d rs
  where
  makeDisjSubsort :: SORT -> SORT -> Named (FORMULA f)
  makeDisjSubsort s1 s2 = let
     n = mkSimpleId "x"
     pd = posOfId d
     p1 = posOfId s1
     p2 = posOfId s2
     p = pd `appRange` p1 `appRange` p2
     v = Var_decl [n] d pd
     qv = toQualVar v
     in makeNamed ("ga_disjoint_sorts_" ++ showId s1 "_" ++ showId s2 "")
         $ mkForallRange [v] (Negation (Junction Con [
              Membership qv s1 p1, Membership qv s2 p2] p) p) p

makeDisjToSort :: (Id, OpType, [COMPONENTS]) -> SORT -> Named (FORMULA f)
makeDisjToSort a s =
    let (c, v, t, _) = selForms1 "X" a
        p = posOfId s
    in makeNamed ("ga_disjoint_" ++ showId c "_sort_" ++ showId s "")
         $ mkForallRange v (Negation (Membership t s p) p) p

makeInjective :: (Id, OpType, [COMPONENTS]) -> Named (FORMULA f)
makeInjective a =
    let (c, v1, t1, _) = selForms1 "X" a
        (_, v2, t2, _) = selForms1 "Y" a
        p = posOfId c
    in makeNamed ("ga_injective_" ++ showId c "")
        $ mkForallRange (v1 ++ v2)
        (Relation (Equation t1 Strong t2 p) Equivalence
         (let ces = zipWith (\ w1 w2 -> Equation
                              (toQualVar w1) Strong (toQualVar w2) p) v1 v2
          in conjunctRange ces p)
         p) p

makeDisjoint :: [(Id, OpType, [COMPONENTS])] -> [Named (FORMULA f)]
makeDisjoint l = case l of
    [] -> []
    c : cs -> map (makeDisj c) cs ++ makeDisjoint cs
  where
  makeDisj :: (Id, OpType, [COMPONENTS]) -> (Id, OpType, [COMPONENTS])
           -> Named (FORMULA f)
  makeDisj a1 a2 =
    let (c1, v1, t1, _) = selForms1 "X" a1
        (c2, v2, t2, _) = selForms1 "Y" a2
        p = posOfId c1 `appRange` posOfId c2
    in makeNamed ("ga_disjoint_" ++ showId c1 "_" ++ showId c2 "")
        $ mkForallRange (v1 ++ v2) (Negation (Equation t1 Strong t2 p) p) p

catSels :: [(Maybe Id, OpType)] -> [(Id, OpType)]
catSels = map (\ (m, t) -> (fromJust m, t)) .
                 filter (\ (m, _) -> isJust m)

makeUndefForm :: (Id, OpType) -> (Id, [VAR_DECL], TERM f, [(Id, OpType)])
              -> Maybe (Named (FORMULA f))
makeUndefForm (s, ty) (i, vs, t, sels) =
    let p = posOfId s in
    if any (\ (se, ts) -> s == se && opRes ts == opRes ty ) sels
    then Nothing else
       Just $ makeNamed ("ga_selector_undef_" ++ showId s "_" ++ showId i "")
              $ mkForallRange vs
               (Negation
                (Definedness
                 (Application (Qual_op_name s (toOP_TYPE ty) p) [t] p)
                 p) p) p

getAltSubsorts :: ALTERNATIVE -> [SORT]
getAltSubsorts c = case c of
    Subsorts cs _ -> cs
    _ -> []

getConsType :: SORT -> ALTERNATIVE -> (Id, OpType, [COMPONENTS])
getConsType s c =
    let getConsTypeAux (part, i, il) =
          (i, OpType part (concatMap
                            (map (opRes . snd) . getCompType s) il) s, il)
     in case c of
        Subsorts _ _ -> error "getConsType"
        Alt_construct k a l _ -> getConsTypeAux (k, a, l)

getCompType :: SORT -> COMPONENTS -> [(Maybe Id, OpType)]
getCompType s c = case c of
  Cons_select k l cs _ -> map (\ i -> (Just i, OpType k [s] cs)) l
  Sort cs -> [(Nothing, OpType Partial [s] cs)]

genSelVars :: String -> Int -> [OpType] -> [VAR_DECL]
genSelVars str n tys = case tys of
  [] -> []
  ty : rs -> mkVarDecl (mkNumVar str n) (opRes ty)
    : genSelVars str (n + 1) rs

makeSelForms :: Int -> (Id, [VAR_DECL], TERM f, [(Maybe Id, OpType)])
             -> [Named (FORMULA f)]
makeSelForms n (i, vs, t, tys) = case tys of
  [] -> []
  (mi, ty) : rs ->
    (case mi of
            Nothing -> []
            Just j -> let p = posOfId j
                          rty = opRes ty
                          q = posOfId rty in
              [makeNamed ("ga_selector_" ++ showId j "")
                     $ mkForallRange vs
                      (Equation
                       (Application (Qual_op_name j (toOP_TYPE ty) p) [t] p)
                       Strong (Qual_var (mkNumVar "X" n) rty q) p) p]
    ) ++ makeSelForms (n + 1) (i, vs, t, rs)

selForms1 :: String -> (Id, OpType, [COMPONENTS])
          -> (Id, [VAR_DECL], TERM f, [(Maybe Id, OpType)])
selForms1 str (i, ty, il) =
    let cs = concatMap (getCompType (opRes ty)) il
        vs = genSelVars str 1 $ map snd cs
    in (i, vs, mkAppl (mkQualOp i $ toOP_TYPE ty)
            (map toQualVar vs), cs)

selForms :: (Id, OpType, [COMPONENTS]) -> [Named (FORMULA f)]
selForms = makeSelForms 1 . selForms1 "X"

-- | return the constructor and the set of total selectors
ana_ALTERNATIVE :: SORT -> Annoted ALTERNATIVE
                -> State (Sign f e) (Maybe (Component, Set.Set Component))
ana_ALTERNATIVE s c = case item c of
    Subsorts ss _ -> do
        mapM_ (addSubsort s) ss
        return Nothing
    ic -> do
        let cons@(i, ty, il) = getConsType s ic
        addOp c ty i
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
    sels <- mapM (\ (mi, ty) ->
            case mi of
            Nothing -> return Nothing
            Just i -> do
              addOp (emptyAnno ()) ty i
              return $ Just $ Component i ty) cs
    return $ partition (isTotal . compType) $ catMaybes sels

-- | utility
resultToState :: (a -> Result a) -> a -> State (Sign f e) a
resultToState f a = do
    let r = f a
    addDiags $ diags r
    case maybeResult r of
        Nothing -> return a
        Just b -> return b

-- wrap it all up for a logic

type Ana a b s f e = Mix b s f e -> a -> State (Sign f e) a

anaForm :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> Sign f e -> FORMULA f
    -> Result (FORMULA f, FORMULA f)
anaForm mef mixIn sign f = do
    let mix = extendMix (Map.keysSet $ varMap sign) mixIn
    resF <- resolveFormula (putParen mix) (mixResolve mix)
            (globAnnos sign) (mixRules mix) f
    anaF <- minExpFORMULA mef sign resF
    return (resF, anaF)

anaTerm :: (FormExtension f, TermExtension f)
  => Min f e -> Mix b s f e -> Sign f e -> Maybe SORT -> Range -> TERM f
    -> Result (TERM f, TERM f)
anaTerm mef mixIn sign msrt pos t = do
    let mix = extendMix (Map.keysSet $ varMap sign) mixIn
    resT <- resolveMixfix (putParen mix) (mixResolve mix)
            (globAnnos sign) (mixRules mix) t
    anaT <- oneExpTerm mef sign $ maybe resT
      (\ srt -> Sorted_term resT srt pos) msrt
    return (resT, anaT)

getAllIds :: (FormExtension f, TermExtension f) => 
             BASIC_SPEC b s f -> Mix b s f e -> Sign f e -> IdSets
getAllIds bs mix inSig = 
                 unite $ ids_BASIC_SPEC (getBaseIds mix) (getSigIds mix) bs
                 : getExtIds mix (extendedInfo inSig) :
                  [mkIdSets (allConstIds inSig) (allOpIds inSig)
                  $ allPredIds inSig]

basicAnalysis :: (FormExtension f, TermExtension f)
              => Min f e -- ^ type analysis of f
              -> Ana b b s f e  -- ^ static analysis of basic item b
              -> Ana s b s f e  -- ^ static analysis of signature item s
              -> Mix b s f e -- ^ for mixfix analysis
              -> (BASIC_SPEC b s f, Sign f e, GlobalAnnos)
  -> Result (BASIC_SPEC b s f, ExtSign (Sign f e) Symbol, [Named (FORMULA f)])
            {- ^ (BS with analysed mixfix formulas for pretty printing,
            differences to input Sig,accumulated Sig,analysed Sentences) -}
basicAnalysis mef anab anas mix (bs, inSig, ga) =
    let allIds = getAllIds bs mix inSig
        (newBs, accSig) = runState (ana_BASIC_SPEC mef anab anas
               mix { mixRules = makeRules ga allIds }
               bs) inSig { globAnnos = addAssocs inSig ga }
        ds = reverse $ envDiags accSig
        sents = reverse $ sentences accSig
        cleanSig = (emptySign $ extendedInfo accSig)
                   { emptySortSet = emptySortSet accSig
                   , sortRel = sortRel accSig
                   , opMap = opMap accSig
                   , assocOps = assocOps accSig
                   , predMap = predMap accSig
                   , annoMap = annoMap accSig
                   , globAnnos = ga }
    in Result (ds ++ warnUnused accSig sents) $
       Just (newBs, ExtSign cleanSig $ declaredSymbols accSig, sents)

basicCASLAnalysis :: (BASIC_SPEC () () (), Sign () (), GlobalAnnos)
  -> Result (BASIC_SPEC () () (),
             ExtSign (Sign () ()) Symbol,
             [Named (FORMULA ())])
basicCASLAnalysis = basicAnalysis (const return) (const return)
                                  (const return) emptyMix

-- | extra
cASLsen_analysis ::
        (BASIC_SPEC () () (), Sign () (), FORMULA ()) -> Result (FORMULA (), FORMULA ())
cASLsen_analysis (bs, s, f) = let
                         mix = emptyMix
                         allIds = getAllIds bs mix s
                         mix' = mix { mixRules = makeRules emptyGlobalAnnos
                                                           allIds }
                         in anaForm (const return) mix' s f

-- | convert theory

convertCASLTheory :: (Sign f e, [Named (FORMULA f)]) -> BASIC_SPEC b s f
convertCASLTheory (sig, nsens) = trace ("in convertCASLTheory:" ++ (show $ length nsens)) $ 
 case (sig, nsens) of
  (_, []) -> Basic_spec [] -- TODO: the sig should be empty
  _ -> error "convert theory nyi for CASL logic"

-- | test nominal sen

isNominalSen :: Set.Set Id -> FORMULA f -> (Bool, Maybe Id)
isNominalSen noms aSen = 
     case aSen of
      Mixfix_formula (Mixfix_token p) ->
        let pId = simpleIdToId p 
        in if Set.member pId noms then (True, Just pId) else (False, Nothing)
      _ -> (False, Nothing)

-- | CASL hybridization: constraints to CASL sentences

constrToSens :: Sign () () -> SemanticConstraint -> Result [Named (FORMULA ())]
constrToSens sig sc = 
 let 
   st = genName "ST"
   domain = genName "domain"
   defined = genName "defined"
   (totals, partials) = partition (\(_, ot) -> opKind ot == Total) $ MapSet.toPairList $ opMap sig
 in
 case sc of
  SameInterpretation "sort" -> 
    return $
    map (\s -> makeNamed ("ga_sem_constr_"++show s)
                $ mkForall [mkVarDecl (genToken "w1") st, 
                            mkVarDecl (genToken "w2") st, 
                            mkVarDecl (genToken "x") s]
                $ mkEqv 
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w1") st nullRange,
                                  Qual_var (genToken "x") s nullRange])
                  (mkPredication (mkQualPred domain $ Pred_type [st, s] nullRange)
                                 [Qual_var (genToken "w2") st nullRange,
                                  Qual_var (genToken "x") s nullRange]) 
          ) 
                $ Set.toList $ sortSet sig
  SameInterpretation "const" -> error "nyi for const"
  SameInterpretation "op" ->
   let
      xs ot = zip (opArgs ot) [1::Int ..]
      extOt i ot = Qual_op_name i (Op_type Total (st:opArgs ot) (opRes ot) nullRange) nullRange
    in return $
        map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ mkForall 
                                ( [mkVarDecl (genToken "w1") st, 
                                   mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ mkStEq 
                                      (mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
                                      (mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot))
          ) totals
  SameInterpretation "pred" ->
    let
      xs pt = zip (predArgs pt) [1::Int ..]  
      extPt (Pred_type ss r) = Pred_type (st:ss) r 
    in return $
        map (\(i, pt) -> makeNamed ("ga_sem_constr_" ++ show i) $ 
                          mkForall 
                           ( [mkVarDecl (genToken "w1") st, 
                              mkVarDecl (genToken "w2") st]
                              ++ 
                              (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs pt)
                           )
                           $ mkEqv (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $ 
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt))
                                   (mkPredication (mkQualPred i $ extPt $ toPRED_TYPE pt) $
                                     map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs pt)) 
            ) $ MapSet.toPairList $ predMap sig
  SameDomain False -> let
      xs ot = zip (opArgs ot) [1::Int ..]
      extOt i ot = Qual_op_name i (Op_type Total (st:opArgs ot) (opRes ot) nullRange) nullRange
    in return $
     map (\(i,ot) -> makeNamed ("ga_sem_constr_" ++ show i)
                $ mkForall 
                                ( [mkVarDecl (genToken "w1") st, 
                                   mkVarDecl (genToken "w2") st]
                                  ++ 
                                  (map (\(si, ii) -> mkVarDecl (genToken $ "x" ++ show ii) si) $ xs ot)
                                 ) 
                                 $ mkEqv 
                                      (mkPredication (mkQualPred defined $ Pred_type [st, opRes ot] nullRange) $ 
                                       [mkVarTerm (genToken "w1") st,
                                        mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w1", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
                                      (mkPredication (mkQualPred defined $ Pred_type [st, opRes ot] nullRange) $ 
                                       [mkVarTerm (genToken "w2") st,
                                        mkAppl (extOt i ot) $ map (\(a,b) -> mkVarTerm a b) $ (genToken "w2", st):(map (\(si, ii) -> (genToken $ "x" ++ show ii, si)) $ xs ot)
                                       ]
                                       )
          ) 
                partials 
  _ -> error $ "Constraint not supported for CASL logic:" ++ show sc
