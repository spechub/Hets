{- |
Module      :  $Header$
Description :  CASL signatures and local environments for basic analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL signatures also serve as local environments for the basic static analysis
-}

module CASL.Sign where

import CASL.AS_Basic_CASL
import CASL.ToDoc ()
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.State as State
import Common.Keywords
import Common.Id
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Prec (mkPrecIntMap, PrecMap)
import Common.Doc
import Common.DocUtils

import Data.Maybe (fromMaybe)
import Data.List (isPrefixOf)
import Control.Monad (when, unless)

-- constants have empty argument lists
data OpType = OpType {opKind :: OpKind, opArgs :: [SORT], opRes :: SORT}
              deriving (Show, Eq, Ord)

mkTotOpType :: [SORT] -> SORT -> OpType
mkTotOpType = OpType Total

sortToOpType :: SORT -> OpType
sortToOpType = mkTotOpType []

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

sortToPredType :: SORT -> PredType
sortToPredType s = PredType [s]

isBinPredType :: PredType -> Bool
isBinPredType (PredType l) = case l of
  [_, _] -> True
  _ -> False

type OpMap = MapSet.MapSet OP_NAME OpType
type PredMap = MapSet.MapSet PRED_NAME PredType

data SymbType = SortAsItemType
              | SubsortAsItemType SORT -- special symbols for xml output
              | OpAsItemType OpType
                {- since symbols do not speak about totality, the totality
                information in OpType has to be ignored -}
              | PredAsItemType PredType
                deriving (Show, Eq, Ord)

data Symbol = Symbol {symName :: Id, symbType :: SymbType}
              deriving (Show, Eq, Ord)

instance GetRange Symbol where
    getRange = getRange . symName

idToSortSymbol :: Id -> Symbol
idToSortSymbol idt = Symbol idt SortAsItemType

idToOpSymbol :: Id -> OpType -> Symbol
idToOpSymbol idt = Symbol idt . OpAsItemType

idToPredSymbol :: Id -> PredType -> Symbol
idToPredSymbol idt = Symbol idt . PredAsItemType

dummy :: Sign f s -> a -> ()
dummy _ _ = ()

dummyMin :: b -> c -> Result ()
dummyMin _ _ = return ()

type CASLSign = Sign () ()

{- | the data type for the basic static analysis to accumulate variables,
sentences, symbols, diagnostics and annotations, that are removed or ignored
when looking at signatures from outside, i.e. during logic-independent
processing. -}
data Sign f e = Sign
    { sortSet :: Set.Set SORT
    , emptySortSet :: Set.Set SORT
    -- ^ a subset of the sort set of possibly empty sorts
    , sortRel :: Rel.Rel SORT
    , opMap :: OpMap
    , assocOps :: OpMap -- ^ the subset of associative operators
    , predMap :: PredMap
    , varMap :: Map.Map SIMPLE_ID SORT -- ^ temporary variables
    , sentences :: [Named (FORMULA f)] -- ^ current sentences
    , declaredSymbols :: Set.Set Symbol -- ^ introduced or redeclared symbols
    , envDiags :: [Diagnosis] -- ^ diagnostics for basic spec
    , annoMap :: MapSet.MapSet Symbol Annotation -- ^ annotated symbols
    , globAnnos :: GlobalAnnos -- ^ global annotations to use
    , extendedInfo :: e
    } deriving Show

-- better ignore assoc flags for equality
instance Eq e => Eq (Sign f e) where
    a == b = compare a {extendedInfo = ()} b {extendedInfo = ()} == EQ
      && extendedInfo a == extendedInfo b

instance Ord e => Ord (Sign f e) where
  compare a b = compare
    (sortSet a, emptySortSet a, sortRel a, opMap a, predMap a, extendedInfo a)
    (sortSet b, emptySortSet b, sortRel b, opMap b, predMap b, extendedInfo b)

emptySign :: e -> Sign f e
emptySign e = Sign
    { sortSet = Set.empty
    , emptySortSet = Set.empty
    , sortRel = Rel.empty
    , opMap = MapSet.empty
    , assocOps = MapSet.empty
    , predMap = MapSet.empty
    , varMap = Map.empty
    , sentences = []
    , declaredSymbols = Set.empty
    , envDiags = []
    , annoMap = MapSet.empty
    , globAnnos = emptyGlobalAnnos
    , extendedInfo = e }

getSyntaxTable :: Sign f e -> (PrecMap, AssocMap)
getSyntaxTable sig = let gannos = globAnnos sig
                     in (mkPrecIntMap $ prec_annos gannos, assoc_annos gannos)


class SignExtension e where
    isSubSignExtension :: e -> e -> Bool

instance SignExtension () where
    isSubSignExtension _ _ = True

-- | proper subsorts (possibly excluding input sort)
subsortsOf :: SORT -> Sign f e -> Set.Set SORT
subsortsOf s e = Rel.predecessors (sortRel e) s

-- | proper supersorts (possibly excluding input sort)
supersortsOf :: SORT -> Sign f e -> Set.Set SORT
supersortsOf s e = Rel.succs (sortRel e) s

toOP_TYPE :: OpType -> OP_TYPE
toOP_TYPE OpType { opArgs = args, opRes = res, opKind = k } =
    Op_type k args res nullRange

toPRED_TYPE :: PredType -> PRED_TYPE
toPRED_TYPE PredType { predArgs = args } = Pred_type args nullRange

toOpType :: OP_TYPE -> OpType
toOpType (Op_type k args r _) = OpType k args r

toPredType :: PRED_TYPE -> PredType
toPredType (Pred_type args _) = PredType args

instance Pretty OpType where
  pretty = pretty . toOP_TYPE

instance Pretty PredType where
  pretty = pretty . toPRED_TYPE

instance (Show f, Pretty e) => Pretty (Sign f e) where
    pretty = printSign pretty

instance Pretty Symbol where
  pretty sy = let n = pretty (symName sy) in
    case symbType sy of
       SortAsItemType -> keyword sortS <+> n
       SubsortAsItemType s -> keyword sortS <+> n <+> less <+> pretty s
       PredAsItemType pt -> keyword predS <+> n <+> colon <+> pretty pt
       OpAsItemType ot -> keyword opS <+> n <+> colon <> pretty ot

printSign :: (e -> Doc) -> Sign f e -> Doc
printSign fE s = let
  printRel (supersort, subsorts) =
            ppWithCommas (Set.toList subsorts) <+> text lessS <+>
               idDoc supersort
  esorts = emptySortSet s
  srel = sortRel s
  cs = Rel.sccOfClosure $ Rel.transClosure srel
  nsorts = Set.difference (sortSet s) esorts in
    (if Set.null nsorts then empty else text (sortS ++ sS) <+>
       sepByCommas (map idDoc (Set.toList nsorts))) $+$
    (if Set.null esorts then empty else text (esortS ++ sS) <+>
       sepByCommas (map idDoc (Set.toList esorts))) $+$
    (if Rel.null srel then empty
      else text (sortS ++ sS) <+>
       fsep (punctuate semi $
          map (fsep . punctuate (space <> equals) . map pretty)
           (filter ((> 1) . length) $ map Set.toList cs)
         ++ map printRel (Map.toList
         $ Rel.toMap $ Rel.transpose $ Rel.transReduce $ Rel.irreflex
         $ Rel.collaps cs srel)))
    $+$ printSetMap (text opS) empty (MapSet.toMap $ opMap s)
    $+$ printSetMap (text predS) space (MapSet.toMap $ predMap s)
    $+$ fE (extendedInfo s)

-- working with Sign

irreflexClosure :: Ord a => Rel.Rel a -> Rel.Rel a
irreflexClosure = Rel.irreflex . Rel.transClosure

closeSortRel :: Sign f e -> Sign f e
closeSortRel s =
  s { sortRel = irreflexClosure $ sortRel s }

nonEmptySortSet :: Sign f e -> Set.Set Id
nonEmptySortSet s = Set.difference (sortSet s) $ emptySortSet s

-- op kinds of op types

setOpKind :: OpKind -> OpType -> OpType
setOpKind k o = o { opKind = k }

mkPartial :: OpType -> OpType
mkPartial = setOpKind Partial

mkTotal :: OpType -> OpType
mkTotal = setOpKind Total

isTotal :: OpType -> Bool
isTotal = (== Total) . opKind

isPartial :: OpType -> Bool
isPartial = not . isTotal

makePartial :: Set.Set OpType -> Set.Set OpType
makePartial = Set.mapMonotonic mkPartial

-- | remove (True) or add (False) partial op if it is included as total
rmOrAddParts :: Bool -> Set.Set OpType -> Set.Set OpType
rmOrAddParts b s =
  let t = makePartial $ Set.filter isTotal s
  in (if b then Set.difference else Set.union) s t

rmOrAddPartsMap :: Bool -> OpMap -> OpMap
rmOrAddPartsMap b = MapSet.mapSet (rmOrAddParts b)

diffMapSet :: PredMap -> PredMap -> PredMap
diffMapSet = MapSet.difference

diffOpMapSet :: OpMap -> OpMap -> OpMap
diffOpMapSet m = MapSet.difference m . rmOrAddPartsMap False

diffSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
diffSig dif a b = let s = sortSet a `Set.difference` sortSet b in
  closeSortRel a
  { sortSet = s
  , emptySortSet = Set.difference s
      $ nonEmptySortSet a `Set.difference` nonEmptySortSet b
  , sortRel = Rel.difference (Rel.transReduce $ sortRel a)
      . Rel.transReduce $ sortRel b
  , opMap = opMap a `diffOpMapSet` opMap b
  , assocOps = assocOps a `diffOpMapSet` assocOps b
  , predMap = predMap a `diffMapSet` predMap b
  , annoMap = annoMap a `MapSet.difference` annoMap b
  , extendedInfo = dif (extendedInfo a) $ extendedInfo b }
  {- transClosure needed:  {a < b < c} - {a < c; b}
  is not transitive! -}

addOpMapSet :: OpMap -> OpMap -> OpMap
addOpMapSet m = rmOrAddPartsMap True . MapSet.union m

addMapSet :: PredMap -> PredMap -> PredMap
addMapSet = MapSet.union

addSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
addSig ad a b = let s = sortSet a `Set.union` sortSet b in
  closeSortRel a
  { sortSet = s
  , emptySortSet = Set.difference s
      $ nonEmptySortSet a `Set.union` nonEmptySortSet b
  , sortRel = Rel.union (sortRel a) $ sortRel b
  , opMap = addOpMapSet (opMap a) $ opMap b
  , assocOps = addOpMapSet (assocOps a) $ assocOps b
  , predMap = MapSet.union (predMap a) $ predMap b
  , annoMap = MapSet.union (annoMap a) $ annoMap b
  , extendedInfo = ad (extendedInfo a) $ extendedInfo b }

uniteCASLSign :: Sign () () -> Sign () () -> Sign () ()
uniteCASLSign = addSig (\ _ _ -> ())

interRel :: Ord a => Rel.Rel a -> Rel.Rel a -> Rel.Rel a
interRel a = Rel.fromSet
  . Set.intersection (Rel.toSet a) . Rel.toSet

interOpMapSet :: OpMap -> OpMap -> OpMap
interOpMapSet m = rmOrAddPartsMap True
   . MapSet.intersection (rmOrAddPartsMap False m) . rmOrAddPartsMap False

interMapSet :: PredMap -> PredMap -> PredMap
interMapSet = MapSet.intersection

interSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
interSig ef a b = let s = sortSet a `Set.intersection` sortSet b in
  closeSortRel a
  { sortSet = s
  , emptySortSet = Set.difference s
      $ nonEmptySortSet a `Set.intersection` nonEmptySortSet b
  , sortRel = interRel (sortRel a) $ sortRel b
  , opMap = interOpMapSet (opMap a) $ opMap b
  , assocOps = interOpMapSet (assocOps a) $ assocOps b
  , predMap = interMapSet (predMap a) $ predMap b
  , annoMap = MapSet.intersection (annoMap a) $ annoMap b
  , extendedInfo = ef (extendedInfo a) $ extendedInfo b }

isSubOpMap :: OpMap -> OpMap -> Bool
isSubOpMap m = Map.isSubmapOfBy (\ s t -> MapSet.setAll
    (\ e -> Set.member e t || isPartial e && Set.member (mkTotal e) t)
    s) (MapSet.toMap m) . MapSet.toMap

isSubMap :: PredMap -> PredMap -> Bool
isSubMap = MapSet.isSubmapOf

isSubSig :: (e -> e -> Bool) -> Sign f e -> Sign f e -> Bool
isSubSig isSubExt a b = Set.isSubsetOf (sortSet a) (sortSet b)
  && Rel.isSubrelOf (sortRel a) (sortRel b)
         -- ignore empty sort sorts
  && isSubOpMap (opMap a) (opMap b)
         -- ignore associativity properties!
  && isSubMap (predMap a) (predMap b)
  && isSubExt (extendedInfo a) (extendedInfo b)

mapSetToList :: MapSet.MapSet a b -> [(a, b)]
mapSetToList = MapSet.toPairList

addDiags :: [Diagnosis] -> State.State (Sign f e) ()
addDiags ds = do
  e <- State.get
  State.put e { envDiags = reverse ds ++ envDiags e }

addAnnoSet :: Annoted a -> Symbol -> State.State (Sign f e) ()
addAnnoSet a s = do
  addSymbol s
  let v = Set.union (Set.fromList $ l_annos a) $ Set.fromList $ r_annos a
  unless (Set.null v) $ do
    e <- State.get
    State.put e { annoMap = MapSet.update (Set.union v) s $ annoMap e }

addSymbol :: Symbol -> State.State (Sign f e) ()
addSymbol s = do
  e <- State.get
  State.put $ addSymbToDeclSymbs e s

addSymbToDeclSymbs :: Sign e f -> Symbol -> Sign e f
addSymbToDeclSymbs cs sy =
    cs { declaredSymbols = Set.insert sy $ declaredSymbols cs }

addSort :: SortsKind -> Annoted a -> SORT -> State.State (Sign f e) ()
addSort sk a s = do
  e <- State.get
  let m = sortSet e
      em = emptySortSet e
      known = Set.member s m
  if known then addDiags [mkDiag Hint "redeclared sort" s]
    else do
      State.put e { sortSet = Set.insert s m }
      addDiags $ checkNamePrefix s
  case sk of
    NonEmptySorts -> when (Set.member s em) $ do
        e2 <- State.get
        State.put e2 { emptySortSet = Set.delete s em }
        addDiags [mkDiag Warning "redeclared sort as non-empty" s]
    PossiblyEmptySorts -> if known then
      addDiags [mkDiag Warning "non-empty sort remains non-empty" s]
      else do
        e2 <- State.get
        State.put e2 { emptySortSet = Set.insert s em }
  addAnnoSet a $ Symbol s SortAsItemType

hasSort :: Sign f e -> SORT -> [Diagnosis]
hasSort e s =
    [ mkDiag Error "unknown sort" s
    | not $ Set.member s $ sortSet e ]

checkSorts :: [SORT] -> State.State (Sign f e) ()
checkSorts s = do
  e <- State.get
  addDiags $ concatMap (hasSort e) s

addSubsort :: SORT -> SORT -> State.State (Sign f e) ()
addSubsort = addSubsortOrIso True

addSubsortOrIso :: Bool -> SORT -> SORT -> State.State (Sign f e) ()
addSubsortOrIso b super sub = do
  when b $ checkSorts [super, sub]
  e <- State.get
  let r = sortRel e
  State.put e { sortRel = (if b then id else Rel.insert super sub)
                $ Rel.insert sub super r }
  let p = posOfId sub
      rel = " '" ++
        showDoc sub (if b then " < " else " = ") ++ showDoc super "'"
  if super == sub then addDiags [mkDiag Warning "void reflexive subsort" sub]
    else if b then
      if Rel.path super sub r then
        if Rel.path sub super r
        then addDiags [Diag Warning ("sorts are isomorphic" ++ rel) p]
        else addDiags [Diag Warning ("added subsort cycle by" ++ rel) p]
      else when (Rel.path sub super r)
           $ addDiags [Diag Hint ("redeclared subsort" ++ rel) p]
    else if Rel.path super sub r then
      if Rel.path sub super r
      then addDiags [Diag Hint ("redeclared isomoprhic sorts" ++ rel) p]
      else addDiags [Diag Warning ("subsort '" ++
        showDoc super "' made isomorphic by" ++ rel) $ posOfId super]
    else when (Rel.path sub super r)
         $ addDiags [Diag Warning ("subsort  '" ++
           showDoc sub "' made isomorphic by" ++ rel) p]

closeSubsortRel :: State.State (Sign f e) ()
closeSubsortRel =
    do e <- State.get
       State.put e { sortRel = Rel.transClosure $ sortRel e }

checkNamePrefix :: Id -> [Diagnosis]
checkNamePrefix i =
    [ mkDiag Warning "identifier may conflict with generated names" i
    | isPrefixOf genNamePrefix $ showId i ""]

alsoWarning :: String -> String -> Id -> [Diagnosis]
alsoWarning new old i = let is = ' ' : showId i "'" in
    [Diag Warning ("new '" ++ new ++ is ++ " is also known as '" ++ old ++ is)
     $ posOfId i]

checkWithMap :: String -> String -> Map.Map Id a -> Id -> [Diagnosis]
checkWithMap s1 s2 m i = if Map.member i m then alsoWarning s1 s2 i else []

checkWithOtherMap :: String -> String -> MapSet.MapSet Id a -> Id -> [Diagnosis]
checkWithOtherMap s1 s2 = checkWithMap s1 s2 . MapSet.toMap

addVars :: VAR_DECL -> State.State (Sign f e) ()
addVars (Var_decl vs s _) = do
    checkSorts [s]
    mapM_ (addVar s) vs

addVar :: SORT -> SIMPLE_ID -> State.State (Sign f e) ()
addVar s v =
    do e <- State.get
       let m = varMap e
           i = simpleIdToId v
           ds = case Map.lookup v m of
                Just _ -> [mkDiag Hint "known variable shadowed" v]
                Nothing -> []
       State.put e { varMap = Map.insert v s m }
       addDiags $ ds ++ checkWithOtherMap varS opS (opMap e) i
                ++ checkWithOtherMap varS predS (predMap e) i
                ++ checkNamePrefix i

addOpTo :: Id -> OpType -> OpMap -> OpMap
addOpTo = MapSet.insert

type VarSet = Set.Set (VAR, SORT)

{- | extract the sort and free variables from an analysed term. The input
signature for free variables is (currently only) used for statements in the
VSE logic. The conversion for boolean terms to formulas is only used for FPL.
-}
class TermExtension f where
  freeVarsOfExt :: Sign f e -> f -> VarSet
  freeVarsOfExt _ = const Set.empty

  optTermSort :: f -> Maybe SORT
  optTermSort = const Nothing

  sortOfTerm :: f -> SORT
  sortOfTerm = fromMaybe (genName "unknown") . optTermSort

  termToFormula :: TERM f -> Result (FORMULA f)
  termToFormula = const $ Result [] Nothing

instance TermExtension ()

instance TermExtension f => TermExtension (TERM f) where
  optTermSort = optSortOfTerm optTermSort

optSortOfTerm :: (f -> Maybe SORT) -> TERM f -> Maybe SORT
optSortOfTerm f term = case term of
    Qual_var _ ty _ -> Just ty
    Application (Qual_op_name _ ot _) _ _ -> Just $ res_OP_TYPE ot
    Sorted_term _ ty _ -> Just ty
    Cast _ ty _ -> Just ty
    Conditional t1 _ _ _ -> optSortOfTerm f t1
    ExtTERM t -> f t
    _ -> Nothing

-- | create binding if variables are non-null
mkForall :: [VAR_DECL] -> FORMULA f -> Range -> FORMULA f
mkForall vl f ps = if null vl then f else Quantification Universal vl f ps

-- | convert a singleton variable declaration into a qualified variable
toQualVar :: VAR_DECL -> TERM f
toQualVar (Var_decl v s ps) =
    if isSingle v then Qual_var (head v) s ps else error "toQualVar"

mkImpl :: FORMULA f -> FORMULA f -> FORMULA f
mkImpl f f' = Implication f f' True nullRange

mkExEq :: TERM f -> TERM f -> FORMULA f
mkExEq f f' = Existl_equation f f' nullRange

mkStEq :: TERM f -> TERM f -> FORMULA f
mkStEq u v = Strong_equation u v nullRange

mkEqv :: FORMULA f -> FORMULA f -> FORMULA f
mkEqv u v = Equivalence u v nullRange

mkAppl :: OP_SYMB -> [TERM f] -> TERM f
mkAppl op_symb fs = Application op_symb fs nullRange

-- | turn sorted variable into variable delcaration
mkVarDecl :: VAR -> SORT -> VAR_DECL
mkVarDecl v s = Var_decl [v] s nullRange

-- | turn sorted variable into term
mkVarTerm :: VAR -> SORT -> TERM f
mkVarTerm v = toQualVar . mkVarDecl v

-- | optimized conjunction
conjunct :: [FORMULA f] -> FORMULA f
conjunct fs = case fs of
  [] -> True_atom nullRange
  [phi] -> phi
  _ -> Conjunction fs nullRange

mkVarDeclStr :: String -> SORT -> VAR_DECL
mkVarDeclStr = mkVarDecl . mkSimpleId

mkAxName :: String -> SORT -> SORT -> String
mkAxName str s s' = "ga_" ++ str ++ "_" ++ show s ++ "_to_" ++ show s'

mkAxNameSingle :: String -> SORT -> String
mkAxNameSingle str s = "ga_" ++ str ++ "_" ++ show s

mkSortGenName :: [SORT] -> String
mkSortGenName sl = "ga_generated_" ++ showSepList (showString "_") showId sl ""

{- | The sort generation constraint is given a generated name,
built from the sort list -}
toSortGenNamed :: FORMULA f -> [SORT] -> Named (FORMULA f)
toSortGenNamed f sl = makeNamed (mkSortGenName sl) f

-- | adds a symbol to a given signature
addSymbToSign :: Sign e f -> Symbol -> Result (Sign e f)
addSymbToSign sig sy =
    let addSort' cs s =
            cs { sortSet = Set.insert s $ sortSet cs }
        addToMap' m n t = MapSet.insert n t m
        addOp' cs n ot = cs { opMap = addToMap' (opMap cs) n ot }
        addPred' cs n pt = cs { predMap = addToMap' (predMap cs) n pt }
    in do
      let sig' = addSymbToDeclSymbs sig sy
      case symbType sy of
        SortAsItemType -> return $ addSort' sig' $ symName sy
        SubsortAsItemType _ -> return sig
        PredAsItemType pt -> return $ addPred' sig' (symName sy) pt
        OpAsItemType ot -> return $ addOp' sig' (symName sy) ot
