{- |
Module      :  $Header$
Description :  CASL signatures and local environments for basic analysis
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
import qualified Common.Lib.Rel as Rel
import qualified Common.Lib.State as State
import Common.Keywords
import Common.Id
import Common.Result
import Common.AS_Annotation
import Common.GlobalAnnotations
import Common.Doc
import Common.DocUtils

import Data.List (isPrefixOf)
import Control.Monad (when, unless)

-- constants have empty argument lists
data OpType = OpType {opKind :: OpKind, opArgs :: [SORT], opRes :: SORT}
              deriving (Show, Eq, Ord)

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

type OpMap = Map.Map Id (Set.Set OpType)

data SymbType = SortAsItemType
              | OtherTypeKind String
              | OpAsItemType OpType
                -- since symbols do not speak about totality, the totality
                -- information in OpType has to be ignored
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

data Sign f e = Sign
    { sortSet :: Set.Set SORT
    , emptySortSet :: Set.Set SORT
    -- a subset of the sort set of possibly empty sorts
    , sortRel :: Rel.Rel SORT
    , opMap :: OpMap
    , assocOps :: OpMap
    , predMap :: Map.Map Id (Set.Set PredType)
    , varMap :: Map.Map SIMPLE_ID SORT
    , sentences :: [Named (FORMULA f)]
    , declaredSymbols :: Set.Set Symbol
    , envDiags :: [Diagnosis]
    , annoMap :: Map.Map Symbol (Set.Set Annotation)
    , globAnnos :: GlobalAnnos
    , extendedInfo :: e
    } deriving Show

-- better ignore assoc flags for equality
instance Eq e => Eq (Sign f e) where
    e1 == e2 =
        sortSet e1 == sortSet e2 &&
        emptySortSet e1 == emptySortSet e2 &&
        sortRel e1 == sortRel e2 &&
        opMap e1 == opMap e2 &&
        predMap e1 == predMap e2 &&
        extendedInfo e1 == extendedInfo e2

emptySign :: e -> Sign f e
emptySign e = Sign
    { sortSet = Set.empty
    , emptySortSet = Set.empty
    , sortRel = Rel.empty
    , opMap = Map.empty
    , assocOps = Map.empty
    , predMap = Map.empty
    , varMap = Map.empty
    , sentences = []
    , declaredSymbols = Set.empty
    , envDiags = []
    , annoMap = Map.empty
    , globAnnos = emptyGlobalAnnos
    , extendedInfo = e }

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
       SortAsItemType -> n
       OtherTypeKind s -> text s <+> n
       PredAsItemType pt -> let p = n <+> colon <+> pretty pt in
         case predArgs pt of
           [_] -> text predS <+> p
           _ -> p
       OpAsItemType ot -> let o = n <+> colon <> pretty ot in
         case opArgs ot of
           [] | opKind ot == Total -> text opS <+> o
           _ -> o

instance Pretty SymbType where
  pretty st = case st of
     OpAsItemType ot -> pretty ot
     PredAsItemType pt -> space <> pretty pt
     _ -> empty

printSign :: (e -> Doc) -> Sign f e -> Doc
printSign fE s = let
  printRel (supersort, subsorts) =
            ppWithCommas (Set.toList subsorts) <+> text lessS <+>
               idDoc supersort
  esorts = emptySortSet s
  nsorts = Set.difference (sortSet s) esorts in
    (if Set.null nsorts then empty else text (sortS++sS) <+>
       sepByCommas (map idDoc (Set.toList nsorts))) $+$
    (if Set.null esorts then empty else text (esortS++sS) <+>
       sepByCommas (map idDoc (Set.toList esorts))) $+$
    (if Rel.null (sortRel s) then empty
      else text (sortS++sS) <+>
       (fsep $ punctuate semi $ map printRel $ Map.toList
         $ Rel.toMap $ Rel.transpose $ Rel.transReduce $ sortRel s))
    $+$ printSetMap (text opS) empty (opMap s)
    $+$ printSetMap (text predS) space (predMap s)
    $+$ fE (extendedInfo s)

-- working with Sign

irreflexClosure :: Ord a => Rel.Rel a -> Rel.Rel a
irreflexClosure = Rel.irreflex . Rel.transClosure

closeSortRel :: Sign f e -> Sign f e
closeSortRel s =
  s { sortRel = irreflexClosure $ sortRel s }

diffSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
diffSig dif a b = let s = sortSet a `Set.difference` sortSet b in
  closeSortRel a
  { sortSet = s
  , emptySortSet = Set.difference s
      $ nonEmptySortSet a `Set.difference` nonEmptySortSet b
  , sortRel = Rel.difference (sortRel a) $ sortRel b
  , opMap = opMap a `diffOpMapSet` opMap b
  , assocOps = assocOps a `diffOpMapSet` assocOps b
  , predMap = predMap a `diffMapSet` predMap b
  , annoMap = annoMap a `diffMapSet` annoMap b
  , extendedInfo = dif (extendedInfo a) $ extendedInfo b }
  -- transClosure needed:  {a < b < c} - {a < c; b}
  -- is not transitive!

diffOpMapSet :: OpMap -> OpMap -> OpMap
diffOpMapSet m = diffMapSet m . Map.map (rmOrAddParts False)

diffMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b)
           -> Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
diffMapSet = Map.differenceWith
    (\ s t -> let d = Set.difference s t in
              if Set.null d then Nothing else Just d)

addMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
          -> Map.Map a (Set.Set b)
addMapSet = Map.unionWith Set.union

mkPartial :: OpType -> OpType
mkPartial o = o { opKind = Partial }

mkTotal :: OpType -> OpType
mkTotal o = o { opKind = Total }

makePartial :: Set.Set OpType -> Set.Set OpType
makePartial = Set.mapMonotonic mkPartial

--  | remove (True) or add (False) partial op if it is included as total
rmOrAddParts :: Bool -> Set.Set OpType -> Set.Set OpType
rmOrAddParts b s =
  let t = makePartial $ Set.filter ((== Total) . opKind) s
  in (if b then Set.difference else Set.union) s t

addOpMapSet :: OpMap -> OpMap -> OpMap
addOpMapSet m = Map.map (rmOrAddParts True). addMapSet m

interMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
            -> Map.Map a (Set.Set b)
interMapSet m =
  Map.filter (not . Set.null) . Map.intersectionWith Set.intersection m

interOpMapSet :: OpMap -> OpMap -> OpMap
interOpMapSet m = Map.filter (not . Set.null)
  . Map.intersectionWith
  (\ s t -> rmOrAddParts True $ Set.intersection (rmOrAddParts False s)
   $ rmOrAddParts False t) m

uniteCASLSign :: Sign () () -> Sign () () -> Sign () ()
uniteCASLSign = addSig (\_ _ -> ())

nonEmptySortSet :: Sign f e -> Set.Set Id
nonEmptySortSet s = Set.difference (sortSet s) $ emptySortSet s

addSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
addSig ad a b = let s = sortSet a `Set.union` sortSet b in
  closeSortRel a
  { sortSet = s
  , emptySortSet = Set.difference s
      $ nonEmptySortSet a `Set.union` nonEmptySortSet b
  , sortRel = Rel.union (sortRel a) $ sortRel b
  , opMap = addOpMapSet (opMap a) $ opMap b
  , assocOps = addOpMapSet (assocOps a) $ assocOps b
  , predMap = addMapSet (predMap a) $ predMap b
  , annoMap = addMapSet (annoMap a) $ annoMap b
  , extendedInfo = ad (extendedInfo a) $ extendedInfo b }

interRel :: Ord a => Rel.Rel a -> Rel.Rel a -> Rel.Rel a
interRel a = Rel.fromSet
  . Set.intersection (Rel.toSet a) . Rel.toSet

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
  , annoMap = interMapSet (annoMap a) $ annoMap b
  , extendedInfo = ef (extendedInfo a) $ extendedInfo b }

isEmptySig :: (e -> Bool) -> Sign f e -> Bool
isEmptySig ie s =
    Set.null (sortSet s) &&
    Rel.null (sortRel s) &&
    Map.null (opMap s) &&
    Map.null (predMap s) && ie (extendedInfo s)

isSubMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
            -> Bool
isSubMapSet = Map.isSubmapOfBy Set.isSubsetOf

isSubOpMap :: OpMap -> OpMap -> Bool
isSubOpMap = Map.isSubmapOfBy $ \ s t ->
  Set.fold ( \ e r -> r && (Set.member e t || case opKind e of
    Partial -> Set.member (mkTotal e) t
    Total -> False)) True s

isSubSig :: (e -> e -> Bool) -> Sign f e -> Sign f e -> Bool
isSubSig isSubExt a b = Set.isSubsetOf (sortSet a) (sortSet b)
  && Rel.isSubrelOf (sortRel a) (sortRel b)
         -- ignore empty sort sorts
  && isSubOpMap (opMap a) (opMap b)
         -- ignore associativity properties!
  && isSubMapSet (predMap a) (predMap b)
  && isSubExt (extendedInfo a) (extendedInfo b)

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
    State.put e { annoMap = Map.insertWith Set.union s v $ annoMap e }

addSymbol :: Symbol -> State.State (Sign f e) ()
addSymbol s = do
  e <- State.get
  State.put e { declaredSymbols = Set.insert s $ declaredSymbols e }

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
        if  Rel.path sub super r
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
closeSubsortRel=
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

checkWithOtherMap :: String -> String -> Map.Map Id a -> Id -> [Diagnosis]
checkWithOtherMap s1 s2 m i =
    case Map.lookup i m of
    Nothing -> []
    Just _ -> alsoWarning s1 s2 i

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
addOpTo k v m =
    let l = Map.findWithDefault Set.empty k m
    in Map.insert k (Set.insert v l) m

-- | extract the sort from an analysed term
sortOfTerm :: TERM f -> SORT
sortOfTerm t = case t of
    Qual_var _ ty _ -> ty
    Application (Qual_op_name _ ot _) _ _ -> res_OP_TYPE ot
    Sorted_term _ ty _ -> ty
    Cast _ ty _ -> ty
    Conditional t1 _ _ _ -> sortOfTerm t1
    _ -> genName "unknown"

-- | create binding if variables are non-null
mkForall :: [VAR_DECL] -> FORMULA f -> Range -> FORMULA f
mkForall vl f ps = if null vl then f else Quantification Universal vl f ps

-- | convert a singleton variable declaration into a qualified variable
toQualVar :: VAR_DECL -> TERM f
toQualVar (Var_decl v s ps) =
    if isSingle v then Qual_var (head v) s ps else error "toQualVar"


