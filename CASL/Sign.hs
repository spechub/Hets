{- |
Module      :  $Header$
Description :  CASL signatures (serve as local environments for the basic static analysis)
Copyright   :  (c) Christian Maeder and Uni Bremen 2002-2006
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

CASL signatures (serve as local environments for the basic static analysis)
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

-- constants have empty argument lists
data OpType = OpType {opKind :: FunKind, opArgs :: [SORT], opRes :: SORT}
              deriving (Show, Eq, Ord)

data PredType = PredType {predArgs :: [SORT]} deriving (Show, Eq, Ord)

type OpMap = Map.Map Id (Set.Set OpType)

data SymbType = SortAsItemType
              | OpAsItemType OpType
                -- since symbols do not speak about totality, the totality
                -- information in OpType has to be ignored
              | PredAsItemType PredType
                deriving Show

-- Ordering and equality of symbol types has to ingore totality information
instance Ord SymbType where
  compare st1 st2 = case (st1, st2) of
    (SortAsItemType, SortAsItemType) -> EQ
    (SortAsItemType, _) -> LT
    (OpAsItemType ot1, OpAsItemType ot2) ->
      compare (opArgs ot1, opRes ot1) (opArgs ot2, opRes ot2)
    (OpAsItemType _, SortAsItemType) -> GT
    (OpAsItemType _, PredAsItemType _) -> LT
    (PredAsItemType pt1, PredAsItemType pt2) -> compare pt1 pt2
    (PredAsItemType _, _) -> GT

instance Eq SymbType where
  t1 == t2 = compare t1 t2 == EQ

data Symbol = Symbol {symName :: Id, symbType :: SymbType}
              deriving (Show, Eq, Ord)

instance PosItem Symbol where
    getRange = getRange . symName

idToSortSymbol :: Id -> Symbol
idToSortSymbol idt = Symbol idt SortAsItemType

idToOpSymbol :: Id -> OpType -> Symbol
idToOpSymbol idt typ = Symbol idt (OpAsItemType typ)

idToPredSymbol :: Id -> PredType -> Symbol
idToPredSymbol idt typ = Symbol idt (PredAsItemType typ)

data Q_ProofTree = Q_ProofTree String deriving (Eq, Ord)

instance Show Q_ProofTree where
  show (Q_ProofTree st) = st

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
instance (Eq f, Eq e) => Eq (Sign f e) where
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

-- | proper subsorts (possibly excluding input sort)
subsortsOf :: SORT -> Sign f e -> Set.Set SORT
subsortsOf s e = Rel.predecessors (sortRel e) s

-- | proper supersorts (possibly excluding input sort)
supersortsOf :: SORT -> Sign f e -> Set.Set SORT
supersortsOf s e = Rel.succs (sortRel e) s

toOP_TYPE :: OpType -> OP_TYPE
toOP_TYPE OpType { opArgs = args, opRes = res, opKind = k } =
    Op_type k  args res nullRange

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

instance (Pretty f, Pretty e) => Pretty (Sign f e) where
    pretty = printSign pretty pretty

instance Pretty Symbol where
  pretty sy = let n = pretty (symName sy) in
    case symbType sy of
       SortAsItemType -> n
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
     SortAsItemType -> empty

printSign :: (f -> Doc) -> (e -> Doc) -> Sign f e -> Doc
printSign _ fE s = let
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
                       $ Rel.toMap $ Rel.transpose $ sortRel s))
    $+$ printSetMap (text opS) empty (opMap s)
    $+$ printSetMap (text predS) space (predMap s)
    $+$ fE (extendedInfo s)

-- working with Sign

diffSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
diffSig dif a b = a
  { sortSet = sortSet a `Set.difference` sortSet b
  , emptySortSet = emptySortSet a `Set.difference` emptySortSet b
  , sortRel = Rel.irreflex $ Rel.transClosure
              $ Rel.difference (sortRel a) $ sortRel b
  , opMap = opMap a `diffMapSet` opMap b
  , assocOps = assocOps a `diffMapSet` assocOps b
  , predMap = predMap a `diffMapSet` predMap b
  , annoMap = annoMap a `diffMapSet` annoMap b
  , extendedInfo = dif (extendedInfo a) $ extendedInfo b }
  -- transClosure needed:  {a < b < c} - {a < c; b}
  -- is not transitive!

diffMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b)
           -> Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
diffMapSet = Map.differenceWith
    (\ s t -> let d = Set.difference s t in
              if Set.null d then Nothing else Just d)

addMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
          -> Map.Map a (Set.Set b)
addMapSet = Map.unionWith Set.union

interMapSet :: (Ord a, Ord b) => Map.Map a (Set.Set b) -> Map.Map a (Set.Set b)
            -> Map.Map a (Set.Set b)
interMapSet m =
  Map.filter (not . Set.null) . Map.intersectionWith Set.intersection m

uniteCASLSign :: Sign () () -> Sign () () -> Sign () ()
uniteCASLSign a b = addSig (\_ _ -> ()) a b

addSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
addSig ad a b = a
  { sortSet = sortSet a `Set.union` sortSet b
  , emptySortSet = emptySortSet a `Set.union` emptySortSet b
  , sortRel = Rel.irreflex $ Rel.transClosure
              $ Rel.union (sortRel a) $ sortRel b
  , opMap = addMapSet (opMap a) $ opMap b
  , assocOps = addMapSet (assocOps a) $ assocOps b
  , predMap = addMapSet (predMap a) $ predMap b
  , annoMap = addMapSet (annoMap a) $ annoMap b
  , extendedInfo = ad (extendedInfo a) $ extendedInfo b }

interSig :: (e -> e -> e) -> Sign f e -> Sign f e -> Sign f e
interSig ef a b = a
  { sortSet = sortSet a `Set.intersection` sortSet b
  , emptySortSet = emptySortSet a `Set.intersection` emptySortSet b
  , sortRel = Rel.irreflex $ Rel.transClosure
              $ Rel.fromSet $ Set.intersection
                    (Rel.toSet $ sortRel a) $ Rel.toSet $ sortRel b
  , opMap = interMapSet (opMap a) $ opMap b
  , assocOps = interMapSet (assocOps a) $ assocOps b
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
    Partial -> Set.member e {opKind = Total} t
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
  if Set.null v then return () else do
    e <- State.get
    State.put e { annoMap = Map.insertWith (Set.union) s v $ annoMap e }

addSymbol :: Symbol -> State.State (Sign f e) ()
addSymbol s = do
  e <- State.get
  State.put e { declaredSymbols = Set.insert s $ declaredSymbols e }

addSort :: SortsKind -> Annoted a -> SORT -> State.State (Sign f e) ()
addSort sk a s = do
  e <- State.get
  let m = sortSet e
      em = emptySortSet e
  if Set.member s m then addDiags [mkDiag Hint "redeclared sort" s]
    else do
      State.put e { sortSet = Set.insert s m }
      addDiags $ checkNamePrefix s
  case sk of
    NonEmptySorts -> if Set.member s em then
       addDiags [mkDiag Warning "redeclared sort as non-empty" s]
       else return ()
    PossiblyEmptySorts -> if not $ Set.member s em then do
        e2 <- State.get
        State.put e2 { emptySortSet = Set.insert s em }
        if Set.member s m then
          addDiags [mkDiag Warning "redeclared sort as possibly empty" s]
          else return ()
      else return ()
  addAnnoSet a $ Symbol s SortAsItemType

hasSort :: Sign f e -> SORT -> [Diagnosis]
hasSort e s =
    if Set.member s $ sortSet e then [] else [mkDiag Error "unknown sort" s]

checkSorts :: [SORT] -> State.State (Sign f e) ()
checkSorts s = do
  e <- State.get
  addDiags $ concatMap (hasSort e) s

addSubsort :: SORT -> SORT -> State.State (Sign f e) ()
addSubsort = addSubsortOrIso True

addSubsortOrIso :: Bool -> SORT -> SORT -> State.State (Sign f e) ()
addSubsortOrIso b super sub = do
  if b then checkSorts [super, sub] else return ()
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
      else if Rel.path sub super r
           then addDiags [Diag Hint ("redeclared subsort" ++ rel) p]
           else return ()
    else if Rel.path super sub r then
      if Rel.path sub super r
      then addDiags [Diag Hint ("redeclared isomoprhic sorts" ++ rel) p]
      else addDiags [Diag Warning ("subsort '" ++
        showDoc super "' made isomorphic by" ++ rel) $ posOfId super]
    else if Rel.path sub super r
         then addDiags [Diag Warning ("subsort  '" ++
           showDoc sub "' made isomorphic by" ++ rel) p]
         else return()

closeSubsortRel :: State.State (Sign f e) ()
closeSubsortRel=
    do e <- State.get
       State.put e { sortRel = Rel.transClosure $ sortRel e }

checkNamePrefix :: Id -> [Diagnosis]
checkNamePrefix i = if isPrefixOf genNamePrefix $ showId i "" then
    [mkDiag Warning "identifier may conflict with generated names" i]
    else []

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
    _ -> error "sortOfTerm"
