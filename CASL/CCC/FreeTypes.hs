{- |
Module      :  ./CASL/CCC/FreeTypes.hs
Description :  consistency checking of free types
Copyright   :  (c) Mingyi Liu and Till Mossakowski and Uni Bremen 2004-2005
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  non-portable (imports Logic.Logic)

Consistency checking of free types
-}

module CASL.CCC.FreeTypes (checkFreeType) where

import CASL.AlphaConvert
import CASL.AS_Basic_CASL
import CASL.MapSentence
import CASL.Morphism
import CASL.Sign
import CASL.Simplify
import CASL.SimplifySen
import CASL.CCC.TermFormula
import CASL.CCC.TerminationProof (terminationProof)
import CASL.Overload (leqP)
import CASL.Quantification
import CASL.ToDoc
import CASL.Utils

import Common.AS_Annotation
import Common.Consistency (Conservativity (..))
import Common.DocUtils
import Common.Id
import Common.Result
import Common.Utils (number)
import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel

import Control.Monad

import Data.Either
import Data.Function
import Data.List
import Data.Maybe
import Data.Hashable

import qualified Data.HashSet as Set
import qualified Common.HashSetUtils as HSU

-- | check values of constructors (free types have only total ones)
inhabited :: Set.HashSet SORT -> [OP_SYMB] -> Set.HashSet SORT
inhabited sorts cons = iterateInhabited sorts where
  argsRes = foldr (\ os -> case os of
    Qual_op_name _ (Op_type Total args res _) _ -> ((args, res) :)
    _ -> id) [] cons
  iterateInhabited l =
    if changed then iterateInhabited newL else newL where
      (newL, changed) = foldr (\ (ags, rs) p@(l', _) ->
        if all (`Set.member` l') ags && not (Set.member rs l')
        then (Set.insert rs l', True) else p) (l, False) argsRes

-- | just filter out the axioms generated for free types
isGenAx :: Named (FORMULA f) -> Bool
isGenAx ax = case stripPrefix "ga_" $ senAttr ax of
  Nothing -> True
  Just rname -> all (not . (`isPrefixOf` rname))
    ["disjoint_", "injective_", "selector_"]

getFs :: [Named (FORMULA f)] -> [FORMULA f]
getFs = map sentence . filter isGenAx

-- | get the constraints from sort generation axioms
constraintOfAxiom :: [FORMULA f] -> [[Constraint]]
constraintOfAxiom = foldr (\ f -> case f of
  Sort_gen_ax constrs _ -> (constrs :)
  _ -> id) []

recoverSortsAndConstructors :: [FORMULA f] -> (Set.HashSet SORT, Set.HashSet OP_SYMB)
recoverSortsAndConstructors fs = let
  (srts, cons, _) = unzip3 . map recover_Sort_gen_ax
    $ constraintOfAxiom fs
  in (Set.unions $ map Set.fromList srts, Set.unions $ map Set.fromList cons)

-- check that patterns do not overlap, if not, return proof obligation.
getOverlapQuery :: (FormExtension f, TermExtension f, Ord f, Hashable f) => Sign f e
  -> [[FORMULA f]] -> [FORMULA f]
getOverlapQuery sig = filter (not . is_True_atom)
  . mapMaybe (retrySubstForm sig) . concatMap pairs

convert2Forms :: (TermExtension f, FormExtension f, Ord f) => Sign f e
  -> FORMULA f -> FORMULA f
  -> Result ((Subst f, [FORMULA f]), (Subst f, [FORMULA f]))
  -> (FORMULA f, FORMULA f, ((Subst f, [FORMULA f]), (Subst f, [FORMULA f])))
convert2Forms sig f1 f2 (Result ds m) =
  if null ds then let Just r = m in (f1, f2, r) else let
  (f3, c) = alphaConvert 1 id f1
  f4 = convertFormula c id f2
  Result _ (Just p) = getSubstForm sig f3 f4
  in (f3, f4, p)

retrySubstForm :: (FormExtension f, TermExtension f, Ord f, Hashable f) => Sign f e
  -> (FORMULA f, FORMULA f) -> Maybe (FORMULA f)
retrySubstForm sig (f1, f2) =
  let r@(Result ds m) = getSubstForm sig f1 f2
  in case m of
       Nothing -> Nothing
       Just s -> if null ds then Just $ mkOverlapEq sig s f1 f2
         else let (f3, f4, s2) = convert2Forms sig f1 f2 r
              in Just . stripQuant sig . convertFormula 1 id
                     $ mkOverlapEq sig s2 f3 f4

quant :: TermExtension f => Sign f e -> FORMULA f -> FORMULA f
quant sig f = quantFreeVars sig f nullRange

mkOverlapEq :: (TermExtension f, GetRange f, Ord f, Hashable f) => Sign f e
  -> ((Subst f, [FORMULA f]), (Subst f, [FORMULA f]))
  -> FORMULA f -> FORMULA f -> FORMULA f
mkOverlapEq sig ((s1, fs1), (s2, fs2)) f1 f2 = quant sig . simplifyFormula id
     . mkImpl (conjunct $ map (replaceVarsF s1 id) fs2
               ++ map (replaceVarsF s2 id) fs1)
     . overlapQuery (replaceVarsF s1 id $ stripAllQuant f1)
     . replaceVarsF s2 id $ stripAllQuant f2

{-
  check if leading symbols are new (not in the image of morphism),
        if not, return it as proof obligation
-}
getDefsForOld :: GetRange f => Sign f e -> [FORMULA f]
  -> [FORMULA f]
getDefsForOld sig axioms = let
        oldOpMap = opMap sig
        oldPredMap = predMap sig
    in filter (\ f -> case leadingSym f of
         Just (Left (Qual_op_name ident ot _))
           | MapSet.member ident (toOpType ot) oldOpMap -> True
         Just (Right (Qual_pred_name ident pt _))
           | MapSet.member ident (toPredType pt) oldPredMap -> True
         _ -> False) axioms

isFreeSortGen :: FORMULA f -> Bool
isFreeSortGen f = case f of
  Sort_gen_ax _ True -> True
  _ -> False

-- | non-inhabited non-empty sorts
getNefsorts :: Set.HashSet SORT -> Set.HashSet SORT -> Set.HashSet SORT
  -> (Set.HashSet SORT, [OP_SYMB]) -> Set.HashSet SORT
getNefsorts oldSorts nSorts esorts (srts, cons) =
  Set.difference fsorts $ inhabited oldSorts cons where
    fsorts = Set.difference (Set.intersection nSorts srts) esorts

getDataStatus :: Set.HashSet SORT -> Set.HashSet SORT -> Set.HashSet SORT -> Conservativity
getDataStatus nSorts defSubs genSorts
  | Set.null nSorts = Def
  | Set.null $ Set.difference nSorts $ Set.union genSorts defSubs = Mono
  | otherwise = Cons

getConStatus :: Conservativity -> [FORMULA f] -> Conservativity
getConStatus dataStatus fs = min dataStatus $ if null fs then Def else Cons

-- | check whether it is the domain of a partial function
isDomain :: FORMULA f -> Bool
isDomain = isJust . domainDef

-- | check whether it contains a definedness formula in correct form
correctDef :: FORMULA f -> Bool
correctDef f = case stripAllQuant f of
  Relation (Definedness _ _) c _ _ | c /= Equivalence -> True
  Negation (Definedness _ _) _ -> True
  Definedness _ _ -> True
  _ -> False

showForm :: (TermExtension f, FormExtension f) => Sign f e -> FORMULA f
  -> String
showForm s = flip showDoc "" . simplifyCASLSen s

-- check the definitional form of the partial axioms
checkDefinitional :: (FormExtension f, TermExtension f)
  => Sign f e -> [FORMULA f] -> Maybe (Result (Conservativity, [FORMULA f]))
checkDefinitional tsig fs = let
       formatAxiom = showForm tsig
       (noLSyms, withLSyms) = partition (isNothing . fst . snd)
         $ map (\ a -> (a, leadingSymPos a)) fs
       partialLSyms = foldr (\ (a, (ma, _)) -> case ma of
         Just (Left (Application t@(Qual_op_name _ (Op_type k _ _ _) _) _ _))
           | k == Partial -> ((a, t) :)
         _ -> id) [] withLSyms
       (domainDefs, otherPartials) = partition (isDomain . fst) partialLSyms
       (withDefs, withOutDefs) = partition (containDef . fst) otherPartials
       (correctDefs, wrongDefs) = partition (correctDef . fst) withDefs
       grDomainDefs = Rel.partList (on (sameOpSymbs tsig) snd) domainDefs
       (multDomainDefs, oneDomainDefs) = partition (\ l -> case l of
          [_] -> False
          _ -> True) grDomainDefs
       singleDomainDefs = map head oneDomainDefs
       nonCompleteDomainDefs = filter (\ (da, _) -> case domainDef da of
         Just (ta, _) | all isVar $ arguOfTerm ta -> False
         _ -> True) singleDomainDefs
       domainObls = concatMap (\ (da, dt) -> map (\ (de, _) -> (da, de))
           $ filter (sameOpSymbs tsig dt . snd) correctDefs) singleDomainDefs
       nonEqDoms = filter (\ (da, de) ->
         case (domainDef da, stripAllQuant de) of
           (Just (ta, _), Relation (Definedness te _) c _ _)
             | c /= Equivalence && sameOpsApp tsig ta te ->
             case leadingTermPredication de of
               Just (Left t) | eqPattern tsig te t -> False
               _ -> True
           _ -> True) domainObls
       defOpSymbs = Set.fromList $ map (snd . head) grDomainDefs
         ++ map snd correctDefs
       wrongWithoutDefs = filter ((`HSU.notMember` defOpSymbs) . snd)
         withOutDefs
       ds = map (\ (a, (_, pos)) -> Diag
         Warning ("missing leading symbol in:\n  " ++ formatAxiom a) pos)
           noLSyms
         ++ map (\ (a, t) -> Diag
         Warning ("definedness is not definitional:\n  " ++ formatAxiom a)
                $ getRange t) wrongDefs
         ++ map (\ l@((_, t) : _) -> Diag Warning (unlines $
             ("multiple domain axioms for: " ++ showDoc t "")
             : map (("  " ++) . formatAxiom . fst) l) $ getRange t)
           multDomainDefs
         ++ map (\ (a, t) -> Diag
         Warning ("missing definedness condition for partial '"
                      ++ showDoc t "' in:\n  " ++ formatAxiom a)
             $ getRange t) wrongWithoutDefs
         ++ map (\ (da, _) -> Diag
         Warning ("non-complete domain axiom:\n  " ++ formatAxiom da)
             $ getRange da) nonCompleteDomainDefs
         ++ map (\ (da, de) -> Diag
         Warning ("unexpected definedness condition:\n  "
                  ++ formatAxiom de
                  ++ "\nin the presence of domain axiom:\n  "
                  ++ formatAxiom da) $ getRange de) nonEqDoms
       in if null ds then Nothing else Just $ Result ds Nothing

{-
  call the symbols in the image of the signature morphism "new"

- each new sort must be a free type,
  i.e. it must occur in a sort generation constraint that is marked as free
    (Sort_gen_ax constrs True)
    such that the sort is in srts,
        where (srts,ops,_)=recover_Sort_gen_ax constrs
    if not, output "don't know"
  and there must be one term of that sort (inhabited)
    if not, output "no"
- group the axioms according to their leading operation/predicate symbol,
  i.e. the f resp. the p in
  forall x_1:s_n .... x_n:s_n .                  f(t_1,...,t_m)=t
  forall x_1:s_n .... x_n:s_n .       phi =>      f(t_1,...,t_m)=t
                                  Implication  Application  Strong_equation
  forall x_1:s_n .... x_n:s_n .                  p(t_1,...,t_m)<=>phi
  forall x_1:s_n .... x_n:s_n .    phi1  =>      p(t_1,...,t_m)<=>phi
                                 Implication   Predication    Equivalence
  if there are axioms not being of this form, output "don't know"
-}
checkSort :: Bool -> Set.HashSet SORT -> Set.HashSet SORT -> Set.HashSet SORT
  -> Set.HashSet SORT -> Set.HashSet SORT -> Sign f e -> Sign f e
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkSort noSentence nSorts defSubsorts gSorts fSorts nefsorts sSig tSig
    | noSentence && Set.null nSorts =
        let cond = MapSet.null (diffOpMapSet (opMap tSig) $ opMap sSig)
              && MapSet.null (diffMapSet (predMap tSig) $ predMap sSig)
        in Just $ justHint (if cond then Def else Cons, [])
        $ (if cond then "neither symbols"
          else "neither sorts") ++ " nor sentences have been added"
    | not $ Set.null notFreeSorts =
        mkUnknown "some types are not freely generated" notFreeSorts
    | not $ Set.null nefsorts = mkWarn "some sorts are not inhabited"
        nefsorts $ Just (Inconsistent, [])
    | not $ Set.null genNotNew = mkUnknown "some defined sorts are not new"
        genNotNew
    | otherwise = Nothing
    where
        notFreeSorts = Set.intersection nSorts
          $ Set.difference gSorts fSorts
        genNotNew = Set.difference
          (Set.unions [defSubsorts, gSorts, fSorts]) nSorts
        mkWarn s i r = Just $ Result [mkDiag Warning s i] r
        mkUnknown s i = mkWarn s i Nothing

checkLeadingTerms :: (FormExtension f, TermExtension f, Ord f, Hashable f)
  => Sign f e -> [FORMULA f] -> [OP_SYMB]
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkLeadingTerms tsig fsn constructors = let
    ltp = mapMaybe leadingTermPredication fsn
    formatTerm = flip showDoc "" . simplifyCASLTerm tsig
    args = foldr (\ ei -> case ei of
      Left (Application os ts qs) ->
         ((qs, "term for " ++ show (opSymbName os), ts) :)
      Right (Predication ps ts qs) ->
         ((qs, "predicate " ++ show (predSymbName ps), ts) :)
      _ -> id) [] ltp
    ds = foldr (\ (qs, d, ts) l ->
           let vs = concatMap varOfTerm ts
               dupVs = vs \\ Set.toList (Set.fromList vs)
               nonCs = checkTerms tsig constructors ts
               td = " in leading " ++ d ++ ": "
           in map (\ v -> Diag Warning
                    ("duplicate variable" ++ td ++ formatTerm v) qs) dupVs
              ++ map (\ t -> Diag Warning
                     ("non-constructor" ++ td ++ formatTerm t)
                     qs) nonCs
              ++ l) [] args
    in if null ds then Nothing else Just $ Result ds Nothing

-- check the sufficient completeness
checkIncomplete :: (FormExtension f, TermExtension f, Ord f, Hashable f)
  => Sign f e -> [FORMULA f] -> [OP_SYMB] -> [[FORMULA f]] -> [OP_SYMB]
  -> Maybe (Result (Conservativity, [FORMULA f]))
checkIncomplete sig obligations doms fsn cons =
  case getNotComplete sig doms fsn cons of
  [] -> Nothing
  incomplete -> let
    formatAxiom = showForm sig
    in Just $ Result
      (map (\ (Result ds mfs, fs@(hd : _)) -> let
        (lSym, pos) = leadingSymPos hd
        sname = case fmap extractLeadingSymb lSym of
                      Just (Left opS) -> opSymbName opS
                      Just (Right pS) -> predSymbName pS
                      _ -> error "CASL.CCC.FreeTypes.<Symb_Name>"
        in Diag Warning (intercalate "\n" $
             ("the definition of " ++ show sname
              ++ (if null ds then " may not be" else " is not") ++ " complete")
             : "the defining formula group is:"
             : map (\ (f, n) -> "  " ++ shows n ". "
                    ++ formatAxiom f) (number fs)
             ++ map diagString ds
             ++ maybe []
                 (map (\ (p, f) -> "possibly incomplete pattern for: " ++ p
                   ++ "\n  with completeness condition: "
                   ++ formatAxiom f)) mfs
             ) pos)
       incomplete) $ Just (Cons, obligations)

renameVars :: Int -> [FORMULA f] -> (Int, [FORMULA f])
renameVars c = foldr (\ f (c1, l) ->
   let (f2, c2) = alphaConvert c1 id f in
   (c2, f2 : l)) (c, [])

checkTerminal :: (FormExtension f, TermExtension f, Ord f)
  => Sign f e -> Conservativity -> [FORMULA f] -> [FORMULA f] -> [FORMULA f]
  -> IO (Result (Conservativity, [FORMULA f]))
checkTerminal sig conStatus obligations doms fsn =
    if null fsn then return $ justHint (conStatus, obligations)
      "no defining sentences"
    else do
    let (c, domains) = renameVars 1 doms
        fs_terminalProof = snd $ renameVars c fsn
    (proof, str) <- terminationProof sig fs_terminalProof domains
    return $ case proof of
        Just True -> justHint (conStatus, obligations) "termination succeeded"
        _ -> warning (Cons, obligations)
             (if isJust proof then "not terminating"
              else "cannot prove termination: " ++ str) nullRange

checkPos :: FORMULA f -> Bool
checkPos f = case f of
      Quantification _ _ f' _ -> checkPos f'
      Junction _ cs _ -> all checkPos cs
      Relation i1 c i2 _ -> let
        c1 = checkPos i1
        c2 = checkPos i2
        in if c == Equivalence then c1 == c2 else c1 <= c2
      Negation n _ -> not $ checkPos n
      Atom b _ -> b
      Predication {} -> True
      Membership {} -> True
      Definedness {} -> True
      Equation {} -> True
      Sort_gen_ax cs _ -> case cs of
        [c] -> case opSymbs c of
          [_] -> True
            {- just a single constructor creates a unique value
            even for multiple one-point components -}
          _ -> False
        _ -> False
      _ -> False

partitionMaybe :: (a -> Maybe b) -> [a] -> ([b], [a])
partitionMaybe f = foldr (\ a (bs, as) ->
  maybe (bs, a : as) (\ b -> (b : bs, as)) $ f a) ([], [])


{- -----------------------------------------------------------------------
   function checkFreeType:
   - check if leading symbols are new (not in the image of morphism),
           if not, return them as obligations
   - generated datatype is free
   - if new sort is not etype or esort, it can not be empty.
   - the leading terms consist of variables and constructors only,
           if not, return Nothing
     - split function leading_Symb into
       leadingTermPredication
       and
       extractLeadingSymb
     - collect all operation symbols from recover_Sort_gen_ax fconstrs
                                                       (= constructors)
   - no variable occurs twice in a leading term, if not, return Nothing
   - check that patterns do not overlap, if not, return obligations
     This means:
       in each group of the grouped axioms:
       all patterns of leading terms/formulas are disjoint
       this means: either leading symbol is a variable,
                           and there is just one axiom
                   otherwise, group axioms according to leading symbol
                              no symbol may be a variable
                              check recursively the arguments of
                              constructor in each group
  - sufficient completeness
  - termination proof
------------------------------------------------------------------------
free datatypes and recursive equations are consistent -}
checkFreeType :: (FormExtension f, TermExtension f, Ord f, Hashable f)
  => (Sign f e, [Named (FORMULA f)]) -> Morphism f e m
  -> [Named (FORMULA f)] -> IO (Result (Conservativity, [FORMULA f]))
checkFreeType (_, osens) m axs = do
  let sig = mtarget m
      sSig = imageOfMorphism m
      fs = getFs axs -- strip labels and generated sentences
      (exQuants, fs2) = partition isExQuanti fs
      (memShips, fs3) = partition isMembership fs2
      (sortGens1, axioms) = partition isSortGen fs3
      (freeSortGens, sortGens) = partition isFreeSortGen sortGens1
      (domains, axLessDoms) = partition isDomain axioms
      (genSorts1, cons1) =
        recoverSortsAndConstructors $ getFs osens
      (freeSorts, cons2) =
        recoverSortsAndConstructors freeSortGens
      (genSorts2, cons3) =
        recoverSortsAndConstructors sortGens
      sortCons@(genSorts, cons) =
        (Set.unions
         [freeSorts, genSorts2, Set.map (mapSort $ sort_map m) genSorts1]
        , Set.toList $ Set.unions [cons2, cons3, Set.map (mapOpSymb m) cons1])
      oldSorts = sortSet sSig
      newSorts = Set.difference (sortSet sig) oldSorts
      emptySorts = emptySortSet sig
      nonInhabitedSorts = getNefsorts oldSorts newSorts emptySorts sortCons
      (subsortDefns, memShips2) = partitionMaybe isSubsortDef memShips
      defSubsorts = Set.fromList $ map (\ (s, _, _) -> s) subsortDefns
      dataStatus = getDataStatus newSorts defSubsorts genSorts
      defsForOld = getDefsForOld sSig axioms
      opsPredsAndExAxioms = defsForOld ++ exQuants ++ memShips2
      conStatus = getConStatus dataStatus opsPredsAndExAxioms
      memObl = infoSubsorts emptySorts subsortDefns
      axGroup = groupAxioms sig axLessDoms
      overLaps = getOverlapQuery sig axGroup
      obligations = opsPredsAndExAxioms ++ memObl ++ overLaps
      domSyms = lefts $ mapMaybe leadingSym domains
      ms =
        [ checkDefinitional sig axioms
        , checkSort (null axs) newSorts defSubsorts genSorts2 freeSorts
            nonInhabitedSorts sSig sig
        , checkLeadingTerms sig axioms cons
        , checkIncomplete sig obligations domSyms axGroup cons ]
  r <- case catMaybes ms of
    [] -> checkTerminal sig conStatus obligations domains axLessDoms
    a : _ -> return a
  return $ case r of
    Result ds Nothing ->
      case filter (not . checkPos . sentence) $ axs ++ osens of
        [] -> justHint (Cons, []) "theory is positive!"
        l -> let
          ps = map (\ f -> Diag Hint ("formula is not positive:\n  "
            ++ show (printTheoryFormula $ mapNamed (simplifyCASLSen sig) f))
            $ getRange f) $ take 2 l
          in Result (ps ++ ds) Nothing
    _ -> r

{- | group the axioms according to their leading symbol,
output Nothing if there is some axiom in incorrect form -}
groupAxioms :: GetRange f => Sign f e -> [FORMULA f] -> [[FORMULA f]]
groupAxioms sig phis = map (map snd)
   $ Rel.partList (\ (e1, _) (e2, _) -> case (e1, e2) of
       (Left o1, Left o2) -> sameOpSymbs sig o1 o2
       (Right (Qual_pred_name p1 t1 _), Right (Qual_pred_name p2 t2 _)) ->
           p1 == p2 && on (leqP sig) toPredType t1 t2
       _ -> False)
   $ foldr (\ f -> case leadingSym f of
    Just ei -> ((ei, f) :)
    Nothing -> id) [] phis

-- | return the non-constructor terms of arguments of a leading term
checkTerms :: Sign f e -> [OP_SYMB] -> [TERM f] -> [TERM f]
checkTerms sig cons = concatMap checkT
  where checkT t = case unsortedTerm t of
          Qual_var {} -> []
          Application subop subts _ ->
            if isCons sig cons subop then concatMap checkT subts else [t]
          _ -> [t]

{- | check whether the operation symbol is a constructor
(or a related overloaded variant). -}
isCons :: Sign f e -> [OP_SYMB] -> OP_SYMB -> Bool
isCons sig cons os = any (sameOpSymbs sig os) cons

-- | create all possible pairs from a list
pairs :: [a] -> [(a, a)]
pairs ps = case ps of
  hd : tl@(_ : _) -> map (\ x -> (hd, x)) tl ++ pairs tl
  _ -> []

-- | create the proof obligation for a pair of overlapped formulas
overlapQuery :: GetRange f => FORMULA f -> FORMULA f -> FORMULA f
overlapQuery a1 a2 =
        case leadingSym a1 of
          Just (Left _)
            | containNeg a1 && not (containNeg a2) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg (Definedness resT2 nullRange))
            | containNeg a2 && not (containNeg a1) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg (Definedness resT1 nullRange))
            | containNeg a1 && containNeg a2 -> trueForm
            | otherwise ->
                mkImpl (conjunct [con1, con2])
                            (mkStEq resT1 resT2)
          Just (Right _)
            | containNeg a1 && not (containNeg a2) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg resA2)
            | containNeg a2 && not (containNeg a1) ->
                mkImpl (conjunct [con1, con2])
                            (mkNeg resA1)
            | containNeg a1 && containNeg a2 -> trueForm
            | otherwise ->
                mkImpl (conjunct [con1, con2])
                            (conjunct [resA1, resA2])
          _ -> error "CASL.CCC.FreeTypes.<overlapQuery>"
      where [con1, con2] = map conditionAxiom [a1, a2]
            [resT1, resT2] = map resultTerm [a1, a2]
            [resA1, resA2] = map resultAxiom [a1, a2]

getNotComplete :: (Ord f, FormExtension f, TermExtension f, Hashable f)
  => Sign f e -> [OP_SYMB] -> [[FORMULA f]] -> [OP_SYMB]
  -> [(Result [(String, FORMULA f)], [FORMULA f])]
getNotComplete sig doms fsn constructors =
  let consMap = foldr (\ (Qual_op_name o ot _) ->
        MapSet.insert (res_OP_TYPE ot) (o, ot)) MapSet.empty constructors
      consMap2 = foldr (\ (Qual_op_name o ot _) ->
        MapSet.insert o ot) MapSet.empty constructors
  in
  filter (\ (Result ds mfs, _) -> not (null ds)
      || maybe False (not . null) mfs)
  $ map (\ g ->
         (let l = map topIdOfAxiom g in
                  case Set.toList . Set.fromList $ map fst l of
                    [(p, i)] -> completePatterns sig doms consMap consMap2
                      ([(showId p "", i)]
                      , zip g $ map snd l)
                    l2 -> fail $ "wrongly grouped leading terms "
                      ++ show l2
         , g)) fsn

type LeadArgs = [(String, Int)]

getNextArg :: Bool -> String -> LeadArgs -> (Bool, String, LeadArgs)
getNextArg b p l = case l of
  [] -> (False, if b then p else "_", [])
  h : r -> case h of
    (i, c) -> if c == 0 then (b, i, r) else
      let (b1, sl, r2) = getNextN c b p r
      in (b1, i ++ "(" ++ intercalate ", " sl ++ ")", r2)

getNextN :: Int -> Bool -> String -> LeadArgs -> (Bool, [String], LeadArgs)
getNextN c b p l = if c <= 0 then (b, [], l) else
  let (b1, s, r) = getNextArg b p l
      (b2, sl, r2) = getNextN (c - 1) b1 p r
  in (b2, s : sl, r2)

showLeadingArgs :: String -> LeadArgs -> String
showLeadingArgs p l = let (_, r, _) = getNextArg True p $ reverse l in r

-- | check whether the patterns of a function or predicate are complete
completePatterns :: (Ord f, FormExtension f, TermExtension f, Hashable f) => Sign f e
  -> [OP_SYMB] -> MapSet.MapSet SORT (OP_NAME, OP_TYPE)
  -> MapSet.MapSet OP_NAME OP_TYPE
  -> (LeadArgs, [(FORMULA f, [TERM f])])
  -> Result [(String, FORMULA f)]
completePatterns tsig doms consMap consMap2 (leadingArgs, pas)
    | all (null . snd) pas =
       let fs = checkExhaustive tsig doms $ map fst pas
       in return $ map (\ f -> (showLeadingArgs "" leadingArgs, f)) fs
    | any (null . snd) pas = fail "wrongly grouped leading terms"
    | otherwise = let hds = map (\ (f, hd : _) -> (f, hd)) pas in
            if all (isVar . snd) hds
            then let
              tls = map (\ (f, _ : tl) -> (f, tl)) pas
              in completePatterns tsig doms consMap consMap2
                      (("_", 0) : leadingArgs, tls)
            else let
              consAppls@(_ : _) = mapMaybe (\ (f, t) -> case unsortedTerm t of
                Application (Qual_op_name o ot _) _ _ ->
                  Just (f, o, Set.filter (sameOpTypes tsig ot)
                    $ MapSet.lookup o consMap2)
                _ -> Nothing) hds
              consSrt = foldr1 Set.intersection
                $ map (\ (_, _, os) -> Set.map res_OP_TYPE os) consAppls
              in case filter (not . Set.null . (`MapSet.lookup` consMap))
                     $ Set.toList consSrt of
                  [] -> fail $
                    "no common result type for constructors found: "
                       ++ showDoc (map snd hds) ""
                  cSrt : _ -> do
                    let allCons = MapSet.lookup cSrt consMap
                    when (Set.null allCons) . fail
                      $ "no constructors for result type found: " ++ show cSrt
                    let cons_group = map (\ (c, ct) -> (c, ct,
                          filter (\ (_, h : _) -> case unsortedTerm h of
                            Application (Qual_op_name o ot _) _ _ ->
                              c == o && sameOpTypes tsig ct ot
                            _ -> False) pas)) $ Set.toList allCons
                        vars = filter (\ (_, h : _) -> isVar h) pas
                    ffs <- mapM (\ f -> checkConstructor leadingArgs vars f
                        >>= completePatterns tsig doms consMap consMap2)
                      cons_group
                    return $ concat ffs

mkVars :: [SORT] -> [TERM f]
mkVars = zipWith (\ i -> mkVarTerm (mkSimpleId $ 'c' : show i)) [1 :: Int ..]

checkConstructor :: (Ord f, FormExtension f, TermExtension f)
  => LeadArgs -> [(FORMULA f, [TERM f])]
  -> (Id, OP_TYPE, [(FORMULA f, [TERM f])])
  -> Result (LeadArgs, [(FORMULA f, [TERM f])])
checkConstructor leadingArgs vars (c, ct, es) = do
  let args = args_OP_TYPE ct
      nL = (showId c "", length args) : leadingArgs
      varEqs = map (\ (f, _ : t) -> (f, mkVars args ++ t)) vars
      pat = showLeadingArgs
           (showId c "" ++ case args of
             [] -> ""
             l -> "(" ++ intercalate "," (map (const "_") l) ++ ")")
           leadingArgs
  case es of
    [] -> do
      when (null vars) $ justWarn ()
         $ "missing pattern for: " ++ pat
      return (nL, varEqs)
    _ ->
      return (nL, varEqs ++ map (\ (f, h : t) -> (f, arguOfTerm h ++ t)) es)

-- | get condition axiom without matching definedness condition
getCond :: (GetRange f, Eq f) => Sign f e -> [OP_SYMB] -> FORMULA f -> FORMULA f
getCond sig doms f =
  let (cs, e) = splitAxiom f
  in conjunct $ filter (\ c -> case leadingTermPredication e of
       l@(Just (Left (Application os _ _)))
         | any (sameOpSymbs sig os) doms
         -> case c of  -- pattern term must be identical
              Definedness {} | leadingTermPredication c == l -> False
              _ -> True
       _ -> True) cs

checkExhaustive :: (Ord f, FormExtension f, TermExtension f, Hashable f)
  => Sign f e -> [OP_SYMB] -> [FORMULA f] -> [FORMULA f]
checkExhaustive sig doms es = case es of
  f1 : rs ->
    let sfs = map (\ f -> (getSubstForm sig f1 f, f)) rs
        overlap = filter (isJust . maybeResult . fst) sfs
        simpAndQuant = quant sig . simplifyFormula id
    in case overlap of
       [] -> filter (not . is_True_atom)
          (map (simpAndQuant . getCond sig doms) [f1])
          ++ checkExhaustive sig doms rs
       (r, f2) : rrs -> let
          (f3, f4, ((s3, _), (s4, _))) = convert2Forms sig f1 f2 r
          in checkExhaustive sig doms
         $ (simpAndQuant
         . mkImpl (disjunct [ replaceVarsF s3 id $ getCond sig doms f3
                            , replaceVarsF s4 id $ getCond sig doms f4 ])
           . replaceVarsF s3 id $ restAxiom f3) : map snd rrs
  [] -> []
