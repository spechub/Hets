{- |
Module      :  ./CASL/Overload.hs
Description :  Overload resolution
Copyright   :  (c) Martin Kuehl, T. Mossakowski, C. Maeder, 2004-2007
License     :  GPLv2 or higher, see LICENSE.txt

Maintainer  :  Christian.Maeder@dfki.de
Stability   :  provisional
Portability :  portable

Overload resolution (injections are inserted separately)
    Follows Sect. III:3.3 of the CASL Reference Manual.
    The algorthim is from:
      Till Mossakowski, Kolyang, Bernd Krieg-Brueckner:
      Static semantic analysis and theorem proving for CASL.
      12th Workshop on Algebraic Development Techniques, Tarquinia 1997,
      LNCS 1376, p. 333-348
-}

module CASL.Overload
  ( minExpFORMULA
  , minExpFORMULAeq
  , minExpTerm
  , isUnambiguous
  , oneExpTerm
  , mkSorted
  , Min
  , leqF
  , leqP
  , leqSort
  , minimalSupers
  , maximalSubs
  , haveCommonSupersorts
  , haveCommonSubsorts
  , keepMinimals1
  , keepMinimals
  ) where

import CASL.ToDoc (FormExtension)
import CASL.Sign
import CASL.AS_Basic_CASL

import qualified Common.Lib.MapSet as MapSet
import qualified Common.Lib.Rel as Rel
import Common.Lib.State
import Common.Id
import Common.GlobalAnnotations
import Common.DocUtils
import Common.Result
import Common.Partial
import Common.Utils

import Data.List
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Monad

-- | the type of the type checking function of extensions
type Min f e = Sign f e -> f -> Result f

mkSorted :: TermExtension f => Sign f e -> TERM f -> SORT -> Range -> TERM f
mkSorted sign t s r = let nt = Sorted_term t s r in case optTermSort t of
  Nothing -> nt
  Just srt -> if leqSort sign s srt then t else nt

{- ----------------------------------------------------------
    - Minimal expansion of a formula -
  Expand a given formula by typing information.
  * For non-atomic formulae, recurse through subsentences.
  * For trival atomic formulae, no expansion is neccessary.
  * For atomic formulae, the following cases are implemented:
    + Predication is handled by the dedicated expansion function
      'minExpFORMULApred'.
    + Existl_equation and Strong_equation are handled by the dedicated
      expansion function 'minExpFORMULAeq'.
    + Definedness is handled by expanding the subterm.
    + Membership is handled like Cast
---------------------------------------------------------- -}
minExpFORMULA
  :: (FormExtension f, TermExtension f)
   => Min f e -> Sign f e -> FORMULA f -> Result (FORMULA f)
minExpFORMULA mef sign formula = let sign0 = sign { envDiags = [] } in
  case formula of
    Quantification q vars f pos -> do
        -- add 'vars' to signature
        let sign' = execState (mapM_ addVars vars) sign0
        Result (envDiags sign') $ Just ()
        f' <- minExpFORMULA mef sign' f
        return (Quantification q vars f' pos)
    Junction j fs pos -> do
        fs' <- mapR (minExpFORMULA mef sign) fs
        return (Junction j fs' pos)
    Relation f1 c f2 pos ->
        joinResultWith (\ f1' f2' -> Relation f1' c f2' pos)
              (minExpFORMULA mef sign f1) $ minExpFORMULA mef sign f2
    Negation f pos -> do
        f' <- minExpFORMULA mef sign f
        return (Negation f' pos)
    Predication (Pred_name ide) terms pos
        -> minExpFORMULApred mef sign ide Nothing terms pos
    Predication (Qual_pred_name ide ty pos1) terms pos2
        -> minExpFORMULApred mef sign ide (Just $ toPredType ty)
           terms (pos1 `appRange` pos2)
    Equation term1 e term2 pos
        -> minExpFORMULAeq mef sign (`Equation` e) term1 term2 pos
    Definedness term pos -> do
        t <- oneExpTerm mef sign term
        return (Definedness t pos)
    Membership term srt pos -> do
        ts <- minExpTerm mef sign term
        let fs = map (concatMap ( \ t ->
                    map ( \ c ->
                        Membership (mkSorted sign t c pos) srt pos)
                    $ maybe [srt] (minimalSupers sign srt)
                    $ optTermSort t)) ts
            msg = superSortError True sign srt ts
        isUnambiguous msg (globAnnos sign) formula fs pos
    ExtFORMULA f -> fmap ExtFORMULA $ mef sign f
    QuantOp o ty f -> do
        let sign' = sign0 { opMap = addOpTo o (toOpType ty) $ opMap sign0 }
        Result (envDiags sign') $ Just ()
        f' <- minExpFORMULA mef sign' f
        return $ QuantOp o ty f'
    QuantPred p ty f -> do
        let pm = predMap sign0
            sign' = sign0
              { predMap = MapSet.insert p (toPredType ty) pm }
        Result (envDiags sign') $ Just ()
        f' <- minExpFORMULA mef sign' f
        return $ QuantPred p ty f'
    Mixfix_formula term -> do
       t <- oneExpTerm mef sign term
       let Result ds mt = adjustPos (getRangeSpan term) $ termToFormula t
       appendDiags ds
       case mt of
         Nothing -> mkError "not a formula" term
         Just f -> return f
    _ -> return formula -- do not fail even for unresolved cases

superSortError :: TermExtension f
  => Bool -> Sign f e -> SORT -> [[TERM f]] -> String
superSortError super sign srt ts = let
  ds = keepMinimals sign id . map sortOfTerm $ concat ts
  in "\n" ++ showSort ds ++ "found but\na "
     ++ (if super then "super" else "sub") ++ "sort of '"
              ++ shows srt "' was expected."

-- | test if a term can be uniquely resolved
oneExpTerm :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> TERM f -> Result (TERM f)
oneExpTerm minF sign term = do
    ts <- minExpTerm minF sign term
    isUnambiguous "" (globAnnos sign) term ts nullRange

{- ----------------------------------------------------------
    - Minimal expansion of an equation formula -
  see minExpTermCond
---------------------------------------------------------- -}
minExpFORMULAeq :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> (TERM f -> TERM f -> Range -> FORMULA f)
    -> TERM f -> TERM f -> Range -> Result (FORMULA f)
minExpFORMULAeq mef sign eq term1 term2 pos = do
    (ps, msg) <- minExpTermCond mef sign ( \ t1 t2 -> eq t1 t2 pos)
          term1 term2 pos
    isUnambiguous msg (globAnnos sign) (eq term1 term2 pos) ps pos

-- | check if there is at least one solution
hasSolutions :: Pretty f => String -> GlobalAnnos -> f -> [[f]] -> Range
             -> Result [[f]]
hasSolutions msg ga topterm ts pos = let terms = filter (not . null) ts in
   if null terms then Result
    [Diag Error ("no typing for: " ++ showGlobalDoc ga topterm "" ++ msg)
          pos] Nothing
    else return terms

-- | check if there is a unique equivalence class
isUnambiguous :: Pretty f => String -> GlobalAnnos -> f -> [[f]] -> Range
  -> Result f
isUnambiguous msg ga topterm ts pos = do
    terms <- hasSolutions msg ga topterm ts pos
    case terms of
        [ term : _ ] -> return term
        _ -> Result [Diag Error ("ambiguous term\n  " ++
                showSepList (showString "\n  ") (showGlobalDoc ga)
                (take 5 $ map head terms) "") pos] Nothing

checkIdAndArgs :: Id -> [a] -> Range -> Result Int
checkIdAndArgs ide args poss =
    let nargs = length args
        pargs = placeCount ide
    in if isMixfix ide && pargs /= nargs then
    Result [Diag Error
       ("expected " ++ shows pargs " argument(s) of mixfix identifier '"
         ++ showDoc ide "' but found " ++ shows nargs " argument(s)")
       poss] Nothing
    else return nargs

noOpOrPredDiag :: Pretty t => [a] -> DiagKind -> String -> Maybe t -> Id
  -> Range -> Int -> [Diagnosis]
noOpOrPredDiag ops k str mty ide pos nargs = case ops of
  [] -> let
    hd = "no " ++ str ++ " with "
    ft = " found for '" ++ showDoc ide "'"
    in [Diag k (case mty of
      Nothing -> hd ++ shows nargs " argument"
               ++ (if nargs == 1 then "" else "s") ++ ft
      Just ty -> hd ++ "profile '" ++ showDoc ty "'" ++ ft) pos]
  _ -> []

noOpOrPred :: Pretty t => [a] -> String -> Maybe t -> Id -> Range -> Int
  -> Result ()
noOpOrPred ops str mty ide pos nargs = when (null ops) $ Result
      (noOpOrPredDiag ops Error str mty ide pos nargs) Nothing

{- ----------------------------------------------------------
    - Minimal expansion of a predication formula -
    see minExpTermAppl
---------------------------------------------------------- -}
minExpFORMULApred :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> Id -> Maybe PredType -> [TERM f] -> Range
    -> Result (FORMULA f)
minExpFORMULApred mef sign ide mty args pos = do
    nargs <- checkIdAndArgs ide args pos
    let -- predicates matching that name in the current environment
        preds' = Set.filter ((nargs ==) . length . predArgs) $
              MapSet.lookup ide $ predMap sign
        preds = case mty of
                   Nothing -> map (pSortBy predArgs sign)
                              $ Rel.leqClasses (leqP' sign) preds'
                   Just ty -> [[ty] | Set.member ty preds']
        boolAna l cmd = case mty of
          Nothing | null l -> do
            appendDiags $ noOpOrPredDiag preds Hint
              "matching predicate" mty ide pos nargs
            minExpFORMULA mef sign $ Mixfix_formula
              $ Application (Op_name ide) args pos
          _ -> cmd
    boolAna preds $ do
      noOpOrPred preds "predicate" mty ide pos nargs
      tts <- mapM (minExpTerm mef sign) args
      let (goodCombs, msg) = getAllCombs sign nargs ide predArgs preds tts
          qualForms = qualifyGFs qualifyPred ide pos goodCombs
      boolAna qualForms
        $ isUnambiguous msg (globAnnos sign)
              (Predication (Pred_name ide) args pos) qualForms pos

showSort :: [SORT] -> String
showSort s = case s of
         [ft] -> "a term of sort '" ++ shows ft "' was "
         _ -> "terms of sorts " ++ showDoc s " were "

missMsg :: Bool -> Int -> Id -> [[SORT]] -> [SORT] -> [SORT] -> String
missMsg singleArg maxArg ide args foundTs expectedTs =
  "\nin the "
  ++ (if singleArg then "" else show (maxArg + 1) ++ ". ")
  ++ "argument of '" ++ show ide
  ++ (if singleArg then "'\n" else case args of
       [arg] -> " : " ++ showDoc (PredType arg) "'\n"
       _ -> "'\n  with argument sorts " ++ showDoc (map PredType args) "\n")
  ++ showSort foundTs ++ "found but\n"
  ++ showSort expectedTs ++ "expected."

getAllCombs :: TermExtension f => Sign f e -> Int -> Id -> (a -> [SORT])
  -> [[a]] -> [[[TERM f]]] -> ([[(a, [TERM f], Maybe Int)]], String)
getAllCombs sign nargs ide getArgs fs expansions =
      let formCombs = concatMap (getCombs sign getArgs fs . combine)
            $ combine expansions
          partCombs = map (partition $ \ (_, _, m) -> isNothing m) formCombs
          (goodCombs, badCombs) = unzip partCombs
          badCs = concat badCombs
      in if null badCs then (goodCombs, "") else let
          maxArg = maximum $ map (\ (_, _, Just c) -> c) badCs
          badCs2 = filter (\ (_, _, Just c) -> maxArg == c) badCs
          args = Set.toList . Set.fromList
            $ map (\ (a, _, _) -> getArgs a) badCs2
          foundTs = keepMinimals sign id
            $ map (\ (_, ts, _) -> sortOfTerm $ ts !! maxArg) badCs2
          expectedTs = keepMinimals1 False sign id $ map (!! maxArg) args
      in (goodCombs, missMsg (nargs == 1) maxArg ide args foundTs expectedTs)

getCombs :: TermExtension f => Sign f e -> (a -> [SORT]) -> [[a]] -> [[TERM f]]
  -> [[(a, [TERM f], Maybe Int)]]
getCombs sign getArgs = flip $ map . \ cs fs ->
  [ (f, ts, elemIndex False $ zipWith (leqSort sign) (map sortOfTerm ts)
            $ getArgs f) | f <- fs, ts <- cs ]

qualifyGFs :: (Id -> Range -> (a, [TERM f]) -> b) -> Id -> Range
  -> [[(a, [TERM f], Maybe Int)]] -> [[b]]
qualifyGFs f ide pos = map $ map (f ide pos . \ (a, b, _) -> (a, b))

-- | qualify a single pred, given by its signature and its arguments
qualifyPred :: Id -> Range -> (PredType, [TERM f]) -> FORMULA f
qualifyPred ide pos (pred', terms') =
    Predication (Qual_pred_name ide (toPRED_TYPE pred') pos) terms' pos

-- | expansions of an equation formula or a conditional
minExpTermEq :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> TERM f -> TERM f -> Result [[(TERM f, TERM f)]]
minExpTermEq mef sign term1 term2 = do
    exps1 <- minExpTerm mef sign term1
    exps2 <- minExpTerm mef sign term2
    return $ map (minimizeEq sign . getPairs) $ combine [exps1, exps2]

getPairs :: [[TERM f]] -> [(TERM f, TERM f)]
getPairs cs = [ (t1, t2) | [t1, t2] <- combine cs ]

minimizeEq :: TermExtension f => Sign f e -> [(TERM f, TERM f)]
           -> [(TERM f, TERM f)]
minimizeEq s = keepMinimals s (sortOfTerm . snd)
  . keepMinimals s (sortOfTerm . fst)

{- ----------------------------------------------------------
    - Minimal expansion of a term -
  Expand a given term by typing information.
  * 'Qual_var' terms are handled by 'minExpTerm_var'
  * 'Application' terms are handled by 'minExpTermOp'.
  * 'Conditional' terms are handled by 'minExpTermCond'.
---------------------------------------------------------- -}
minExpTerm :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> TERM f -> Result [[TERM f]]
minExpTerm mef sign top = let ga = globAnnos sign in case top of
    Qual_var var srt _ -> let ts = minExpTermVar sign var (Just srt) in
        if null ts then mkError "no matching qualified variable found" var
        else return ts
    Application op terms pos -> minExpTermOp mef sign op terms pos
    Sorted_term term srt pos -> do
      expandedTerm <- minExpTerm mef sign term
      -- choose expansions that fit the given signature, then qualify
      let validExps =
              map (filter (maybe True (flip (leqSort sign) srt)
                                   . optTermSort))
                      expandedTerm
          msg = superSortError False sign srt expandedTerm
      hasSolutions msg ga top (map (map (\ t ->
                 Sorted_term t srt pos)) validExps) pos
    Cast term srt pos -> do
      expandedTerm <- minExpTerm mef sign term
      -- find a unique minimal common supersort
      let ts = map (concatMap (\ t ->
                    map ( \ c ->
                        Cast (mkSorted sign t c pos) srt pos)
                    $ maybe [srt] (minimalSupers sign srt)
                    $ optTermSort t)) expandedTerm
          msg = superSortError True sign srt expandedTerm
      hasSolutions msg ga top ts pos
    Conditional term1 formula term2 pos -> do
      f <- minExpFORMULA mef sign formula
      (ts, msg) <- minExpTermCond mef sign ( \ t1 t2 -> Conditional t1 f t2 pos)
            term1 term2 pos
      hasSolutions msg ga (Conditional term1 formula term2 pos) ts pos
    ExtTERM t -> do
      nt <- mef sign t
      return [[ExtTERM nt]]
    _ -> mkError "unexpected kind of term" top

-- | Minimal expansion of a possibly qualified variable identifier
minExpTermVar :: Sign f e -> Token -> Maybe SORT -> [[TERM f]]
minExpTermVar sign tok ms = case Map.lookup tok $ varMap sign of
    Nothing -> []
    Just s -> let qv = [[Qual_var tok s nullRange]] in
              case ms of
              Nothing -> qv
              Just s2 -> if s == s2 then qv else []

-- | minimal expansion of an (possibly qualified) operator application
minExpTermAppl :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> Id -> Maybe OpType -> [TERM f] -> Range
    -> Result [[TERM f]]
minExpTermAppl mef sign ide mty args pos = do
    nargs <- checkIdAndArgs ide args pos
    let -- functions matching that name in the current environment
        ops' = Set.filter ( \ o -> length (opArgs o) == nargs) $
              MapSet.lookup ide $ opMap sign
        ops = case mty of
                   Nothing -> map (pSortBy opArgs sign)
                              $ Rel.leqClasses (leqF' sign) ops'
                   Just ty -> [[ty] | Set.member ty ops' ||
                                  -- might be known to be total
                                 Set.member (mkTotal ty) ops' ]
    noOpOrPred ops "operation" mty ide pos nargs
    expansions <- mapM (minExpTerm mef sign) args
    let  -- generate profiles as descr. on p. 339 (Step 3)
        (goodCombs, msg) = getAllCombs sign nargs ide opArgs ops expansions
        qualTerms = qualifyGFs qualifyOp ide pos
                    $ map (minimizeOp sign) goodCombs
    hasSolutions msg (globAnnos sign)
        (Application (Op_name ide) args pos) qualTerms pos

    -- qualify a single op, given by its signature and its arguments
qualifyOp :: Id -> Range -> (OpType, [TERM f]) -> TERM f
qualifyOp ide pos (op', terms') =
    Application (Qual_op_name ide (toOP_TYPE op') pos) terms' pos

{- ----------------------------------------------------------
    - Minimal expansion of a function application or a variable -
  Expand a function application by typing information.
  1. First expand all argument subterms.
  2. Combine these expansions so we compute the set of tuples
    { (C_1, ..., C_n) | (C_1, ..., C_n) \in
                        minExpTerm(t_1) x ... x minExpTerm(t_n) }
    where t_1, ..., t_n are the given argument terms.
  3. For each element of this set compute the set of possible profiles
    (as described on p. 339).
  4. Define an equivalence relation ~ on these profiles
    (as described on p. 339).
  5. Separate each profile into equivalence classes by the relation ~
    and take the unification of these sets.
  6. Minimize each element of this unified set (as described on p. 339).
  7. Transform each term in the minimized set into a qualified function
    application term.
---------------------------------------------------------- -}
minExpTermOp :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> OP_SYMB -> [TERM f] -> Range -> Result [[TERM f]]
minExpTermOp mef sign osym args pos = case osym of
  Op_name ide@(Id ts _ _) ->
    let res = minExpTermAppl mef sign ide Nothing args pos in
      if null args && isSimpleId ide then
          let vars = minExpTermVar sign (head ts) Nothing
          in if null vars then res else
             case maybeResult res of
             Nothing -> return vars
             Just ops -> return $ ops ++ vars
      else res
  Qual_op_name ide ty pos1 ->
   if length args /= length (args_OP_TYPE ty) then
      mkError "type qualification does not match number of arguments" ide
   else minExpTermAppl mef sign ide (Just $ toOpType ty) args
        (pos1 `appRange` pos)

{- ----------------------------------------------------------
    - Minimal expansion of a conditional -
  Expand a conditional by typing information (see minExpTermEq)
  First expand the subterms and subformula. Then calculate a profile
  P(C_1, C_2) for each (C_1, C_2) \in minExpTerm(t1) x minExpTerm(t_2).
  Separate these profiles into equivalence classes and take the
  unification of all these classes. Minimize each equivalence class.
  Finally transform the eq. classes into lists of
  conditionals with equally sorted terms.
---------------------------------------------------------- -}
minExpTermCond :: (FormExtension f, TermExtension f)
  => Min f e -> Sign f e -> (TERM f -> TERM f -> a) -> TERM f -> TERM f
    -> Range -> Result ([[a]], String)
minExpTermCond mef sign f term1 term2 pos = do
    pairs <- minExpTermEq mef sign term1 term2
    let (lhs, rhs) = unzip $ concat pairs
        mins = keepMinimals sign id . map sortOfTerm
        ds = "\n" ++ showSort (mins lhs) ++ "on the lhs but\n"
          ++ showSort (mins rhs) ++ "on the rhs."
    return (map (concatMap ( \ (t1, t2) ->
              let s1 = sortOfTerm t1
                  s2 = sortOfTerm t2
              in map ( \ s -> f (mkSorted sign t1 s pos)
                                (mkSorted sign t2 s pos))
                   $ minimalSupers sign s1 s2)) pairs, ds)

{- ----------------------------------------------------------
    Let P be a set of equivalence classes of qualified terms.
    For each C \in P, let C' choose _one_
    t:s \in C for each s minimal such that t:s \in C.
    That is, discard all terms whose sort is a supersort of
    any other term in the same equivalence class.
---------------------------------------------------------- -}
minimizeOp :: Sign f e -> [(OpType, [TERM f], a)] -> [(OpType, [TERM f], a)]
minimizeOp sign = keepMinimals sign (opRes . \ (a, _, _) -> a)

-- | the (possibly incomplete) list of supersorts common to both sorts
commonSupersorts :: Bool -> Sign f e -> SORT -> SORT -> [SORT]
commonSupersorts b sign s1 s2 =
    if s1 == s2 then [s1] else
    let l1 = supersortsOf s1 sign
        l2 = supersortsOf s2 sign in
    if Set.member s2 l1 then if b then [s2] else [s1] else
    if Set.member s1 l2 then if b then [s1] else [s2] else
    Set.toList $ if b then Set.intersection l1 l2
                 else Set.intersection (subsortsOf s1 sign)
                             $ subsortsOf s2 sign

-- | True if both sorts have a common supersort
haveCommonSupersorts :: Bool -> Sign f e -> SORT -> SORT -> Bool
haveCommonSupersorts b s s1 = not . null . commonSupersorts b s s1

-- True if both sorts have a common subsort
haveCommonSubsorts :: Sign f e -> SORT -> SORT -> Bool
haveCommonSubsorts = haveCommonSupersorts False

-- | if True test if s1 > s2
geqSort :: Bool -> Sign f e -> SORT -> SORT -> Bool
geqSort b sign s1 s2 = s1 == s2 || let rel = sortRel sign in
    if b then Rel.member s2 s1 rel else Rel.member s1 s2 rel

-- | test if s1 < s2
leqSort :: Sign f e -> SORT -> SORT -> Bool
leqSort = geqSort False

-- | minimal common supersorts of the two input sorts
minimalSupers :: Sign f e -> SORT -> SORT -> [SORT]
minimalSupers = minimalSupers1 True

minimalSupers1 :: Bool -> Sign f e -> SORT -> SORT -> [SORT]
minimalSupers1 b s s1 = keepMinimals1 b s id . commonSupersorts b s s1

-- | maximal common subsorts of the two input sorts
maximalSubs :: Sign f e -> SORT -> SORT -> [SORT]
maximalSubs = minimalSupers1 False

-- | only keep elements with minimal (and different) sorts
keepMinimals :: Sign f e -> (a -> SORT) -> [a] -> [a]
keepMinimals = keepMinimals1 True

keepMinimals1 :: Bool -> Sign f e -> (a -> SORT) -> [a] -> [a]
keepMinimals1 b s f = let lt x y = geqSort b s (f y) (f x) in keepMins lt

-- | True if both ops are in the overloading relation
leqF :: Sign f e -> OpType -> OpType -> Bool
leqF sign o1 o2 = length (opArgs o1) == length (opArgs o2) && leqF' sign o1 o2

leqF' :: Sign f e -> OpType -> OpType -> Bool
leqF' sign o1 o2 = haveCommonSupersorts True sign (opRes o1) (opRes o2) &&
    and (zipWith (haveCommonSubsorts sign) (opArgs o1) (opArgs o2))

-- | True if both preds are in the overloading relation
leqP :: Sign f e -> PredType -> PredType -> Bool
leqP sign p1 p2 = length (predArgs p1) == length (predArgs p2)
                  && leqP' sign p1 p2

leqP' :: Sign f e -> PredType -> PredType -> Bool
leqP' sign p1 =
    and . zipWith (haveCommonSubsorts sign) (predArgs p1) . predArgs

cmpSubsort :: Sign f e -> POrder SORT
cmpSubsort sign s1 s2 =
    if s1 == s2 then Just EQ else
    let l1 = supersortsOf s1 sign
        l2 = supersortsOf s2 sign
        b = Set.member s1 l2 in
    if Set.member s2 l1 then
        Just $ if b then EQ else LT
    else if b then Just GT else Nothing

cmpSubsorts :: Sign f e -> POrder [SORT]
cmpSubsorts sign l1 l2 =
    let l = zipWith (cmpSubsort sign) l1 l2
    in if null l then Just EQ else foldr1
       ( \ c1 c2 -> if c1 == c2 then c1 else case (c1, c2) of
           (Just EQ, _) -> c2
           (_, Just EQ) -> c1
           _ -> Nothing) l

pSortBy :: (a -> [SORT]) -> Sign f e -> [a] -> [a]
pSortBy f sign = let pOrd a b = cmpSubsorts sign (f a) (f b)
                 in concat . rankBy pOrd
