{- |
Module      :  $Header$
Description :  Overload resolution
Copyright   :  (c) Martin Kuehl, T. Mossakowski, C. Maeder, 2004-2007
License     :  similar to LGPL, see HetCATS/LICENSE.txt or LIZENZ.txt

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
  , oneExpTerm
  , Min
  , combine
  , is_unambiguous
  , leqF
  , leqP
  , leq_SORT
  , minimalSupers
  , maximalSubs
  , have_common_supersorts
  , keepMinimals1
  , keepMinimals
  , leqClasses
  ) where

import CASL.Sign
import CASL.AS_Basic_CASL

import qualified Common.Lib.Rel as Rel
import qualified Data.Map as Map
import qualified Data.Set as Set
import Common.Lib.State
import Common.Id
import Common.GlobalAnnotations
import Common.DocUtils
import Common.Result
import Common.Partial
import Common.Utils

-- | the type of the type checking function of extensions
type Min f e = Sign f e -> f -> Result f

{-----------------------------------------------------------
    - Minimal expansion of a formula -
  Expand a given formula by typing information.
  * For non-atomic formulae, recurse through subsentences.
  * For trival atomic formulae, no expansion is neccessary.
  * For atomic formulae, the following cases are implemented:
    + Predication is handled by the dedicated expansion function
      'minExpFORMULA_pred'.
    + Existl_equation and Strong_equation are handled by the dedicated
      expansion function 'minExpFORMULA_eq'.
    + Definedness is handled by expanding the subterm.
    + Membership is handled like Cast
-----------------------------------------------------------}
minExpFORMULA :: (GetRange f, Pretty f) => Min f e -> Sign f e -> FORMULA f
              -> Result (FORMULA f)
minExpFORMULA mef sign formula = case formula of
    Quantification q vars f pos -> do
        -- add 'vars' to signature
        let (_, sign') = runState (mapM_ addVars vars) sign { envDiags = [] }
        Result (envDiags sign') $ Just ()
        -- expand subformula
        f' <- minExpFORMULA mef sign' f
        return (Quantification q vars f' pos)
    Conjunction fs pos -> do
        fs' <- mapR (minExpFORMULA mef sign) fs
        return (Conjunction fs' pos)
    Disjunction fs pos -> do
        fs' <- mapR (minExpFORMULA mef sign) fs
        return (Disjunction fs' pos)
    Implication f1 f2 b pos ->
        joinResultWith (\ f1' f2' -> Implication f1' f2' b pos)
              (minExpFORMULA mef sign f1) $ minExpFORMULA mef sign f2
    Equivalence f1 f2 pos ->
        joinResultWith (\ f1' f2' -> Equivalence f1' f2' pos)
              (minExpFORMULA mef sign f1) $ minExpFORMULA mef sign f2
    Negation f pos -> do
        f' <- minExpFORMULA mef sign f
        return (Negation f' pos)
    Predication (Pred_name ide) terms pos
        -> minExpFORMULA_pred mef sign ide Nothing terms pos
    Predication (Qual_pred_name ide ty pos1) terms pos2
        -> minExpFORMULA_pred mef sign ide (Just $ toPredType ty)
           terms (pos1 `appRange` pos2)
    Existl_equation term1 term2 pos
        -> minExpFORMULA_eq mef sign Existl_equation term1 term2 pos
    Strong_equation term1 term2 pos
        -> minExpFORMULA_eq mef sign Strong_equation term1 term2 pos
    Definedness term pos -> do
        t <- oneExpTerm mef sign term
        return (Definedness t pos)
    Membership term sort pos -> do
        ts   <- minExpTerm mef sign term
        let fs = map (concatMap ( \ t ->
                    let s = sortOfTerm t in
                    if leq_SORT sign sort s then
                    [Membership t sort pos] else
                    map ( \ c ->
                        Membership (Sorted_term t c pos) sort pos)
                    $ minimalSupers sign s sort)) ts
        is_unambiguous (globAnnos sign) formula fs pos
    ExtFORMULA f -> fmap ExtFORMULA $ mef sign f
    _ -> return formula -- do not fail even for unresolved cases

-- | test if a term can be uniquely resolved
oneExpTerm :: (GetRange f, Pretty f) => Min f e -> Sign f e
           -> TERM f -> Result (TERM f)
oneExpTerm minF sign term = do
    ts <- minExpTerm minF sign term
    is_unambiguous (globAnnos sign) term ts nullRange

{-----------------------------------------------------------
    - Minimal expansion of an equation formula -
  see minExpTerm_cond
-----------------------------------------------------------}
minExpFORMULA_eq :: (GetRange f, Pretty f) => Min f e -> Sign f e
                 -> (TERM f -> TERM f -> Range -> FORMULA f)
                 -> TERM f -> TERM f -> Range -> Result (FORMULA f)
minExpFORMULA_eq mef sign eq term1 term2 pos = do
    ps <- minExpTerm_cond mef sign ( \ t1 t2 -> eq t1 t2 pos)
          term1 term2 pos
    is_unambiguous (globAnnos sign) (eq term1 term2 pos) ps pos

-- | check if there is at least one solution
hasSolutions :: Pretty f => GlobalAnnos -> f -> [[f]] -> Range
             -> Result [[f]]
hasSolutions ga topterm ts pos = let terms = filter (not . null) ts in
   if null terms then Result
    [Diag Error ("no typing for: " ++ showGlobalDoc ga topterm "")
          pos] Nothing
    else return terms

-- | check if there is a unique equivalence class
is_unambiguous :: Pretty f => GlobalAnnos -> f -> [[f]] -> Range
               -> Result f
is_unambiguous ga topterm ts pos = do
    terms <- hasSolutions ga topterm ts pos
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


noOpOrPred :: Pretty t => [a] -> String -> Maybe t -> Id -> Range
           -> Int -> Result ()
noOpOrPred ops str mty ide pos nargs =
    if null ops then case mty of
           Nothing -> Result [Diag Error
             ("no " ++ str ++ " with " ++ shows nargs " argument"
              ++ (if nargs == 1 then "" else "s") ++ " found for '"
              ++ showDoc ide "'") pos] Nothing
           Just ty -> Result [Diag Error
             ("no " ++ str ++ " with profile '"
              ++ showDoc ty "' found for '"
              ++ showDoc ide "'") pos] Nothing
       else return ()

{-----------------------------------------------------------
    - Minimal expansion of a predication formula -
    see minExpTerm_appl
-----------------------------------------------------------}
minExpFORMULA_pred :: (GetRange f, Pretty f) => Min f e -> Sign f e -> Id
                   -> Maybe PredType -> [TERM f] -> Range
                   -> Result (FORMULA f)
minExpFORMULA_pred mef sign ide mty args pos = do
    nargs <- checkIdAndArgs ide args pos
    let -- predicates matching that name in the current environment
        preds' = Set.filter ( \ p -> length (predArgs p) == nargs) $
              Map.findWithDefault Set.empty ide $ predMap sign
        preds = case mty of
                   Nothing -> map (pSortBy predArgs sign)
                              $ leqClasses (leqP' sign) preds'
                   Just ty -> if Set.member ty preds'
                              then [[ty]] else []
    noOpOrPred preds "predicate" mty ide pos nargs
    expansions <- mapM (minExpTerm mef sign) args
    let get_profiles :: [[TERM f]] -> [[(PredType, [TERM f])]]
        get_profiles cs = map (get_profile cs) preds
        get_profile :: [[TERM f]] -> [PredType] -> [(PredType, [TERM f])]
        get_profile cs ps = [ (pred', ts) |
                             pred' <- ps,
                             ts <- cs,
                             and $ zipWith (leq_SORT sign)
                             (map sortOfTerm ts)
                             (predArgs pred') ]
        qualForms = qualifyPreds ide pos
                       $ concatMap (get_profiles . combine)
                       $ combine expansions
    is_unambiguous (globAnnos sign)
                       (Predication (Pred_name ide) args pos) qualForms pos

qualifyPreds :: Id -> Range -> [[(PredType, [TERM f])]] -> [[FORMULA f]]
qualifyPreds ide pos = map $ map $ qualify_pred ide pos

-- | qualify a single pred, given by its signature and its arguments
qualify_pred :: Id -> Range -> (PredType, [TERM f]) -> FORMULA f
qualify_pred ide pos (pred', terms') =
    Predication (Qual_pred_name ide (toPRED_TYPE pred') pos) terms' pos

-- | expansions of an equation formula or a conditional
minExpTerm_eq :: (GetRange f, Pretty f) =>  Min f e -> Sign f e -> TERM f
              -> TERM f -> Result [[(TERM f, TERM f)]]
minExpTerm_eq mef sign term1 term2 = do
    exps1 <- minExpTerm mef sign term1
    exps2 <- minExpTerm mef sign term2
    return $ map (minimize_eq sign)
           $ map getPairs $ combine [exps1, exps2]

getPairs :: [[TERM f]] -> [(TERM f, TERM f)]
getPairs cs = [ (t1, t2) | [t1,t2] <- combine cs ]

minimize_eq :: Sign f e -> [(TERM f, TERM f)] -> [(TERM f, TERM f)]
minimize_eq s = keepMinimals s (sortOfTerm . snd)
  . keepMinimals s (sortOfTerm . fst)

{-----------------------------------------------------------
    - Minimal expansion of a term -
  Expand a given term by typing information.
  * 'Qual_var' terms are handled by 'minExpTerm_var'
  * 'Application' terms are handled by 'minExpTerm_op'.
  * 'Conditional' terms are handled by 'minExpTerm_cond'.
-----------------------------------------------------------}
minExpTerm :: (GetRange f, Pretty f) => Min f e -> Sign f e -> TERM f
           -> Result [[TERM f]]
minExpTerm mef sign top = let ga = globAnnos sign in case top of
    Qual_var var sort _ -> let ts = minExpTerm_var sign var (Just sort) in
        if null ts then mkError "no matching qualified variable found" var
        else return ts
    Application op terms pos -> minExpTerm_op mef sign op terms pos
    Sorted_term term sort pos -> do
      expandedTerm <- minExpTerm mef sign term
      -- choose expansions that fit the given signature, then qualify
      let validExps = map (filter $ \ t -> leq_SORT sign (sortOfTerm t) sort)
                      expandedTerm
      hasSolutions ga top (map (map (\ t ->
                 Sorted_term t sort pos)) validExps) pos
    Cast term sort pos -> do
      expandedTerm <- minExpTerm mef sign term
      -- find a unique minimal common supersort
      let ts = map (concatMap (\ t -> let s = sortOfTerm t in
                    if leq_SORT sign sort s then
                    if leq_SORT sign s sort then [t] else
                    [Cast t sort pos] else
                    map ( \ c ->
                        Cast (Sorted_term t c pos) sort pos)
                    $ minimalSupers sign s sort)) expandedTerm
      hasSolutions ga top ts pos
    Conditional term1 formula term2 pos -> do
      f <- minExpFORMULA mef sign formula
      ts <- minExpTerm_cond mef sign ( \ t1 t2 -> Conditional t1 f t2 pos)
            term1 term2 pos
      hasSolutions ga (Conditional term1 formula term2 pos) ts pos
    _ -> mkError "unexpected kind of term" top

-- | Minimal expansion of a possibly qualified variable identifier
minExpTerm_var :: Sign f e -> Token -> Maybe SORT -> [[TERM f]]
minExpTerm_var sign tok ms = case Map.lookup tok $ varMap sign of
    Nothing -> []
    Just s -> let qv = [[Qual_var tok s nullRange]] in
              case ms of
              Nothing -> qv
              Just s2 -> if s == s2 then qv else []

-- | minimal expansion of an (possibly qualified) operator application
minExpTerm_appl :: (GetRange f, Pretty f) => Min f e -> Sign f e -> Id
                -> Maybe OpType -> [TERM f] -> Range -> Result [[TERM f]]
minExpTerm_appl mef sign ide mty args pos = do
    nargs <- checkIdAndArgs ide args pos
    let -- functions matching that name in the current environment
        ops' = Set.filter ( \ o -> length (opArgs o) == nargs) $
              Map.findWithDefault Set.empty ide $ opMap sign
        ops = case mty of
                   Nothing -> map (pSortBy opArgs sign)
                              $ leqClasses (leqF' sign) ops'
                   Just ty -> if Set.member ty ops' ||
                                  -- might be known to be total
                                 Set.member ty {opKind = Total} ops'
                              then [[ty]] else []
    noOpOrPred ops "operation" mty ide pos nargs
    expansions <- mapM (minExpTerm mef sign) args
    let  -- generate profiles as descr. on p. 339 (Step 3)
        get_profiles cs = map (get_profile cs) ops
        get_profile cs os = [ (op', ts) |
                             op' <- os,
                             ts  <- cs,
                             and $ zipWith (leq_SORT sign)
                             (map sortOfTerm ts)
                             (opArgs op') ]
        qualTerms = qualifyOps ide pos
                       $ map (minimize_op sign)
                       $ concatMap (get_profiles . combine)
                       $ combine expansions
    hasSolutions (globAnnos sign)
        (Application (Op_name ide) args pos) qualTerms pos

qualifyOps :: Id -> Range -> [[(OpType, [TERM f])]] -> [[TERM f]]
qualifyOps ide = map . map . qualify_op ide

    -- qualify a single op, given by its signature and its arguments
qualify_op :: Id -> Range -> (OpType, [TERM f]) -> TERM f
qualify_op ide pos (op', terms') =
    Application (Qual_op_name ide (toOP_TYPE op') pos) terms' pos

{-----------------------------------------------------------
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
-----------------------------------------------------------}
minExpTerm_op :: (GetRange f, Pretty f) => Min f e -> Sign f e -> OP_SYMB
              -> [TERM f] -> Range -> Result [[TERM f]]
minExpTerm_op mef sign osym args pos = case osym of
  Op_name ide@(Id ts _ _) ->
    let res = minExpTerm_appl mef sign ide Nothing args pos in
      if null args && isSimpleId ide then
          let vars = minExpTerm_var sign (head ts) Nothing
          in if null vars then res else
             case maybeResult res of
             Nothing -> return vars
             Just ops -> return $ ops ++ vars
      else res
  Qual_op_name ide ty pos1 ->
   if length args /= length (args_OP_TYPE ty) then
      mkError "type qualification does not match number of arguments" ide
   else minExpTerm_appl mef sign ide (Just $ toOpType ty) args
        (pos1 `appRange` pos)

{-----------------------------------------------------------
    - Minimal expansion of a conditional -
  Expand a conditional by typing information (see minExpTerm_eq)
  First expand the subterms and subformula. Then calculate a profile
  P(C_1, C_2) for each (C_1, C_2) \in minExpTerm(t1) x minExpTerm(t_2).
  Separate these profiles into equivalence classes and take the
  unification of all these classes. Minimize each equivalence class.
  Finally transform the eq. classes into lists of
  conditionals with equally sorted terms.
-----------------------------------------------------------}
minExpTerm_cond :: (GetRange f, Pretty f) => Min f e -> Sign f e
                -> (TERM f -> TERM f -> a) -> TERM f -> TERM f -> Range
                -> Result [[a]]
minExpTerm_cond mef sign f term1 term2 pos = do
    pairs <- minExpTerm_eq mef sign term1 term2
    return $ map (concatMap ( \ (t1, t2) ->
              let s1 = sortOfTerm t1
                  s2 = sortOfTerm t2
              in if s1 == s2 then [f t1 t2]
              else if leq_SORT sign s2 s1 then
                   [f t1 (Sorted_term t2 s1 pos)]
              else if leq_SORT sign s1 s2 then
                   [f (Sorted_term t1 s2 pos) t2]
              else map ( \ s -> f (Sorted_term t1 s pos)
                                (Sorted_term t2 s pos))
                   $ minimalSupers sign s1 s2)) pairs

{-----------------------------------------------------------
    Let P be a set of equivalence classes of qualified terms.
    For each C \in P, let C' choose _one_
    t:s \in C for each s minimal such that t:s \in C.
    That is, discard all terms whose sort is a supersort of
    any other term in the same equivalence class.
-----------------------------------------------------------}
minimize_op :: Sign f e -> [(OpType, [TERM f])] -> [(OpType, [TERM f])]
minimize_op sign = keepMinimals sign (opRes . fst)

-- | the (possibly incomplete) list of supersorts common to both sorts
common_supersorts :: Bool -> Sign f e -> SORT -> SORT -> [SORT]
common_supersorts b sign s1 s2 =
    if s1 == s2 then [s1] else
    let l1 = supersortsOf s1 sign
        l2 = supersortsOf s2 sign in
    if Set.member s2 l1 then if b then [s2] else [s1] else
    if Set.member s1 l2 then if b then [s1] else [s2] else
    Set.toList $ if b then Set.intersection l1 l2
                 else Set.intersection (subsortsOf s1 sign)
                             $ subsortsOf s2 sign

-- | True if both sorts have a common supersort
have_common_supersorts :: Bool -> Sign f e -> SORT -> SORT -> Bool
have_common_supersorts b s s1 = not . null . common_supersorts b s s1

-- True if both sorts have a common subsort
have_common_subsorts :: Sign f e -> SORT -> SORT -> Bool
have_common_subsorts = have_common_supersorts False

-- | if True test if s1 > s2
geq_SORT :: Bool -> Sign f e -> SORT -> SORT -> Bool
geq_SORT b sign s1 s2 = s1 == s2 || let rel = sortRel sign in
    if b then Rel.member s2 s1 rel else Rel.member s1 s2 rel

-- | test if s1 < s2
leq_SORT :: Sign f e -> SORT -> SORT -> Bool
leq_SORT = geq_SORT False

-- | minimal common supersorts of the two input sorts
minimalSupers :: Sign f e -> SORT -> SORT -> [SORT]
minimalSupers = minimalSupers1 True

minimalSupers1 :: Bool -> Sign f e -> SORT -> SORT -> [SORT]
minimalSupers1 b s s1 = keepMinimals1 b s id . common_supersorts b s s1

-- | maximal common subsorts of the two input sorts
maximalSubs :: Sign f e -> SORT -> SORT -> [SORT]
maximalSubs = minimalSupers1 False

-- | only keep elements with minimal (and different) sorts
keepMinimals :: Sign f e -> (a -> SORT) -> [a] -> [a]
keepMinimals = keepMinimals1 True

keepMinimals1 :: Bool -> Sign f e -> (a -> SORT) -> [a] -> [a]
keepMinimals1 b s f = let lt x y = geq_SORT b s (f y) (f x) in keepMins lt

-- | True if both ops are in the overloading relation
leqF :: Sign f e -> OpType -> OpType -> Bool
leqF sign o1 o2 = length (opArgs o1) == length (opArgs o2) && leqF' sign o1 o2

leqF' :: Sign f e -> OpType -> OpType -> Bool
leqF' sign o1 o2 = have_common_supersorts True sign (opRes o1) (opRes o2) &&
    and (zipWith (have_common_subsorts sign) (opArgs o1) (opArgs o2))

-- | True if both preds are in the overloading relation
leqP :: Sign f e -> PredType -> PredType -> Bool
leqP sign p1 p2 = length (predArgs p1) == length (predArgs p2)
                  && leqP' sign p1 p2

leqP' :: Sign f e -> PredType -> PredType -> Bool
leqP' sign p1 =
    and . zipWith (have_common_subsorts sign) (predArgs p1) . predArgs

-- | Divide a Set (List) into equivalence classes w.r.t. eq
leqClasses :: Ord a => (a -> a -> Bool) -> Set.Set a -> [[a]]
leqClasses eq = map Set.toList . Rel.partSet eq

-- | Transform a list [l1,l2, ... ln] to (in sloppy notation)
-- [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
combine      :: [[a]] -> [[a]]
combine []    = [[]]
combine (x:l) = concatMap ((`map` combine l) . (:)) x

cmpSubsort :: Sign f e -> POrder SORT
cmpSubsort sign s1 s2 =
    if s1 == s2 then Just EQ else
    let l1 = supersortsOf s1 sign
        l2 = supersortsOf s2 sign
        b = Set.member s1 l2 in
    if Set.member s2 l1 then
        if b then Just EQ
        else Just LT
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
