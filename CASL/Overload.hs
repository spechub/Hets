{- |
    Module      :  $Header$
    Copyright   :  (c) Martin Kuehl, T. Mossakowski, C. Maeder, Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

    Overload resolution
    Follows Sect. III:3.3 of the CASL Reference Manual.
    The algorthim is from:
      Till Mossakowski, Kolyang, Bernd Krieg-Brueckner:
      Static semantic analysis and theorem proving for CASL.
      12th Workshop on Algebraic Development Techniques, Tarquinia 1997,
      LNCS 1376, p. 333-348
-}

module CASL.Overload where

import CASL.Sign
import CASL.AS_Basic_CASL

import qualified Common.Lib.Map         as Map
import qualified Common.Lib.Set         as Set
import           Common.Lib.Pretty
import           Common.Lib.State

import qualified Common.AS_Annotation   as Named
import qualified Common.Id              as Id
import           Common.GlobalAnnotations
import           Common.ListUtils
import           Common.PrettyPrint
import           Common.Result

import Data.Maybe

{-  Outline:
    - calculate global information from signature and pass it through
    - recurse through sentences until atomic sentences are reached
    - calculate expansions of atomic sentences
-}

{-  TODO-List:
    * generalize 'is_unambiguous' (see 'choose') and make it available globally
    * replace 'case' statements w/ pattern matching where possible
    * generalize minExpFORMULA_pred/minExpTerm_op/minExpTerm_cond
    * utilize Sets instead of Lists
    * generalize pairing func.s to inl/inr
    * generalize expansion for Qual_var and Sorted_term
    * move structural logic to higher levels, as e.g. in
        qualifyOps = map (map qualify_op) -- map should go somewhere above
    * sweep op-like logic from minExpTerm_cond where it is unneeded
    * generalize zipped_all
    * generalize qualifyTerms or implement locally - too much structural force
    * gemeralize minimize_* or implement locally - needed only in one f. each
    * use more let/in constructs (instead of where) to simulate workflow

    To find more items or pitfalls, search this file for:
      BEWARE
      FIXME
      TODO
-}

-- | the type of the type checking function
type Min f e = GlobalAnnos -> Sign f e -> f -> Result f

{-----------------------------------------------------------
    - Overload Resolution -
  Apply the algorithm for overload resolution described in
    Till Mossakowski, Kolyang, Bernd Krieg-Brueckner:
    Static semantic analysis and theorem proving for CASL.
    12th Workshop on Algebraic Development Techniques, Tarquinia 1997,
    LNCS 1376, p. 333-348
  to all given formulae/sentences w.r.t. the given annotations and
  signature.  All real work is done by 'minExpFORMULA', which is
  applied to any given formula in turn.
-----------------------------------------------------------}
overloadResolution :: (Eq f, PrettyPrint f)     =>
                      Min f e                   ->
                      GlobalAnnos               ->
                      Sign f e                  ->
                      [Named.Named (FORMULA f)] ->
                      Result [Named.Named (FORMULA f)]
                      -- neat type signature, eh?
overloadResolution mef ga sign = mapM overload
    where overload sent = do let sent' = Named.sentence sent
                             exp_sent  <- minExpFORMULA mef ga sign sent'
                             return sent { Named.sentence = exp_sent }


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
    + Membership is handled by expanding the subterm, followed by
      checking the found expansions' appropriateness to the stated
      Membership.
    + TODO: I don't know about 'Sort_gen_ax' and 'ExtFORMULA'.
-----------------------------------------------------------}
minExpFORMULA :: (Eq f, PrettyPrint f) =>
                 Min f e               ->
                 GlobalAnnos           ->
                 Sign f e              ->
                 (FORMULA f)           ->
                 Result (FORMULA f)
minExpFORMULA mef ga sign formula = case formula of
    --- Trivial atomic formula   -> return sentence unmodified
    True_atom _     -> return formula
    False_atom _    -> return formula
    Sort_gen_ax _ _ -> return formula
    --- Non-atomic formula       -> recurse through subsentences
    Quantification q vars f pos -> do
        -- add 'vars' to signature
        let (_, sign') = runState (mapM_ addVars vars) sign
        -- expand subformula
        f' <- minExpFORMULA mef ga sign' f
        -- wrap 'Quantification' around expanded sentence
        return (Quantification q vars f' pos)
    Conjunction fs pos -> do
        -- expand all subformulae
        fs' <- mapM (minExpFORMULA mef ga sign) fs
        -- wrap 'Conjunction' around expanded sentences
        return (Conjunction fs' pos)
    Disjunction fs pos -> do
        -- expand all subformulae
        fs' <- mapM (minExpFORMULA mef ga sign) fs
        -- wrap 'Disjunction' around expanded sentences
        return $ Disjunction fs' pos
        -- TODO: reminds of 'Conjunction'...
    Implication f1 f2 b pos -> do
        -- expand all subformulae
        f1' <- minExpFORMULA mef ga sign f1
        f2' <- minExpFORMULA mef ga sign f2
        -- wrap 'Implication' around expanded sentences
        return (Implication f1' f2' b pos)
    Equivalence f1 f2 pos -> do
        -- expand all subformulae
        f1' <- minExpFORMULA mef ga sign f1
        f2' <- minExpFORMULA mef ga sign f2
        -- wrap 'Equivalence' around expanded sentences
        return (Equivalence f1' f2' pos)
        -- TODO: reminds of 'Implication'...
    Negation f pos -> do
        -- expand subformula
        f' <- minExpFORMULA mef ga sign f
        -- wrap 'Negation' around expanded sentence
        return (Negation f' pos)
        -- TODO: reminds of ... all of the above
    --- Atomic formula           -> expand and check for ambiguities
    Predication predicate terms pos
        -- pass information to dedicated helper function
        -> minExpFORMULA_pred mef ga sign predicate terms pos
    Existl_equation term1 term2 pos
        -- pass information to dedicated helper function
        -> minExpFORMULA_eq mef ga sign Existl_equation term1 term2 pos
    Strong_equation term1 term2 pos
        -- pass information to dedicated helper function
        -> minExpFORMULA_eq mef ga sign Strong_equation term1 term2 pos
    Definedness term pos -> do
        -- expand subterm
        t  <- minExpTerm mef ga sign term
        -- check expansions for ambiguity
        t' <- is_unambiguous term t pos
        -- wrap 'Definedness' around expanded term
        return (Definedness t' pos)
    Membership term sort pos -> do
        -- expand subterm
        t   <- minExpTerm mef ga sign term
        -- choose expansions that fulfill 'Membership' to the given 'sort'
        t'  <- let leq_term [] = False
                   leq_term (t1:_) = leq_SORT sign sort $ term_sort t1
                in return $ filter leq_term t
        -- check chosen expansions for ambiguity
        t'' <- is_unambiguous term t' pos
        -- wrap 'Membership' around expanded term
        return (Membership t'' sort pos)
    ExtFORMULA f -> fmap ExtFORMULA $ mef ga sign f
    --- unknown formula         -> signal error
    _ -> error "minExpFORMULA: unexpected type of FORMULA: "


{-----------------------------------------------------------
    - Check expanded terms for ambiguity -
  Check, whether the given expansions contain ambiguity.
  If so, return any of the equivalent expansions, otherwise, or in
  case no correct expansions were found, signal an error.
-----------------------------------------------------------}
is_unambiguous :: (Eq f, PrettyPrint f) =>
                  TERM f                ->
                  [[TERM f]]            ->
                  [Id.Pos]              ->
                  Result (TERM f)
--- unambiguous expansion found -> return first expansion
is_unambiguous _ ((term:_):_) _ = return term
-- TODO: pattern should read '((term:_):[])' to really filter ambiguities
--- no expansions found         -> signal error
is_unambiguous topterm [] pos
    = pplain_error (Unparsed_term "<error>" [])
                   (ptext "No correct typing for " <+> (printText topterm))
                   (Id.headPos pos)
--- ambiguous expansions found  -> signal error
is_unambiguous _ term pos
    = pplain_error (Unparsed_term "<error>" [])
                   (ptext "Cannot disambiguate!\nPossible Expansions: "
                     <+> (printText term))
                   (Id.headPos pos)


{-----------------------------------------------------------
    - Minimal expansion of a predication formula -
  Expand a predicate application by typing information.
  1. First expand all argument subterms.
  2. Permute these expansions so we compute the set of tuples
    { (C_1, ..., C_n) | (C_1, ..., C_n) \in
                        minExpTerm(t_1) x ... x minExpTerm(t_n) }
    where t_1, ..., t_n are the given argument terms.
  3. For each element of this set compute the set of possible profiles
    (as described on p. 339).
  3a. For each profile inject all arguments t_i (elements of the list
    t_1:s_1,...,t_n:s_n) that don't exactly match the expected type (s_i)
    so that they do. E.g. if t_j is of sort s_j' but sort s_j, replace
    the term with the injection of t_j from s_j' to s_j.
  4. Define an equivalence relation ~ on these profiles
    (as described on p. 339).
  5. Separate each profile into equivalence classes by the relation ~
    and take the unification of these sets.
  6. Transform each term in the minimized set into a qualified predication.
  This process is analogous to expanding a function application (s. below),
  just with the minimization step being left out.
-----------------------------------------------------------}
minExpFORMULA_pred :: (Eq f, PrettyPrint f) =>
                      Min f e               ->
                      GlobalAnnos           ->
                      Sign f e              ->
                      PRED_SYMB             ->
                      [TERM f]              ->
                      [Id.Pos]              ->
                      Result (FORMULA f)
minExpFORMULA_pred mef ga sign predicate terms pos = do
    -- expand argument subterms (Step 1)
    expansions <- mapM (minExpTerm mef ga sign) terms
    -- permute expansions (Step 2)
    permuted_exps <- return (permute expansions)
    -- convert each permutation to a profile (Step 3)
    -- then inject arguments that don't match the predicate's expected type
    profiles <- return $ map (map insert_injections) $
                       map get_profile permuted_exps
    -- collect generated profiles into equivalence classes (Step 5)
    -- by the computed equivalence relation (Step 4)
    -- and unify them (also Step 5)
    p <- return $ concat
                $ map (equivalence_Classes pred_eq)
                  profiles
    -- choose profile if unambiguous, otherwise signal error
    p' <- choose p
    -- transform chosen profile into a qualified predicate application
    return (qualify_pred p')
    where -- the predicate's name
          name :: PRED_NAME
          name = pred_name predicate
          -- predicates matching that name in the current environment
          preds :: [PredType]
          preds = Set.toList
                  $ Map.findWithDefault Set.empty name $ predMap sign
          -- extract a predicate's name from its definition
          pred_name :: PRED_SYMB -> PRED_NAME
          pred_name (Pred_name name') = name'
          pred_name (Qual_pred_name name' _ _) = name'
          -- if an unambiguous class of expansions is found, choose its head
          -- otherwise signal an error
          --choose :: [[(PredType, [TERM f])]] -> Result (PredType, [TERM f])
          -- TODO: Signature throws an Error that I don't understand...
          choose ((p:_):_) = return p
          choose [] = pplain_error (PredType [], [])
                                   (ptext "No correct typing for "
                                    <+> printText (Predication predicate terms pos))
                                   (Id.posOfId name)
          choose ps = pplain_error (PredType [], terms)
                                   (ptext "Cannot disambiguate! Term: "
                                    <+> (printText (predicate, terms))
                                    $$ ptext "Possible Expansions: "
                                    <+> (printText ps))
                                   (Id.posOfId name)
          -- wrap qualified predication around predicate and its argument terms
          qualify_pred :: (PredType, [TERM f]) -> FORMULA f
          qualify_pred (pred', terms')
              = (Predication (Qual_pred_name name (toPRED_TYPE pred') [])
                             terms'
                             pos)
          -- generate profiles as descr. on p. 339 (Step 3)
          get_profile :: [[TERM f]] -> [(PredType, [TERM f])]
          get_profile cs = [ (pred', ts) |
                             pred' <- preds,
                             ts    <- (permute cs),
                             zipped_all (leq_SORT sign)
                             (map term_sort ts)
                             (predArgs pred') ]
          -- insert injections for all argument terms where neccessary
          insert_injections :: (PredType, [TERM f]) -> (PredType, [TERM f])
          insert_injections (pred', args)
              = (pred', (zipWith inject args (predArgs pred')))
          -- the eq. relation for predicates as descr. on p. 339 (Step 4)
          pred_eq :: (PredType, [TERM f]) -> (PredType, [TERM f]) -> Bool
          -- * TODO: Documentation!
          -- * neuer Algorithmus:
          --   checken, ob Praedikatsymbole und Argument-Terme Aequivalent sind.
          --   Fuer letzteres pro Argument-Position in expansions nachgucken.
          --   Ditto. fuer Operationen!
          pred_eq (pred1,ts1) (pred2,ts2)
              = let   w1 = predArgs pred1
                      w2 = predArgs pred2
                      s1 = map term_sort ts1
                      s2 = map term_sort ts2
                      b1 = zipped_all (leq_SORT sign) s1 w1
                      b2 = zipped_all (leq_SORT sign) s2 w2
                      preds_equal = (pred1 == pred2)
                      preds_equiv = leqP sign pred1 pred2
                      types_equal = False -- and (zipWith (==) s1 s2)
                      -- TODO: check whether argtypes are equal
                  in  b1 && b2 && (preds_equal
                                   || (preds_equiv
                                       && types_equal))


-- Handy shortcut for the type signature of 'Existl_equation' et al.
type Eq_constructor f = TERM f -> TERM f -> [Id.Pos] -> FORMULA f

{-----------------------------------------------------------
    - Minimal expansion of an equation formula -
  Expand an equation formula by typing information.
  Expand all subterms w.r.t. the given environment, then find pairs of
  expansions that belong to a common supersort.  Check these pairs for
  ambiguity and, if none is found, wrap them into an equation formula
  specified by the given 'Eq_constructor'.  If no correct expansions
  are found or the found expansions are ambiguous, signal an error.
-----------------------------------------------------------}
minExpFORMULA_eq :: (Eq f, PrettyPrint f) =>
                    Min f e               ->
                    GlobalAnnos           ->
                    Sign f e              ->
                    Eq_constructor f      ->
                    TERM f                ->
                    TERM f                ->
                    [Id.Pos]              ->
                    Result (FORMULA f)
minExpFORMULA_eq mef ga sign eq term1 term2 pos = do
    -- expand subterms
    exps1 <- minExpTerm mef ga sign term1
    exps2 <- minExpTerm mef ga sign term2
    -- choose head of any generated equivalence class, wrap into pairs
    pairs <- return (permute [catMaybes (map maybeHead exps1),
                              catMaybes (map maybeHead exps2)])
    -- choose pairs that belong to a common supersort
    candidates <- return (filter fit pairs)
    -- check candidate pairs for ambiguity
    case candidates of
        -- unambiguous expansion found -> wrap 'eq' around expansions
        ([t1,t2]:_) -> return (eq t1 t2 pos)
        -- no expansions found         -> signal error
        [] -> pplain_error (eq term1 term2 pos)
                           (ptext "No correct typing for "
                             <+> printText (eq term1 term2 pos))
                           (Id.headPos pos)
        -- ambiguous expansions found  -> signal error
        _ -> pplain_error (eq term1 term2 pos)
                          (ptext "Cannot disambiguate! Possible Expansions: "
                            <+> (printText exps1) $$ (printText exps2))
                          (Id.headPos pos)
    where -- True if the sorts of all given terms have a common supersort
          fit :: [TERM f] -> Bool
          fit = (have_common_supersorts sign) . (map term_sort)
          -- 'Just . head' if there is a head, 'Nothing' else
          maybeHead :: [a] -> Maybe a
          maybeHead (x:_) = Just x
          maybeHead _ = Nothing


{-----------------------------------------------------------
    - Minimal expansion of a term -
  Expand a given term by typing information.
  * 'Simple_id' terms are handled by 'minExpTerm_simple'.
  * 'Qual_var' terms are handled by 'minExpTerm_qual'.
  * 'Application' terms are handled by 'minExpTerm_op'.
  * 'Sorted_term' terms are handled by 'minExpTerm_sorted'.
  * 'Cast' terms are handled by 'minExpTerm_cast'.
  * 'Conditional' terms are handled by 'minExpTerm_cond'.
-----------------------------------------------------------}
minExpTerm :: (Eq f, PrettyPrint f) =>
              Min f e               ->
              GlobalAnnos           ->
              Sign f e              ->
              TERM f                ->
              Result [[TERM f]]
minExpTerm _ _ sign (Simple_id var)
    = minExpTerm_simple sign var
minExpTerm _ _ sign (Qual_var var sort pos)
    = minExpTerm_qual sign var sort pos
minExpTerm mef ga sign (Application op terms pos)
    = minExpTerm_op mef ga sign op terms pos
minExpTerm mef ga sign (Sorted_term term sort pos)
    = minExpTerm_sorted mef ga sign term sort pos
minExpTerm mef ga sign (Cast term sort pos)
    = minExpTerm_cast mef ga sign term sort pos
minExpTerm mef ga sign (Conditional term1 formula term2 pos)
    = minExpTerm_cond mef ga sign term1 formula term2 pos
minExpTerm _ _ _n _
    = error "minExpTerm"


{-----------------------------------------------------------
    - Minimal expansion of a simple identifier -
  Expand a simple identifier by typing information.
  Look up the given identifier in the given environment (as a variable
  or a constant).  Sort the found definitions into equivalence
  classes, then construct a qualified term from each.
-----------------------------------------------------------}
minExpTerm_simple :: Sign f e     ->
                     Id.SIMPLE_ID ->
                     Result [[TERM f]]
minExpTerm_simple sign var = do
    -- look up identifier as variable in environment
    vars <- return (Map.findWithDefault Set.empty var (varMap sign))
    -- look up constant matching name in environment
    ops' <- return $ Set.filter is_const_op
                   $ Map.findWithDefault Set.empty name (opMap sign)
    ops <- return (Set.image opRes ops')
    cs <- return (Set.union vars ops)
    least <- return
    -- BEWARE: Restriction to minimal sorts is not correct
    --         in case of downcasts: here, it may be the
    --         case that the cast is only correct for non-minimal sorts!
        $ {-Set.filter (is_least_sort cs)-} cs      -- :: Set.Set SORT
    return $ qualifyTerms []
           $ (equivalence_Classes eq)
           $ map pair_with_id
           $ Set.toList least
    -- FIXME: Christian states that the result must be an
    --        'Application' if var is indeed a constant!
    where -- get name of identifier
          name = Id.simpleIdToId var
          -- True if operation takes no arguments (i.e. op is a constant)
          is_const_op :: OpType -> Bool
          is_const_op = null . opArgs
          -- True if given set of sorts contains no subsort of the given sort
          is_least_sort :: Set.Set SORT -> SORT -> Bool
          is_least_sort ss s
              = Set.size (Set.intersection ss (subsortsOf s sign)) == 1
          -- True if of the given sorts is a supersort of the other
          eq = xeq_TUPLE sign
          -- wrap 'Qual_var' and the current identifier around the given sort
          pair_with_id :: SORT -> (TERM f, SORT)
          pair_with_id sort
              | isVar sort = ((Qual_var var sort []), sort)
              | otherwise  = (Application (Qual_op_name name (Total_op_type [] sort []) []) [] [], sort) -- should deal with partial constants as well!
          isVar :: SORT -> Bool
          isVar s = Set.member s (Map.findWithDefault Set.empty var (varMap sign))


{-----------------------------------------------------------
    - Minimal expansion of a qualified variable -
  Expand a qualified identifier by typing information.
  First expand the identifier, disregarding the given qualification.
  Then choose only expansions that satisfy that qualification, and
  wrap the typing information around them.
-----------------------------------------------------------}
minExpTerm_qual :: Sign f e ->
                   VAR      ->
                   SORT     ->
                   [Id.Pos] ->
                   Result [[TERM f]]
minExpTerm_qual sign var sort pos = do
    -- expand subterm
    expandedVar <- minExpTerm_simple sign var
    -- choose expansions that fit the given signature, then qualify
    return $ qualifyTerms pos
           $ map selectExpansions expandedVar
    where -- True if identifier and sort match the current signature
          fits :: TERM f -> Bool
          fits term = case term of
              (Sorted_term (Qual_var var' _ _) sort' _)
                  -> (var == var') && (sort == sort')
              _   -> error "minExpTerm_qual: unsorted TERM after expansion"
          -- TODO: this type-checking might be too restrictive, see 'term_sort'
          -- choose all given terms that satisfy 'fits'
          selectExpansions :: [TERM f] -> [(TERM f, SORT)]
          selectExpansions c = [ ((Qual_var var sort []), sort) |
                                 sorted <- c,
                                 fits sorted ]
          -- TODO: this looks very wrong, doesn't it?


{-----------------------------------------------------------
    - Minimal expansion of a sorted term -
  Expand a sorted term by typing information.
  First expand the subterm, disregarding the given qualification.
  Then choose only expansions that satisfy that qualification, and
  wrap the typing information around them.
-----------------------------------------------------------}
minExpTerm_sorted :: (Eq f, PrettyPrint f) =>
                     Min f e               ->
                     GlobalAnnos           ->
                     Sign f e              ->
                     TERM f                ->
                     SORT                  ->
                     [Id.Pos]              ->
                     Result [[TERM f]]
minExpTerm_sorted mef ga sign term sort pos = do
    -- expand subterm
    expandedTerm <- minExpTerm mef ga sign term
    -- choose expansions that fit the given signature, then qualify
    return $ qualifyTerms pos
           $ map selectExpansions expandedTerm
    where -- choose all given terms that match the current sort
          selectExpansions :: [TERM f] -> [(TERM f, SORT)]
          selectExpansions c = [ (sorted, sort) |
                                 sorted <- c,
                                 term_sort sorted == sort ]


{-----------------------------------------------------------
    - Minimal expansion of a function application -
  Expand a function application by typing information.
  1. First expand all argument subterms.
  2. Permute these expansions so we compute the set of tuples
    { (C_1, ..., C_n) | (C_1, ..., C_n) \in
                        minExpTerm(t_1) x ... x minExpTerm(t_n) }
    where t_1, ..., t_n are the given argument terms.
  3. For each element of this set compute the set of possible profiles
    (as described on p. 339).
  3a. For each profile inject all arguments t_i (elements of the list
    t_1:s_1,...,t_n:s_n) that don't exactly match the expected type (s_i)
    so that they do. E.g. if t_j is of sort s_j' but sort s_j, replace
    the term with the injection of t_j from s_j' to s_j.
  4. Define an equivalence relation ~ on these profiles
    (as described on p. 339).
  5. Separate each profile into equivalence classes by the relation ~
    and take the unification of these sets.
  6. Minimize each element of this unified set (as described on p. 339).
  7. Transform each term in the minimized set into a qualified function
    application term.
-----------------------------------------------------------}
minExpTerm_op :: (Eq f, PrettyPrint f) =>
                 Min f e               ->
                 GlobalAnnos           ->
                 Sign f e              ->
                 OP_SYMB               ->
                 [TERM f]              ->
                 [Id.Pos]              ->
                 Result [[TERM f]]
-- If the op is indeed a constant, expand it as a simple identifier
minExpTerm_op _ _ sign (Op_name (Id.Id [tok] [] _)) [] _
    = minExpTerm_simple sign tok
-- FIXME: Christian states that the above is too restrictive.
--        It should probably expand into an application again...
minExpTerm_op mef ga sign op terms pos = do
    -- expand argument subterms (Step 1)
    expansions <- mapM (minExpTerm mef ga sign) terms
    -- permute expansions (Step 2)
    permuted_exps <- return (permute expansions)
    -- convert each permutation to a profile (Step 3)
    -- then inject arguments that don't match the function's expected type
    profiles <- return $ map (map insert_injections) $
                       map get_profile permuted_exps
    -- collect generated profiles into equivalence classes (Step 5)
    -- by the computed equivalence relation (Step 4)
    -- and unify them (also Step 5)
    p <- return $ concat
                $ map (equivalence_Classes op_eq)
                  profiles
    -- minimize generated equivalence classes (Step 6)
    p' <- return (map (minimize_op sign) p)
    -- transform minimized eq.classes into qualified function application terms
    return $ qualifyTerms pos
           $ qualifyOps p'
    where -- the function's name
          name :: OP_NAME
          name = op_name op
          -- functions matching that name in the current environment
          ops :: [OpType]
          ops = Set.toList $ Map.findWithDefault Set.empty name (opMap sign)
          -- extract a function's name from its definition
          op_name :: OP_SYMB -> OP_NAME
          op_name (Op_name name') = name'
          op_name (Qual_op_name name' _ _) = name'
          -- qualify all ops in a list of eq.classes of ops
          qualifyOps :: [[(OpType, [TERM f])]] -> [[(TERM f, SORT)]]
          qualifyOps = map (map qualify_op)
          -- qualify a single op, given by its signature and its arguments
          qualify_op :: (OpType, [TERM f]) -> (TERM f, SORT)
          qualify_op (op', terms')
              = ((Application (Qual_op_name name (toOP_TYPE op') [])
                              terms'
                              [])
                , (opRes op'))
          -- generate profiles as descr. on p. 339 (Step 3)
          get_profile :: [[TERM f]] -> [(OpType, [TERM f])]
          get_profile cs = [ (op', ts) |
                             op' <- ops,
                             ts  <- (permute cs),
                             zipped_all (leq_SORT sign)
                             (map term_sort ts)
                             (opArgs op') ]
          -- insert injections for all argument terms where neccessary
          insert_injections :: (OpType, [TERM f]) -> (OpType, [TERM f])
          insert_injections (op', args)
              = (op', (zipWith inject args (opArgs op')))
          -- the equivalence relation as descr. on p. 339 (Step 4)
          op_eq :: (OpType, [TERM f]) -> (OpType, [TERM f]) -> Bool
          op_eq (op1,ts1) (op2,ts2)
              = let w1 = opArgs op1
                    w2 = opArgs op2
                    s1 = map term_sort ts1
                    s2 = map term_sort ts2
                    b1 = zipped_all (leq_SORT sign) s1 w1
                    b2 = zipped_all (leq_SORT sign) s2 w2
                    ops_equal = (op1 == op2)
                    ops_equiv = leqF sign op1 op2
                    types_equal = False -- and (zipWith (==) s1 s2)
                    -- TODO: check whether arg.types are equal
                 in b1 && b2 && (ops_equal
                                 || (ops_equiv
                                     && types_equal))


{-----------------------------------------------------------
    - Minimal expansion of a type-cast -
  Expand a type-cast by typing information.
  First expand the contained subterm.  Of the generated expansions,
  choose those that are of a subsort of the given target sort.
  Qualify the chosen expansions as terms of the target sort.
-----------------------------------------------------------}
minExpTerm_cast :: (Eq f, PrettyPrint f) =>
                   Min f e               ->
                   GlobalAnnos           ->
                   Sign f e              ->
                   TERM f                ->
                   SORT                  ->
                   [Id.Pos]              ->
                   Result [[TERM f]]
minExpTerm_cast mef ga sign term sort pos = do
    -- expand subterm
    expandedTerm <- minExpTerm mef ga sign term
    -- choose only expansions that are subsorts of the given sort
    validExps <- return $ map (filter (leq_SORT sign sort . term_sort))
                          expandedTerm
    -- pair expansions w/ the given sort, then wrap qualification around
    return $ qualifyTerms pos
           $ map (map (\ t -> (t, sort))) validExps


{-----------------------------------------------------------
    - Minimal expansion of a conditional -
  Expand a conditional by typing information.
  First expand the subterms and subformula. Then calculate a profile
  P(C_1, C_2) for each (C_1, C_2) \in minExpTerm(t1) x minExpTerm(t_2).
  Separate these profiles into equivalence classes and take the
  unification of all these classes. Minimize each equivalence class.
  Finally transform the eq. classes into lists of qualified
  conditional terms.
-----------------------------------------------------------}
minExpTerm_cond :: (Eq f, PrettyPrint f) =>
                   Min f e               ->
                   GlobalAnnos           ->
                   Sign f e              ->
                   TERM f                ->
                   FORMULA f             ->
                   TERM f                ->
                   [Id.Pos]              ->
                   Result [[TERM f]]
minExpTerm_cond  mef ga sign term1 formula term2 pos = do
    -- expand both subterms and the subsentence
    expansions1      <- minExpTerm mef ga sign term1
    expansions2      <- minExpTerm mef ga sign term2
    expanded_formula <- minExpFORMULA mef ga sign formula
    -- permute to get all possible combinations of eq.classes
    permuted_exps <- return (permute [expansions1, expansions2])
    -- generate profiles as per function applications
    profiles <- return (map get_profile permuted_exps)
    -- collect generated profiles into equivalence classes and unify
    p <- return (concat (map (equivalence_Classes eq) profiles))
    -- minimize generated eq.classes
    p' <- return (map (minimize_cond sign) p)
    -- transform eq.classes into qualified conditional terms
    return $ qualifyTerms pos
           $ qualifyConds expanded_formula p'
    where -- True if all terms in a given list have a common supersort
          have_supersort :: [TERM f] -> Bool
          have_supersort = not . Set.isEmpty . supersorts
          -- generate the Set op supersorts from a list of qualified terms
          supersorts :: [TERM f] -> Set.Set SORT
          supersorts = common_supersorts sign . map term_sort
          -- True if one term is a supersort of the other
          eq = xeq_TUPLE sign
          -- qualify all conditionals in a list of eq.classes
          qualifyConds :: FORMULA f ->
                          [[([TERM f], SORT)]] ->
                          [[(TERM f, SORT)]]
          qualifyConds f = map (map (qualify_cond f))
          -- qualify a single conditional
          qualify_cond :: FORMULA f ->
                          ([TERM f], SORT) ->
                          (TERM f, SORT)
          qualify_cond f (ts, s) = case ts of
              [t1, t2] -> (Conditional t1 f t2 [], s)
              _        -> error "Overload qualify_cond"
          -- generate profiles by checking whether
          -- the (two) terms have a common supersort
          get_profile :: [[TERM f]] -> [([TERM f], SORT)]
          get_profile cs = [ (c, s) |
                             c <- permute cs,
                             have_supersort c,
                             s <- Set.toList (supersorts c) ]


{-----------------------------------------------------------
    Construct a TERM of type Sorted_term from each (TERM, SORT) tuple
    TODO: 'Sorted_term' does _not_ fit in all cases!
-----------------------------------------------------------}
qualifyTerms :: [Id.Pos] -> [[(TERM f, SORT)]] -> [[TERM f]]
qualifyTerms pos pairs = map (map qualify_term) pairs
    where qualify_term :: (TERM f, SORT) -> TERM f
          qualify_term (t, s) = Sorted_term t s pos


{-----------------------------------------------------------
    Construct explicit Injection to 'result_type'
    if SORT of 'argument' does not match 'result_type'
-----------------------------------------------------------}
inject :: TERM f -> SORT -> TERM f
inject argument result_type
    | argument_type == result_type
        = argument
    | otherwise
        = (Application (injOpSymb argument_type result_type) [argument] [])
    where argument_type = term_sort argument

injName :: Id.Id
injName = Id.mkId [Id.Token {Id.tokStr="inj",
                             Id.tokPos=Id.nullPos}]

injOpSymb :: SORT -> SORT -> OP_SYMB
injOpSymb s1 s2 =
    Qual_op_name injName
                 (Total_op_type [s1] s2 [Id.nullPos])
                 []


{-----------------------------------------------------------
    Let P be a set of equivalence classes of qualified terms.
    For each C \in P, let C' choose _one_
    t:s \in C for each s minimal such that t:s \in C.
    That is, discard all terms whose sort is a supersort of
    any other term in the same equivalence class.
-----------------------------------------------------------}
minimize_op :: Sign f e -> [(OpType, [TERM f])] -> [(OpType, [TERM f])]
minimize_op sign ops_n_terms = concat $ map reduce ops_n_terms
    where results :: Set.Set SORT
          results = Set.fromList (map (opRes . fst) ops_n_terms)
          lesserSorts :: SORT -> Set.Set SORT
          lesserSorts s = Set.intersection results (subsortsOf s sign)
          leastSort :: SORT -> Bool
          leastSort s = Set.size (lesserSorts s) == 1
          reduce :: (OpType, [TERM f]) -> [(OpType, [TERM f])]
          reduce x@(op,_) = if (leastSort (opRes op)) then [x] else []


{-----------------------------------------------------------
    Let P be a set of equivalence classes of qualified terms.
    For each C \in P, let C' choose _one_
    t:s \in C for each s minimal such that t:s \in C.
    That is, discard all terms whose sort is a supersort of
    any other term in the same equivalence class.
    (Workalike for minimize_op, but used inside m_e_t_cond.)
-----------------------------------------------------------}
minimize_cond :: Sign f e -> [([TERM f], SORT)] -> [([TERM f], SORT)]
minimize_cond sign terms_n_sort = concat $ map reduce terms_n_sort
    where sorts :: Set.Set SORT
          sorts = Set.fromList (map snd terms_n_sort)
          lesserSorts :: SORT -> Set.Set SORT
          lesserSorts s = Set.intersection sorts (subsortsOf s sign)
          leastSort :: SORT -> Bool
          leastSort s = Set.size (lesserSorts s) == 1
          reduce :: ([TERM f], SORT) -> [([TERM f], SORT)]
          reduce x@(_,s) = if (leastSort s) then [x] else []


{-----------------------------------------------------------
    - Extract the sort from a given term -
  If the given term contains information about its sort, return that,
  otherwise signal an error.
-----------------------------------------------------------}
term_sort :: TERM f -> SORT
term_sort term' = case term' of
    (Sorted_term _ sort _)                  -> sort
    (Qual_var _ sort _)                     -> sort
    (Cast _ sort _)                         -> sort
    (Application (Qual_op_name _ ty _) _ _) -> res_OP_TYPE ty
    _ -> error "term_sort: unsorted TERM after expansion"


{-----------------------------------------------------------
    - Return the set of subsorts common to all given sorts -
-----------------------------------------------------------}
common_subsorts :: Sign f e -> [SORT] -> Set.Set SORT
common_subsorts sign srts = let get_subsorts = flip subsortsOf sign
                             in foldr1 Set.intersection
                                    $ map get_subsorts $ srts


{-----------------------------------------------------------
    - Return the set of supersorts common to all given sorts -
-----------------------------------------------------------}
common_supersorts :: Sign f e -> [SORT] -> Set.Set SORT
common_supersorts _ [] = Set.empty
common_supersorts sign srts = let get_supersorts = flip supersortsOf sign
                               in foldr1 Set.intersection
                                      $ map get_supersorts $ srts


{-----------------------------------------------------------
    - True if all sorts have a common subsort -
-----------------------------------------------------------}
have_common_subsorts :: Sign f e -> [SORT] -> Bool
have_common_subsorts s = (not . Set.isEmpty . common_subsorts s)


{-----------------------------------------------------------
    - True if all sorts have a common supersort -
-----------------------------------------------------------}
have_common_supersorts :: Sign f e -> [SORT] -> Bool
have_common_supersorts s = (not . Set.isEmpty . common_supersorts s)


{-----------------------------------------------------------
    - True if s1 <= s2 OR s1 >= s2 -
-----------------------------------------------------------}
xeq_SORT :: Sign f e -> SORT -> SORT -> Bool
xeq_SORT sign s1 s2 = (leq_SORT sign s1 s2) || (geq_SORT sign s1 s2)


{-----------------------------------------------------------
    - True if s1 <= s2 OR s1 >= s2 -
-----------------------------------------------------------}
xeq_TUPLE :: Sign f e -> (a, SORT) -> (a, SORT) -> Bool
xeq_TUPLE sign (_,s1) (_,s2) = xeq_SORT sign s1 s2


{-----------------------------------------------------------
    - True if s1 <= s2 -
-----------------------------------------------------------}
leq_SORT :: Sign f e -> SORT -> SORT -> Bool
leq_SORT sign s1 s2 = Set.member s2 (supersortsOf s1 sign)


{-----------------------------------------------------------
    - True if s1 >= s2 -
-----------------------------------------------------------}
geq_SORT :: Sign f e -> SORT -> SORT -> Bool
geq_SORT sign s1 s2 = Set.member s2 (subsortsOf s1 sign)


{-----------------------------------------------------------
    - True if o1 ~F o2 -
-----------------------------------------------------------}
leqF :: Sign f e -> OpType -> OpType -> Bool
leqF sign o1 o2 = zipped_all are_legal (opArgs o1) (opArgs o2)
                && have_common_supersorts sign [(opRes o1), (opRes o2)]
    where are_legal a b = have_common_subsorts sign [a, b]


{-----------------------------------------------------------
    - True if p1 ~P p2 -
-----------------------------------------------------------}
leqP :: Sign f e -> PredType -> PredType -> Bool
leqP sign p1 p2 = zipped_all are_legal (predArgs p1) (predArgs p2)
    where are_legal a b = have_common_subsorts sign [a, b]


