{- | 
   
    Module      :  $Header$
    Copyright   :  (c) Martin Kühl, T. Mossakowski, C. Maeder, Uni Bremen 2004
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

    Overload resolution
    Follows Sect. III:3.3 of the CASL Reference Manual.
    The algorthim is from
    Till Mossakowski, Kolyang, Bernd Krieg-Brueckner: 
    Static semantic analysis and theorem proving for CASL.
    12th Workshop on Algebraic Development Techniques, Tarquinia 1997, 
    LNCS 1376, p. 333-348
-}

-- does anyone ever need anything else from me? (yes, in Logic_Modal!)
module CASL.Overload where

import Debug.Trace

import CASL.Sign                -- Sign, OpType
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import Common.Result            -- Result

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Id      as Id
import qualified Common.AS_Annotation   as Named
import Common.GlobalAnnotations
import Common.PrettyPrint
import Common.Lib.Pretty
import Common.Lib.State
import Common.ListUtils

import Data.Maybe

{-
    Idee: 
    - global Infos aus Sign berechnen + mit durchreichen
      (connected compenents, s.u.)
    - rekursiv in FORMULA absteigen, bis atomare Formel erreicht wird
    - atomaren Formeln mit minExpTerm behandeln
-}
{-
    TODO-List:
    * generalize 'is_unambiguous' (see 'choose') and make it available globally
    * replace 'case' statements w/ pattern matching where possible
    * generalize minExpFORMULA_pred/minExpTerm_op/minExpTerm_cond
    * utilize Sets instead of Lists
    * generalize pairing func.s to inl/inr
    * check whether Qual_var expansion works as it is supposed to
    * generalize expansion for Qual_var and Sorted_term
    * move structural logic to higher levels, as e.g. in
        qualifyOps = map (map qualify_op) -- map should go somewhere above
    * sweep op-like logic from minExpTerm_cond where it is unneeded
    * generalize zipped_all
    * generalize qualifyTerms or implement locally - too much structural force
    * gemeralize minimize_* or implement locally - needed only in one f. each
    * use more let/in constructs (instead of where) to simulate workflow

    * use common upper bounds for membership and projection
          then re-include "BEWARE: Restriction to minimal...."
-}

{-----------------------------------------------------------
    Overload Resolution
-----------------------------------------------------------}

type Min f e = GlobalAnnos -> Sign f e -> f -> Result f

overloadResolution      :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos -> Sign f e 
			-> [Named.Named (FORMULA f)]
			-> Result [Named.Named (FORMULA f)]
overloadResolution mef ga sign  = mapM overload
    where
        overload sent = do
            let sent' = Named.sentence sent
            --debug 1 ("sent'",sent')
            exp_sent    <- minExpFORMULA mef ga sign sent'
            --debug 2 ("exp_sent",exp_sent)
            return sent { Named.sentence = exp_sent }

{-----------------------------------------------------------
    Minimal Expansions of a FORMULA
-----------------------------------------------------------}
minExpFORMULA :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> (FORMULA f) -> Result (FORMULA f)
minExpFORMULA mef ga sign formula
    = case formula of
        -- Trivial Atom         -> Return untouched
        True_atom _     -> return formula                       -- :: FORMULA
        False_atom _    -> return formula                       -- :: FORMULA
	-- Non-Atomic FORMULA   -> Recurse through subFORMULAe
	Quantification q vars f pos -> do
            let (_, sign') = runState (mapM_ addVars vars) sign
	    f' <- minExpFORMULA mef ga sign' f
	    return $ Quantification q vars f' pos
	Conjunction fs pos -> do
	    fs' <- mapM (minExpFORMULA mef ga sign) fs
	    return $ Conjunction fs' pos
	Disjunction fs pos -> do
	    fs' <- mapM (minExpFORMULA mef ga sign) fs
	    return $ Disjunction fs' pos
	Implication f1 f2 b pos -> do
	    f1' <- minExpFORMULA mef ga sign f1
	    f2' <- minExpFORMULA mef ga sign f2
	    return $ Implication f1' f2' b pos
	Equivalence f1 f2 pos -> do
	    f1' <- minExpFORMULA mef ga sign f1
	    f2' <- minExpFORMULA mef ga sign f2
	    return $ Equivalence f1' f2' pos
	Negation f pos -> do
	    f' <- minExpFORMULA mef ga sign f
	    return $ Negation f' pos
        -- Atomic FORMULA      -> Check for Ambiguities
        Predication predicate terms pos ->
            minExpFORMULA_pred mef ga sign predicate terms pos  -- :: FORMULA
        Definedness term pos            -> do
            t   <- minExpTerm mef ga sign term                  -- :: [[TERM]]
            --debug 4 ("t", t)
            t'  <- is_unambiguous term t pos                         -- :: TERM
            return $ Definedness t' pos                         -- :: FORMULA
	Existl_equation term1 term2 pos ->
            minExpFORMULA_eq mef ga sign Existl_equation term1 term2 pos
        Strong_equation term1 term2 pos ->
            minExpFORMULA_eq mef ga sign Strong_equation term1 term2 pos
        Membership term sort pos        -> do
            t   <- minExpTerm mef ga sign term                  -- :: [[TERM]]
            t'  <- let leq_term [] = False
                       leq_term (t1:_) =
                        leq_SORT sign sort $ term_sort t1 
                    in return $ filter leq_term t               -- :: TERM
                
            t'' <- is_unambiguous term t' pos                        -- :: [[TERM]]
            return $ Membership t'' sort pos                    -- :: FORMULA
	Sort_gen_ax _ _ -> return formula
	ExtFORMULA f -> fmap ExtFORMULA $ mef ga sign f
	_ -> error $ "minExpFORMULA: unexpected type of FORMULA: "
            ++ (show formula)

is_unambiguous :: (Eq f, PrettyPrint f) => TERM f -> [[TERM f]] 
	       -> [Id.Pos] -> Result (TERM f)
is_unambiguous topterm term pos = do
            case term of
                [] -> pplain_error (Unparsed_term "<error>" [])
                   (ptext "No correct typing for " <+> printText topterm)
                   (Id.headPos pos)
                (_:_):_   -> return $ head $ head $ term         -- :: TERM
        -- BEWARE! Oversimplified disambiguation!
                --(_:_):[]   -> return head $ head term           -- :: TERM
                _       -> pplain_error (Unparsed_term "<error>" [])
                    (ptext "Cannot disambiguate!\nPossible Expansions: "
                     <+> (printText term)) (Id.headPos pos)

{-----------------------------------------------------------
    Minimal Expansions of a Predicate Application Formula
-----------------------------------------------------------}
minExpFORMULA_pred :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> PRED_SYMB -> [TERM f] -> [Id.Pos] 
                -> Result (FORMULA f)
minExpFORMULA_pred mef ga sign predicate terms pos = do
    expansions          <- mapM
        (minExpTerm mef ga sign) terms          -- ::        [[[TERM]]]
    --debug 5 ("expansions", expansions)
    permuted_exps       <- return
        $ permute expansions                    -- ::        [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[(PredType, [TERM])]]
    --debug 6 ("profiles", profiles)
    p                   <- return
        $ concat                                -- ::  [[(PredType, [TERM])]]
        $ map (equivalence_Classes pred_eq)     -- :: [[[(PredType, [TERM])]]]
          profiles                              -- ::  [[(PredType, [TERM])]]
    --debug 7 ("p", p)
    p'                  <- choose p             -- ::    (PredType, [TERM])
    return $ qualify_pred p'
    where
        name            :: PRED_NAME
        name             = pred_name predicate
        preds           :: [PredType]
        preds            = Set.toList
            $ Map.findWithDefault
                Set.empty name $ (predMap sign)
        pred_name       :: PRED_SYMB -> PRED_NAME
        pred_name pred'  = case pred' of
            (Pred_name name')           -> name'
            (Qual_pred_name name' _ _)  -> name'
--   choose :: [[(PredType, [TERM f])]] -> Result (PredType, [TERM f])
        choose ps        = case ps of
            [] -> pplain_error (PredType [],[])
                   (ptext "No correct typing for " <+> printText ps)
                   (Id.headPos pos)
        -- BEWARE! Oversimplified disambiguation!
            --(p:_):[] -> return p
            (_:_):_ -> return $ head $ head ps
            _   -> pplain_error (PredType [], terms)
                   (ptext "Cannot disambiguate! Term: " 
                    <+> (printText (predicate, terms))
                    $$ ptext "Possible Expansions: " 
                    <+> (printText ps)) (Id.headPos pos)
        qualify_pred    :: (PredType, [TERM f]) -> FORMULA f
        qualify_pred (pred', terms')
            = (Predication                                      -- :: FORMULA
                (Qual_pred_name name (toPRED_TYPE pred') [])    -- :: PRED_SYMB
                terms'                                          -- :: [TERM]
                pos)                                            -- :: [Pos]
        get_profile     :: [[TERM f]] -> [(PredType, [TERM f])]
        get_profile cs
            = [ (pred', ts) |
                pred' <- preds,                                 -- :: PredType
                ts <- (permute cs),                             -- ::  [TERM]
                zipped_all (leq_SORT sign)                      -- ::   Bool
                    (map term_sort ts)                          -- ::  [SORT]
                    (predArgs pred') ]                          -- ::  [SORT]
        pred_eq         :: (PredType, [TERM f]) -> (PredType, [TERM f]) -> Bool
{- todo
   Doku

   neuer Algorithmus:
   checken, ob Prädikatsymbole und Argument-Terme äquivalent sind.
   Für letzteres pro Argument-Position in expansions nachgucken.
   Dto. für Operationen.

   Injektionen: op:w->s(t_i) : s'   ---->  "_inj":s->s'(op:w->s(t_i)) : s'
-}
        pred_eq (pred1,ts1) (pred2,ts2)
            = let   w1 = predArgs pred1                         -- :: [SORT]
                    w2 = predArgs pred2                         -- :: [SORT]
                    s1 = map term_sort ts1                      -- :: [SORT]
                    s2 = map term_sort ts2                      -- :: [SORT]
                    b1 = zipped_all (leq_SORT sign) s1 w1       -- ::  Bool
                    b2 = zipped_all (leq_SORT sign) s2 w2       -- ::  Bool
                    preds_equal = (pred1 == pred2)              -- ::  Bool
                    preds_equiv = leqP sign pred1 pred2         -- ::  Bool
                    types_equal = False -- and (zipWith (==) s1 s2) -- ::  Bool
                in  b1 && b2 && (preds_equal
                                 || (preds_equiv
                                     && types_equal))

{-----------------------------------------------------------
    Minimal Expansions of a Strong/Existl. Equation Formula
-----------------------------------------------------------}
minExpFORMULA_eq :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> (TERM f -> TERM f -> [Id.Pos] -> FORMULA f)
                    -> TERM f -> TERM f -> [Id.Pos] -> Result (FORMULA f)
minExpFORMULA_eq mef ga sign eq term1 term2 pos = do
    exps1       <- minExpTerm mef ga sign term1                -- :: [[TERM]]
    exps2       <- minExpTerm mef ga sign term2                -- :: [[TERM]]
    --debug 1 ("exps1",exps1)
    --debug 2 ("exps2",exps2)
    pairs       <- return
        $ permute [catMaybes (map maybeHead exps1), 
                   catMaybes (map maybeHead exps2)]  -- :: [[TERM]]
    --debug 3 ("pairs",pairs)
    candidates  <- return
        $ filter fit pairs                              -- :: [[TERM]]
    --debug 3 ("candidates",candidates)
    case candidates of
        [] -> pplain_error (eq term1 term2 pos)
               (ptext "No correct typing for " 
		<+> printText (eq term1 term2 pos))
               (Id.headPos pos)
        -- BEWARE! Oversimplified disambiguation!
        ([t1,t2]:_)       -> return $ eq t1 t2 pos
        --([t1,t2]:[])       -> return $ eq t1 t2 pos
        _               -> pplain_error (eq term1 term2 pos)
            (ptext "Cannot disambiguate! Possible Expansions: "
             <+> (printText exps1) $$ (printText exps2)) (Id.headPos pos)
    where
        fit     :: [TERM f] -> Bool
        fit      = (have_common_supersorts sign) . (map term_sort)
        maybeHead :: [a] -> Maybe a
        maybeHead (x:_) = Just x
        maybeHead _ = Nothing

{-----------------------------------------------------------
    Minimal Expansions of a TERM
-----------------------------------------------------------}
minExpTerm :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> TERM f -> Result [[TERM f]]
minExpTerm mef ga sign term'
 = do -- debug 6 ("term'",term')
      u <- case term' of
        Simple_id var
            -> minExpTerm_simple sign var
        Qual_var var sort pos
            -> minExpTerm_qual sign var sort pos
        Application op terms pos
            -> minExpTerm_op mef ga sign op terms pos
        Sorted_term term sort pos
            -> minExpTerm_sorted mef ga sign term sort pos
        Cast term sort pos
            -> minExpTerm_cast mef ga sign term sort pos
        Conditional term1 formula term2 pos
            -> minExpTerm_cond mef ga sign term1 formula term2 pos
        _   -> error "minExpTerm"
      return u

{-----------------------------------------------------------
    Minimal Expansions of a Simple_id Term
-----------------------------------------------------------}
minExpTerm_simple :: 
                Sign f e -> Id.SIMPLE_ID -> Result [[TERM f]]
minExpTerm_simple sign var = do
    vars        <- return
        $ Map.findWithDefault                   -- :: Set.Set SORT
            Set.empty var (varMap sign)
    ops'        <- return
        $ (Set.filter is_const_op)              -- :: Set.Set OpType
        $ Map.findWithDefault                   -- :: Set.Set OpType
            Set.empty name (opMap sign)
    ops         <- return
        $ Set.fromList                          -- :: Set.Set SORT
        $ (map opRes)                           -- :: [SORT]
        $ Set.toList                            -- :: [OpType]
            ops'                                -- :: Set.Set OpType
        -- maybe use Set.fold instead of List.map?
    cs          <- return
        $ Set.union vars ops                    -- :: Set.Set SORT
    least       <- return
    -- BEWARE: Restriction to minimal sorts is not correct
    --         in case of downcasts: here, it may be the
    --         case that the cast is only correct for non-minimal sorts!
        $ {-Set.filter (is_least_sort cs)-} cs      -- :: Set.Set SORT
    return
        $ qualifyTerms []                       -- :: [[TERM]]
        $ (equivalence_Classes eq)              -- :: [[(TERM, SORT)]]
        $ map pair_with_id                      -- :: [(TERM, SORT)]
        $ Set.toList least                      -- :: [SORT]
    where
        name                    :: Id.Id
        name                     = Id.simpleIdToId var
        is_const_op             :: OpType -> Bool
        is_const_op op           = (null . opArgs) op
        is_least_sort           :: Set.Set SORT -> SORT -> Bool
        is_least_sort ss s
            = Set.size (Set.intersection ss (subsortsOf s sign)) == 1
        eq                       = xeq_TUPLE sign
        pair_with_id            :: SORT -> (TERM f, SORT)
        pair_with_id sort        = ((Qual_var var sort []), sort)

{-----------------------------------------------------------
    Minimal Expansions of a Qual_var Term
-----------------------------------------------------------}
minExpTerm_qual :: 
                Sign f e -> VAR -> SORT -> [Id.Pos] -> Result [[TERM f]]
minExpTerm_qual sign var sort pos = do
    expandedVar <- minExpTerm_simple sign var   -- :: [[TERM]]
    return
        $ qualifyTerms pos                      -- :: [[TERM]]
        $ map selectExpansions expandedVar      -- :: [[(TERM, SORT)]]
    where
        fits                    :: TERM f -> Bool
        fits term                = case term of
            (Sorted_term (Qual_var var' _ _) sort' _)
                -> (var == var') && (sort == sort')
            _   -> error "minExpTerm_qual: unsorted TERM after expansion"
        selectExpansions        :: [TERM f] -> [(TERM f, SORT)]
        selectExpansions c
            = [ ((Qual_var var sort []), sort) |       -- :: (TERM, SORT)
                sorted <- c,                    -- :: TERM
                fits sorted ]                   -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Sorted_term Term
-----------------------------------------------------------}
minExpTerm_sorted :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> TERM f -> SORT -> [Id.Pos] -> Result [[TERM f]]
minExpTerm_sorted mef ga sign term sort pos = do
    expandedTerm <- minExpTerm mef ga sign term   -- :: [[TERM]]
    --debug 7 ("expandedTerm", expandedTerm)
    return
        $ qualifyTerms pos                      -- :: [[TERM]]
        $ map selectExpansions expandedTerm     -- :: [[(TERM, SORT)]]
    where
        selectExpansions        :: [TERM f] -> [(TERM f, SORT)]
        selectExpansions c
            = [ (sorted, sort) |                   -- :: (TERM, SORT)
                sorted <- c,                       -- :: TERM
                term_sort sorted == sort ]         -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Function Application Term
-----------------------------------------------------------}
minExpTerm_op :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
              Sign f e -> OP_SYMB -> [TERM f] -> [Id.Pos] -> Result [[TERM f]]
minExpTerm_op _ _ sign (Op_name (Id.Id [tok] [] _)) [] _ = 
  minExpTerm_simple sign tok
minExpTerm_op mef ga sign op terms pos = 
    minExpTerm_op1 mef ga sign op terms pos

minExpTerm_op1 :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
               Sign f e -> OP_SYMB -> [TERM f] -> [Id.Pos] -> Result [[TERM f]]
minExpTerm_op1 mef ga sign op terms pos = do
    --debug 3 ("op",op)
    --debug 3 ("terms",show terms)
    expansions          <- mapM
        (minExpTerm mef ga sign) terms          -- ::       [[[TERM]]]
    --debug 9 ("expansions", expansions)
    permuted_exps       <- return
        $ permute expansions                    -- ::       [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[(OpType, [TERM])]]
    --debug 10 ("profiles", profiles)
    p                   <- return
        $ concat                                -- ::  [[(OpType, [TERM])]]
        $ map (equivalence_Classes op_eq)       -- :: [[[(OpType, [TERM])]]]
          profiles                              -- ::  [[(OpType, [TERM])]]
    --debug 3 ("p",show p)
    p'                  <- return
        $ map (minimize_op sign) p              -- ::  [[(OpType, [TERM])]]
{- debug 3 ("p'",show p')
   debug 3 (" qualifyOps p'",show $  qualifyOps p')
   debug 3 ("qualifyTerms pos $ qualifyOps p'",
      show $ qualifyTerms pos $ qualifyOps p')
-}
    return
        $ qualifyTerms pos                      -- ::        [[TERM]]
        $ qualifyOps p'                         -- ::    [[(TERM, SORT)]]
    where
        name            :: OP_NAME
        name             = op_name op
        ops             :: [OpType]
        ops              = Set.toList
            $ Map.findWithDefault
                Set.empty name $ (opMap sign)
        op_name         :: OP_SYMB -> OP_NAME
        op_name op'      = case op' of
            (Op_name name')             -> name'
            (Qual_op_name name' _ _)    -> name'
        qualifyOps      :: [[(OpType, [TERM f])]] -> [[(TERM f, SORT)]]
        qualifyOps       = map (map qualify_op)
        qualify_op      :: (OpType, [TERM f]) -> (TERM f, SORT)
        qualify_op (op', terms')
            = ((Application                                     -- ::  TERM
                (Qual_op_name name (toOP_TYPE op') [])          -- :: OP_SYMB
                terms'                                          -- :: [TERM]
                [])                                             -- :: [Pos]
              , (opRes op'))                                    -- ::  SORT
        get_profile     :: [[TERM f]] -> [(OpType, [TERM f])]
        get_profile cs
            = [ (op', ts) |                             -- :: (OpType, [TERM])
                op'     <- ops,                         -- ::  OpType
                ts      <- (permute cs),                -- ::  [TERM]
                zipped_all (leq_SORT sign)              -- ::   Bool
                    (map term_sort ts)                  -- ::  [SORT]
                    (opArgs op') ]                      -- ::  [SORT]
        op_eq           :: (OpType, [TERM f]) -> (OpType, [TERM f]) -> Bool
        op_eq (op1,ts1) (op2,ts2)
            = let   w1 = opArgs op1                             -- :: [SORT]
                    w2 = opArgs op2                             -- :: [SORT]
                    s1 = map term_sort ts1                      -- :: [SORT]
                    s2 = map term_sort ts2                      -- :: [SORT]
                    b1 = zipped_all (leq_SORT sign) s1 w1       -- ::  Bool
                    b2 = zipped_all (leq_SORT sign) s2 w2       -- ::  Bool
                    ops_equal = (op1 == op2)                    -- ::  Bool
                    ops_equiv = leqF sign op1 op2               -- ::  Bool
                    types_equal = False -- and (zipWith (==) s1 s2) -- ::  Bool
                in  b1 && b2 && (ops_equal
                                || (ops_equiv
                                    && types_equal))

{-----------------------------------------------------------
    Minimal Expansions of a Cast Term
-----------------------------------------------------------}
minExpTerm_cast :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> TERM f -> SORT -> [Id.Pos] -> Result [[TERM f]]
minExpTerm_cast mef ga sign term sort pos = do
    expandedTerm <- minExpTerm mef ga sign term         -- :: [[TERM]]
    --debug 1 ("expandedTerm",expandedTerm)
    validExps    <- return
        $ map (filter (leq_SORT sign sort . term_sort)) -- ::  [[TERM]]
        $ expandedTerm                                  -- ::  [[TERM]]
    --debug 2 ("validExps",validExps)
    return
        $ qualifyTerms pos                              -- :: [[TERM]]
        $ map (map (\ t -> (t, sort))) validExps        -- :: [[(TERM, SORT)]]

{-----------------------------------------------------------
    Minimal Expansions of a Conditional Term
-----------------------------------------------------------}
minExpTerm_cond :: (Eq f, PrettyPrint f) => Min f e -> GlobalAnnos ->
                Sign f e -> TERM f -> FORMULA f -> TERM f -> [Id.Pos]
                -> Result [[TERM f]]
minExpTerm_cond  mef ga sign term1 formula term2 pos = do
    expansions1
        <- minExpTerm mef ga sign term1                -- ::       [[TERM]]
    expansions2
        <- minExpTerm mef ga sign term2                -- ::       [[TERM]]
    expanded_formula
        <- minExpFORMULA mef ga sign formula           -- ::       FORMULA
    permuted_exps       <- return
        $ permute [expansions1, expansions2]    -- ::      [[[TERM]]]
    --debug 7 ("permuted_exps",permuted_exps)
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[([TERM], SORT)]]
    --debug 7 ("profiles",profiles)
    p                   <- return
        $ concat                                -- ::  [[([TERM], SORT)]]
        $ map                                   -- :: [[[([TERM], SORT)]]]
          (equivalence_Classes eq)
          profiles                              -- ::  [[([TERM], SORT)]]
    --debug 7 ("p",p)
    p'                  <- return
        $ map (minimize_cond sign) p            -- ::  [[([TERM], SORT)]]
    --debug 7 ("p'",p')
    return
        $ qualifyTerms pos                      -- ::       [[TERM]]
        $ qualifyConds expanded_formula p'      -- ::   [[(TERM, SORT)]]
    where
        have_supersort          :: [TERM f] -> Bool
        have_supersort           = not . Set.isEmpty . supersorts
        supersorts              :: [TERM f] -> Set.Set SORT
        supersorts               = common_supersorts sign . map term_sort
        eq                       = xeq_TUPLE sign
        qualifyConds :: FORMULA f -> [[([TERM f], SORT)]] -> [[(TERM f, SORT)]]
        qualifyConds f           = map $ map (qualify_cond f)
        qualify_cond :: FORMULA f -> ([TERM f], SORT) -> (TERM f, SORT)
        qualify_cond f (ts, s)   = case ts of
            [t1, t2]    -> (Conditional t1 f t2 [], s)
            _           -> (Unparsed_term "" [],s) {-error
                $ "Internal Error: wrong number of TERMs in qualify_cond!"-}
        get_profile             :: [[TERM f]] -> [([TERM f], SORT)]
        get_profile cs
            = [ (c, s) |                                -- :: ([TERM], SORT)
                c <- permute cs,                        -- ::  [TERM]
                have_supersort c,                       -- ::   Bool
                s <- Set.toList $ supersorts c ]        -- ::   SORT


{-----------------------------------------------------------
    Construct a TERM of type Sorted_term
    from each (TERM, SORT) tuple
-----------------------------------------------------------}
qualifyTerms            :: [Id.Pos] -> [[(TERM f, SORT)]] -> [[TERM f]]
qualifyTerms pos pairs = 
    map (map qualify_term) pairs
    where
        qualify_term       :: (TERM f, SORT) -> TERM f
        qualify_term (t, s) = Sorted_term t s pos

{-----------------------------------------------------------
    For each C in P (see above), let C' choose _one_
    f:s \in C for each s minimal such that f:s \in C
-----------------------------------------------------------}
minimize_op :: 
                Sign f e -> [(OpType, [TERM f])] -> [(OpType, [TERM f])]
minimize_op sign ops_n_terms
    = concat $ map reduce ops_n_terms
    where
        results         :: Set.Set SORT
        results          = Set.fromList (map (opRes . fst) ops_n_terms)
        lesserSorts     :: SORT -> Set.Set SORT
        lesserSorts s    = Set.intersection results (subsortsOf s sign)
        leastSort       :: SORT -> Bool
        leastSort s      = Set.size (lesserSorts s) == 1
        reduce          :: (OpType, [TERM f]) -> [(OpType, [TERM f])]
        reduce x@(op,_)  = if (leastSort (opRes op)) then [x] else []

{-----------------------------------------------------------
    Workalike for minimize_op, but used inside m_e_t_cond
-----------------------------------------------------------}
minimize_cond :: 
                Sign f e -> [([TERM f], SORT)] -> [([TERM f], SORT)]
minimize_cond sign terms_n_sort
    = concat $ map reduce terms_n_sort
    where
        sorts           :: Set.Set SORT
        sorts            = Set.fromList (map snd terms_n_sort)
        lesserSorts     :: SORT -> Set.Set SORT
        lesserSorts s    = Set.intersection sorts (subsortsOf s sign)
        leastSort       :: SORT -> Bool
        leastSort s      = Set.size (lesserSorts s) == 1
        reduce          :: ([TERM f], SORT) -> [([TERM f], SORT)]
        reduce x@(_,s)   = if (leastSort s) then [x] else []

term_sort   :: TERM f -> SORT
term_sort term'  = case term' of
    (Sorted_term _ sort _ )     -> sort
    _                           -> error                -- unlikely
        "term_sort: unsorted TERM after expansion"

{-----------------------------------------------------------
    Set of SubSORTs common to all given SORTs
-----------------------------------------------------------}
common_subsorts :: 
                Sign f e -> [SORT] -> Set.Set SORT
common_subsorts sign srts = let
    get_subsorts = flip subsortsOf sign
    in foldr1 Set.intersection $ map get_subsorts $ srts
    -- in (foldr Set.intersection Set.empty) . (map get_subsorts)

{-----------------------------------------------------------
    Set of SuperSORTs common to all given SORTs
-----------------------------------------------------------}
common_supersorts :: 
                Sign f e -> [SORT] -> Set.Set SORT
common_supersorts _ [] = Set.empty
common_supersorts sign srts = let
    get_supersorts = flip supersortsOf sign
    in foldr1 Set.intersection $ map get_supersorts $ srts

{-----------------------------------------------------------
    True if all SORTs have a common subSORT
-----------------------------------------------------------}
have_common_subsorts :: 
                Sign f e -> [SORT] -> Bool
have_common_subsorts s = (not . Set.isEmpty . common_subsorts s)

{-----------------------------------------------------------
    True if all SORTs have a common superSORT
-----------------------------------------------------------}
have_common_supersorts :: 
                Sign f e -> [SORT] -> Bool
have_common_supersorts s = (not . Set.isEmpty . common_supersorts s)

{-----------------------------------------------------------
    True if s1 <= s2 OR s1 >= s2
-----------------------------------------------------------}
xeq_SORT :: 
                Sign f e -> SORT -> SORT -> Bool
xeq_SORT sign s1 s2 = (leq_SORT sign s1 s2) || (geq_SORT sign s1 s2)

{-----------------------------------------------------------
    True if s1 <= s2 OR s1 >= s2
-----------------------------------------------------------}
xeq_TUPLE :: 
                Sign f e -> (a, SORT) -> (a, SORT) -> Bool
xeq_TUPLE sign (_,s1) (_,s2) = xeq_SORT sign s1 s2

{-----------------------------------------------------------
    True if s1 <= s2
-----------------------------------------------------------}
leq_SORT :: 
                Sign f e -> SORT -> SORT -> Bool
leq_SORT sign s1 s2 = Set.member s2 (supersortsOf s1 sign)
-- leq_SORT = (flip Set.member) . (flip supersortsOf)

{-----------------------------------------------------------
    True if s1 >= s2
-----------------------------------------------------------}
geq_SORT :: 
                Sign f e -> SORT -> SORT -> Bool
geq_SORT sign s1 s2 = Set.member s2 (subsortsOf s1 sign)
-- geq_SORT = (flip Set.member) . (flip subsortsOf)

{-----------------------------------------------------------
    True if o1 ~F o2
-----------------------------------------------------------}
leqF :: 
                Sign f e -> OpType -> OpType -> Bool
leqF sign o1 o2 = zipped_all are_legal (opArgs o1) (opArgs o2)
                && have_common_supersorts sign [(opRes o1), (opRes o2)]
    where are_legal a b = have_common_subsorts sign [a, b]
            
{-----------------------------------------------------------
    True if p1 ~P p2
-----------------------------------------------------------}
leqP :: 
                Sign f e -> PredType -> PredType -> Bool
leqP sign p1 p2 = zipped_all are_legal (predArgs p1) (predArgs p2)
    where are_legal a b = have_common_subsorts sign [a, b]

{-

Die alten SML-Funktionen, die hier verwandt wurden.
Den Beschreibungen nach sind das genau die beiden, mit denen eine Menge in
Aequivalenzklassen unterteilt wird.
Wie die erste davon funktioniert, ist mir nicht offen ersichtlich,
aber vielleicht brauch ich die eigentlich auch gar nicht?

(* Compute the connected compenents of a graph which is given
   by a list of nodes and a boolean function indicating whether
   there is an egde between two nodes.
   For each node, the algorithm splits the connected components
   which have been computed so far into two categories:
   those which are connected to the node and those which are not.
   The former are all linked with @ in order to form a new connected
   component, the latter are left untouched. *)
     			 
fun compute_conn_components (edges:'a*'a->bool) (nodes:'a list):'a list list =
  let
    fun is_connected(node,nil) = false
      | is_connected(node,n::c) = 
          edges(node,n) orelse edges(n,node) orelse is_connected(node,c)
    fun split_components(node,nil,acc_comp_of_node,acc_other_comps) = 
    	(node::acc_comp_of_node)::acc_other_comps
      | split_components(node,current_comp::
             other_comps,acc_comp_of_node,acc_other_comps) =
        if is_connected(node,current_comp)
        then split_components(node,other_comps,
	     current_comp@acc_comp_of_node,acc_other_comps)
        else split_components(node,other_comps,acc_comp_of_node,
             current_comp::acc_other_comps)
    fun add_node (node:'a,components:'a list list):'a list list =
        split_components(node,components,nil,nil)
  in
  foldr add_node (nodes,[])
  end 

(* Compute the equivalence classes of the equivalence closures of leqF
   and leqP resp.  and store them in a table indexed by function and
   predicate names, resp.  This is needed when checking if terms or
   predications are equivalent, since this equivalence is defined in
   terms of the equivalence closures of leqF and leqP resp. *)


     			 
fun get_conn_components (env:local_env) : local_env1 =
	let
	    val (srts,vars,funs,preds) = env
	in
	    (env,(Symtab_id.map (compute_conn_components (leqF env)) funs ,
	          Symtab_id.map (compute_conn_components (leqP env)) preds) )
	end

-}

