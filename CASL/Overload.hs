{- | 
   
    Module      :  $Header$
    Copyright   :  (c)  Martin Kühl and Till Mossakowski and Uni Bremen 2003
    Licence     :  similar to LGPL, see HetCATS/LICENCE.txt or LIZENZ.txt

    Maintainer  :  hets@tzi.de
    Stability   :  provisional
    Portability :  portable

    Overload resolution

-}

-- does anyone ever need anything else from me?
module CASL.Overload (
    overloadResolution          -- :: Sign -> [FORMULA] -> Result [FORMULA]
    ) where

import CASL.Sign                -- Sign, OpType
import CASL.AS_Basic_CASL       -- FORMULA, OP_{NAME,SYMB}, TERM, SORT, VAR
import Common.Result            -- Result

import qualified Common.Lib.Map as Map
import qualified Common.Lib.Set as Set
import qualified Common.Id      as Id
import qualified Common.Named   as Named

import Data.List                ( partition )

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
-}

{-----------------------------------------------------------
    Overload Resolution
-----------------------------------------------------------}
overloadResolution      :: Sign -> [Named.Named FORMULA]
                        -> Result [Named.Named FORMULA]
overloadResolution sign  = mapM overload
    where
        overload :: (Named.Named FORMULA) -> Result (Named.Named FORMULA)
        overload sent = do
            sent'       <- return $ Named.sentence sent
            exp_sent    <- minExpFORMULA sign sent'
            return sent { Named.sentence = exp_sent }

{-----------------------------------------------------------
    Minimal Expansions of a FORMULA
-----------------------------------------------------------}
minExpFORMULA :: Sign -> FORMULA -> Result FORMULA
minExpFORMULA sign formula
    = case formula of
        -- Trivial Atom         -> Return untouched
        True_atom _     -> return formula                       -- :: FORMULA
        False_atom _    -> return formula                       -- :: FORMULA
        -- Atomic FORMULA      -> Check for Ambiguities
        Predication predicate terms pos ->
            minExpFORMULA_pred sign predicate terms pos         -- :: FORMULA
        Definedness term pos            -> do
            t   <- minExpTerm sign term                         -- :: [[TERM]]
            t'  <- is_unambiguous t                             -- :: TERM
            return $ Definedness t' pos                         -- :: FORMULA
	Quantification q vars formula' pos -> do
	    f <- minExpFORMULA sign formula'
	    return $ Quantification q vars f pos
	Existl_equation term1 term2 pos ->
            minExpFORMULA_eq sign Existl_equation term1 term2 pos
        Strong_equation term1 term2 pos ->
            minExpFORMULA_eq sign Strong_equation term1 term2 pos
        Membership term sort pos        -> do
            t   <- minExpTerm sign term                         -- :: [[TERM]]
            t'  <- return
                $ filter (                                      -- :: [[TERM]]
                    (geq_SORT sign sort)                        -- :: Bool
                    . term_sort                                 -- :: SORT
                    . head) t                                   -- :: TERM
            t'' <- is_unambiguous t'                            -- :: [[TERM]]
            return $ Membership t'' sort pos                    -- :: FORMULA
        -- Unparsed FORMULA    -> Error in Parser, Bail out!
        Mixfix_formula term             -> error
            $ "Parser Error: Unparsed `Mixfix_formula' received: "
            ++ (show term)
        Unparsed_formula string _       -> error
            $ "Parser Error: Unparsed `Unparsed_formula' received: "
            ++ (show string)
        -- "Other" FORMULA     -> Unknown Error, Bail out!
        _                               -> error
            $ "Internal Error: Unknown type of FORMULA received: "
            ++ (show formula)
    where
        is_unambiguous          :: [[TERM]] -> Result TERM
        is_unambiguous term      = do
            case term of
                [_]     -> return $ head $ head term            -- :: TERM
                _       -> error
                    $ "Cannot disambiguate! Possible Expansions: "
                    ++ (show term)

{-----------------------------------------------------------
    Minimal Expansions of a Predicate Application Formula
-----------------------------------------------------------}
minExpFORMULA_pred :: Sign -> PRED_SYMB -> [TERM] -> [Id.Pos] -> Result FORMULA
minExpFORMULA_pred sign predicate terms pos = do
    expansions          <- mapM
        (minExpTerm sign) terms                 -- ::        [[[TERM]]]
    permuted_exps       <- return
        $ permute expansions                    -- ::        [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[(PredType, [TERM])]]
    p                   <- return
        $ concat                                -- ::  [[(PredType, [TERM])]]
        $ map (equivalence_Classes pred_eq)     -- :: [[[(PredType, [TERM])]]]
          profiles                              -- ::  [[(PredType, [TERM])]]
    p'                  <- return $ choose p    -- ::    (PredType, [TERM])
    return $ qualify_pred p'
    where
        name            :: PRED_NAME
        name             = pred_name predicate
        preds           :: [PredType]
        preds            = Set.toList
            $ Map.find name $ (predMap sign)
        pred_name       :: PRED_SYMB -> PRED_NAME
        pred_name pred'  = case pred' of
            (Pred_name name')           -> name'
            (Qual_pred_name name' _ _)  -> name'
        choose          :: [[(PredType, [TERM])]] -> (PredType, [TERM])
        choose ps        = case ps of
            [_] -> head $ head ps
            _   -> error
                $ "Cannot disambiguate! Term: " ++ (show (predicate, terms))
                ++ "\n  Possible Expansions: " ++ (show ps)
        qualify_pred    :: (PredType, [TERM]) -> FORMULA
        qualify_pred (pred', terms')
            = (Predication                                      -- :: FORMULA
                (Qual_pred_name name (toPRED_TYPE pred') [])    -- :: PRED_SYMB
                terms'                                          -- :: [TERM]
                pos)                                            -- :: [Pos]
        get_profile     :: [[TERM]] -> [(PredType, [TERM])]
        get_profile cs
            = [ (pred', ts) |
                pred' <- preds,                                 -- :: PredType
                ts <- (permute cs),                             -- ::  [TERM]
                zipped_all (leq_SORT sign)                      -- ::   Bool
                    (map term_sort ts)                          -- ::  [SORT]
                    (predArgs pred') ]                          -- ::  [SORT]
        pred_eq         :: (PredType, [TERM]) -> (PredType, [TERM]) -> Bool
        pred_eq (pred1,ts1) (pred2,ts2)
            = let   w1 = predArgs pred1                         -- :: [SORT]
                    w2 = predArgs pred2                         -- :: [SORT]
                    s1 = map term_sort ts1                      -- :: [SORT]
                    s2 = map term_sort ts2                      -- :: [SORT]
                    b1 = zipped_all (leq_SORT sign) s1 w1       -- ::  Bool
                    b2 = zipped_all (leq_SORT sign) s2 w2       -- ::  Bool
                    preds_equal = (pred1 == pred2)              -- ::  Bool
                    preds_equiv = leqP sign pred1 pred2         -- ::  Bool
                    types_equal = and ( zipWith (==) ts1 ts2 )  -- ::  Bool
                in b1 && b2 && (preds_equal || (preds_equiv && types_equal))

{-----------------------------------------------------------
    Minimal Expansions of a Strong/Existl. Equation Formula
-----------------------------------------------------------}
minExpFORMULA_eq :: Sign -> (TERM -> TERM -> [Id.Pos] -> FORMULA)
                    -> TERM -> TERM -> [Id.Pos] -> Result FORMULA
minExpFORMULA_eq sign eq term1 term2 pos = do
    exps1       <- minExpTerm sign term1                -- :: [[TERM]]
    exps2       <- minExpTerm sign term2                -- :: [[TERM]]
    pairs       <- return
        $ permute [(map head exps1), (map head exps2)]  -- :: [[TERM]]
    candidates  <- return
        $ filter fit pairs                              -- :: [[TERM]]
    case candidates of
        [[t1,t2]]       -> return $ eq t1 t2 pos
        _               -> error
            $ "Cannot disambiguate! Possible Expansions: "
            ++ (show exps1) ++ "\n\t" ++ (show exps2)
    where
        fit     :: [TERM] -> Bool
        fit      = (have_common_supersorts sign) . (map term_sort)

{-----------------------------------------------------------
    Minimal Expansions of a TERM
-----------------------------------------------------------}
minExpTerm :: Sign -> TERM -> Result [[TERM]]
minExpTerm sign term'
    = case term' of
        Simple_id var
            -> minExpTerm_simple sign var
        Qual_var var sort pos
            -> minExpTerm_qual sign var sort pos
        Application op terms pos
            -> minExpTerm_op sign op terms pos
        Sorted_term term sort pos
            -> minExpTerm_sorted sign term sort pos
        Cast term sort pos
            -> minExpTerm_cast sign term sort pos
        Conditional term1 formula term2 pos
            -> minExpTerm_cond sign term1 formula term2 pos
        Unparsed_term string _
            -> error $ "minExpTerm: Parser Error - Unparsed `Unparsed_term' "
               ++ string
        _   -> error $ "minExpTerm: Parser Error - Unparsed `Mixfix' term "
               ++ (show term')

{-----------------------------------------------------------
    Minimal Expansions of a Simple_id Term
-----------------------------------------------------------}
minExpTerm_simple :: Sign -> Id.SIMPLE_ID -> Result [[TERM]]
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
        $ Set.filter (is_least_sort cs) cs      -- :: Set.Set SORT
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
        pair_with_id            :: SORT -> (TERM, SORT)
        pair_with_id sort        = ((Simple_id var), sort)

{-----------------------------------------------------------
    Minimal Expansions of a Qual_var Term
-----------------------------------------------------------}
minExpTerm_qual :: Sign -> VAR -> SORT -> [Id.Pos] -> Result [[TERM]]
minExpTerm_qual sign var sort pos = do
    expandedVar <- minExpTerm_simple sign var   -- :: [[TERM]]
    return
        $ qualifyTerms pos                      -- :: [[TERM]]
        $ map selectExpansions expandedVar      -- :: [[(TERM, SORT)]]
    where
        fits                    :: TERM -> Bool
        fits term                = case term of
            (Sorted_term (Simple_id var') sort' _)
                -> (var == var') && (sort == sort')
            _   -> error "minExpTerm: unsorted TERM after expansion"
        selectExpansions        :: [TERM] -> [(TERM, SORT)]
        selectExpansions c
            = [ ((Simple_id var), sort) |       -- :: (TERM, SORT)
                sorted <- c,                    -- :: TERM
                fits sorted ]                   -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Sorted_term Term
-----------------------------------------------------------}
minExpTerm_sorted :: Sign -> TERM -> SORT -> [Id.Pos] -> Result [[TERM]]
minExpTerm_sorted sign term sort pos = do
    expandedTerm <- minExpTerm sign term        -- :: [[TERM]]
    return
        $ qualifyTerms pos                      -- :: [[TERM]]
        $ map selectExpansions expandedTerm     -- :: [[(TERM, SORT)]]
    where
        fits                    :: TERM -> Bool
        fits term'               = case term' of
            (Sorted_term term'' sort' _)
                -> (term == term'') && (sort == sort')
            _   -> error "minExpTerm: unsorted TERM after expansion"
        selectExpansions        :: [TERM] -> [(TERM, SORT)]
        selectExpansions c
            = [ (term, sort) |                  -- :: (TERM, SORT)
                sorted <- c,                    -- :: TERM
                fits sorted ]                   -- :: Bool

{-----------------------------------------------------------
    Minimal Expansions of a Function Application Term
-----------------------------------------------------------}
minExpTerm_op :: Sign -> OP_SYMB -> [TERM] -> [Id.Pos] -> Result [[TERM]]
minExpTerm_op sign op terms pos = do
    expansions          <- mapM
        (minExpTerm sign) terms                 -- ::       [[[TERM]]]
    permuted_exps       <- return
        $ permute expansions                    -- ::       [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[(OpType, [TERM])]]
    p                   <- return
        $ concat                                -- ::  [[(OpType, [TERM])]]
        $ map (equivalence_Classes op_eq)       -- :: [[[(OpType, [TERM])]]]
          profiles                              -- ::  [[(OpType, [TERM])]]
    p'                  <- return
        $ map (minimize_op sign) p              -- ::  [[(OpType, [TERM])]]
    return
        $ qualifyTerms pos                      -- ::        [[TERM]]
        $ qualifyOps p'                         -- ::    [[(TERM, SORT)]]
    where
        name            :: OP_NAME
        name             = op_name op
        ops             :: [OpType]
        ops              = Set.toList
            $ Map.find name $ (opMap sign)
        op_name         :: OP_SYMB -> OP_NAME
        op_name op'      = case op' of
            (Op_name name')             -> name'
            (Qual_op_name name' _ _)    -> name'
        qualifyOps      :: [[(OpType, [TERM])]] -> [[(TERM, SORT)]]
        qualifyOps       = map (map qualify_op)
        qualify_op      :: (OpType, [TERM]) -> (TERM, SORT)
        qualify_op (op', terms')
            = ((Application                                     -- ::  TERM
                (Qual_op_name name (toOP_TYPE op') [])          -- :: OP_SYMB
                terms'                                          -- :: [TERM]
                [])                                             -- :: [Pos]
              , (opRes op'))                                    -- ::  SORT
        get_profile     :: [[TERM]] -> [(OpType, [TERM])]
        get_profile cs
            = [ (op', ts) |                             -- :: (OpType, [TERM])
                op'     <- ops,                         -- ::  OpType
                ts      <- (permute cs),                -- ::  [TERM]
                zipped_all (leq_SORT sign)              -- ::   Bool
                    (map term_sort ts)                  -- ::  [SORT]
                    (opArgs op') ]                      -- ::  [SORT]
        op_eq           :: (OpType, [TERM]) -> (OpType, [TERM]) -> Bool
        op_eq (op1,ts1) (op2,ts2)
            = let   w1 = opArgs op1                             -- :: [SORT]
                    w2 = opArgs op2                             -- :: [SORT]
                    s1 = map term_sort ts1                      -- :: [SORT]
                    s2 = map term_sort ts2                      -- :: [SORT]
                    b1 = zipped_all (leq_SORT sign) s1 w1       -- ::  Bool
                    b2 = zipped_all (leq_SORT sign) s2 w2       -- ::  Bool
                    ops_equal = (op1 == op2)                    -- ::  Bool
                    ops_equiv = leqF sign op1 op2               -- ::  Bool
                    types_equal = and ( zipWith (==) ts1 ts2 )  -- ::  Bool
                in b1 && b2 && (ops_equal || (ops_equiv && types_equal))

{-----------------------------------------------------------
    Minimal Expansions of a Cast Term
-----------------------------------------------------------}
minExpTerm_cast :: Sign -> TERM -> SORT -> [Id.Pos] -> Result [[TERM]]
minExpTerm_cast sign term sort pos = do
    expandedTerm        <- minExpTerm sign term         -- :: [[TERM]]
    validExps           <- return
        $ filter (leq_SORT sign sort . term_sort)       -- ::  [TERM]
        $ map head expandedTerm                         -- ::  [TERM]
    return
        $ qualifyTerms pos                              -- :: [[TERM]]
        $ [map (\ t -> (t, sort)) validExps]            -- :: [[(TERM, SORT)]]

{-----------------------------------------------------------
    Minimal Expansions of a Conditional Term
-----------------------------------------------------------}
minExpTerm_cond :: Sign -> TERM -> FORMULA -> TERM -> [Id.Pos]
                -> Result [[TERM]]
minExpTerm_cond sign term1 formula term2 pos = do
    expansions1
        <- minExpTerm sign term1                -- ::       [[TERM]]
    expansions2
        <- minExpTerm sign term2                -- ::       [[TERM]]
    expanded_formula
        <- minExpFORMULA sign formula           -- ::       FORMULA
    permuted_exps       <- return
        $ permute [expansions1, expansions2]    -- ::      [[[TERM]]]
    profiles            <- return
        $ map get_profile permuted_exps         -- ::  [[([TERM], SORT)]]
    p                   <- return
        $ concat                                -- ::  [[([TERM], SORT)]]
        $ map                                   -- :: [[[([TERM], SORT)]]]
          (equivalence_Classes eq)
          profiles                              -- ::  [[([TERM], SORT)]]
    p'                  <- return
        $ map (minimize_cond sign) p            -- ::  [[([TERM], SORT)]]
    return
        $ qualifyTerms pos                      -- ::       [[TERM]]
        $ qualifyConds expanded_formula p'      -- ::   [[(TERM, SORT)]]
    where
        have_supersort          :: [TERM] -> Bool
        have_supersort           = not . Set.isEmpty . supersorts
        supersorts              :: [TERM] -> Set.Set SORT
        supersorts               = common_supersorts sign . map term_sort
        eq                       = xeq_TUPLE sign
        qualifyConds            :: FORMULA -> [[([TERM], SORT)]] -> [[(TERM, SORT)]]
        qualifyConds f           = map $ map (qualify_cond f)
        qualify_cond            :: FORMULA -> ([TERM], SORT) -> (TERM, SORT)
        qualify_cond f (ts, s)   = case ts of
            [t1, t2]    -> (Conditional t1 f t2 [], s)
            _           -> error
                $ "Internal Error: wrong number of TERMs in qualify_cond!"
        get_profile             :: [[TERM]] -> [([TERM], SORT)]
        get_profile cs
            = [ (c, s) |                                -- :: ([TERM], SORT)
                c <- cs,                                -- ::  [TERM]
                have_supersort c,                       -- ::   Bool
                s <- Set.toList $ supersorts c ]        -- ::   SORT

{-----------------------------------------------------------
    Divide a Set (List) into equivalence classes w.r. to eq
-----------------------------------------------------------}
-- also look below for Till's SML-version of this
equivalence_Classes         :: (a -> a -> Bool) -> [a] -> [[a]]
equivalence_Classes _ []     = []
equivalence_Classes eq (x:l) = xs':(equivalence_Classes eq ys)
    where
        (xs, ys) = partition (eq x) l
        xs'      = (x:xs)

{-----------------------------------------------------------
    Transform a list [l1,l2, ... ln] to (in sloppy notation)
    [[x1,x2, ... ,xn] | x1<-l1, x2<-l2, ... xn<-ln]
-----------------------------------------------------------}
permute      :: [[a]] -> [[a]]
permute []    = [[]]
permute [x]   = map (\y -> [y]) x
permute (x:l) = concat (map (distribute (permute l)) x)
    where
        distribute perms y = map ((:) y) perms

{-----------------------------------------------------------
    Like 'and (zipWith p as bs)',
    but must return False if lengths don't match
-----------------------------------------------------------}
zipped_all                :: (a -> b -> Bool) -> [a] -> [b] -> Bool
zipped_all _ []     []     = True
zipped_all p (a:as) (b:bs) = (p a b) && (zipped_all p as bs)
zipped_all _  _      _     = False

{-----------------------------------------------------------
    Construct a TERM of type Sorted_term
    from each (TERM, SORT) tuple
-----------------------------------------------------------}
qualifyTerms            :: [Id.Pos] -> [[(TERM, SORT)]] -> [[TERM]]
qualifyTerms pos pairs   = map (map qualify_term) pairs
    where
        qualify_term       :: (TERM, SORT) -> TERM
        qualify_term (t, s) = Sorted_term t s pos

{-----------------------------------------------------------
    For each C in P (see above), let C' choose _one_
    f:s \in C for each s minimal such that f:s \in C
-----------------------------------------------------------}
minimize_op :: Sign -> [(OpType, [TERM])] -> [(OpType, [TERM])]
minimize_op sign ops_n_terms
    = concat $ map reduce ops_n_terms
    where
        results         :: Set.Set SORT
        results          = Set.fromList (map (opRes . fst) ops_n_terms)
        lesserSorts     :: SORT -> Set.Set SORT
        lesserSorts s    = Set.intersection results (subsortsOf s sign)
        leastSort       :: SORT -> Bool
        leastSort s      = Set.size (lesserSorts s) == 1
        reduce          :: (OpType, [TERM]) -> [(OpType, [TERM])]
        reduce x@(op,_)  = if (leastSort (opRes op)) then [x] else []

{-----------------------------------------------------------
    Workalike for minimize_op, but used inside m_e_t_cond
-----------------------------------------------------------}
minimize_cond :: Sign -> [([TERM], SORT)] -> [([TERM], SORT)]
minimize_cond sign terms_n_sort
    = concat $ map reduce terms_n_sort
    where
        sorts           :: Set.Set SORT
        sorts            = Set.fromList (map snd terms_n_sort)
        lesserSorts     :: SORT -> Set.Set SORT
        lesserSorts s    = Set.intersection sorts (subsortsOf s sign)
        leastSort       :: SORT -> Bool
        leastSort s      = Set.size (lesserSorts s) == 1
        reduce          :: ([TERM], SORT) -> [([TERM], SORT)]
        reduce x@(_,s)   = if (leastSort s) then [x] else []

term_sort       :: TERM -> SORT
term_sort term'  = case term' of
    (Sorted_term _ sort _ )     -> sort
    _                           -> error                -- unlikely
        "minExpTerm: unsorted TERM after expansion"

{-----------------------------------------------------------
    Set of SubSORTs common to all given SORTs
-----------------------------------------------------------}
common_subsorts :: Sign -> [SORT] -> Set.Set SORT
common_subsorts sign = let
    get_subsorts = flip subsortsOf sign
    in (foldr Set.intersection Set.empty) . (map get_subsorts)

{-----------------------------------------------------------
    Set of SuperSORTs common to all given SORTs
-----------------------------------------------------------}
common_supersorts :: Sign -> [SORT] -> Set.Set SORT
common_supersorts sign = let
    get_supersorts = flip supersortsOf sign
    in (foldr Set.intersection Set.empty) . (map get_supersorts)

{-----------------------------------------------------------
    True if all SORTs have a common subSORT
-----------------------------------------------------------}
have_common_subsorts :: Sign -> [SORT] -> Bool
have_common_subsorts s = (not . Set.isEmpty . common_subsorts s)

{-----------------------------------------------------------
    True if all SORTs have a common superSORT
-----------------------------------------------------------}
have_common_supersorts :: Sign -> [SORT] -> Bool
have_common_supersorts s = (not . Set.isEmpty . common_supersorts s)

{-----------------------------------------------------------
    True if s1 <= s2 OR s1 >= s2
-----------------------------------------------------------}
xeq_SORT :: Sign -> SORT -> SORT -> Bool
xeq_SORT sign s1 s2 = (leq_SORT sign s1 s2) || (geq_SORT sign s1 s2)

{-----------------------------------------------------------
    True if s1 <= s2 OR s1 >= s2
-----------------------------------------------------------}
xeq_TUPLE :: Sign -> (a, SORT) -> (a, SORT) -> Bool
xeq_TUPLE sign (_,s1) (_,s2) = xeq_SORT sign s1 s2

{-----------------------------------------------------------
    True if s1 <= s2
-----------------------------------------------------------}
leq_SORT :: Sign -> SORT -> SORT -> Bool
leq_SORT sign s1 s2 = Set.member s2 (supersortsOf s1 sign)
-- leq_SORT = (flip Set.member) . (flip supersortsOf)

{-----------------------------------------------------------
    True if s1 >= s2
-----------------------------------------------------------}
geq_SORT :: Sign -> SORT -> SORT -> Bool
geq_SORT sign s1 s2 = Set.member s2 (subsortsOf s1 sign)
-- geq_SORT = (flip Set.member) . (flip subsortsOf)

{-----------------------------------------------------------
    True if o1 ~F o2
-----------------------------------------------------------}
leqF :: Sign -> OpType -> OpType -> Bool
leqF sign o1 o2 = zipped_all are_legal (opArgs o1) (opArgs o2)
                && have_common_supersorts sign [(opRes o1), (opRes o2)]
    where are_legal a b = have_common_subsorts sign [a, b]
            
{-----------------------------------------------------------
    True if p1 ~P p2
-----------------------------------------------------------}
leqP :: Sign -> PredType -> PredType -> Bool
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
      | split_components(node,current_comp::other_comps,acc_comp_of_node,acc_other_comps) =
        if is_connected(node,current_comp)
        then split_components(node,other_comps,current_comp@acc_comp_of_node,acc_other_comps)
        else split_components(node,other_comps,acc_comp_of_node,current_comp::acc_other_comps)
    fun add_node (node:'a,components:'a list list):'a list list =
        split_components(node,components,nil,nil)
  in
  foldr add_node (nodes,[])
  end 

(* Compute the equivalence classes of the equivalence closures of leqF and leqP resp.
   and store them in a table indexed by function and predicate names, resp.
   This is needed when checking if terms or predications are equivalent, since
   this equivalence is defined in terms of  the equivalence closures of leqF and leqP resp. *)


     			 
fun get_conn_components (env:local_env) : local_env1 =
	let
		val (srts,vars,funs,preds) = env
	in
		(env,(Symtab_id.map (compute_conn_components (leqF env)) funs ,
		      Symtab_id.map (compute_conn_components (leqP env)) preds) )
	end

-}

